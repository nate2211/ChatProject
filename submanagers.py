from __future__ import annotations

import asyncio
import collections  # For collections.Counter
import hashlib
import math
import os
import re
import sqlite3
import ssl
import threading
import time
import zlib
from dataclasses import dataclass, field, fields
from html.parser import HTMLParser
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Sequence, Iterable
from urllib.parse import urlparse, urljoin, parse_qsl, urlencode, urlunparse
import random  # For random delays
import json  # For JSON parsing in NetworkSniffer and JSSniffer
import xml.etree.ElementTree as ET

import aiohttp
from aiohttp import ClientTimeout
from bs4 import BeautifulSoup

from loggers import DEBUG_LOGGER

try:
    from playwright.async_api import BrowserContext, Response, Page, Request, async_playwright
except ImportError:  # allow import in non-PW envs
    print("Playwright not installed. Some features will be unavailable.")
    BrowserContext = Response = Page = Request = async_playwright = None

# --- Common Utilities (Moved from VideoLinkTrackerBlock for self-containment) ---
_STOPWORDS = {
    "a", "an", "the", "and", "or", "but", "about", "above", "after", "again", "against",
    "all", "am", "an", "and", "any", "are", "as", "at", "be", "because", "been", "before",
    "being", "below", "between", "both", "by", "can", "did", "do", "does", "doing",
    "down", "during", "each", "few", "for", "from", "further", "had", "has", "have",
    "having", "he", "her", "here", "hers", "herself", "him", "himself", "his", "how",
    "i", "if", "in", "into", "is", "it", "its", "itself", "just", "me", "more", "most",
    "my", "myself", "no", "nor", "not", "now", "of", "off", "on", "once", "only", "or",
    "other", "our", "ours", "ourselves", "out", "over", "own", "s", "same", "she",
    "should", "so", "some", "such", "t", "than", "that", "their", "theirs", "them",
    "themselves", "then", "there", "these", "they", "this", "those", "through", "to",
    "too", "under", "until", "up", "very", "was", "we", "were", "what", "when", "where",
    "which", "while", "who", "whom", "why", "will", "with", "you", "your", "yours",
    "yourself", "yourselves"
}

_VOLATILE_QS = {
    "ui", "psid", "token", "sig", "signature", "expires", "expire",
    "download", "dl", "session", "sess", "key", "auth", "utm_source",
    "utm_medium", "utm_campaign", "utm_term", "utm_content", "ref", "referrer",
}


def _canonicalize_url(u: str) -> str:
    """
    Canonicalize a URL by stripping volatile query parameters and normalizing host.
    This helps in deduplication.
    """
    try:
        pu = urlparse(u)
        host = pu.netloc.lower().split(":")[0]

        # Optional: drop typical CDN sharding prefix if you want
        # host = re.sub(r"^(cdn\d+|cdn\d+-vid)\.", "cdn.", host)

        # strip volatile query params
        qs = parse_qsl(pu.query, keep_blank_values=False)
        qs = [(k, v) for k, v in qs if k.lower() not in _VOLATILE_QS]

        new_query = urlencode(qs, doseq=True)
        return urlunparse((pu.scheme, host, pu.path, pu.params, new_query, ""))

    except Exception:
        return u


# ======================================================================
# NetworkSniffer
# ======================================================================

class NetworkSniffer:
    """
    Advanced Playwright network sniffer for VIDEO + AUDIO + IMAGES
    + Evidence collection
    + URL salvage (token stripping / path-only / origin swapping + probing)

    FIX: "Cannot mix str and non-str arguments" (urllib.parse) happens when *any*
    bytes / non-str object leaks into urlparse/urlunparse/urljoin/urlencode/parse_qsl.
    This version wraps *all* URL plumbing with hard str-normalization.

    Rewrite goals (this patch):
      1) Salvage is **less noisy** while still effective:
           - Only salvage URLs that look like they *need* salvage
           - Score + pick best targets (not “everything”)
           - Stop probing early once a good variant is found
           - Quiet logging by default (configurable)
      2) Salvage is **more programmatic**, not just a static list:
           - Learn “signature-ish” params by key + value heuristics (entropy/length/base64/hex)
           - Generate host swap variants via rules (cf-/cdn-/i1..i9)
           - Generate query simplifications via heuristics

    Return:
      (html: str, merged_items: list[dict[str,str]], json_hits: list[dict[str,Any]])
    """

    # ---------------------------- minimal internal deps ---------------------------- #
    from dataclasses import dataclass, field
    from typing import Any, Dict, List, Optional, Set, Tuple
    import asyncio, json, re, hashlib, time
    from urllib.parse import urlparse, urlunparse, urlencode, parse_qsl, urljoin

    try:
        import xml.etree.ElementTree as ET
    except Exception:  # pragma: no cover
        ET = None

    # ---------------------------- fallback logger ---------------------------- #
    class _FallbackLogger:
        def log_message(self, msg: str) -> None:
            try:
                print(msg)
            except Exception:
                pass

    # ---------------------------- safe string coercion ---------------------------- #
    @staticmethod
    def _to_str(x: Any) -> str:
        """Coerce possibly-bytes / URL objects / odd objects into str."""
        if x is None:
            return ""
        if isinstance(x, str):
            return x
        if isinstance(x, (bytes, bytearray, memoryview)):
            b = bytes(x)
            try:
                return b.decode("utf-8", "ignore")
            except Exception:
                try:
                    return b.decode("latin-1", "ignore")
                except Exception:
                    return ""
        try:
            return str(x)
        except Exception:
            return ""

    # ---------------------------- "safe urllib" wrappers ---------------------------- #
    @classmethod
    def _safe_urlparse(cls, url: Any):
        return cls.urlparse(cls._to_str(url))

    @classmethod
    def _safe_urlunparse(cls, parts) -> str:
        try:
            a, b, c, d, e, f = parts
            return cls.urlunparse((
                cls._to_str(a), cls._to_str(b), cls._to_str(c),
                cls._to_str(d), cls._to_str(e), cls._to_str(f),
            ))
        except Exception:
            try:
                return cls._to_str(cls.urlunparse(parts))
            except Exception:
                return ""

    @classmethod
    def _safe_urljoin(cls, base: Any, url: Any) -> str:
        try:
            return cls.urljoin(cls._to_str(base), cls._to_str(url))
        except Exception:
            b = cls._to_str(base).rstrip("/")
            u = cls._to_str(url).lstrip("/")
            return f"{b}/{u}" if b and u else (b or u)

    @classmethod
    def _safe_parse_qsl(cls, query: Any) -> List[Tuple[str, str]]:
        out: List[Tuple[str, str]] = []
        try:
            for k, v in cls.parse_qsl(cls._to_str(query), keep_blank_values=True):
                out.append((cls._to_str(k), cls._to_str(v)))
        except Exception:
            pass
        return out

    @classmethod
    def _safe_urlencode(cls, pairs: List[Tuple[Any, Any]]) -> str:
        try:
            norm = [(cls._to_str(k), cls._to_str(v)) for (k, v) in (pairs or [])]
            return cls.urlencode(norm, doseq=True)
        except Exception:
            return ""

    # ---------------------------- canonicalize ---------------------------- #
    _TRACKING_KEYS = {
        "utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
        "utm_id", "utm_name", "utm_reader", "utm_viz_id",
        "gclid", "dclid", "gbraid", "wbraid", "fbclid", "msclkid", "ttclid", "twclid", "yclid",
        "mc_cid", "mc_eid",
    }

    @classmethod
    def _canonicalize_url(cls, url: Any) -> str:
        """Light canonicalization: scheme/host lower, drop fragments, drop tracking params."""
        u = cls._to_str(url).strip()
        if not u:
            return ""
        try:
            p = cls._safe_urlparse(u)
            scheme = cls._to_str(p.scheme).lower()
            netloc = cls._to_str(p.netloc).lower()
            path = cls._to_str(p.path)
            params = cls._to_str(p.params)

            kept: List[Tuple[str, str]] = []
            for k, v in cls._safe_parse_qsl(p.query):
                if cls._to_str(k).lower() in cls._TRACKING_KEYS:
                    continue
                kept.append((cls._to_str(k), cls._to_str(v)))

            query = cls._safe_urlencode(kept)
            return cls._safe_urlunparse((scheme, netloc, path, params, query, ""))  # drop fragment
        except Exception:
            return u

    # ---------------------------- config ---------------------------- #
    @dataclass
    class Config:
        timeout: float = 8.0
        max_items: int = 250
        max_json_hits: int = 150

        max_derived_per_manifest: int = 200
        max_manifests_to_expand: int = 10

        accept_unknown_streams: bool = True

        # auto-scroll
        enable_auto_scroll: bool = True
        max_scroll_steps: int = 20
        scroll_step_delay_ms: int = 400
        scroll_back_to_top: bool = False

        goto_wait_until: str = "domcontentloaded"

        # host filters
        enable_host_allowlist: bool = False
        host_allow_substrings: Set[str] = field(default_factory=set)

        enable_host_denylist: bool = False
        host_deny_substrings: Set[str] = field(default_factory=set)

        # extensions
        video_extensions: Set[str] = field(default_factory=lambda: {
            ".mp4", ".webm", ".mkv", ".mov", ".avi", ".flv", ".wmv",
            ".m3u8", ".mpd", ".ts", ".3gp", ".m4v", ".f4v", ".ogv", ".m4s"
        })
        audio_extensions: Set[str] = field(default_factory=lambda: {
            ".mp3", ".m4a", ".aac", ".flac", ".ogg", ".opus", ".wav",
            ".weba", ".alac", ".aiff", ".wma"
        })
        image_extensions: Set[str] = field(default_factory=lambda: {
            ".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".svg",
            ".avif", ".heic", ".heif", ".tiff"
        })
        junk_extensions: Set[str] = field(default_factory=lambda: {
            ".js", ".css", ".json", ".html", ".woff", ".woff2", ".ttf", ".map", ".vtt", ".srt"
        })

        # content-types
        video_prefixes: Set[str] = field(default_factory=lambda: {"video/"})
        audio_prefixes: Set[str] = field(default_factory=lambda: {"audio/"})
        image_prefixes: Set[str] = field(default_factory=lambda: {"image/"})
        hls_types: Set[str] = field(default_factory=lambda: {
            "application/x-mpegurl", "application/vnd.apple.mpegurl"
        })
        dash_types: Set[str] = field(default_factory=lambda: {
            "application/dash+xml", "application/vnd.mpeg.dash.mpd", "application/xml", "text/xml"
        })

        deny_content_substrings: Set[str] = field(default_factory=lambda: {"javascript", "css", "font/"})
        deny_resource_types: Set[str] = field(default_factory=lambda: {"stylesheet", "font", "manifest", "other"})

        # stream hints
        video_stream_hints: Set[str] = field(default_factory=lambda: {
            ".m3u8", "manifest.mpd", "master.m3u8", "chunklist.m3u8",
            "videoplayback", "dash", "hls", "stream", "cdn",
            "seg-", "segment", "/seg/", "/segments/", "m4s"
        })
        audio_stream_hints: Set[str] = field(default_factory=lambda: {
            "audio", "sound", "stream", ".mp3", ".m4a", ".aac",
            ".flac", ".ogg", ".opus", "weba"
        })

        # ad/tracker
        ad_host_substrings: Set[str] = field(default_factory=lambda: {
            "doubleclick", "googlesyndication", "adservice", "adserver",
            "adsystem", "adnxs", "tracking", "analytics", "metrics",
            "scorecardresearch", "pixel.", "trk.", "stats.", "ad."
        })
        ad_path_keywords: Set[str] = field(default_factory=lambda: {
            "/ads/", "/adserver/", "/banner/", "/promo/", "/tracking/",
            "/click/", "/impression", "/pixel", "/sponsor/", "/advert/"
        })

        # JSON sniff
        enable_json_sniff: bool = True
        json_url_hints: Set[str] = field(default_factory=lambda: {
            "player", "manifest", "api", "metadata", "m3u8", "mpd",
            "playlist", "video", "audio", "graphql"
        })
        json_content_types: Set[str] = field(default_factory=lambda: {
            "application/json", "text/json", "application/problem+json"
        })
        json_body_max_kb: int = 256
        json_url_patterns: Set[str] = field(default_factory=lambda: {
            "/api/player", "/player_api", "/player/",
            "/manifest", "/playlist", "/video/", "/audio/", "/graphql"
        })

        # GraphQL sniff
        enable_graphql_sniff: bool = True
        graphql_endpoint_keywords: Set[str] = field(default_factory=lambda: {"/graphql"})
        graphql_max_body_kb: int = 256

        # header mining
        enable_header_url_mining: bool = True
        max_header_url_events: int = 250
        header_url_keys: Set[str] = field(default_factory=lambda: {
            "location", "link", "content-location", "refresh"
        })

        # redirect tracking
        enable_redirect_tracking: bool = True
        max_redirect_events: int = 200

        # manifest safety
        max_manifest_bytes: int = 512 * 1024
        prefer_master_manifests: bool = True

        # segment heuristics
        enable_segment_heuristics: bool = True
        min_segment_bytes: int = 64 * 1024
        max_segment_bytes: int = 50 * 1024 * 1024
        accept_range_requests_as_media: bool = True

        # forensics
        enable_forensics: bool = True
        max_forensics_events: int = 250
        forensics_body_prefix_bytes: int = 8192
        forensics_hash_via_probe: bool = True
        forensics_probe_timeout_ms: int = 6000
        forensics_include_headers_subset: Set[str] = field(default_factory=lambda: {
            "content-type", "content-length", "content-range", "accept-ranges",
            "etag", "last-modified", "cache-control", "expires",
            "server", "via", "x-cache", "cf-cache-status", "age",
            "location", "content-disposition",
        })
        forensics_include_request_headers_subset: Set[str] = field(default_factory=lambda: {
            "referer", "origin", "range", "user-agent", "accept", "accept-language",
        })

        # ---------------- URL salvage (less-noisy + more programmatic) ----------------
        enable_url_salvage: bool = True

        # target selection (less noisy)
        salvage_max_targets_total: int = 30          # was 80: pick fewer, better
        salvage_max_targets_per_host: int = 8        # avoid hammering one CDN
        salvage_only_if_mediaish: bool = True
        salvage_only_if_suspect: bool = True         # new: require “needs salvage” signal
        salvage_suspect_statuses: Set[int] = field(default_factory=lambda: {401, 403, 404, 410, 416, 429})
        salvage_min_score_to_probe: float = 2.0      # new: score threshold
        salvage_score_bonus_if_signed: float = 2.0
        salvage_score_bonus_if_mediaish: float = 1.0
        salvage_score_bonus_if_segmenty: float = 0.5

        # probing
        salvage_probe_timeout_ms: int = 6500
        salvage_probe_concurrency: int = 6
        salvage_range_bytes: int = 8192

        # output/logging
        salvage_log_level: str = "ok"  # "none" | "ok" | "all"
        salvage_record_non_200: bool = False  # default quieter
        salvage_emit_only_ok_variants_in_bundle: bool = True

        # variant generation caps
        salvage_max_variants_per_url: int = 10
        salvage_max_query_simplify_variants: int = 4
        salvage_max_host_swap_variants: int = 6

        # signature-ish detection seeds (still useful, but not the only guide)
        salvage_strip_query_keys_substrings: Set[str] = field(default_factory=lambda: {
            "token", "expires", "exp", "sig", "signature", "policy", "key-pair-id",
            "x-amz-", "x-goog-", "x-ms-", "hdnts", "acl", "hmac",
            "cdn_hash", "hash", "auth", "authorization", "session",
        })

        # optional static origin swaps (kept), but we also do programmatic swaps
        salvage_origin_swaps: Dict[str, Set[str]] = field(default_factory=lambda: {
            "cf-hls-media.sndcdn.com": {"cf-media.sndcdn.com", "hls-media.sndcdn.com"},
            "media.sndcdn.com": {"cf-media.sndcdn.com"},
            "i1.sndcdn.com": {"i2.sndcdn.com", "i3.sndcdn.com", "i4.sndcdn.com"},
            "lh3.googleusercontent.com": {"lh4.googleusercontent.com", "lh5.googleusercontent.com", "lh6.googleusercontent.com"},
        })

    # ---------------------------- init ---------------------------- #
    def __init__(self, config: Optional["NetworkSniffer.Config"] = None, logger=None, http=None):
        self.cfg = config or self.Config()

        if logger is not None:
            self.logger = logger
        else:
            self.logger = globals().get("DEBUG_LOGGER", None) or self._FallbackLogger()

        self._log("[NetworkSniffer] Initialized (evidence + salvage) [hard str-safe + programmatic salvage]", None)

        self.http= http
        # SoundCloud nudges (optional)
        try:
            self.cfg.video_stream_hints.add("cf-hls-media.sndcdn.com")
            self.cfg.audio_stream_hints.add(".m3u8")
        except Exception:
            pass

    # ---------------------------- logging ---------------------------- #
    def _log(self, msg: Any, log_list: Optional[List[str]]) -> None:
        s = self._to_str(msg)
        try:
            if log_list is not None:
                log_list.append(s)
            if self.logger is not None:
                self.logger.log_message(s)
        except Exception:
            pass

    # ---------------------------- helpers ---------------------------- #
    def _extract_urls_from_text(self, s: Any) -> List[str]:
        s = self._to_str(s)
        if not s:
            return []
        rx = self.re.compile(r"\b(?:https?|wss?)://[^\s\"'<>]+", self.re.IGNORECASE)
        out: List[str] = []
        seen: Set[str] = set()
        for u in rx.findall(s):
            uu = self._to_str(u)
            if uu and uu not in seen:
                seen.add(uu)
                out.append(uu)
        return out

    def _host_allowed(self, url: Any) -> bool:
        try:
            p = self._safe_urlparse(url)
            host = self._to_str(p.netloc).lower()
        except Exception:
            return True

        if self.cfg.enable_host_denylist and self.cfg.host_deny_substrings:
            if any(self._to_str(x).lower() in host for x in self.cfg.host_deny_substrings):
                return False

        if self.cfg.enable_host_allowlist and self.cfg.host_allow_substrings:
            return any(self._to_str(x).lower() in host for x in self.cfg.host_allow_substrings)

        return True

    def _looks_like_ad(self, netloc: str, path: str) -> bool:
        host = (netloc or "").lower()
        p = (path or "").lower()
        if any(sub in host for sub in self.cfg.ad_host_substrings):
            return True
        if any(kw in p for kw in self.cfg.ad_path_keywords):
            return True
        return False

    def _is_junk_by_extension(self, path: str) -> bool:
        p = (path or "").lower()
        return any(p.endswith(ext) for ext in self.cfg.junk_extensions)

    def _deny_by_content_type(self, ctype: str) -> bool:
        ct = (ctype or "").lower()
        return any(bad in ct for bad in self.cfg.deny_content_substrings)

    def _deny_by_resource_type(self, rtype: str) -> bool:
        rt = (rtype or "").lower()
        return rt in self.cfg.deny_resource_types

    def _classify_by_extension(self, path: str) -> Optional[str]:
        p = (path or "").lower()
        if any(p.endswith(ext) for ext in self.cfg.video_extensions):
            return "video"
        if any(p.endswith(ext) for ext in self.cfg.audio_extensions):
            return "audio"
        if any(p.endswith(ext) for ext in self.cfg.image_extensions):
            return "image"
        return None

    def _classify_by_content_type(self, ctype: str) -> Optional[str]:
        ct = (ctype or "").lower()
        if any(ct.startswith(pfx) for pfx in self.cfg.video_prefixes):
            return "video"
        if ct in self.cfg.hls_types or ct in self.cfg.dash_types:
            return "video"
        if any(ct.startswith(pfx) for pfx in self.cfg.audio_prefixes):
            return "audio"
        if any(ct.startswith(pfx) for pfx in self.cfg.image_prefixes):
            return "image"
        return None

    def _classify_by_stream_hint(self, url_lower: str) -> Optional[str]:
        if any(h in url_lower for h in self.cfg.video_stream_hints):
            return "video"
        if any(h in url_lower for h in self.cfg.audio_stream_hints):
            return "audio"
        return None

    def _matches_json_pattern(self, url_lower: str) -> bool:
        return any(pat in url_lower for pat in self.cfg.json_url_patterns)

    def _should_sniff_json(self, url_lower: str, ctype: str, content_length: Optional[int]) -> bool:
        if not self.cfg.enable_json_sniff:
            return False
        ct = (ctype or "").lower()
        if not (any(jt in ct for jt in self.cfg.json_content_types) or "/metadata/" in url_lower):
            return False
        if not any(h in url_lower for h in self.cfg.json_url_hints):
            return False
        if content_length is None:
            return False
        if content_length > int(self.cfg.json_body_max_kb) * 1024:
            return False
        if not self._matches_json_pattern(url_lower):
            return False
        return True

    def _looks_like_graphql_endpoint(self, url_lower: str) -> bool:
        return any(k in url_lower for k in self.cfg.graphql_endpoint_keywords)

    def _is_allowed_by_extensions(self, url: str, extensions: Optional[Set[str]], kind: Optional[str]) -> bool:
        if not extensions:
            return True
        parsed = self._safe_urlparse(url)
        path = self._to_str(parsed.path).lower()
        if any(path.endswith(ext.lower()) for ext in extensions):
            return True
        if self.cfg.accept_unknown_streams and kind in ("video", "audio"):
            return True
        return False

    def _is_manifest(self, url: str, ctype: str) -> Optional[str]:
        ul = (url or "").lower()
        ct = (ctype or "").lower()
        if ul.endswith(".m3u8") or ct in self.cfg.hls_types:
            return "hls"
        if ul.endswith(".mpd") or ct in self.cfg.dash_types:
            return "dash"
        return None

    def _looks_like_segment(self, url_lower: str, ctype: str, content_length: Optional[int], headers: Dict[str, str]) -> Optional[str]:
        if not self.cfg.enable_segment_heuristics:
            return None

        ct = (ctype or "").lower()
        k = self._classify_by_content_type(ct)
        if k in ("video", "audio"):
            return k

        if self.cfg.accept_range_requests_as_media:
            cr = (headers.get("content-range") or "").lower()
            if cr.startswith("bytes "):
                return "video"

        if content_length is None:
            return None
        if content_length < int(self.cfg.min_segment_bytes):
            return None
        if content_length > int(self.cfg.max_segment_bytes) and not any(x in url_lower for x in (".m3u8", ".mpd")):
            return None

        if any(h in url_lower for h in ("seg", "segment", "chunk", "frag", "m4s", "/range/", "bytestream")):
            return "video"

        return None

    # ------------------ manifest parsing ------------------ #
    _HLS_LINE_RE = re.compile(r"^(?!#)(.+)$", re.MULTILINE)

    def _parse_hls_manifest(self, manifest_text: Any, base_url: str) -> List[str]:
        txt = self._to_str(manifest_text)
        out: List[str] = []
        seen: Set[str] = set()
        for m in self._HLS_LINE_RE.finditer(txt or ""):
            line = (m.group(1) or "").strip()
            if not line:
                continue
            full = self._canonicalize_url(self._safe_urljoin(base_url, line))
            if full and full not in seen:
                seen.add(full)
                out.append(full)
        return out

    def _parse_mpd_manifest(self, manifest_text: Any, base_url: str) -> List[str]:
        txt = self._to_str(manifest_text)
        out: List[str] = []
        seen: Set[str] = set()

        if self.ET is not None:
            try:
                root = self.ET.fromstring(txt)
                for el in root.iter():
                    for attr_name in ("media", "initialization", "sourceURL", "href"):
                        u = el.attrib.get(attr_name)
                        if not u:
                            continue
                        full = self._canonicalize_url(self._safe_urljoin(base_url, self._to_str(u).strip()))
                        if full and full not in seen:
                            seen.add(full)
                            out.append(full)
            except Exception:
                pass

        if not out:
            rx = self.re.compile(r'(?:media|initialization|sourceURL|href)\s*=\s*["\']([^"\']+)["\']', self.re.I)
            for m in rx.finditer(txt or ""):
                u = (m.group(1) or "").strip()
                if not u:
                    continue
                full = self._canonicalize_url(self._safe_urljoin(base_url, u))
                if full and full not in seen:
                    seen.add(full)
                    out.append(full)

        return out

    async def _expand_manifest(self, response, manifest_kind: str, url: str, log: Optional[List[str]]) -> List[str]:
        try:
            txt = await response.text()
            txt = self._to_str(txt)
            if txt and len(txt) > int(self.cfg.max_manifest_bytes):
                txt = txt[: int(self.cfg.max_manifest_bytes)]
        except Exception as e:
            self._log(f"[NetworkSniffer] Manifest read failed: {url} ({e})", log)
            return []

        derived = self._parse_hls_manifest(txt, url) if manifest_kind == "hls" else self._parse_mpd_manifest(txt, url)
        self._log(f"[NetworkSniffer] Expanded {manifest_kind} manifest: {url} -> {len(derived)} derived", log)
        return derived

    # ------------------ auto-scroll ------------------ #
    async def _auto_scroll(self, page, tmo: float, log: Optional[List[str]]) -> None:
        if not self.cfg.enable_auto_scroll:
            return
        try:
            max_steps = max(1, int(self.cfg.max_scroll_steps))
            step_delay = max(50, int(self.cfg.scroll_step_delay_ms))
            max_total_ms = int(tmo * 1000 * 0.8)
            used_ms = 0

            self._log(f"[NetworkSniffer] Auto-scroll enabled: steps={max_steps}, step_delay={step_delay}ms", log)
            last_height = await page.evaluate("() => document.body ? document.body.scrollHeight : 0")

            for i in range(max_steps):
                if used_ms >= max_total_ms:
                    self._log("[NetworkSniffer] Auto-scroll: reached time budget; stopping.", log)
                    break

                await page.evaluate("() => window.scrollBy(0, window.innerHeight);")
                await page.wait_for_timeout(step_delay)
                used_ms += step_delay

                new_height = await page.evaluate("() => document.body ? document.body.scrollHeight : 0")
                self._log(f"[NetworkSniffer] Auto-scroll step {i+1}/{max_steps}: height {last_height} -> {new_height}", log)

                if new_height <= last_height:
                    self._log("[NetworkSniffer] Auto-scroll: no further height growth; stopping.", log)
                    break
                last_height = new_height

            if self.cfg.scroll_back_to_top:
                await page.evaluate("() => window.scrollTo(0, 0);")
                self._log("[NetworkSniffer] Auto-scroll: scrolled back to top.", log)

        except Exception as e:
            self._log(f"[NetworkSniffer] Auto-scroll error: {e}", log)

    # ------------------ output normalization ------------------ #
    def _normalize_item(self, it: Dict[str, Any]) -> Dict[str, str]:
        return {
            "url": self._to_str(it.get("url")),
            "text": self._to_str(it.get("text")),
            "tag": self._to_str(it.get("tag") or "network_sniff"),
            "kind": self._to_str(it.get("kind") or "unknown"),
            "content_type": self._to_str(it.get("content_type") or "?"),
            "size": self._to_str(it.get("size") or "?"),
        }

    # ============================== URL salvage ============================== #
    _B64URL_RE = re.compile(r"^[A-Za-z0-9\-_]+={0,2}$")
    _HEX_RE = re.compile(r"^[0-9a-fA-F]+$")
    _JWT_LIKE_RE = re.compile(r"^[A-Za-z0-9\-_]+\.[A-Za-z0-9\-_]+\.[A-Za-z0-9\-_]+$")

    def _is_mediaish_url(self, url: str) -> bool:
        try:
            u = self._to_str(url)
            ul = u.lower()
            p = self._safe_urlparse(u)
            path = self._to_str(p.path).lower()
            if self._classify_by_extension(path):
                return True
            if any(h in ul for h in self.cfg.video_stream_hints) or any(h in ul for h in self.cfg.audio_stream_hints):
                return True
            if any(x in ul for x in ("seg", "segment", "chunk", "frag", "m4s", "bytestream", "videoplayback", "hls", "dash")):
                return True
            return False
        except Exception:
            return False

    def _signaturey_key(self, k: str) -> bool:
        kl = (k or "").lower()
        if not kl:
            return False
        if any(sub in kl for sub in (self.cfg.salvage_strip_query_keys_substrings or set())):
            return True
        # extra heuristics (programmatic)
        if kl in ("sig", "signature", "token", "auth", "authorization", "expires", "exp", "policy"):
            return True
        if kl.startswith(("x-amz-", "x-goog-", "x-ms-")):
            return True
        return False

    def _signaturey_value(self, v: str) -> bool:
        vv = (v or "").strip()
        if not vv:
            return False
        # timestamps and epoch-like values often live next to signatures
        if vv.isdigit() and len(vv) in (10, 13):
            return True
        # long/high-entropy-ish
        if len(vv) >= 48:
            if self._JWT_LIKE_RE.match(vv):
                return True
            if self._B64URL_RE.match(vv):
                return True
            if self._HEX_RE.match(vv) and len(vv) >= 32:
                return True
        return False

    def _has_signaturey_params(self, url: str) -> bool:
        try:
            p = self._safe_urlparse(url)
            if not p.query:
                return False
            for k, v in self._safe_parse_qsl(p.query):
                if self._signaturey_key(self._to_str(k)) or self._signaturey_value(self._to_str(v)):
                    return True
            return False
        except Exception:
            return False

    def _build_query_variants(self, url: str) -> List[Tuple[str, str]]:
        """
        Programmatic query simplification variants:
          - drop signature-ish keys
          - drop signature-ish values (even if key is unknown)
          - drop ALL query (path-only)
          - drop “obviously noisy” keys by length/entropy
        """
        out: List[Tuple[str, str]] = []
        try:
            p = self._safe_urlparse(url)
            if not p.scheme or not p.netloc:
                return out

            pairs = self._safe_parse_qsl(p.query)
            if not pairs:
                # still allow path-only variant via caller
                return out

            # 1) drop signature-ish keys/values
            kept1: List[Tuple[str, str]] = []
            dropped_any = False
            for k, v in pairs:
                ks = self._to_str(k)
                vs = self._to_str(v)
                if self._signaturey_key(ks) or self._signaturey_value(vs):
                    dropped_any = True
                    continue
                kept1.append((ks, vs))
            if dropped_any:
                q1 = self._safe_urlencode(kept1)
                u1 = self._safe_urlunparse((p.scheme, p.netloc, p.path, p.params, q1, ""))
                out.append((u1, "query_drop_signature"))

            # 2) keep only “short/simple” params (often id= / itag= / range=)
            kept2: List[Tuple[str, str]] = []
            for k, v in pairs:
                ks = self._to_str(k)
                vs = self._to_str(v)
                if len(ks) <= 16 and len(vs) <= 64 and not self._signaturey_key(ks) and not self._signaturey_value(vs):
                    kept2.append((ks, vs))
            if kept2 and kept2 != pairs:
                q2 = self._safe_urlencode(kept2)
                u2 = self._safe_urlunparse((p.scheme, p.netloc, p.path, p.params, q2, ""))
                out.append((u2, "query_keep_simple"))

            # 3) drop query entirely (path-only)
            u3 = self._safe_urlunparse((p.scheme, p.netloc, p.path, p.params, "", ""))
            out.append((u3, "path_only"))

        except Exception:
            pass

        # dedupe + cap
        seen: Set[str] = set()
        uniq: List[Tuple[str, str]] = []
        for u, k in out:
            cu = self._canonicalize_url(u)
            if not cu or cu in seen:
                continue
            seen.add(cu)
            uniq.append((cu, k))
            if len(uniq) >= int(self.cfg.salvage_max_query_simplify_variants):
                break
        return uniq

    def _programmatic_host_swaps(self, host: str) -> Set[str]:
        """
        Generate host alternatives via rules, not just config lists:
          - toggle common CDN prefixes: cf- , cdn. , media. , img. (conservative)
          - i1..i9 numeric subdomain bump
        """
        h = (host or "").strip().lower()
        if not h:
            return set()

        out: Set[str] = set()

        # numeric subdomain i1 -> i2..i5
        m = self.re.match(r"^(i)(\d+)\.(.+)$", h)
        if m:
            base = m.group(1)
            n = int(m.group(2))
            rest = m.group(3)
            for nn in range(max(1, n - 1), min(9, n + 4) + 1):
                if nn != n:
                    out.add(f"{base}{nn}.{rest}")

        # cf- prefix toggle
        if h.startswith("cf-"):
            out.add(h[len("cf-"):])
        else:
            out.add("cf-" + h)

        # cdn. toggle
        if h.startswith("cdn."):
            out.add(h[len("cdn."):])
        else:
            out.add("cdn." + h)

        return {x for x in out if x and x != h}

    def _origin_swap_variants(self, url: str) -> List[Tuple[str, str]]:
        out: List[Tuple[str, str]] = []
        try:
            p = self._safe_urlparse(url)
            host = self._to_str(p.netloc).lower()
            if not host:
                return out

            # 1) configured swaps (kept)
            for ah in (self.cfg.salvage_origin_swaps.get(host) or set()):
                ahs = self._to_str(ah).strip().lower()
                if ahs and ahs != host:
                    out.append((self._safe_urlunparse((p.scheme, ahs, p.path, p.params, p.query, p.fragment)), "origin_swap_static"))

            # 2) programmatic swaps
            for ahs in self._programmatic_host_swaps(host):
                out.append((self._safe_urlunparse((p.scheme, ahs, p.path, p.params, p.query, p.fragment)), "origin_swap_rule"))

        except Exception:
            pass

        # dedupe + cap
        seen: Set[str] = set()
        uniq: List[Tuple[str, str]] = []
        for u, k in out:
            cu = self._canonicalize_url(u)
            if not cu or cu in seen:
                continue
            seen.add(cu)
            uniq.append((cu, k))
            if len(uniq) >= int(self.cfg.salvage_max_host_swap_variants):
                break
        return uniq

    def _salvage_score(self, url: str, *, status: Optional[int], kind: Optional[str]) -> float:
        u = self._to_str(url)
        ul = u.lower()
        score = 0.0

        if self._is_mediaish_url(u):
            score += float(self.cfg.salvage_score_bonus_if_mediaish)

        if kind in ("video", "audio"):
            score += 0.5

        if any(x in ul for x in ("seg", "segment", "chunk", "frag", "m4s", "bytestream", "range")):
            score += float(self.cfg.salvage_score_bonus_if_segmenty)

        if self._has_signaturey_params(u):
            score += float(self.cfg.salvage_score_bonus_if_signed)

        if status is not None:
            if status in self.cfg.salvage_suspect_statuses:
                score += 2.0
            elif 500 <= status <= 599:
                score += 0.5

        return score

    def _salvage_should_target(self, url: str, *, status: Optional[int], kind: Optional[str]) -> bool:
        if not self.cfg.enable_url_salvage:
            return False
        if not self._host_allowed(url):
            return False
        if self.cfg.salvage_only_if_mediaish and (not self._is_mediaish_url(url)) and (not self._has_signaturey_params(url)):
            return False
        if self.cfg.salvage_only_if_suspect:
            suspect = False
            if status is not None and status in self.cfg.salvage_suspect_statuses:
                suspect = True
            if self._has_signaturey_params(url):
                suspect = True
            if not suspect:
                return False
        score = self._salvage_score(url, status=status, kind=kind)
        return score >= float(self.cfg.salvage_min_score_to_probe)

    def _salvage_log(self, msg: str, log: Optional[List[str]], *, level: str):
        lvl = (self.cfg.salvage_log_level or "ok").lower()
        if lvl == "none":
            return
        if lvl == "ok" and level != "ok":
            return
        self._log(msg, log)

    async def _probe_url(self, api_ctx, url: str, req_headers: Dict[str, str], *, timeout_ms: int) -> Dict[str, Any]:
        """
        HYBRID PROBE: Uses industrial engine if available, else falls back to Playwright api_ctx.
        """
        url = self._to_str(url)
        result = {
            "url": url, "ok": False, "status": None, "final_url": url,
            "content_type": None, "content_length": None, "hash_prefix_sha256": None,
            "method": None, "error": "",
        }

        # --- Path A: HTTPSSubmanager (High Resiliency) ---
        if self.http:
            try:
                # 1. HEAD request for metadata
                status, hdrs = await self.http.head(url)
                result.update({
                    "method": "ENGINE_GET",
                    "status": status,
                    "content_type": hdrs.get("Content-Type") or hdrs.get("content-type"),
                    "content_length": hdrs.get("Content-Length") or hdrs.get("content-length")
                })

                # 2. Bounded GET for hashing
                body = await self.http.get_bytes(url)
                if body:
                    result["hash_prefix_sha256"] = hashlib.sha256(body[:int(self.cfg.salvage_range_bytes)]).hexdigest()

                # Check success
                if status and 200 <= status < 300:
                    result["ok"] = True
                return result
            except Exception as e:
                self._log(f"[NetworkSniffer] Engine probe failed, trying fallback: {e}", None)
                # If engine fails, we don't return yet; we try Path B fallback

        # --- Path B: Playwright Fallback (Original Logic) ---
        if api_ctx is None:
            result["error"] = "no_context_or_engine"
            return result

        h = {self._to_str(k): self._to_str(v) for k, v in (req_headers or {}).items() if k and v}
        h_get = dict(h)
        if "range" not in {k.lower() for k in h_get.keys()}:
            h_get["Range"] = f"bytes=0-{max(0, int(self.cfg.salvage_range_bytes) - 1)}"

        try:
            resp = await api_ctx.get(url, headers=h_get, timeout=timeout_ms)
            result["method"] = "PW_GET"
            result["status"] = getattr(resp, "status", None)
            rh = {k.lower(): v for k, v in (getattr(resp, "headers", None) or {}).items()}
            result["content_type"] = rh.get("content-type")
            result["content_length"] = rh.get("content-length")

            b = await resp.body()
            if b:
                result["hash_prefix_sha256"] = hashlib.sha256(b[: int(self.cfg.salvage_range_bytes)]).hexdigest()

            if result["status"] in (200, 206):
                result["ok"] = True
        except Exception as e:
            result["error"] = f"pw_fallback_failed:{e}"

        return result

    async def _salvage_one(self, api_ctx, observed_url: str, req_headers_subset: Dict[str, str], *,
                          log: Optional[List[str]], observed_status: Optional[int], observed_kind: Optional[str]) -> Dict[str, Any]:
        observed = self._canonicalize_url(observed_url)
        if not observed:
            return {"observed_url": self._to_str(observed_url), "variants": [], "ok_variants": []}

        # build variants programmatically
        variants: List[Tuple[str, str]] = []

        # A) query simplifications (signature drop, keep-simple, path-only)
        variants.extend(self._build_query_variants(observed))

        # B) host swaps (static + rule-based)
        variants.extend(self._origin_swap_variants(observed))

        # C) host swaps of query variants (limited)
        #    (useful when cdn host differs but query already simplified)
        for (u, k) in list(variants)[:3]:
            for (u2, k2) in self._origin_swap_variants(u):
                variants.append((u2, f"{k}+{k2}"))

        # de-dupe + cap
        seen: Set[str] = {observed}
        uniq: List[Tuple[str, str]] = []
        for u, k in variants:
            cu = self._canonicalize_url(u)
            if not cu or cu in seen:
                continue
            if not self._host_allowed(cu):
                continue
            seen.add(cu)
            uniq.append((cu, k))
            if len(uniq) >= int(self.cfg.salvage_max_variants_per_url):
                break

        out_variants: List[Dict[str, Any]] = []
        ok_variants: List[Dict[str, Any]] = []

        tmo = int(self.cfg.salvage_probe_timeout_ms)

        # Probe order: try the “most likely” first
        def variant_rank(vk: str) -> int:
            vk = (vk or "").lower()
            if "query_drop_signature" in vk:
                return 0
            if "query_keep_simple" in vk:
                return 1
            if "path_only" in vk:
                return 2
            if "origin_swap" in vk:
                return 3
            return 9

        uniq.sort(key=lambda t: variant_rank(t[1]))

        # Less noisy: stop early once we find a good variant
        for (u, vkind) in uniq:
            pr = await self._probe_url(api_ctx, u, req_headers_subset, timeout_ms=tmo)
            pr["variant_kind"] = vkind
            out_variants.append(pr)

            if pr.get("ok"):
                ok_variants.append(pr)
                self._salvage_log(
                    f"[NetworkSniffer] Salvage OK ({observed_status}/{observed_kind}): {observed} -> {u} ({pr.get('status')})",
                    log, level="ok"
                )
                # early stop: 1 good result is usually enough
                break
            else:
                if self.cfg.salvage_record_non_200:
                    self._salvage_log(
                        f"[NetworkSniffer] Salvage miss: {observed} -> {u} ({pr.get('status')})",
                        log, level="all"
                    )

        # optionally emit only ok variants to keep the bundle clean
        variants_emit = ok_variants if self.cfg.salvage_emit_only_ok_variants_in_bundle else out_variants
        return {"observed_url": observed, "variants": variants_emit, "ok_variants": ok_variants}

    # ============================== forensics ============================== #
    def _pick_headers_subset(self, headers_lc: Dict[str, str], allow: Set[str]) -> Dict[str, str]:
        out: Dict[str, str] = {}
        for k in (allow or set()):
            kk = self._to_str(k).lower()
            v = headers_lc.get(kk)
            if v:
                out[kk] = self._to_str(v)
        return out

    def _hash_post_data(self, post_data: Any, max_bytes: int = 4096) -> Dict[str, Any]:
        try:
            if post_data is None:
                return {"size": 0, "sha256": None}
            if isinstance(post_data, str):
                b = post_data.encode("utf-8", "ignore")
            elif isinstance(post_data, (bytes, bytearray, memoryview)):
                b = bytes(post_data)
            else:
                b = self._to_str(post_data).encode("utf-8", "ignore")
            return {"size": len(b), "sha256": self.hashlib.sha256(b[:max_bytes]).hexdigest()}
        except Exception:
            return {"size": None, "sha256": None}

    async def _hash_body_prefix_via_probe(self, api_ctx, url: str, req_headers_subset: Dict[str, str], *,
                                          timeout_ms: int, prefix_bytes: int) -> Optional[str]:
        """
        HYBRID HASHING: Uses engine if available, else Playwright context.
        """
        # Engine path
        if self.http:
            try:
                b = await self.http.get_bytes(self._to_str(url))
                return hashlib.sha256(b[:prefix_bytes]).hexdigest() if b else None
            except:
                pass  # fall through to PW

        # Original PW path
        if api_ctx is None: return None
        try:
            h = {self._to_str(k): self._to_str(v) for k, v in (req_headers_subset or {}).items() if k and v}
            h["Range"] = f"bytes=0-{max(0, int(prefix_bytes) - 1)}"
            resp = await api_ctx.get(self._to_str(url), headers=h, timeout=timeout_ms)
            b = await resp.body()
            return hashlib.sha256(b[:prefix_bytes]).hexdigest() if b else None
        except:
            return None

    # ============================== sniff ============================== #
    async def sniff(
        self,
        context,
        page_url: str,
        *,
        timeout: Optional[float] = None,
        log: Optional[List[str]] = None,
        extensions: Optional[Set[str]] = None,
    ):
        if context is None:
            self._log("[NetworkSniffer] No Playwright context; skipping sniff.", log)
            return "", [], []

        tmo = float(timeout if timeout is not None else self.cfg.timeout)
        canonical_page_url = self._canonicalize_url(page_url)

        found_items: List[Dict[str, Any]] = []
        derived_items: List[Dict[str, Any]] = []
        json_hits: List[Dict[str, Any]] = []

        seen_network: Set[str] = set()
        seen_derived: Set[str] = set()

        blob_placeholders: List[Dict[str, Any]] = []
        req_types: Dict[str, str] = {}

        request_evidence: Dict[str, Dict[str, Any]] = {}
        redirect_events: List[Dict[str, Any]] = []
        seen_redirect: Set[str] = set()

        forensics: List[Dict[str, Any]] = []
        seen_forensics: Set[str] = set()

        # new: salvage target table (url -> info), scored + per-host limited
        salvage_info: Dict[str, Dict[str, Any]] = {}
        salvage_host_counts: Dict[str, int] = {}

        salvage_bundles: List[Dict[str, Any]] = []

        html: str = ""

        page = await context.new_page()
        wait_mode = getattr(self.cfg, "goto_wait_until", "domcontentloaded")

        api_ctx = None
        try:
            api_ctx = getattr(context, "request", None) or getattr(page, "request", None)
        except Exception:
            api_ctx = None

        max_items = int(self.cfg.max_items)
        max_json = int(self.cfg.max_json_hits)
        max_derived_per_manifest = int(self.cfg.max_derived_per_manifest)
        max_manifests = int(self.cfg.max_manifests_to_expand)

        manifests_to_expand: List[Tuple[Any, str, str]] = []

        self._log(f"[NetworkSniffer] Start sniff: {canonical_page_url} (timeout={tmo}s)", log)

        # ---------------- request handler ---------------- #
        def handle_request(req):
            try:
                rurl = self._to_str(getattr(req, "url", None))
                req_types[rurl] = self._to_str(getattr(req, "resource_type", None))
            except Exception:
                pass

            # request-side redirect chain
            try:
                if self.cfg.enable_redirect_tracking:
                    prev = getattr(req, "redirected_from", None)
                    if prev:
                        prev_url = self._to_str(getattr(prev, "url", None))
                        cur_url = self._to_str(getattr(req, "url", None))
                        key = f"{prev_url} -> {cur_url}"
                        if prev_url and cur_url and key not in seen_redirect:
                            seen_redirect.add(key)
                            redirect_events.append({"from": prev_url, "to": cur_url})
            except Exception:
                pass

            # request evidence
            try:
                if self.cfg.enable_forensics:
                    url = self._to_str(getattr(req, "url", None))
                    if url and url not in request_evidence:
                        try:
                            rh_raw = getattr(req, "headers", None) or {}
                            rh_lc = {self._to_str(k).lower(): self._to_str(v) for k, v in rh_raw.items()}
                        except Exception:
                            rh_lc = {}
                        req_hdr_subset = self._pick_headers_subset(rh_lc, self.cfg.forensics_include_request_headers_subset)

                        post_data = getattr(req, "post_data", None)
                        post_hash = self._hash_post_data(post_data, max_bytes=4096)

                        frame_url = None
                        try:
                            fr = getattr(req, "frame", None)
                            if fr is not None:
                                frame_url = self._to_str(getattr(fr, "url", None))
                        except Exception:
                            frame_url = None

                        request_evidence[url] = {
                            "method": self._to_str(getattr(req, "method", None)),
                            "resource_type": self._to_str(getattr(req, "resource_type", None)),
                            "frame_url": frame_url,
                            "headers_subset": req_hdr_subset,
                            "post_data_hash": post_hash,
                        }
            except Exception:
                pass

            # GraphQL sniff
            try:
                if self.cfg.enable_graphql_sniff and self._to_str(getattr(req, "method", "")).upper() == "POST":
                    url_lower = self._to_str(getattr(req, "url", None)).lower()
                    if self._looks_like_graphql_endpoint(url_lower):
                        body = self._to_str(getattr(req, "post_data", None) or "")
                        if not body:
                            return
                        if len(body) > int(self.cfg.graphql_max_body_kb) * 1024:
                            return

                        try:
                            gql_payload = self.json.loads(body)
                        except Exception:
                            return

                        payloads = gql_payload if isinstance(gql_payload, list) else [gql_payload]
                        for pay in payloads:
                            if not isinstance(pay, dict):
                                continue
                            op_name = pay.get("operationName")
                            vars_obj = pay.get("variables")
                            query = pay.get("query") or ""
                            is_introspection = isinstance(query, str) and ("__schema" in query or "__type" in query)
                            var_keys = list(vars_obj.keys()) if isinstance(vars_obj, dict) else None

                            if len(json_hits) >= max_json:
                                break

                            json_hits.append({
                                "url": self._to_str(getattr(req, "url", None)),
                                "json": {
                                    "graphql": True,
                                    "operationName": op_name,
                                    "variable_keys": var_keys,
                                    "is_introspection": is_introspection,
                                    "query_preview": query[:2048] if isinstance(query, str) else None,
                                },
                                "source_page": canonical_page_url,
                            })
            except Exception as e:
                self._log(f"[NetworkSniffer] handle_request GraphQL sniff error: {e}", log)

        page.on("request", handle_request)

        # ---------------- header mining ---------------- #
        def mine_headers(url: str, headers_lc: Dict[str, str]):
            if not self.cfg.enable_header_url_mining:
                return
            if len(json_hits) >= max_json:
                return
            if int(self.cfg.max_header_url_events) <= 0:
                return
            try:
                for k in (self.cfg.header_url_keys or set()):
                    kk = self._to_str(k).lower()
                    v = headers_lc.get(kk)
                    if not v:
                        continue
                    for u in self._extract_urls_from_text(v)[:50]:
                        if len(json_hits) >= max_json:
                            return
                        json_hits.append({
                            "url": url,
                            "json": {"header_url": u, "header_key": kk},
                            "source_page": canonical_page_url,
                        })
            except Exception:
                pass

        async def handle_json(resp, url: str):
            if len(json_hits) >= max_json:
                return
            try:
                data = await resp.json()
                json_hits.append({"url": url, "json": data, "source_page": canonical_page_url})
            except Exception as e:
                self._log(f"[NetworkSniffer] Failed to parse JSON from {url}: {e}", log)

        # ---------------- response handler ---------------- #
        def handle_response(response):
            try:
                raw_url = self._to_str(getattr(response, "url", None))
                canonical_url = self._canonicalize_url(raw_url)

                if not canonical_url or canonical_url in seen_network:
                    return
                if not self._host_allowed(canonical_url):
                    return

                is_blob = canonical_url.startswith("blob:")
                resource_type = self._to_str(req_types.get(raw_url, ""))

                if not is_blob:
                    p = self._safe_urlparse(canonical_url)
                    path = self._to_str(p.path or "/").lower()
                    netloc = self._to_str(p.netloc or "")
                    if self._is_junk_by_extension(path):
                        return
                    if self._looks_like_ad(netloc, path):
                        return

                seen_network.add(canonical_url)

                # normalize headers to {lower:str -> str}
                try:
                    hdr_raw = getattr(response, "headers", None) or {}
                    headers = {self._to_str(k).lower(): self._to_str(v) for (k, v) in hdr_raw.items()}
                except Exception:
                    headers = {}

                ctype = (headers.get("content-type") or "").lower()
                url_lower = canonical_url.lower()

                # header URL mining
                mine_headers(canonical_url, headers)

                # response redirect info
                try:
                    if self.cfg.enable_redirect_tracking:
                        loc = self._to_str(headers.get("location"))
                        if loc:
                            key = f"{canonical_url} -> {loc}"
                            if key not in seen_redirect and len(redirect_events) < int(self.cfg.max_redirect_events):
                                seen_redirect.add(key)
                                redirect_events.append({"from": canonical_url, "to": loc, "status": getattr(response, "status", None)})
                except Exception:
                    pass

                # content-length parse
                cl_header = self._to_str(headers.get("content-length") or "")
                content_length: Optional[int] = None
                try:
                    if cl_header.isdigit():
                        content_length = int(cl_header)
                except Exception:
                    content_length = None

                if (not is_blob) and ctype and self._deny_by_content_type(ctype):
                    return
                if (not is_blob) and resource_type and self._deny_by_resource_type(resource_type):
                    return

                # SAFE JSON sniff
                if (not is_blob) and self._should_sniff_json(url_lower, ctype, content_length):
                    self.asyncio.create_task(handle_json(response, canonical_url))
                    return

                # blob media placeholder
                if is_blob:
                    if resource_type == "media":
                        blob_placeholders.append({
                            "url": canonical_url,
                            "text": "[Network Video Blob]",
                            "tag": "network_sniff",
                            "kind": "video",
                            "content_type": ctype or "?",
                            "size": headers.get("content-length", "?"),
                        })
                        if len(json_hits) < max_json:
                            json_hits.append({
                                "url": canonical_url,
                                "json": {"blob_media": canonical_url, "reason": "blob-media-detected"},
                                "source_page": canonical_page_url
                            })
                    return

                p = self._safe_urlparse(canonical_url)
                path = self._to_str(p.path or "/").lower()

                kind = (
                    self._classify_by_extension(path)
                    or (self._classify_by_content_type(ctype) if ctype else None)
                    or self._classify_by_stream_hint(url_lower)
                )

                if not kind:
                    seg_kind = self._looks_like_segment(url_lower, ctype, content_length, headers)
                    if seg_kind:
                        kind = seg_kind

                if not kind:
                    return

                if not self._is_allowed_by_extensions(canonical_url, extensions, kind):
                    return

                # manifest tracking
                mkind = self._is_manifest(canonical_url, ctype)
                if mkind and kind == "video" and len(manifests_to_expand) < max_manifests:
                    manifests_to_expand.append((response, mkind, canonical_url))
                    if self.cfg.prefer_master_manifests:
                        manifests_to_expand.sort(key=lambda t: (0 if "master" in self._to_str(t[2]).lower() else 1))

                if len(found_items) < max_items:
                    # content-disposition filename hint
                    cd = self._to_str(headers.get("content-disposition") or "")
                    filename = None
                    if cd:
                        m = self.re.search(r'filename\*?=(?:UTF-8\'\')?"?([^";]+)"?', cd, self.re.I)
                        if m:
                            filename = self._to_str(m.group(1))

                    item: Dict[str, Any] = {
                        "url": canonical_url,
                        "text": f"[Network {kind.capitalize()}]",
                        "tag": "network_sniff",
                        "kind": kind,
                        "content_type": ctype or "?",
                        "size": headers.get("content-length", "?"),
                    }
                    if filename:
                        item["text"] = f"[Network {kind.capitalize()}] {filename}"
                    found_items.append(item)

                # forensics bundle
                if self.cfg.enable_forensics and len(forensics) < int(self.cfg.max_forensics_events):
                    req_ev = request_evidence.get(raw_url) or request_evidence.get(canonical_url) or {}
                    req_hdr_subset = (req_ev.get("headers_subset") or {})
                    resp_hdr_subset = self._pick_headers_subset(headers, self.cfg.forensics_include_headers_subset)

                    timing = None
                    try:
                        rreq = getattr(response, "request", None)
                        if rreq is not None:
                            timing = getattr(rreq, "timing", None)
                            if callable(timing):
                                timing = timing()
                    except Exception:
                        timing = None

                    bundle = {
                        "url": canonical_url,
                        "final_url": canonical_url,
                        "status": getattr(response, "status", None),
                        "content_type": headers.get("content-type"),
                        "content_length": headers.get("content-length"),
                        "discovered_at": self.time.time(),
                        "source_page": canonical_page_url,
                        "initiator_frame": req_ev.get("frame_url"),
                        "resource_type": req_ev.get("resource_type") or resource_type,
                        "request_method": req_ev.get("method"),
                        "request_headers_subset": req_hdr_subset,
                        "request_post_data_hash": req_ev.get("post_data_hash"),
                        "response_headers_subset": resp_hdr_subset,
                        "timing": timing,
                        "sha256_body_prefix": None,
                    }
                    k = f"{bundle.get('url')}|{bundle.get('status')}|{bundle.get('content_type')}|{bundle.get('content_length')}"
                    if k not in seen_forensics:
                        seen_forensics.add(k)
                        forensics.append(bundle)

                # salvage targets (LESS NOISY + SCORED)
                if self.cfg.enable_url_salvage:
                    status = getattr(response, "status", None)
                    if self._salvage_should_target(canonical_url, status=status, kind=kind):
                        host = self._to_str(self._safe_urlparse(canonical_url).netloc).lower()
                        if host:
                            cnt = salvage_host_counts.get(host, 0)
                            if cnt >= int(self.cfg.salvage_max_targets_per_host):
                                return
                        score = self._salvage_score(canonical_url, status=status, kind=kind)

                        # keep best score per URL
                        prev = salvage_info.get(canonical_url)
                        if (prev is None) or (float(prev.get("score", 0.0)) < score):
                            salvage_info[canonical_url] = {
                                "url": canonical_url,
                                "score": score,
                                "status": status,
                                "kind": kind,
                            }
                            if host:
                                salvage_host_counts[host] = salvage_host_counts.get(host, 0) + 1

            except Exception as e:
                self._log(
                    f"[NetworkSniffer][handle_response] Error processing {self._to_str(getattr(response,'url',None))}: {self._to_str(e)}",
                    log
                )

        page.on("response", handle_response)

        # ---------------- run page ---------------- #
        try:
            sniff_goto_timeout = max(15000, int(tmo * 1000))
            try:
                await page.goto(canonical_page_url, wait_until=wait_mode, timeout=sniff_goto_timeout)
            except Exception as e:
                self._log(f"[NetworkSniffer] goto timeout on {canonical_page_url} (wait_until={wait_mode}): {e}", log)

            await self._auto_scroll(page, tmo, log)
            await page.wait_for_timeout(int(tmo * 1000 * 0.2))

            # redirect chain
            if self.cfg.enable_redirect_tracking and redirect_events and len(json_hits) < max_json:
                json_hits.append({
                    "url": canonical_page_url,
                    "json": {"redirect_chain": redirect_events[: int(self.cfg.max_redirect_events)]},
                    "source_page": canonical_page_url,
                })

            # manifest expansion
            if manifests_to_expand:
                async def expand_one(resp, mkind: str, murl: str):
                    derived_urls = await self._expand_manifest(resp, mkind, murl, log)
                    if not derived_urls:
                        return
                    for u in derived_urls[:max_derived_per_manifest]:
                        if not u:
                            continue
                        if u in seen_derived or u in seen_network:
                            continue
                        if not self._host_allowed(u):
                            continue
                        seen_derived.add(u)
                        dk = self._classify_by_extension(self._to_str(self._safe_urlparse(u).path)) or "video"
                        if not self._is_allowed_by_extensions(u, extensions, dk):
                            continue
                        derived_items.append({
                            "url": u,
                            "text": f"[Network {dk.capitalize()} Segment]",
                            "tag": "network_sniff",
                            "kind": dk,
                            "content_type": mkind,
                            "size": "?",
                        })
                        if len(json_hits) < max_json:
                            json_hits.append({
                                "url": u,
                                "json": {"derived_from": murl, "manifest_type": mkind},
                                "source_page": canonical_page_url
                            })

                await self.asyncio.gather(*[
                    expand_one(resp, mkind, murl)
                    for (resp, mkind, murl) in manifests_to_expand
                ])

            # forensics hash fill
            if self.cfg.enable_forensics and self.cfg.forensics_hash_via_probe and api_ctx is not None and forensics:
                sem = self.asyncio.Semaphore(8)

                async def guard_hash(bundle: Dict[str, Any]):
                    async with sem:
                        hp = await self._hash_body_prefix_via_probe(
                            api_ctx,
                            bundle["url"],
                            bundle.get("request_headers_subset") or {},
                            timeout_ms=int(self.cfg.forensics_probe_timeout_ms),
                            prefix_bytes=int(self.cfg.forensics_body_prefix_bytes),
                        )
                        bundle["sha256_body_prefix"] = hp

                await self.asyncio.gather(*[guard_hash(b) for b in forensics])

            # salvage stage (SCORED + TOP-N)
            if self.cfg.enable_url_salvage and api_ctx is not None and salvage_info:
                # select top targets
                targets = list(salvage_info.values())
                targets.sort(key=lambda d: float(d.get("score", 0.0)), reverse=True)
                targets = targets[: int(self.cfg.salvage_max_targets_total)]

                sem = self.asyncio.Semaphore(int(self.cfg.salvage_probe_concurrency))

                def req_hdrs_for(u: str) -> Dict[str, str]:
                    ev = request_evidence.get(u) or request_evidence.get(self._canonicalize_url(u)) or {}
                    return ev.get("headers_subset") or {}

                async def salvage_guard(info: Dict[str, Any]):
                    async with sem:
                        u = self._to_str(info.get("url"))
                        return await self._salvage_one(
                            api_ctx,
                            u,
                            req_hdrs_for(u),
                            log=log,
                            observed_status=info.get("status"),
                            observed_kind=info.get("kind"),
                        )

                salvage_bundles = await self.asyncio.gather(*[salvage_guard(i) for i in targets])

            # emit bundles
            if self.cfg.enable_forensics and forensics and len(json_hits) < max_json:
                json_hits.append({
                    "url": canonical_page_url,
                    "json": {"forensics_bundle": {
                        "source_page": canonical_page_url,
                        "count": len(forensics),
                        "items": forensics[: int(self.cfg.max_forensics_events)],
                    }},
                    "source_page": canonical_page_url,
                })

            if self.cfg.enable_url_salvage and salvage_bundles and len(json_hits) < max_json:
                # keep bundle clean by removing empty salvage results
                clean = []
                for b in salvage_bundles:
                    if not isinstance(b, dict):
                        continue
                    if b.get("ok_variants"):
                        clean.append(b)
                    elif not self.cfg.salvage_emit_only_ok_variants_in_bundle and b.get("variants"):
                        clean.append(b)

                json_hits.append({
                    "url": canonical_page_url,
                    "json": {"salvage_bundle": {
                        "source_page": canonical_page_url,
                        "count": len(clean),
                        "items": clean,
                    }},
                    "source_page": canonical_page_url,
                })

            try:
                html = await page.content()
            except Exception as e:
                self._log(f"[NetworkSniffer] Failed to get page content: {e}", log)
                html = ""

        except Exception as e:
            self._log(f"[NetworkSniffer] Unexpected error during sniff for {canonical_page_url}: {e}", log)

        finally:
            try:
                await self.asyncio.wait_for(page.close(), timeout=3.0)
            except Exception:
                pass

        merged_items_any = found_items + derived_items + blob_placeholders
        merged_items = [self._normalize_item(it) for it in merged_items_any if it.get("url")]

        summary = (
            f"[NetworkSniffer] Finished sniff for {canonical_page_url}: "
            f"media={len(found_items)} derived={len(derived_items)} "
            f"blob={len(blob_placeholders)} json_hits={len(json_hits)} "
            f"forensics={len(forensics)} salvage={len(salvage_bundles)} "
            f"(Total output: {len(merged_items)})"
        )
        self._log(summary, log)

        return html, merged_items, json_hits

# ======================================================================
# JSSniffer
# ======================================================================

class JSSniffer:
    """
    Shared-context Playwright JS + DOM + SPA-state link sniffer.

    Output schema:
      link = {url, text, tag}

    NEW "long-lost content" additions:
      - performance entries mining (resource timing URLs)
      - <link rel=preload/prefetch/modulepreload> + meta/content mining
      - srcset parsing + background-image/style url() extraction
      - JSON-LD + script[type=application/json] + common SPA blobs (__NEXT_DATA__, __NUXT__, etc.)
      - localStorage/sessionStorage URL mining (bounded)
      - optional global JSON scan from known window keys (bounded)
      - stronger URL unescaping (\\u0026, \\/, \\u003a, etc.)
    """

    # ------------------------------------------------------------------ #
    # Config
    # ------------------------------------------------------------------ #
    @dataclass
    class Config:
        timeout: float = 8.0
        max_links: int = 700
        wait_after_goto_ms: int = 500
        include_shadow_dom: bool = True

        # How Playwright waits in page.goto; for Camoufox you can set "commit"
        goto_wait_until: str = "domcontentloaded"

        # ------------------ auto-scroll options ------------------ #
        enable_auto_scroll: bool = True
        max_scroll_steps: int = 20
        scroll_step_delay_ms: int = 400
        scroll_back_to_top: bool = False

        # ------------------ anti-freeze budgets ------------------ #
        evaluate_timeout_s: float = 6.0          # hard timeout for page.evaluate
        content_timeout_s: float = 4.0           # hard timeout for page.content
        max_items_soft_limit: int = 1800         # browser-side cap before returning to Python

        # Shadow DOM traversal caps
        shadow_host_soft_limit: int = 400        # how many potential shadow hosts to inspect
        max_dom_nodes_scanned: int = 14000       # global cap for scanned elements

        # Script scanning caps
        enable_script_scan: bool = True
        script_soft_limit: int = 90              # number of <script> tags to inspect
        max_script_chars: int = 80_000           # truncate per-script text

        # Optional click simulation
        enable_click_simulation: bool = False
        max_click_targets: int = 6
        click_timeout_ms: int = 2500
        click_target_selectors: List[str] = field(default_factory=lambda: [
            "a[href]", "button", "[role=button]", "[onclick]",
            "div[role=link]", "span[role=link]"
        ])

        # ------------------ Webpack module scan ------------------ #
        enable_webpack_scan: bool = True
        webpack_module_soft_limit: int = 250
        max_webpack_fn_chars: int = 90_000
        webpack_url_regex: str = r"(https?:\/\/[^\s'\"`]+|\/api\/[a-zA-Z0-9_\/\-\?\=&]+)"
        webpack_api_hints: Set[str] = field(default_factory=lambda: {
            "/api/", "/graphql", "/auth", "/login", "/logout", "/stream",
            ".m3u8", ".mpd", "/cdn/", "/v1/", "/v2/"
        })

        # ------------------ "long lost content" scans ------------------ #
        enable_perf_entries: bool = True
        max_perf_entries: int = 700

        enable_meta_scan: bool = True  # meta content, canonical, og:, twitter:
        enable_link_rel_scan: bool = True  # preload/prefetch/modulepreload/alternate

        enable_srcset_scan: bool = True
        enable_css_url_scan: bool = True   # style tags + inline style url(...)
        max_style_chars: int = 90_000

        enable_storage_scan: bool = True
        max_storage_keys: int = 120
        max_storage_chars: int = 120_000

        enable_spa_state_scan: bool = True
        max_spa_json_chars: int = 140_000
        spa_state_keys: List[str] = field(default_factory=lambda: [
            "__NEXT_DATA__", "__NUXT__", "__NUXT_DATA__", "__APOLLO_STATE__",
            "__INITIAL_STATE__", "__PRELOADED_STATE__", "__SSR_STATE__",
            "REDUX_STATE", "INITIAL_REDUX_STATE",
        ])

        # optional: try scanning a few known global objects (bounded stringify)
        enable_global_json_scan: bool = False
        global_json_keys: List[str] = field(default_factory=lambda: [
            "webpackChunk", "__VUE_DEVTOOLS_GLOBAL_HOOK__", "requirejs",
        ])
        max_global_json_chars: int = 80_000

        # selectors for direct URL-bearing elements
        selectors: List[str] = field(default_factory=lambda: [
            "a[href]",
            "video[src]", "video source[src]", "source[src]",
            "audio[src]", "audio source[src]",
            "img[src]", "img[srcset]",
            "iframe[src]", "embed[src]",
            "link[href]",  # rel scans filter in JS
            "meta[content]",
        ])

        junk_prefixes: Set[str] = field(default_factory=lambda: {
            "blob:", "javascript:", "data:"
        })

        video_extensions: Set[str] = field(default_factory=lambda: {
            ".mp4", ".webm", ".mkv", ".mov", ".avi", ".flv", ".wmv",
            ".m3u8", ".mpd", ".ts", ".3gp", ".m4v", ".f4v", ".ogv"
        })
        audio_extensions: Set[str] = field(default_factory=lambda: {
            ".mp3", ".m4a", ".aac", ".flac", ".ogg", ".opus", ".wav",
            ".weba", ".alac", ".aiff", ".wma"
        })
        image_extensions: Set[str] = field(default_factory=lambda: {
            ".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".svg",
            ".avif", ".heic", ".heif", ".tiff"
        })

        data_url_keys: Set[str] = field(default_factory=lambda: {
            "data-href", "data-url", "data-src", "data-srcset",
            "data-video", "data-video-url", "data-poster",
            "data-file", "data-stream", "data-mp4", "data-m3u8", "data-mpd",
            "data-audio", "data-audio-url", "data-image", "data-media-url"
        })

        onclick_url_regexes: List[str] = field(default_factory=lambda: [
            r"""['"]((?:https?:)?//[^'"]+)['"]""",
            r"""location\.href\s*=\s*['"]([^'"]+)['"]""",
            r"""window\.open\(\s*['"]([^'"]+)['"]""",
            r"""window\.location\.assign\(\s*['"]([^'"]+)['"]\)""",
            r"""window\.location\.replace\(\s*['"]([^'"]+)['"]\)""",
            r"""decodeURIComponent\s*\(\s*['"]([^'"]+)['"]\)""",
        ])

        redirect_hints: Set[str] = field(default_factory=lambda: {
            "location.href", "window.location", "window.open", "document.location",
            "location.replace", "location.assign", "navigate", "redirect"
        })

        script_json_hints: Set[str] = field(default_factory=lambda: {
            "url", "src", "file", "video", "audio", "stream", "manifest",
            "m3u8", "mpd", "playlist", "dash", "hls", "media"
        })

        # Optional: speed up pages by blocking heavy resources (OFF by default)
        block_resource_types: bool = False
        blocked_types: Set[str] = field(default_factory=lambda: {"image", "media", "font"})

    def __init__(self, config: Optional["JSSniffer.Config"] = None, logger=None):
        self.cfg = config or self.Config()
        self.logger = logger or DEBUG_LOGGER
        self._log("JSSniffer initialized", None)

    # ------------------------- helpers ------------------------- #

    def _log(self, msg: str, log_list: Optional[List[str]]) -> None:
        full = f"[JSSniffer] {msg}"
        try:
            if log_list is not None:
                log_list.append(full)
            if self.logger is not None:
                self.logger.log_message(full)
        except Exception:
            pass

    def _is_junk_url(self, url: str) -> bool:
        if not url:
            return True
        u = url.lower()
        return any(u.startswith(pfx) for pfx in self.cfg.junk_prefixes)

    def _classify_kind(self, url: str) -> Optional[str]:
        parsed = urlparse(url)
        p = (parsed.path or "").lower()
        if any(p.endswith(ext) for ext in self.cfg.video_extensions):
            return "video"
        if any(p.endswith(ext) for ext in self.cfg.audio_extensions):
            return "audio"
        if any(p.endswith(ext) for ext in self.cfg.image_extensions):
            return "image"
        return None

    def _is_allowed_by_extensions(self, url: str, extensions: Optional[Set[str]], kind: Optional[str]) -> bool:
        if not extensions:
            return True
        parsed = urlparse(url)
        p = (parsed.path or "").lower()
        if any(p.endswith(ext.lower()) for ext in extensions):
            return True
        # keep video/audio even if extension filter is narrow (your prior behavior)
        if kind in ("video", "audio"):
            return True
        return False

    def _normalize_link(self, url: str, text: str, tag: str) -> Dict[str, str]:
        return {"url": url, "text": text or "", "tag": tag or "a"}

    def _fix_common_escapes(self, url: str) -> str:
        """
        JS-heavy apps love escaping:
          \\u0026, %5Cu0026, \\/, \\u003a, \\u002f, etc.
        We keep it conservative (no heavy unescape libs).
        """
        if not url:
            return url
        try:
            url = url.replace("\\u0026", "&")
            url = url.replace("\\u003a", ":").replace("\\u002f", "/")
            url = url.replace("\\/", "/")
        except Exception:
            pass
        try:
            url = url.replace("%5Cu0026", "%26").replace("%5cu0026", "%26")
        except Exception:
            pass
        return url

    async def _auto_scroll(self, page: "Page", tmo: float, log: Optional[List[str]]) -> None:
        if not self.cfg.enable_auto_scroll:
            return
        try:
            max_steps = max(1, int(self.cfg.max_scroll_steps))
            step_delay = max(50, int(self.cfg.scroll_step_delay_ms))
            max_total_ms = int(tmo * 1000 * 0.7)
            used_ms = 0

            self._log(f"Auto-scroll enabled: steps={max_steps}, step_delay={step_delay}ms", log)

            last_height = await page.evaluate("() => document.body ? document.body.scrollHeight : 0")

            for i in range(max_steps):
                if used_ms >= max_total_ms:
                    self._log("Auto-scroll: reached time budget; stopping.", log)
                    break

                await page.evaluate("() => window.scrollBy(0, window.innerHeight);")
                await page.wait_for_timeout(step_delay)
                used_ms += step_delay

                new_height = await page.evaluate("() => document.body ? document.body.scrollHeight : 0")
                self._log(f"Auto-scroll step {i+1}/{max_steps}: height {last_height} -> {new_height}", log)

                if new_height <= last_height:
                    self._log("Auto-scroll: no further height growth; stopping.", log)
                    break
                last_height = new_height

            if self.cfg.scroll_back_to_top:
                try:
                    await page.evaluate("() => window.scrollTo(0, 0);")
                    self._log("Auto-scroll: scrolled back to top.", log)
                except Exception as e:
                    self._log(f"Auto-scroll: failed to scroll back to top: {e}", log)
        except Exception as e:
            self._log(f"Auto-scroll error: {e}", log)

    # ------------------------- main sniff ------------------------- #

    async def sniff(
        self,
        context: "BrowserContext",
        page_url: str,
        *,
        timeout: Optional[float] = None,
        log: Optional[List[str]] = None,
        extensions: Optional[Set[str]] = None,
    ) -> Tuple[str, List[Dict[str, str]]]:

        if context is None:
            self._log("No Playwright context; skipping JS sniff.", log)
            return "", []

        tmo = float(timeout if timeout is not None else self.cfg.timeout)
        canonical_page_url = _canonicalize_url(page_url)

        html: str = ""
        links: List[Dict[str, str]] = []
        seen_urls_in_js: Set[str] = set()

        page: "Page" = await context.new_page()

        try:
            page.set_default_timeout(int(max(1.0, tmo) * 1000))
            page.set_default_navigation_timeout(int(max(5.0, tmo) * 1000))
        except Exception:
            pass

        if self.cfg.block_resource_types:
            try:
                async def _route_handler(route):
                    try:
                        req = route.request
                        if req.resource_type in self.cfg.blocked_types:
                            return await route.abort()
                    except Exception:
                        pass
                    return await route.continue_()
                await page.route("**/*", _route_handler)
            except Exception as e:
                self._log(f"Resource blocking setup failed: {e}", log)

        js_timeout_ms = int(max(tmo, 10.0) * 1000)
        wait_after_ms = int(self.cfg.wait_after_goto_ms)
        wait_mode = getattr(self.cfg, "goto_wait_until", "domcontentloaded")

        selector_js = ", ".join(self.cfg.selectors)

        self._log(f"Start: {canonical_page_url} timeout={tmo}s", log)

        try:
            try:
                await page.goto(canonical_page_url, wait_until=wait_mode, timeout=js_timeout_ms)
            except Exception as e:
                self._log(f"goto timeout on {canonical_page_url} (wait_until={wait_mode}): {e}", log)

            if wait_after_ms > 0:
                await page.wait_for_timeout(wait_after_ms)

            await self._auto_scroll(page, tmo, log)

            extra_wait = max(200, int(tmo * 1000 * 0.1))
            await page.wait_for_timeout(extra_wait)

            try:
                html = await asyncio.wait_for(page.content(), timeout=self.cfg.content_timeout_s)
            except Exception as e:
                self._log(f"page.content() skipped/timeout: {e}", log)
                html = ""

            eval_args = {
                "selectors": selector_js,
                "includeShadow": bool(self.cfg.include_shadow_dom),
                "dataKeys": list(self.cfg.data_url_keys),
                "onclickRegexes": [r.replace("\\", "\\\\") for r in self.cfg.onclick_url_regexes],
                "redirectHints": list(self.cfg.redirect_hints),
                "scriptJsonHints": list(self.cfg.script_json_hints),
                "baseUrl": canonical_page_url,

                "maxItems": int(self.cfg.max_items_soft_limit),
                "maxDomNodes": int(self.cfg.max_dom_nodes_scanned),
                "shadowHostLimit": int(self.cfg.shadow_host_soft_limit),

                "enableScriptScan": bool(self.cfg.enable_script_scan),
                "scriptLimit": int(self.cfg.script_soft_limit),
                "maxScriptChars": int(self.cfg.max_script_chars),

                "enableWebpack": bool(self.cfg.enable_webpack_scan),
                "webpackLimit": int(self.cfg.webpack_module_soft_limit),
                "maxWebpackFnChars": int(self.cfg.max_webpack_fn_chars),
                "webpackUrlRegex": self.cfg.webpack_url_regex,
                "webpackApiHints": list(self.cfg.webpack_api_hints),

                # long-lost content toggles/budgets
                "enablePerf": bool(self.cfg.enable_perf_entries),
                "maxPerf": int(self.cfg.max_perf_entries),

                "enableMeta": bool(self.cfg.enable_meta_scan),
                "enableRelLinks": bool(self.cfg.enable_link_rel_scan),

                "enableSrcset": bool(self.cfg.enable_srcset_scan),
                "enableCssUrls": bool(self.cfg.enable_css_url_scan),
                "maxStyleChars": int(self.cfg.max_style_chars),

                "enableStorage": bool(self.cfg.enable_storage_scan),
                "maxStorageKeys": int(self.cfg.max_storage_keys),
                "maxStorageChars": int(self.cfg.max_storage_chars),

                "enableSpa": bool(self.cfg.enable_spa_state_scan),
                "maxSpaChars": int(self.cfg.max_spa_json_chars),
                "spaKeys": list(self.cfg.spa_state_keys),

                "enableGlobalJson": bool(self.cfg.enable_global_json_scan),
                "globalKeys": list(self.cfg.global_json_keys),
                "maxGlobalChars": int(self.cfg.max_global_json_chars),
            }

            raw_payload = {}
            try:
                raw_payload = await asyncio.wait_for(
                    page.evaluate(
                        r"""
                        (args) => {
                          const {
                            selectors, includeShadow,
                            dataKeys, onclickRegexes, redirectHints, scriptJsonHints,
                            baseUrl,
                            maxItems, maxDomNodes, shadowHostLimit,
                            enableScriptScan, scriptLimit, maxScriptChars,
                            enableWebpack, webpackLimit, maxWebpackFnChars, webpackUrlRegex, webpackApiHints,

                            enablePerf, maxPerf,
                            enableMeta, enableRelLinks,
                            enableSrcset, enableCssUrls, maxStyleChars,
                            enableStorage, maxStorageKeys, maxStorageChars,
                            enableSpa, maxSpaChars, spaKeys,
                            enableGlobalJson, globalKeys, maxGlobalChars,
                          } = args;

                          const out = [];
                          const seen = new Set();

                          function normalizeUrlRaw(u) {
                            if (!u) return "";
                            try { u = String(u); } catch { return ""; }
                            try { u = u.replace(/\\u0026/gi, "&"); } catch {}
                            try { u = u.replace(/%5Cu0026/gi, "%26"); } catch {}
                            try { u = u.replace(/\\u003a/gi, ":").replace(/\\u002f/gi, "/"); } catch {}
                            try { u = u.replace(/\\\//g, "/"); } catch {}
                            return u;
                          }

                          function absUrl(u) {
                            if (!u) return "";
                            try {
                              u = normalizeUrlRaw(String(u).trim());
                              return new URL(u, baseUrl).href;
                            } catch {
                              return String(u).trim();
                            }
                          }

                          function push(el, url, tag, reason=null) {
                            if (out.length >= maxItems) return false;
                            url = absUrl(url);
                            if (!url ||
                                url.startsWith("blob:") ||
                                url.startsWith("javascript:") ||
                                url.startsWith("data:") ||
                                seen.has(url)) {
                              return true;
                            }
                            seen.add(url);

                            let text = "";
                            try { text = (el && (el.innerText || el.textContent || el.title) || "").trim(); } catch {}
                            const item = { url, text, tag };
                            if (reason) item.reason = reason;
                            out.push(item);
                            return true;
                          }

                          function pushAny(el, s, tag, reason) {
                            if (!s) return true;
                            const txt = normalizeUrlRaw(s);
                            if (!txt) return true;

                            // find URL-ish tokens in text
                            const rx = /((https?:)?\/\/[^\s'"`<>]{6,}|\/[^\s'"`<>]{6,})/ig;
                            let m;
                            rx.lastIndex = 0;
                            while ((m = rx.exec(txt)) !== null) {
                              const cand = m[1];
                              if (!cand) continue;
                              if (!push(el, cand, tag, reason)) return false;
                              if (out.length >= maxItems) return false;
                            }
                            return true;
                          }

                          function parseSrcsetValue(v) {
                            // "url1 1x, url2 2x" / "url 640w"
                            const parts = String(v || "").split(",");
                            const urls = [];
                            for (const p of parts) {
                              const u = (p || "").trim().split(/\s+/)[0];
                              if (u) urls.push(u);
                            }
                            return urls;
                          }

                          function sniffDataAttrs(el) {
                            for (const k of dataKeys) {
                              const v = el.getAttribute?.(k);
                              if (v) { if (!push(el, v, (el.tagName||"").toLowerCase(), "data-attr")) return false; }
                            }
                            for (const attr of (el.attributes || [])) {
                              const n = (attr.name || "").toLowerCase();
                              const v = attr.value;
                              if (n.startsWith("data-") && v && (v.includes("http") || v.includes("://") || v.startsWith("/"))) {
                                if (!pushAny(el, v, (el.tagName||"").toLowerCase(), "data-generic")) return false;
                              }
                            }
                            return true;
                          }

                          function sniffOnclick(el) {
                            const oc = el.getAttribute?.("onclick") || "";
                            if (!oc) return true;

                            for (const rx of onclickRegexes) {
                              try {
                                const r = new RegExp(rx, "ig");
                                let m;
                                while ((m = r.exec(oc)) !== null) {
                                  if (m[1]) { if (!push(el, m[1], (el.tagName||"").toLowerCase(), "onclick")) return false; }
                                }
                              } catch {}
                            }

                            const ocl = oc.toLowerCase();
                            for (const h of redirectHints) {
                              if (ocl.includes(h)) {
                                const urlMatch = ocl.match(/(https?:)?\/\/[^\s'"]+/);
                                if (urlMatch) {
                                  if (!push(el, urlMatch[0], (el.tagName||"").toLowerCase(), "redirect-hint-url")) return false;
                                } else {
                                  if (!pushAny(el, oc, (el.tagName||"").toLowerCase(), "redirect-hint")) return false;
                                }
                                break;
                              }
                            }
                            return true;
                          }

                          function sniffInlineListeners(el) {
                            const inlineEvents = ["onclick","onmousedown","onmouseup","ontouchstart","ontouchend","onplay","oncanplay"];
                            for (const k of inlineEvents) {
                              const v = el.getAttribute?.(k);
                              if (!v) continue;
                              for (const rx of onclickRegexes) {
                                try {
                                  const r = new RegExp(rx, "ig");
                                  let m;
                                  while ((m = r.exec(v)) !== null) {
                                    if (m[1]) { if (!push(el, m[1], (el.tagName||"").toLowerCase(), `inline-listener-${k}`)) return false; }
                                  }
                                } catch {}
                              }
                              if (!pushAny(el, v, (el.tagName||"").toLowerCase(), `inline-listener-text-${k}`)) return false;
                            }
                            return true;
                          }

                          function sniffStyleUrls(el) {
                            if (!enableCssUrls) return true;

                            // inline style attr
                            try {
                              const st = el.getAttribute?.("style") || "";
                              if (st) { if (!pushAny(el, st, (el.tagName||"").toLowerCase(), "style-attr")) return false; }
                            } catch {}

                            // computed background-image (cheap-ish, but bounded by DOM scan caps)
                            try {
                              const cs = window.getComputedStyle?.(el);
                              const bg = cs && cs.getPropertyValue && cs.getPropertyValue("background-image");
                              if (bg && bg.includes("url(")) {
                                if (!pushAny(el, bg, (el.tagName||"").toLowerCase(), "style-bg")) return false;
                              }
                            } catch {}
                            return true;
                          }

                          // ---- bounded DOM scan (NO querySelectorAll("*") everywhere) ----
                          function scanRoot(root) {
                            let scanned = 0;
                            try {
                              const els = root.querySelectorAll?.(selectors) || [];
                              for (const el of els) {
                                scanned++;
                                if (scanned > maxDomNodes) break;

                                const tag = (el.tagName || "a").toLowerCase();

                                // direct URLs
                                const url = el.href || el.currentSrc || el.src ||
                                            el.getAttribute?.("href") || el.getAttribute?.("src") || "";
                                if (!push(el, url, tag, "dom")) return;

                                // srcset
                                if (enableSrcset) {
                                  try {
                                    const ss = el.getAttribute?.("srcset") || "";
                                    if (ss) {
                                      for (const u of parseSrcsetValue(ss)) {
                                        if (!push(el, u, tag, "srcset")) return;
                                      }
                                    }
                                  } catch {}
                                }

                                // video poster
                                try {
                                  const poster = el.getAttribute?.("poster") || "";
                                  if (poster) { if (!push(el, poster, tag, "poster")) return; }
                                } catch {}

                                if (!sniffDataAttrs(el)) return;
                                if (!sniffOnclick(el)) return;
                                if (!sniffInlineListeners(el)) return;
                                if (!sniffStyleUrls(el)) return;

                                if (out.length >= maxItems) return;
                              }
                            } catch {}
                          }

                          function scanShadowRootsBounded() {
                            if (!includeShadow) return;
                            let hosts = [];
                            try {
                              hosts = Array.from(document.querySelectorAll("[id],[class],*")).slice(0, shadowHostLimit);
                            } catch {
                              try { hosts = Array.from(document.querySelectorAll("*")).slice(0, shadowHostLimit); } catch {}
                            }
                            for (const el of hosts) {
                              try {
                                if (el && el.shadowRoot) {
                                  scanRoot(el.shadowRoot);
                                  if (out.length >= maxItems) return;
                                }
                              } catch {}
                            }
                          }

                          function scanMetaAndRelLinks() {
                            if (!enableMeta && !enableRelLinks) return;
                            const host = document.head || document.documentElement || document.body || document;

                            if (enableRelLinks) {
                              try {
                                const rels = new Set(["preload","prefetch","modulepreload","dns-prefetch","preconnect","alternate","canonical"]);
                                const links = Array.from(document.querySelectorAll("link[href]")).slice(0, 500);
                                for (const l of links) {
                                  if (out.length >= maxItems) return;
                                  const rel = String(l.getAttribute("rel") || "").toLowerCase().trim();
                                  if (!rel) continue;
                                  // rel can be space-separated
                                  const relParts = rel.split(/\s+/);
                                  if (!relParts.some(r => rels.has(r))) continue;
                                  const href = l.getAttribute("href") || "";
                                  if (!push(l, href, "link", `link-rel-${rel}`)) return;
                                }
                              } catch {}
                            }

                            if (enableMeta) {
                              try {
                                const metas = Array.from(document.querySelectorAll("meta[content]")).slice(0, 600);
                                for (const m of metas) {
                                  if (out.length >= maxItems) return;
                                  const content = m.getAttribute("content") || "";
                                  const name = (m.getAttribute("name") || m.getAttribute("property") || "").toLowerCase();
                                  // prefer url-ish meta keys, but still mine content for URLs
                                  if (name.includes("url") || name.startsWith("og:") || name.startsWith("twitter:") || name.includes("image")) {
                                    if (!pushAny(m, content, "meta", `meta-${name || "content"}`)) return;
                                  } else if (content.includes("http") || content.includes("://") || content.startsWith("/")) {
                                    if (!pushAny(m, content, "meta", "meta-content")) return;
                                  }
                                }
                              } catch {}
                            }
                          }

                          function scanCssTextBounded() {
                            if (!enableCssUrls) return;
                            let styleText = "";
                            try {
                              const styles = Array.from(document.querySelectorAll("style")).slice(0, 40);
                              for (const s of styles) {
                                if (out.length >= maxItems) return;
                                let t = "";
                                try { t = (s.textContent || "").trim(); } catch {}
                                if (!t) continue;
                                styleText += "\n" + t;
                                if (styleText.length >= maxStyleChars) break;
                              }
                            } catch {}
                            if (!styleText) return;
                            if (styleText.length > maxStyleChars) styleText = styleText.slice(0, maxStyleChars);
                            // mine url(...) and raw url-like tokens
                            pushAny(document, styleText, "style", "style-tag");
                          }

                          function scanScriptsBounded() {
                            if (!enableScriptScan) return;
                            let scripts = [];
                            try { scripts = Array.from(document.querySelectorAll("script")).slice(0, scriptLimit); } catch {}
                            for (const s of scripts) {
                              if (out.length >= maxItems) return;

                              // prioritize JSON-ish script types too
                              const type = String(s.getAttribute("type") || "").toLowerCase();
                              const isJsonType = type.includes("json") || type.includes("ld+json");

                              let txt = "";
                              try { txt = (s.textContent || "").trim(); } catch {}
                              if (!txt) continue;
                              if (txt.length > maxScriptChars) txt = txt.slice(0, maxScriptChars);

                              // raw URL-ish tokens
                              pushAny(s, txt, "script", "script-text");

                              // JSON parse for JSON-ish blobs
                              const head = txt.slice(0, 1);
                              if (isJsonType || head === "{" || head === "[") {
                                try {
                                  const data = JSON.parse(txt);
                                  const stack = [data];
                                  const visited = new WeakSet();
                                  while (stack.length) {
                                    if (out.length >= maxItems) return;
                                    const cur = stack.pop();
                                    if (!cur || typeof cur !== "object" || visited.has(cur)) continue;
                                    visited.add(cur);

                                    if (Array.isArray(cur)) {
                                      for (let i = cur.length - 1; i >= 0; i--) stack.push(cur[i]);
                                      continue;
                                    }

                                    for (const [k, v] of Object.entries(cur)) {
                                      const kl = String(k || "").toLowerCase();
                                      if (typeof v === "string") {
                                        const low = v.toLowerCase();
                                        if (low.includes("http") || low.includes("m3u8") || low.includes("mpd") || low.startsWith("/")) {
                                          if (!push(s, v, "script", "script-json-string")) return;
                                        }
                                        if (scriptJsonHints.some(h => kl.includes(h))) {
                                          if (!push(s, v, "script", "script-json-key")) return;
                                        }
                                      } else {
                                        stack.push(v);
                                      }
                                    }
                                  }
                                } catch {}
                              }
                            }
                          }

                          function scanPerfEntries() {
                            if (!enablePerf) return;
                            try {
                              const entries = performance.getEntriesByType?.("resource") || [];
                              const sliced = entries.slice(0, Math.max(1, maxPerf));
                              for (const e of sliced) {
                                if (out.length >= maxItems) return;
                                const n = e && e.name;
                                if (!n) continue;
                                if (!push(document, n, "perf", "performance-resource")) return;
                              }
                            } catch {}
                          }

                          function scanStorage() {
                            if (!enableStorage) return;

                            function dumpStorage(st, tag) {
                              try {
                                if (!st) return true;
                                const n = Math.min(st.length || 0, Math.max(1, maxStorageKeys));
                                let acc = "";
                                for (let i = 0; i < n; i++) {
                                  if (out.length >= maxItems) return false;
                                  const k = st.key(i);
                                  if (!k) continue;
                                  const v = st.getItem(k) || "";
                                  // mine key + value
                                  acc += "\n" + k + "\n" + v;
                                  if (acc.length >= maxStorageChars) break;
                                }
                                if (acc) {
                                  if (acc.length > maxStorageChars) acc = acc.slice(0, maxStorageChars);
                                  return pushAny(document, acc, tag, `${tag}-dump`);
                                }
                              } catch {}
                              return true;
                            }

                            if (!dumpStorage(window.localStorage, "localStorage")) return;
                            if (!dumpStorage(window.sessionStorage, "sessionStorage")) return;
                          }

                          function scanSpaState() {
                            if (!enableSpa) return;

                            // 1) known window keys
                            for (const k of spaKeys || []) {
                              if (out.length >= maxItems) return;
                              try {
                                const v = window[k];
                                if (!v) continue;
                                let s = "";
                                try { s = JSON.stringify(v); } catch { s = String(v); }
                                if (!s) continue;
                                if (s.length > maxSpaChars) s = s.slice(0, maxSpaChars);
                                if (!pushAny(document, s, "spa", `spa-${k}`)) return;
                              } catch {}
                            }

                            // 2) common embedded JSON nodes
                            try {
                              const nodes = [];
                              // next.js often uses this id; nuxt has __NUXT__ script sometimes
                              const n1 = document.querySelector("script#__NEXT_DATA__");
                              if (n1) nodes.push(n1);
                              const n2 = document.querySelector("script[type='application/ld+json']");
                              if (n2) nodes.push(n2);

                              for (const n of nodes.slice(0, 6)) {
                                if (out.length >= maxItems) return;
                                let txt = "";
                                try { txt = (n.textContent || "").trim(); } catch {}
                                if (!txt) continue;
                                if (txt.length > maxSpaChars) txt = txt.slice(0, maxSpaChars);
                                if (!pushAny(n, txt, "spa", "spa-embedded-script")) return;
                              }
                            } catch {}
                          }

                          function scanGlobalJson() {
                            if (!enableGlobalJson) return;
                            for (const k of globalKeys || []) {
                              if (out.length >= maxItems) return;
                              try {
                                const v = window[k];
                                if (!v) continue;
                                let s = "";
                                try { s = JSON.stringify(v); } catch { s = String(v); }
                                if (!s) continue;
                                if (s.length > maxGlobalChars) s = s.slice(0, maxGlobalChars);
                                if (!pushAny(document, s, "global", `global-${k}`)) return;
                              } catch {}
                            }
                          }

                          function scanWebpackModulesBounded() {
                            if (!enableWebpack) return;
                            let req = null;
                            try {
                              if (window.__webpack_require__ && window.__webpack_require__.c) req = window.__webpack_require__;
                            } catch {}
                            if (!req || !req.c) return;

                            let modules = [];
                            try { modules = Object.values(req.c || {}); } catch {}
                            if (!modules.length) return;

                            const limit = Math.max(1, webpackLimit);
                            if (modules.length > limit) modules = modules.slice(0, limit);

                            let rx;
                            try { rx = new RegExp(webpackUrlRegex, "ig"); } catch { return; }

                            const host = document.documentElement || document.body || document;

                            for (const mod of modules) {
                              if (out.length >= maxItems) return;
                              let src = "";
                              try {
                                let fn = null;
                                if (mod && typeof mod.toString === "function") fn = mod;
                                else if (mod && mod.exports && typeof mod.exports.toString === "function") fn = mod.exports;
                                if (!fn) continue;
                                src = String(fn.toString());
                              } catch { continue; }

                              if (!src) continue;
                              if (src.length > maxWebpackFnChars) src = src.slice(0, maxWebpackFnChars);

                              rx.lastIndex = 0;
                              let m;
                              while ((m = rx.exec(src)) !== null) {
                                if (out.length >= maxItems) return;
                                const candidate = m[0];
                                if (!candidate) continue;
                                const low = candidate.toLowerCase();
                                let ok = false;
                                for (const hint of webpackApiHints) {
                                  if (low.includes(String(hint).toLowerCase())) { ok = true; break; }
                                }
                                if (!ok) continue;
                                if (!push(host, candidate, "webpack", "webpack-module")) return;
                              }
                            }
                          }

                          // Execute (ordered from “cheap + high signal” → “heavier”)
                          scanRoot(document);
                          scanShadowRootsBounded();
                          scanMetaAndRelLinks();
                          scanPerfEntries();
                          scanCssTextBounded();
                          scanStorage();
                          scanSpaState();
                          scanScriptsBounded();
                          scanGlobalJson();
                          scanWebpackModulesBounded();

                          return { items: out, capped: out.length >= maxItems };
                        }
                        """,
                        eval_args,
                    ),
                    timeout=self.cfg.evaluate_timeout_s,
                ) or {}
            except Exception as e:
                self._log(f"page.evaluate() timed out/failed: {e}", log)
                raw_payload = {}

            raw_links = raw_payload.get("items") or []
            self._log(f"Raw links from DOM/scripts/webpack/perf/storage/spa: {len(raw_links)}", log)

            # Optional click simulation (still bounded)
            if self.cfg.enable_click_simulation:
                self._log("Starting click simulation…", log)
                try:
                    click_sel = ", ".join(self.cfg.click_target_selectors)
                    handles = await page.query_selector_all(click_sel)
                    handles = handles[: int(self.cfg.max_click_targets)]
                    self._log(f"Found {len(handles)} click targets.", log)

                    for h_idx, h in enumerate(handles):
                        try:
                            el_info = await h.evaluate("""el => ({
                                tagName: (el.tagName || "").toLowerCase(),
                                hasHref: !!el.href,
                                innerText: el.innerText,
                                isVisible: el.offsetParent !== null
                            })""")

                            if (not el_info["isVisible"] or (el_info["tagName"] == "a" and el_info["hasHref"])):
                                continue

                            await h.scroll_into_view_if_needed(timeout=1000)
                            await h.click(timeout=int(self.cfg.click_timeout_ms))
                            await page.wait_for_timeout(250)

                            click_raw = await asyncio.wait_for(
                                page.evaluate(
                                    r"""
                                    (baseUrl) => {
                                      const out = [];
                                      const seen = new Set();
                                      function normalizeUrlRaw(u) {
                                        if (!u) return "";
                                        try { u = String(u); } catch { return ""; }
                                        try { u = u.replace(/\\u0026/gi, "&"); } catch {}
                                        try { u = u.replace(/\\u003a/gi, ":").replace(/\\u002f/gi, "/"); } catch {}
                                        try { u = u.replace(/\\\//g, "/"); } catch {}
                                        return u;
                                      }
                                      function absUrl(u) {
                                        if (!u) return "";
                                        try { u = normalizeUrlRaw(String(u).trim()); return new URL(u, baseUrl).href; }
                                        catch { return String(u).trim(); }
                                      }
                                      document.querySelectorAll("a[href], video[src], audio[src], img[src], source[src], link[href]").forEach(el => {
                                        const url = absUrl(el.href || el.currentSrc || el.src || el.getAttribute("href") || el.getAttribute("src"));
                                        if (!url || seen.has(url)) return;
                                        seen.add(url);
                                        out.push({url, tag: (el.tagName || "a").toLowerCase()});
                                      });
                                      return out.slice(0, 500);
                                    }
                                    """,
                                    canonical_page_url,
                                ),
                                timeout=2.5,
                            ) or []

                            for it in click_raw:
                                raw_links.append({
                                    "url": it.get("url"),
                                    "text": "",
                                    "tag": it.get("tag") or "a",
                                    "reason": "click-sim",
                                })

                        except Exception as click_e:
                            self._log(f"Error during click sim for target {h_idx + 1}: {click_e}", log)
                            continue
                except Exception as e:
                    self._log(f"Overall click-sim error: {e}", log)

            # Filter + normalize (Python-side)
            max_links = int(self.cfg.max_links)
            for item in raw_links:
                if len(links) >= max_links:
                    break

                url = (item.get("url") or "").strip()
                if not url:
                    continue

                url = self._fix_common_escapes(url)

                canonical_url_py = _canonicalize_url(url)
                if canonical_url_py in seen_urls_in_js:
                    continue
                seen_urls_in_js.add(canonical_url_py)

                if self._is_junk_url(url):
                    continue

                kind = self._classify_kind(url)
                if not self._is_allowed_by_extensions(url, extensions, kind):
                    continue

                links.append(self._normalize_link(
                    url=canonical_url_py,
                    text=(item.get("text") or "").strip(),
                    tag=(item.get("tag") or "a"),
                ))

            self._log(f"Done: {len(links)} links for {canonical_page_url}", log)

        except Exception as e:
            self._log(f"Overall error on {canonical_page_url}: {e}", log)

        # Robust close
        try:
            try:
                await asyncio.wait_for(page.close(), timeout=3.0)
            except asyncio.TimeoutError:
                self._log("page.close() timed out; ignoring and continuing.", log)
        except Exception as e:
            self._log(f"Failed to close page: {e}", log)

        return html, links


# ======================================================================
# RuntimeSniffer (upgraded with Runtime URL Hooks + MutationObserver + Response Header Mining)
# ======================================================================

class RuntimeSniffer:
    """
    Extra-channel sniffing that complements NetworkSniffer + JSSniffer.

    Covers:
      - WebSockets (URLs + small frames with URL/manifest hints).
      - Request body JSON (GraphQL / player POSTs) via page.route.
      - Performance entries (resource timing with URL / proto).
      - localStorage / sessionStorage keys with URL-ish values.
      - Media events (play/pause/timeupdate) and src changes.
      - MediaSource / blob: instrumentation (createObjectURL, addSourceBuffer).
      - Console logs that mention manifests / streams.
      - JSON.parse hook (captures structured JSON before app logic).
      - Hydration globals (__NEXT_DATA__, __NUXT__, etc.).

    NEW (advanced):
      - Runtime URL hooks: fetch/XHR/WebSocket/EventSource/sendBeacon (URL-only ring buffer)
      - MutationObserver URL collector: href/src/data-* inserted dynamically (URL-only ring buffer)
      - Response header mining: Location + Link headers via page.on("response")
    """

    @dataclass
    class Config:
        timeout: float = 8.0

        # --- feature toggles ---
        enable_websocket_sniff: bool = True
        enable_request_body_sniff: bool = True
        enable_perf_sniff: bool = True
        enable_storage_sniff: bool = True
        enable_media_events_sniff: bool = True
        enable_mediasource_sniff: bool = True
        enable_console_sniff: bool = True

        # --- NEW: runtime URL hooks (URL-only) ---
        enable_runtime_url_hooks: bool = True
        max_runtime_url_events: int = 500
        runtime_url_keywords: Set[str] = field(default_factory=lambda: {
            "api", "graphql", "manifest", "playlist", "m3u8", "mpd", "stream", "vod", "hls", "dash"
        })

        # --- NEW: mutation observer (URL-only) ---
        enable_mutation_observer: bool = True
        mutation_observer_ms: int = 1500
        max_mutation_url_events: int = 400

        # --- NEW: response header mining (URL-only) ---
        enable_response_header_mining: bool = True
        max_header_url_events: int = 200

        # --- JSON.parse hook ---
        enable_json_parse_sniff: bool = True
        json_parse_max_bytes: int = 64 * 1024  # max source string length
        json_parse_keywords: Set[str] = field(default_factory=lambda: {
            "manifest", "playlist", "m3u8", "mpd", "stream",
            "video", "audio", "hls", "dash", "api", "graphql", "next"
        })
        json_parse_store_parsed: bool = True  # keep your previous behavior

        # --- hydration globals ---
        enable_hydration_sniff: bool = True
        hydration_keys: Set[str] = field(default_factory=lambda: {
            "__NEXT_DATA__",
            "__NUXT__",
            "__REMIX_CONTEXT__",
            "__INITIAL_STATE__",
            "__ApolloState__",
        })
        hydration_max_bytes: int = 256 * 1024  # after JSON.stringify in JS

        # --- WebSocket limits ---
        max_ws_frames: int = 50
        max_ws_frame_bytes: int = 4096

        # --- Request body limits ---
        json_body_max_kb: int = 256
        json_body_url_hints: Set[str] = field(default_factory=lambda: {
            "player", "api", "manifest", "playlist", "video", "audio", "graphql"
        })

        # --- Storage limits ---
        storage_value_max_bytes: int = 8192

        # --- Perf sniff ---
        perf_url_regex: str = r"\.(m3u8|mpd|ts|m4s|mp4|webm|mp3|aac|wav)(\?|$)"

        # --- Media events ---
        auto_play_media: bool = True
        media_event_timeout_ms: int = 4000

        # --- Console sniff ---
        console_keywords: Set[str] = field(default_factory=lambda: {
            "manifest", "m3u8", "mpd", "hls", "dash", "stream", "graphql", "/api/"
        })

        # How Playwright waits in page.goto
        goto_wait_until: str = "domcontentloaded"

    def __init__(self, config: Optional["RuntimeSniffer.Config"] = None, logger=None):
        self.cfg = config or self.Config()
        self.logger = logger or DEBUG_LOGGER
        self._log("RuntimeSniffer Initialized (advanced)", None)

        self.cfg.json_body_url_hints.update({
            "api-v2.soundcloud.com/tracks",
            "api-v2.soundcloud.com/media",
            "client_id="
        })
    # ------------------------------ logging ------------------------------ #

    def _log(self, msg: str, log_list: Optional[List[str]]) -> None:
        full = f"[RuntimeSniffer] {msg}"
        try:
            if log_list is not None:
                log_list.append(full)
            if self.logger is not None:
                self.logger.log_message(full)
        except Exception:
            pass

    # ------------------------------ helpers ------------------------------ #

    def _extract_urls_from_text(self, s: str) -> List[str]:
        if not s:
            return []
        rx = re.compile(r"\b(?:https?|wss?)://[^\s\"'<>]+", re.IGNORECASE)
        # stable de-dupe preserving order
        out: List[str] = []
        seen: Set[str] = set()
        for m in rx.findall(s):
            if m not in seen:
                seen.add(m)
                out.append(m)
        return out

    def _should_sniff_request_json(
        self,
        url_lower: str,
        ctype: str,
        content_length: Optional[int],
    ) -> bool:
        ct = (ctype or "").lower()
        if "json" not in ct:
            return False
        if not any(h in url_lower for h in self.cfg.json_body_url_hints):
            return False
        if content_length is None:
            return False
        max_bytes = int(self.cfg.json_body_max_kb) * 1024
        return content_length <= max_bytes

    # ------------------------- NEW: runtime URL hooks ------------------------- #

    async def _inject_runtime_url_hooks(
        self,
        context: "BrowserContext",
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_runtime_url_hooks:
            return

        max_events = int(self.cfg.max_runtime_url_events)
        kws = sorted({k.lower() for k in (self.cfg.runtime_url_keywords or set()) if k})
        kws_js = json.dumps(kws)

        try:
            await context.add_init_script(
                f"""
                (() => {{
                  try {{
                    const STORE = "__runtimeUrlEvents";
                    const MAX = {max_events};
                    const KWS = {kws_js};
                    const out = [];
                    const seen = new Set();

                    function want(u) {{
                      try {{
                        if (!KWS || !KWS.length) return true;
                        const low = String(u || "").toLowerCase();
                        for (const k of KWS) if (low.includes(k)) return true;
                        return false;
                      }} catch (e) {{ return true; }}
                    }}

                    function abs(u) {{
                      try {{ return new URL(String(u), location.href).href; }}
                      catch {{ return String(u || ""); }}
                    }}

                    function add(u, kind) {{
                      try {{
                        if (!u) return;
                        u = abs(u);
                        const low = u.toLowerCase();
                        if (low.startsWith("blob:") || low.startsWith("data:") || low.startsWith("javascript:")) return;
                        if (!want(u)) return;

                        const key = kind + "|" + u;
                        if (seen.has(key)) return;
                        seen.add(key);

                        out.push({{ ts: Date.now(), kind, url: u }});
                        if (out.length > MAX) out.shift();
                        window[STORE] = out;
                      }} catch (e) {{}}
                    }}

                    // fetch
                    try {{
                      const origFetch = window.fetch;
                      if (typeof origFetch === "function") {{
                        window.fetch = function(input, init) {{
                          try {{
                            const u = (typeof input === "string") ? input : (input && input.url);
                            add(u, "fetch");
                          }} catch (e) {{}}
                          return origFetch.apply(this, arguments);
                        }};
                      }}
                    }} catch (e) {{}}

                    // XHR
                    try {{
                      const origOpen = XMLHttpRequest.prototype.open;
                      XMLHttpRequest.prototype.open = function(method, url) {{
                        try {{ add(url, "xhr"); }} catch (e) {{}}
                        return origOpen.apply(this, arguments);
                      }};
                    }} catch (e) {{}}

                    // WebSocket (constructor)
                    try {{
                      const OrigWS = window.WebSocket;
                      if (typeof OrigWS === "function") {{
                        window.WebSocket = function(url, protocols) {{
                          try {{ add(url, "websocket"); }} catch (e) {{}}
                          return new OrigWS(url, protocols);
                        }};
                        window.WebSocket.prototype = OrigWS.prototype;
                      }}
                    }} catch (e) {{}}

                    // EventSource
                    try {{
                      const OrigES = window.EventSource;
                      if (typeof OrigES === "function") {{
                        window.EventSource = function(url, cfg) {{
                          try {{ add(url, "eventsource"); }} catch (e) {{}}
                          return new OrigES(url, cfg);
                        }};
                        window.EventSource.prototype = OrigES.prototype;
                      }}
                    }} catch (e) {{}}

                    // sendBeacon
                    try {{
                      const origSB = navigator.sendBeacon;
                      if (typeof origSB === "function") {{
                        navigator.sendBeacon = function(url, data) {{
                          try {{ add(url, "beacon"); }} catch (e) {{}}
                          return origSB.apply(this, arguments);
                        }};
                      }}
                    }} catch (e) {{}}
                  }} catch (e) {{
                    try {{ console.log("[RuntimeSniffer] runtime URL hook init error:", e); }} catch (_) {{}}
                  }}
                }})();
                """
            )
            self._log("Injected runtime URL hooks (fetch/xhr/ws/eventsource/beacon).", log)
        except Exception as e:
            self._log(f"Failed to inject runtime URL hooks: {e}", log)

    async def _collect_runtime_url_events(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_runtime_url_hooks:
            return

        try:
            events = await page.evaluate(
                "() => Array.isArray(window.__runtimeUrlEvents) ? window.__runtimeUrlEvents : []"
            ) or []
        except Exception as e:
            self._log(f"Error reading __runtimeUrlEvents: {e}", log)
            return

        if not events:
            return

        # de-dupe by kind|url on Python side too
        seen: Set[str] = set()
        for ev in events:
            if not isinstance(ev, dict):
                continue
            u = (ev.get("url") or "").strip()
            kind = (ev.get("kind") or "runtime").strip()
            if not u:
                continue
            k = f"{kind}|{u}"
            if k in seen:
                continue
            seen.add(k)
            runtime_hits.append({
                "url": u,
                "json": {"runtime_url": u, "kind": kind, "ts": ev.get("ts")},
                "source_page": canonical_page_url,
            })

        self._log(f"Runtime URL hook events captured: {len(seen)}", log)

    # ------------------------- NEW: mutation observer URLs ------------------------- #

    async def _inject_mutation_observer(
        self,
        context: "BrowserContext",
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_mutation_observer:
            return

        max_events = int(self.cfg.max_mutation_url_events)

        try:
            await context.add_init_script(
                f"""
                (() => {{
                  try {{
                    const STORE = "__mutationUrlEvents";
                    const MAX = {max_events};
                    const out = [];
                    const seen = new Set();

                    function abs(u) {{
                      try {{ return new URL(String(u), location.href).href; }}
                      catch {{ return String(u || ""); }}
                    }}

                    function add(u, kind) {{
                      try {{
                        if (!u) return;
                        u = abs(u);
                        const low = u.toLowerCase();
                        if (low.startsWith("blob:") || low.startsWith("data:") || low.startsWith("javascript:")) return;

                        const key = kind + "|" + u;
                        if (seen.has(key)) return;
                        seen.add(key);

                        out.push({{ ts: Date.now(), kind, url: u }});
                        if (out.length > MAX) out.shift();
                        window[STORE] = out;
                      }} catch (e) {{}}
                    }}

                    function scanEl(el) {{
                      try {{
                        if (!el || !el.getAttribute) return;
                        const href = el.getAttribute("href");
                        const src  = el.getAttribute("src");
                        if (href) add(href, "attr-href");
                        if (src) add(src, "attr-src");

                        const attrs = el.attributes || [];
                        for (let i = 0; i < attrs.length; i++) {{
                          const a = attrs[i];
                          const n = (a && a.name || "").toLowerCase();
                          const v = (a && a.value || "");
                          if (!n.startsWith("data-") || !v) continue;
                          if (/(https?:\\/\\/|wss?:\\/\\/|\\.m3u8|\\.mpd|\\/api\\/|graphql)/i.test(v)) {{
                            add(v, "data-attr");
                          }}
                        }}
                      }} catch (e) {{}}
                    }}

                    const obs = new MutationObserver((muts) => {{
                      for (const m of muts) {{
                        const nodes = m.addedNodes || [];
                        for (const node of nodes) {{
                          if (!node) continue;
                          if (node.nodeType === 1) {{
                            scanEl(node);
                            try {{
                              const kids = node.querySelectorAll ? node.querySelectorAll("[href],[src]") : [];
                              for (const k of kids) scanEl(k);
                            }} catch (e) {{}}
                          }}
                        }}
                      }}
                    }});

                    obs.observe(document.documentElement || document, {{
                      childList: true,
                      subtree: true
                    }});
                  }} catch (e) {{
                    try {{ console.log("[RuntimeSniffer] mutation observer init error:", e); }} catch (_) {{}}
                  }}
                }})();
                """
            )
            self._log("Injected MutationObserver URL collector.", log)
        except Exception as e:
            self._log(f"Failed to inject MutationObserver collector: {e}", log)

    async def _collect_mutation_url_events(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_mutation_observer:
            return

        try:
            events = await page.evaluate(
                "() => Array.isArray(window.__mutationUrlEvents) ? window.__mutationUrlEvents : []"
            ) or []
        except Exception as e:
            self._log(f"Error reading __mutationUrlEvents: {e}", log)
            return

        if not events:
            return

        seen: Set[str] = set()
        for ev in events:
            if not isinstance(ev, dict):
                continue
            u = (ev.get("url") or "").strip()
            kind = (ev.get("kind") or "mutation").strip()
            if not u:
                continue
            k = f"{kind}|{u}"
            if k in seen:
                continue
            seen.add(k)
            runtime_hits.append({
                "url": u,
                "json": {"mutation_url": u, "kind": kind, "ts": ev.get("ts")},
                "source_page": canonical_page_url,
            })

        self._log(f"Mutation URL events captured: {len(seen)}", log)

    # ------------------------- NEW: response header mining ------------------------- #

    def _attach_response_header_miner(
        self,
        page: "Page",
        runtime_hits: List[Dict[str, Any]],
        canonical_page_url: str,
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_response_header_mining:
            return

        max_events = int(self.cfg.max_header_url_events)
        seen: Set[str] = set()

        def on_response(resp: "Response"):
            try:
                hdrs = resp.headers or {}
                for k in ("location", "link"):
                    v = hdrs.get(k)
                    if not v:
                        continue
                    urls = self._extract_urls_from_text(v)
                    for u in urls:
                        kk = f"{k}|{u}"
                        if kk in seen:
                            continue
                        seen.add(kk)
                        runtime_hits.append({
                            "url": resp.url,
                            "json": {"header": k, "url": u},
                            "source_page": canonical_page_url,
                        })
                        if len(seen) >= max_events:
                            return
            except Exception:
                pass

        page.on("response", on_response)
        self._log("Attached response header miner (Location/Link).", log)

    # ------------------------- JSON.parse hook ------------------------- #

    async def _inject_json_parse_hook(
        self,
        context: "BrowserContext",
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_json_parse_sniff:
            return

        max_bytes = int(self.cfg.json_parse_max_bytes)
        kw_pattern = "|".join(sorted(self.cfg.json_parse_keywords)) or "manifest"
        kw_pattern_js = json.dumps(kw_pattern)

        try:
            await context.add_init_script(
                f"""
                (() => {{
                  try {{
                    const MAX_LEN = {max_bytes};
                    const KW_RX = new RegExp({kw_pattern_js}, "i");
                    const origParse = JSON.parse;

                    if (!window.__jsonParseSnifferEvents) {{
                      window.__jsonParseSnifferEvents = [];
                    }}

                    JSON.parse = function(str, reviver) {{
                      const val = origParse.call(this, str, reviver);
                      try {{
                        if (typeof str === "string" && str.length <= MAX_LEN) {{
                          if (KW_RX.test(str)) {{
                            window.__jsonParseSnifferEvents.push({{
                              ts: Date.now(),
                              preview: str.slice(0, MAX_LEN),
                              length: str.length
                            }});
                          }}
                        }}
                      }} catch (_) {{}}
                      return val;
                    }};
                  }} catch (e) {{
                    try {{ console.log("[RuntimeSniffer] JSON.parse hook error:", e); }} catch (_e) {{}}
                  }}
                }})();
                """
            )
            self._log("Injected JSON.parse hook script.", log)
        except Exception as e:
            self._log(f"Failed to inject JSON.parse hook script: {e}", log)

    async def _collect_json_parse_events(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_json_parse_sniff:
            return

        try:
            events = await page.evaluate(
                "() => Array.isArray(window.__jsonParseSnifferEvents) ? window.__jsonParseSnifferEvents : []"
            ) or []
        except Exception as e:
            self._log(f"Error reading __jsonParseSnifferEvents: {e}", log)
            return

        if not events:
            return

        for ev in events:
            if not isinstance(ev, dict):
                continue
            preview = ev.get("preview") or ""
            ts = ev.get("ts")
            length = ev.get("length")

            payload: Dict[str, Any] = {
                "json_parse_preview": preview[: self.cfg.json_parse_max_bytes],
                "length": length,
                "timestamp": ts,
            }

            if self.cfg.json_parse_store_parsed and preview and isinstance(preview, str):
                try:
                    payload["parsed"] = json.loads(preview)
                except Exception:
                    pass

            runtime_hits.append({
                "url": canonical_page_url,
                "json": {"json_parse": payload},
                "source_page": canonical_page_url,
            })

        self._log(f"JSON.parse events captured: {len(events)}", log)

    # ------------------------- hydration globals ------------------------- #

    async def _collect_hydration_state(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_hydration_sniff:
            return

        keys = list(self.cfg.hydration_keys) if self.cfg.hydration_keys else []
        if not keys:
            return

        max_bytes = int(self.cfg.hydration_max_bytes)

        try:
            hydration_dump = await page.evaluate(
                """
                (args) => {
                  const { keys, maxBytes } = args;
                  const out = [];
                  for (const k of keys || []) {
                    try {
                      if (!(k in window)) continue;
                      const v = window[k];
                      let jsonStr;
                      try { jsonStr = JSON.stringify(v); } catch { continue; }
                      if (!jsonStr) continue;
                      if (jsonStr.length > maxBytes) jsonStr = jsonStr.slice(0, maxBytes);
                      out.push({ key: k, json: jsonStr });
                    } catch {}
                  }
                  return out;
                }
                """,
                {"keys": keys, "maxBytes": max_bytes},
            ) or []
        except Exception as e:
            self._log(f"Hydration sniff error: {e}", log)
            return

        if not hydration_dump:
            return

        for item in hydration_dump:
            if not isinstance(item, dict):
                continue
            key = item.get("key")
            js_json = item.get("json") or ""

            payload: Dict[str, Any] = {
                "hydration_key": key,
                "preview": js_json[: max_bytes],
            }

            # keep your prior "parsed" behavior
            try:
                payload["parsed"] = json.loads(js_json)
            except Exception:
                pass

            runtime_hits.append({
                "url": canonical_page_url,
                "json": {"hydration": payload},
                "source_page": canonical_page_url,
            })

        self._log(f"Hydration globals captured: {len(hydration_dump)}", log)

    # ------------------------- attach hooks ------------------------- #

    def _attach_console_sniffer(
        self,
        page: "Page",
        runtime_hits: List[Dict[str, Any]],
        canonical_page_url: str,
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_console_sniff:
            return

        def on_console(msg):
            try:
                text = msg.text()
                low = text.lower()
                if any(kw in low for kw in self.cfg.console_keywords):
                    runtime_hits.append({
                        "url": canonical_page_url,
                        "json": {"console": text},
                        "source_page": canonical_page_url,
                    })
                    self._log(f"Console hit: {text[:200]!r}", log)
            except Exception:
                pass

        page.on("console", on_console)

    def _attach_websocket_sniffer(
        self,
        page: "Page",
        runtime_hits: List[Dict[str, Any]],
        canonical_page_url: str,
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_websocket_sniff:
            return

        max_frames = int(self.cfg.max_ws_frames)
        max_bytes = int(self.cfg.max_ws_frame_bytes)

        def on_ws(ws):
            url = getattr(ws, "url", "?")
            self._log(f"WebSocket opened: {url}", log)
            frames_seen = 0

            async def handle_frame(data):
                nonlocal frames_seen
                if frames_seen >= max_frames:
                    return
                frames_seen += 1
                try:
                    if isinstance(data, bytes):
                        if len(data) > max_bytes:
                            return
                        data = data.decode("utf-8", "ignore")
                    text = str(data)
                    low = text.lower()

                    if ("http://" in low or "https://" in low or "ws://" in low or "wss://" in low or
                        ".m3u8" in low or ".mpd" in low):
                        runtime_hits.append({
                            "url": url,
                            "json": {
                                "ws_frame": text[:max_bytes],
                                "urls": self._extract_urls_from_text(text)[:50],
                                "reason": "websocket-sniff",
                            },
                            "source_page": canonical_page_url,
                        })
                        self._log(f"WS frame hit from {url}: {text[:120]!r}", log)
                except Exception as e:
                    self._log(f"WebSocket frame error: {e}", log)

            ws.on("framereceived", lambda msg: asyncio.create_task(handle_frame(msg)))

        page.on("websocket", on_ws)

    async def _attach_request_body_sniffer(
        self,
        page: "Page",
        runtime_hits: List[Dict[str, Any]],
        canonical_page_url: str,
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_request_body_sniff:
            return

        async def route_handler(route, request):
            try:
                url = request.url
                url_lower = url.lower()
                headers = request.headers or {}
                ctype = headers.get("content-type", "")
                cl = headers.get("content-length", "")
                content_length: Optional[int] = None
                if cl and str(cl).isdigit():
                    try:
                        content_length = int(cl)
                    except Exception:
                        content_length = None

                if self._should_sniff_request_json(url_lower, ctype, content_length):
                    body: Optional[str] = None
                    try:
                        pd = getattr(request, "post_data", None)
                        if callable(pd):
                            body = await pd()
                        else:
                            body = pd
                    except Exception as e:
                        self._log(f"post_data retrieval error at {url}: {e}", log)
                        body = None

                    if body:
                        try:
                            if isinstance(body, bytes):
                                body = body.decode("utf-8", "ignore")
                            data = json.loads(body)
                            runtime_hits.append({
                                "url": url,
                                "json": {"request_body": data},
                                "source_page": canonical_page_url,
                            })
                            self._log(f"Request JSON hit at {url}", log)
                        except Exception as e:
                            self._log(f"Failed to parse request JSON at {url}: {e}", log)

            except Exception as e:
                self._log(f"route_handler error: {e}", log)

            await route.continue_()

        await page.route("**/*", route_handler)

    # ---------------------- MediaSource / MSE hook ---------------------- #

    async def _inject_mediasource_script(self, context: "BrowserContext", log: Optional[List[str]]) -> None:
        if not self.cfg.enable_mediasource_sniff:
            return

        try:
            await context.add_init_script("""
            (() => {
              try {
                const origCreateObjectURL = URL.createObjectURL;
                const origAddSourceBuffer = MediaSource.prototype.addSourceBuffer;
                window.__networkMediaEvents = window.__networkMediaEvents || [];

                function logMedia(event, payload) {
                  try {
                    window.__networkMediaEvents.push(Object.assign(
                      {event, ts: Date.now()},
                      payload || {}
                    ));
                  } catch {}
                }

                URL.createObjectURL = function(obj) {
                  const url = origCreateObjectURL.call(this, obj);
                  if (obj instanceof MediaSource) {
                    logMedia('createObjectURL', { url, mediaSourceType: 'MediaSource' });
                  }
                  return url;
                };

                MediaSource.prototype.addSourceBuffer = function(mime) {
                  let container = null;
                  let codecs = null;
                  try {
                    const m = /^([^;]+)(?:;\\s*codecs=\\"?([^\\"]+)\\"?)?$/i.exec(String(mime || ""));
                    if (m) {
                      container = m[1] || null;
                      codecs = m[2] || null;
                    }
                  } catch {}
                  logMedia('addSourceBuffer', {
                    mime: String(mime || ""),
                    container,
                    codecs
                  });
                  return origAddSourceBuffer.call(this, mime);
                };

                const desc = Object.getOwnPropertyDescriptor(HTMLMediaElement.prototype, 'src');
                if (desc && desc.set) {
                  const origSet = desc.set;
                  Object.defineProperty(HTMLMediaElement.prototype, 'src', {
                    set(value) {
                      logMedia('setMediaSrc', {
                        tagName: this.tagName.toLowerCase(),
                        src: String(value || "")
                      });
                      return origSet.call(this, value);
                    }
                  });
                }
              } catch (e) {
                try { console.log("[RuntimeSniffer] MediaSource instrumentation error:", e); } catch {}
              }
            })();
            """)
            self._log("Injected MediaSource instrumentation script.", log)
        except Exception as e:
            self._log(f"Failed to inject MediaSource script: {e}", log)

    async def _collect_mediasource_events(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_mediasource_sniff:
            return

        try:
            events = await page.evaluate(
                "() => Array.isArray(window.__networkMediaEvents) ? window.__networkMediaEvents : []"
            ) or []
        except Exception as e:
            self._log(f"Error reading __networkMediaEvents: {e}", log)
            return

        if not events:
            return

        runtime_hits.append({
            "url": canonical_page_url,
            "json": {"mse_events": events},
            "source_page": canonical_page_url,
        })
        self._log(f"MSE events captured: {len(events)}", log)

    # ---------------------- media events script ---------------------- #

    async def _inject_media_events_script(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_media_events_sniff:
            return

        try:
            auto_play = bool(self.cfg.auto_play_media)
            timeout_ms = int(self.cfg.media_event_timeout_ms)

            await page.evaluate(
                """
                (args) => {
                  const { autoPlay } = args;
                  window.__mediaEvents = [];

                  function log(ev, el) {
                    try {
                      window.__mediaEvents.push({
                        event: ev.type,
                        currentTime: el.currentTime,
                        duration: el.duration,
                        src: el.currentSrc || el.src || null,
                        muted: el.muted,
                        tag: el.tagName.toLowerCase(),
                        ts: Date.now()
                      });
                    } catch {}
                  }

                  const media = Array.from(document.querySelectorAll("video, audio"));
                  for (const el of media) {
                    ["play","pause","ended","timeupdate","error"].forEach(evt => {
                      el.addEventListener(evt, e => log(e, el));
                    });
                    if (autoPlay) {
                      try { el.muted = true; el.play().catch(() => {}); } catch {}
                    }
                  }
                }
                """,
                {"autoPlay": auto_play}
            )

            if timeout_ms > 0:
                await page.wait_for_timeout(timeout_ms)

            media_events = await page.evaluate("() => window.__mediaEvents || []") or []
            if media_events:
                runtime_hits.append({
                    "url": canonical_page_url,
                    "json": {"media_events": media_events},
                    "source_page": canonical_page_url,
                })
                self._log(f"Captured {len(media_events)} media events.", log)
        except Exception as e:
            self._log(f"Media events sniff error: {e}", log)

    async def _collect_perf_entries(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_perf_sniff:
            return

        try:
            regex_str = self.cfg.perf_url_regex
            perf_resources = await page.evaluate(
                """
                (rxStr) => {
                  let rx;
                  try { rx = new RegExp(rxStr, "i"); }
                  catch { return []; }
                  const out = [];
                  const entries = performance.getEntriesByType("resource") || [];
                  for (const e of entries) {
                    if (e && e.name && rx.test(e.name)) {
                      out.push({
                        name: e.name,
                        type: e.initiatorType || null,
                        proto: e.nextHopProtocol || null,
                        startTime: e.startTime || null,
                        duration: e.duration || null
                      });
                    }
                  }
                  return out;
                }
                """,
                regex_str
            ) or []

            if perf_resources:
                runtime_hits.append({
                    "url": canonical_page_url,
                    "json": {"perf_entries": perf_resources},
                    "source_page": canonical_page_url,
                })
                self._log(f"Perf entries hit: {len(perf_resources)}", log)
        except Exception as e:
            self._log(f"Perf sniff error: {e}", log)

    async def _collect_storage(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_storage_sniff:
            return

        try:
            max_bytes = int(self.cfg.storage_value_max_bytes)
            storage_hits = await page.evaluate(
                """
                (maxBytes) => {
                  const out = [];
                  function scan(kind, store) {
                    try {
                      const len = store.length || 0;
                      for (let i = 0; i < len; i++) {
                        const key = store.key(i);
                        const val = store.getItem(key) || "";
                        if (!val) continue;
                        if (val.length > maxBytes) continue;
                        if (/(https?:\\/\\/|\\.m3u8|\\.mpd|\\/api\\/|graphql)/i.test(val)) {
                          out.push({ kind, key, value: val });
                        }
                      }
                    } catch {}
                  }
                  try { scan("localStorage", window.localStorage); } catch {}
                  try { scan("sessionStorage", window.sessionStorage); } catch {}
                  return out;
                }
                """,
                max_bytes
            ) or []

            if storage_hits:
                runtime_hits.append({
                    "url": canonical_page_url,
                    "json": {"storage": storage_hits},
                    "source_page": canonical_page_url,
                })
                self._log(f"Storage hits: {len(storage_hits)}", log)
        except Exception as e:
            self._log(f"Storage sniff error: {e}", log)

    # ------------------------- main sniff ------------------------- #

    async def sniff(
        self,
        context: "BrowserContext",
        page_url: str,
        *,
        timeout: Optional[float] = None,
        log: Optional[List[str]] = None,
    ) -> Tuple[str, List[Dict[str, Any]]]:

        if context is None:
            self._log("No Playwright context; skipping runtime sniff.", log)
            return "", []
        if Page is None:
            self._log("Playwright classes not found; skipping runtime sniff.", log)
            return "", []

        tmo = float(timeout if timeout is not None else self.cfg.timeout)
        canonical_page_url = _canonicalize_url(page_url)
        runtime_hits: List[Dict[str, Any]] = []

        # Context-level hooks (MUST run before new_page / navigation)
        await self._inject_mediasource_script(context, log)
        await self._inject_json_parse_hook(context, log)
        await self._inject_runtime_url_hooks(context, log)
        await self._inject_mutation_observer(context, log)

        page: Page = await context.new_page()
        html: str = ""
        wait_mode = getattr(self.cfg, "goto_wait_until", "domcontentloaded")
        goto_timeout_ms = max(15000, int(tmo * 1000))

        # Attach page-level hooks BEFORE navigation
        self._attach_console_sniffer(page, runtime_hits, canonical_page_url, log)
        self._attach_websocket_sniffer(page, runtime_hits, canonical_page_url, log)
        if self.cfg.enable_response_header_mining:
            self._attach_response_header_miner(page, runtime_hits, canonical_page_url, log)
        await self._attach_request_body_sniffer(page, runtime_hits, canonical_page_url, log)

        self._log(f"Start runtime sniff: {canonical_page_url} timeout={tmo}s", log)

        try:
            try:
                await page.goto(
                    canonical_page_url,
                    wait_until=wait_mode,
                    timeout=goto_timeout_ms,
                )
            except Exception as e:
                self._log(
                    f"goto timeout on {canonical_page_url} (wait_until={wait_mode}): {e}",
                    log,
                )

            # Let page settle a bit
            await page.wait_for_timeout(int(tmo * 1000 * 0.2))
            try:
                await page.click('button[title="Play"], button[aria-label="Play"]', timeout=1500)
            except Exception:
                pass
            # Give MutationObserver a small window to accumulate SPA inserts
            if self.cfg.enable_mutation_observer:
                await page.wait_for_timeout(max(0, int(self.cfg.mutation_observer_ms)))

            # Media events (may auto-play)
            await self._inject_media_events_script(page, canonical_page_url, runtime_hits, log)

            # Perf entries
            await self._collect_perf_entries(page, canonical_page_url, runtime_hits, log)

            # Storage
            await self._collect_storage(page, canonical_page_url, runtime_hits, log)

            # MSE events
            await self._collect_mediasource_events(page, canonical_page_url, runtime_hits, log)

            # JSON.parse hook results
            await self._collect_json_parse_events(page, canonical_page_url, runtime_hits, log)

            # Hydration globals
            await self._collect_hydration_state(page, canonical_page_url, runtime_hits, log)

            # NEW: runtime URL hook ring buffer
            await self._collect_runtime_url_events(page, canonical_page_url, runtime_hits, log)

            # NEW: mutation observer URL ring buffer
            await self._collect_mutation_url_events(page, canonical_page_url, runtime_hits, log)

            try:
                html = await page.content()
            except Exception as e:
                self._log(f"Failed to get page content: {e}", log)
                html = ""

        except Exception as e:
            self._log(f"Unexpected error during runtime sniff: {e}", log)
        finally:
            try:
                try:
                    await asyncio.wait_for(page.close(), timeout=3.0)
                except asyncio.TimeoutError:
                    self._log("page.close() timed out; ignoring.", log)
            except Exception as e:
                self._log(f"Failed to close page: {e}", log)

        self._log(f"Finished runtime sniff for {canonical_page_url}: hits={len(runtime_hits)}", log)
        return html, runtime_hits

# ======================================================================
# ReactSniffer (Advanced: Fiber + Router + State URLs)
# ======================================================================

class ReactSniffer:
    """
    Playwright-based sniffer focused on React / SPA behavior.

    Goals (structural):
      • Match the API of other sniffers (NetworkSniffer, JSSniffer, RuntimeSniffer).
      • Single public entrypoint: `await sniff(context, page_url, timeout, log, extensions=None)`.
      • Return `(html, hits)` so it can be dropped into existing pipelines.

    `hits` is a list of dicts like:
        {
            "page": <page_url>,
            "url": <derived or navigated URL>,
            "route": <react route / pathname>,
            "tag": "react_route" | "react_link" | "react_nav" | "react_meta",
            "kind": "initial" | "pushState" | "replaceState" | "popstate"
                    | "hashchange" | "click"
                    | "react_devtools" | "summary"
                    | "router_config" | "fiber_link" | "fiber_state_url",
            "meta": {...anything extra...},
        }

    New “active” capabilities:
      • React Router Extraction:
            - Reads router-like configs discovered in memory (paths, children).
      • Fiber Tree Crawling:
            - Walks React Fiber roots to find props like:
                to="/dashboard", href="...", path="..."
              even when not present in the DOM yet.
      • State Inspection:
            - Examines memoizedState / state for URL-like strings
              (API endpoints, internal routes, etc).
    """

    # ------------------------------------------------------------------ #
    # Config
    # ------------------------------------------------------------------ #
    @dataclass
    class Config:
        # generic controls
        timeout: float = 8.0
        max_hits: int = 200

        # how long to wait after first load for SPA nav / route changes
        wait_after_load_ms: int = 1000

        # whether to instrument history / pushState / replaceState
        hook_history_api: bool = True

        # whether to instrument common React-link clicks
        hook_link_clicks: bool = True

        # whether to attempt to read React DevTools global hook as a hint
        inspect_react_devtools_hook: bool = False

        # advanced controls
        capture_hashchange: bool = True
        dedupe_events: bool = True
        max_events_per_kind: int = 500  # safety cap per kind inside the browser

        # whether to emit an aggregate summary hit
        emit_summary_hit: bool = True

        # ----- NEW: Fiber / Router / State inspection toggles -----
        enable_fiber_traversal: bool = True
        enable_router_inspection: bool = True
        enable_state_url_scan: bool = True

        # Limits for traversal / extraction
        max_fiber_nodes: int = 5000
        max_router_entries: int = 500

        # Heuristic: what looks like a URL / route?
        url_like_regex: str = r"(https?://[^\s\"']+|/[A-Za-z0-9_./-]+)"

    # ------------------------------------------------------------------ #
    # Internal memory data structures ("sniffer memory")
    # ------------------------------------------------------------------ #
    @dataclass
    class RouteEvent:
        kind: str
        url: str
        pathname: str
        timestamp: Optional[float] = None

    @dataclass
    class ClickEvent:
        url: str
        pathname: str
        text: str
        timestamp: Optional[float] = None

    @dataclass
    class DevtoolsSummary:
        has_react: bool = False
        renderer_ids: List[str] = field(default_factory=list)
        timestamp: Optional[float] = None

    def __init__(self, config: "ReactSniffer.Config", logger=None):
        self.cfg = config
        self.logger = logger or DEBUG_LOGGER
        self._reset_memory()
        self._log("ReactSniffer Initialized", None)

    # ------------------------------------------------------------------ #
    # Logging helper
    # ------------------------------------------------------------------ #
    def _log(self, msg: str, log_list: Optional[List[str]]) -> None:
        full = f"[ReactSniffer] {msg}"
        try:
            if log_list is not None:
                log_list.append(full)
            if self.logger is not None:
                self.logger.log_message(full)
        except Exception:
            pass

    # ------------------------------------------------------------------ #
    # Memory lifecycle
    # ------------------------------------------------------------------ #
    def _reset_memory(self) -> None:
        self._nav_events: List[ReactSniffer.RouteEvent] = []
        self._click_events: List[ReactSniffer.ClickEvent] = []
        self._routes_seen: Set[str] = set()
        self._urls_seen: Set[str] = set()
        # Router config extracted from fiber / globals
        self._router_routes: List[Dict[str, Any]] = []
        # event fingerprints so we don't double-count same browser event
        # fingerprint = (kind, url, pathname, timestamp)
        self._event_fingerprint_seen: Set[Tuple[Any, Any, Any, Any]] = set()
        self._summary: Optional[ReactSniffer.DevtoolsSummary] = None

    # ------------------------------------------------------------------ #
    # Public API (matches other sniffers)
    # ------------------------------------------------------------------ #
    async def sniff(
        self,
        context,              # Playwright BrowserContext
        page_url: str,
        timeout: float,
        log: List[str],
        extensions=None,      # kept for signature compatibility; usually unused
    ) -> Tuple[str, List[Dict[str, Any]]]:
        """
        Main entrypoint.

        Returns:
            (html, hits)
        Where:
            html: final outerHTML / document HTML snapshot (str)
            hits: list of dicts describing React routes / SPA navigations.
        """
        from playwright.async_api import TimeoutError as PWTimeoutError

        # fresh memory for each sniff run
        self._reset_memory()
        self._log(f"Start React sniff: {page_url} timeout={timeout}s", log)

        page = None
        hits: List[Dict[str, Any]] = []
        html: str = ""

        try:
            page = await context.new_page()
            await page.goto(
                page_url,
                wait_until="domcontentloaded",
                timeout=int(timeout * 1000),
            )

            # Install instrumentation before SPA settles
            await self._install_instrumentation(page, page_url, log)

            # Give React / SPA some time to bootstrap & navigate
            await page.wait_for_timeout(self.cfg.wait_after_load_ms)

            # Grab HTML
            try:
                html = await page.content()
            except Exception as e:
                self._log(f"Error getting HTML for {page_url}: {e}", log)

            # Extract SPA / React hints into memory
            try:
                raw_hits = await self._collect_raw_hits(page, page_url, log)
                self._ingest_raw_hits(raw_hits, page_url, log)
                hits = self._materialize_hits(page_url)
            except Exception as e:
                self._log(f"Error collecting hits for {page_url}: {e}", log)

        except PWTimeoutError:
            self._log(f"Timeout while loading {page_url}", log)
        except Exception as e:
            self._log(f"Fatal error on {page_url}: {e}", log)
        finally:
            if page is not None:
                try:
                    await page.close()
                except Exception as e:
                    self._log(f"Error closing page for {page_url}: {e}", log)

        # Enforce max_hits
        if len(hits) > self.cfg.max_hits:
            hits = hits[: self.cfg.max_hits]

        self._log(f"Finished React sniff for {page_url}: hits={len(hits)}", log)
        return html or "", hits

    # ------------------------------------------------------------------ #
    # Internal helpers: JS injection
    # ------------------------------------------------------------------ #
    async def _install_instrumentation(self, page, page_url: str, log: List[str]) -> None:
        """
        Inject JavaScript into the page to observe:
          • history.pushState / replaceState
          • popstate
          • hashchange (optional)
          • link clicks
          • optional React DevTools hook
          • OPTIONAL (advanced):
                - Fiber traversal
                - Router config extraction
                - State URL sniffing

        Stashes events on window.__PROMPTCHAT_REACT_SNIFFER_HITS__.
        """
        script_parts: List[str] = []

        max_events_per_kind = int(self.cfg.max_events_per_kind)

        # ------------------------------------------------------------------
        # Shared event buffer + pushEvent helper
        # ------------------------------------------------------------------
        script_parts.append(
            f"""
            (function() {{
                try {{
                    if (!window.__PROMPTCHAT_REACT_SNIFFER_HITS__) {{
                        window.__PROMPTCHAT_REACT_SNIFFER_HITS__ = [];
                    }}

                    var MAX_EVENTS_PER_KIND = {max_events_per_kind};

                    function __RS_pushEvent(evt) {{
                        try {{
                            var arr = window.__PROMPTCHAT_REACT_SNIFFER_HITS__;
                            if (!Array.isArray(arr)) {{
                                arr = [];
                                window.__PROMPTCHAT_REACT_SNIFFER_HITS__ = arr;
                            }}
                            var kind = evt && evt.kind || "unknown";
                            var count = 0;
                            for (var i = 0; i < arr.length; i++) {{
                                if (arr[i] && arr[i].kind === kind) {{
                                    count++;
                                    if (count >= MAX_EVENTS_PER_KIND) {{
                                        return;
                                    }}
                                }}
                            }}
                            arr.push(evt);
                        }} catch (_) {{}}
                    }}

                    window.__RS_pushEvent = __RS_pushEvent;
                }} catch (e) {{
                    try {{
                        console.log("[ReactSniffer] Shared buffer init error:", e);
                    }} catch (_e) {{}}
                }}
            }})();"""
        )

        # ------------------------------------------------------------------
        # History / SPA navigation hooks
        # ------------------------------------------------------------------
        if self.cfg.hook_history_api or self.cfg.capture_hashchange:
            script_parts.append(
                """
                (function() {
                    try {
                        if (typeof window.__RS_pushEvent !== "function") return;

                        function recordReactNav(kind, url) {
                            try {
                                window.__RS_pushEvent({
                                    kind: kind,
                                    url: String(url || location.href),
                                    href: String(location.href),
                                    pathname: location.pathname,
                                    search: location.search,
                                    hash: location.hash,
                                    timestamp: Date.now()
                                });
                            } catch (_) {}
                        }
                """
            )

            if self.cfg.hook_history_api:
                script_parts.append(
                    """
                        var origPush = history.pushState;
                        var origReplace = history.replaceState;

                        history.pushState = function(state, title, url) {
                            try { origPush.apply(this, arguments); } catch (_) {}
                            recordReactNav("pushState", url);
                        };

                        history.replaceState = function(state, title, url) {
                            try { origReplace.apply(this, arguments); } catch (_) {}
                            recordReactNav("replaceState", url);
                        };

                        window.addEventListener("popstate", function() {
                            recordReactNav("popstate", location.href);
                        });

                        // initial page load
                        recordReactNav("initial", location.href);
                    """
                )

            if self.cfg.capture_hashchange:
                script_parts.append(
                    """
                        window.addEventListener("hashchange", function() {
                            recordReactNav("hashchange", location.href);
                        });
                    """
                )

            script_parts.append(
                """
                    } catch (e) {
                        try {
                            console.log("[ReactSniffer] History instrumentation error:", e);
                        } catch (_e) {}
                    }
                })();
                """
            )

        # ------------------------------------------------------------------
        # Link click hooks
        # ------------------------------------------------------------------
        if self.cfg.hook_link_clicks:
            script_parts.append(
                """
                (function() {
                    try {
                        if (typeof window.__RS_pushEvent !== "function") return;

                        document.addEventListener("click", function(ev) {
                            try {
                                var t = ev.target;
                                // climb up to nearest <a> if needed
                                while (t && t !== document && !t.href) {
                                    t = t.parentElement;
                                }
                                if (!t || !t.href) { return; }

                                window.__RS_pushEvent({
                                    kind: "click",
                                    url: String(t.href),
                                    href: String(t.href),
                                    pathname: location.pathname,
                                    search: location.search,
                                    hash: location.hash,
                                    text: (t.innerText || "").trim(),
                                    timestamp: Date.now()
                                });
                            } catch (_) {}
                        }, true);
                    } catch (e) {
                        try {
                            console.log("[ReactSniffer] Link instrumentation error:", e);
                        } catch (_e) {}
                    }
                })();
                """
            )

        # ------------------------------------------------------------------
        # Optional React DevTools hook inspection
        # ------------------------------------------------------------------
        if self.cfg.inspect_react_devtools_hook:
            script_parts.append(
                """
                (function() {
                    try {
                        if (typeof window.__RS_pushEvent !== "function") return;

                        var hook = window.__REACT_DEVTOOLS_GLOBAL_HOOK__;
                        if (hook && hook.renderers) {
                            var rendererIds = Object.keys(hook.renderers || {});
                            window.__RS_pushEvent({
                                kind: "react_devtools",
                                rendererIds: rendererIds,
                                hasReact: rendererIds.length > 0,
                                pathname: location.pathname,
                                href: String(location.href),
                                timestamp: Date.now()
                            });
                        }
                    } catch (e) {
                        try {
                            console.log("[ReactSniffer] DevTools hook inspection error:", e);
                        } catch (_e) {}
                    }
                })();
                """
            )

        # ------------------------------------------------------------------
        # NEW: Fiber traversal + Router/state extraction
        # ------------------------------------------------------------------
        if (
            self.cfg.enable_fiber_traversal
            or self.cfg.enable_router_inspection
            or self.cfg.enable_state_url_scan
        ):
            url_rx = self.cfg.url_like_regex or r"(https?://[^\\s\"']+|/[A-Za-z0-9_./-]+)"
            # safe JSON string for JS
            url_rx_js = json.dumps(url_rx)

            script_parts.append(
                f"""
                (function() {{
                    try {{
                        if (typeof window.__RS_pushEvent !== "function") return;

                        var MAX_FIBER_NODES = {int(self.cfg.max_fiber_nodes)};
                        var MAX_ROUTES = {int(self.cfg.max_router_entries)};
                        var URL_RX = new RegExp({url_rx_js}, "i");

                        function isUrlish(str) {{
                            if (typeof str !== "string") return false;
                            if (!str) return false;
                            if (URL_RX.test(str)) return true;
                            if (str[0] === "/" && str.length <= 256) return true;
                            return false;
                        }}

                        function emitFiberLink(url, meta) {{
                            try {{
                                if (!url || !isUrlish(url)) return;
                                window.__RS_pushEvent({{
                                    kind: "fiber_link",
                                    url: String(url),
                                    href: String(location.href),
                                    pathname: location.pathname,
                                    meta: meta || {{}},
                                    timestamp: Date.now()
                                }});
                            }} catch (_) {{}}
                        }}

                        function emitStateUrl(url, meta) {{
                            try {{
                                if (!url || !isUrlish(url)) return;
                                window.__RS_pushEvent({{
                                    kind: "fiber_state_url",
                                    url: String(url),
                                    href: String(location.href),
                                    pathname: location.pathname,
                                    meta: meta || {{}},
                                    timestamp: Date.now()
                                }});
                            }} catch (_) {{}}
                        }}

                        function scanObjectForUrls(obj, meta, depth, maxDepth, cb) {{
                            if (!obj || typeof obj !== "object") return;
                            if (depth > maxDepth) return;
                            var seen = new WeakSet();
                            function walk(o, d) {{
                                if (!o || typeof o !== "object") return;
                                if (seen.has(o)) return;
                                seen.add(o);
                                if (d > maxDepth) return;
                                var keys = Object.keys(o);
                                for (var i = 0; i < keys.length; i++) {{
                                    var k = keys[i];
                                    var v = o[k];
                                    if (typeof v === "string") {{
                                        if (isUrlish(v)) {{
                                            cb(v, Object.assign({{ key: k }}, meta || {{}}));
                                        }}
                                    }} else if (v && typeof v === "object") {{
                                        walk(v, d + 1);
                                    }}
                                }}
                            }}
                            walk(obj, depth);
                        }}

                        function gatherRouterRoutesFromConfig(config, meta, out) {{
                            if (!config || typeof config !== "object") return;
                            var seen = new WeakSet();
                            function walkRouteNode(node, baseMeta) {{
                                if (!node || typeof node !== "object") return;
                                if (seen.has(node)) return;
                                seen.add(node);
                                var path = null;
                                var hasIndex = false;

                                try {{
                                    if (typeof node.path === "string") {{
                                        path = node.path;
                                    }} else if (typeof node.route === "string") {{
                                        path = node.route;
                                    }}
                                    if (node.index === true) {{
                                        hasIndex = true;
                                    }}
                                }} catch (_) {{}}

                                if (path || hasIndex) {{
                                    out.push({{
                                        path: path || null,
                                        index: !!hasIndex,
                                        meta: baseMeta || meta || {{}}
                                    }});
                                }}

                                var children = null;
                                try {{
                                    children = node.children || node.routes || node.childRoutes || null;
                                }} catch (_) {{}}

                                if (Array.isArray(children)) {{
                                    for (var i = 0; i < children.length; i++) {{
                                        walkRouteNode(children[i], baseMeta || meta);
                                        if (out.length >= MAX_ROUTES) return;
                                    }}
                                }}
                            }}

                            walkRouteNode(config, meta || {{}});
                        }}

                        function getFiberRootsFromDevtools() {{
                            var hook = window.__REACT_DEVTOOLS_GLOBAL_HOOK__;
                            if (!hook || !hook.getFiberRoots) return [];
                            var roots = [];
                            try {{
                                var rendererIds = Object.keys(hook.renderers || {{}});
                                for (var i = 0; i < rendererIds.length; i++) {{
                                    var id = Number(rendererIds[i]);
                                    var rootSet = hook.getFiberRoots(id);
                                    if (!rootSet) continue;
                                    if (typeof rootSet.forEach === "function") {{
                                        rootSet.forEach(function(root) {{
                                            if (root && root.current) {{
                                                roots.push(root.current);
                                            }} else if (root) {{
                                                roots.push(root);
                                            }}
                                        }});
                                    }}
                                }}
                            }} catch (e) {{
                                try {{
                                    console.log("[ReactSniffer] getFiberRoots error", e);
                                }} catch (_e) {{}}
                            }}
                            return roots;
                        }}

                        function traverseFiberRoot(root, routerRoutes) {{
                            var seen = new WeakSet();
                            var count = 0;

                            function visit(node) {{
                                if (!node || typeof node !== "object") return;
                                if (seen.has(node)) return;
                                seen.add(node);

                                if (count >= MAX_FIBER_NODES) return;
                                count++;

                                var elementTypeName = null;
                                try {{
                                    var et = node.elementType || node.type || null;
                                    if (et && typeof et === "function" && et.name) {{
                                        elementTypeName = et.name;
                                    }} else if (typeof et === "string") {{
                                        elementTypeName = et;
                                    }}
                                }} catch (_) {{}}

                                // ----- props scan -----
                                try {{
                                    var props = node.memoizedProps || node.pendingProps || node.props || null;
                                    if (props && typeof props === "object") {{
                                        // Common React Router / link props
                                        ["to", "href", "as", "path"].forEach(function(key) {{
                                            if (props && typeof props[key] === "string") {{
                                                var val = props[key];
                                                if (isUrlish(val)) {{
                                                    emitFiberLink(val, {{
                                                        where: "props",
                                                        key: key,
                                                        elementType: elementTypeName
                                                    }});
                                                    if (key === "path" && routerRoutes.length < MAX_ROUTES) {{
                                                        routerRoutes.push({{
                                                            path: val,
                                                            index: false,
                                                            meta: {{ source: "fiber_props", elementType: elementTypeName }}
                                                        }});
                                                    }}
                                                }}
                                            }}
                                        }});

                                        // Also scan nested objects for URL-ish strings
                                        scanObjectForUrls(
                                            props,
                                            {{ where: "props_deep", elementType: elementTypeName }},
                                            0,
                                            2,
                                            emitFiberLink
                                        );
                                    }}
                                }} catch (_) {{}}

                                // ----- state scan -----
                                try {{
                                    var st = node.memoizedState || (node.stateNode && node.stateNode.state) || null;
                                    if (st && typeof st === "object") {{
                                        scanObjectForUrls(
                                            st,
                                            {{ where: "state", elementType: elementTypeName }},
                                            0,
                                            2,
                                            emitStateUrl
                                        );
                                    }}
                                }} catch (_) {{}}

                                // descend
                                try {{ visit(node.child); }} catch (_) {{}}
                                try {{ visit(node.sibling); }} catch (_) {{}}
                            }}

                            visit(root);
                        }}

                        function scanReactRouterFromGlobals(routerRoutes) {{
                            try {{
                                // Heuristic search in window for route configs
                                var rootKeys = Object.keys(window || {{}});
                                for (var i = 0; i < rootKeys.length; i++) {{
                                    var k = rootKeys[i];
                                    if (!k) continue;
                                    // skip obvious noise
                                    if (k === "webpackJsonp" || k === "__PROMPTCHAT_REACT_SNIFFER_HITS__" || k === "__RS_pushEvent") continue;
                                    if (k.indexOf("route") === -1 && k.indexOf("Router") === -1) continue;

                                    var v;
                                    try {{ v = window[k]; }} catch (_e) {{ v = null; }}
                                    if (!v || typeof v !== "object") continue;
                                    gatherRouterRoutesFromConfig(
                                        v,
                                        {{ source: "window:"+k }},
                                        routerRoutes
                                    );
                                    if (routerRoutes.length >= MAX_ROUTES) break;
                                }}
                            }} catch (e) {{
                                try {{
                                    console.log("[ReactSniffer] scanReactRouterFromGlobals error", e);
                                }} catch (_e) {{}}
                            }}
                        }}

                        function runFiberScan() {{
                            try {{
                                var routerRoutes = [];
                                var roots = getFiberRootsFromDevtools();
                                for (var i = 0; i < roots.length; i++) {{
                                    traverseFiberRoot(roots[i], routerRoutes);
                                    if (routerRoutes.length >= MAX_ROUTES) break;
                                }}

                                scanReactRouterFromGlobals(routerRoutes);

                                if (routerRoutes.length) {{
                                    window.__RS_pushEvent({{
                                        kind: "react_router_routes",
                                        url: String(location.href),
                                        href: String(location.href),
                                        pathname: location.pathname,
                                        meta: {{
                                            routes: routerRoutes.slice(0, MAX_ROUTES)
                                        }},
                                        timestamp: Date.now()
                                    }});
                                }}
                            }} catch (e) {{
                                try {{
                                    console.log("[ReactSniffer] runFiberScan error", e);
                                }} catch (_e) {{}}
                            }}
                        }}

                        // Schedule after initial React bootstraps
                        setTimeout(runFiberScan, 0);
                    }} catch (e) {{
                        try {{
                            console.log("[ReactSniffer] Fiber instrumentation error:", e);
                        }} catch (_e) {{}}
                    }}
                }})();
                """
            )

        final_script = "\n".join(script_parts)

        try:
            await page.add_init_script(final_script)
            # also run immediately for the already-loaded document
            await page.evaluate(final_script)
            self._log(f"Instrumentation installed on {page_url}", log)
        except Exception as e:
            self._log(f"Failed to install instrumentation on {page_url}: {e}", log)

    # ------------------------------------------------------------------ #
    # Collect & ingest raw hits
    # ------------------------------------------------------------------ #
    async def _collect_raw_hits(self, page, page_url: str, log: List[str]) -> List[Dict[str, Any]]:
        """
        Read back the window.__PROMPTCHAT_REACT_SNIFFER_HITS__ array.
        """
        try:
            raw_hits = await page.evaluate(
                """() => {
                    try {
                        return Array.isArray(window.__PROMPTCHAT_REACT_SNIFFER_HITS__)
                            ? window.__PROMPTCHAT_REACT_SNIFFER_HITS__
                            : [];
                    } catch (e) {
                        return [];
                    }
                }"""
            )
        except Exception as e:
            self._log(f"Error reading hits from {page_url}: {e}", log)
            return []

        if not isinstance(raw_hits, list):
            raw_hits = []

        self._log(f"Raw hits length={len(raw_hits)} for {page_url}", log)
        return raw_hits

    def _ingest_raw_hits(self, raw_hits: List[Dict[str, Any]], page_url: str, log: List[str]) -> None:
        """
        Convert JS-side events into internal dataclasses (sniffer memory).
        """
        for h in raw_hits or []:
            if not isinstance(h, dict):
                continue

            kind = str(h.get("kind") or "react_nav")
            url = str(h.get("url") or h.get("href") or page_url)
            pathname = str(h.get("pathname") or "")
            timestamp = h.get("timestamp")

            # dedupe based on event fingerprint if enabled
            fp = (kind, url, pathname, timestamp)
            if self.cfg.dedupe_events and fp in self._event_fingerprint_seen:
                continue
            self._event_fingerprint_seen.add(fp)

            if kind in ("initial", "pushState", "replaceState", "popstate", "hashchange", "react_nav"):
                self._register_nav(kind, url, pathname, timestamp)

            elif kind == "click":
                text = str(h.get("text") or "")
                self._register_click(url, pathname, text, timestamp)

            elif kind == "react_devtools":
                renderer_ids = list(h.get("rendererIds") or [])
                has_react = bool(h.get("hasReact"))
                self._register_summary(has_react, renderer_ids, timestamp)

            elif kind == "react_router_routes":
                # Router config dump; meta.routes is a list of {path, index, meta}
                meta = h.get("meta") or {}
                routes = meta.get("routes") or []
                if isinstance(routes, list):
                    for r in routes:
                        if not isinstance(r, dict):
                            continue
                        path = str(r.get("path") or "")
                        idx_flag = bool(r.get("index", False))
                        rmeta = r.get("meta") or {}
                        if path:
                            self._router_routes.append(
                                {
                                    "path": path,
                                    "index": idx_flag,
                                    "meta": rmeta,
                                }
                            )
                            # treat as navigation-type route as well
                            self._register_nav("router_config", url, path, timestamp)

            else:
                # unknown kinds (fiber_link, fiber_state_url, etc.) treated as generic nav
                self._register_nav(kind, url, pathname, timestamp)

        self._log(
            f"Memory populated: "
            f"{len(self._nav_events)} nav_events, "
            f"{len(self._click_events)} click_events, "
            f"router_routes={len(self._router_routes)}, "
            f"summary={'present' if self._summary else 'none'}",
            log,
        )

    # ------------------------------------------------------------------ #
    # Memory helpers
    # ------------------------------------------------------------------ #
    def _register_nav(self, kind: str, url: str, pathname: str, timestamp: Optional[float]) -> None:
        self._nav_events.append(
            ReactSniffer.RouteEvent(
                kind=kind,
                url=url,
                pathname=pathname,
                timestamp=timestamp,
            )
        )
        self._urls_seen.add(url)
        if pathname:
            self._routes_seen.add(pathname)

    def _register_click(self, url: str, pathname: str, text: str, timestamp: Optional[float]) -> None:
        self._click_events.append(
            ReactSniffer.ClickEvent(
                url=url,
                pathname=pathname,
                text=text,
                timestamp=timestamp,
            )
        )
        self._urls_seen.add(url)
        if pathname:
            self._routes_seen.add(pathname)

    def _register_summary(self, has_react: bool, renderer_ids: List[str], timestamp: Optional[float]) -> None:
        self._summary = ReactSniffer.DevtoolsSummary(
            has_react=has_react,
            renderer_ids=renderer_ids,
            timestamp=timestamp,
        )

    # ------------------------------------------------------------------ #
    # Memory -> final hits
    # ------------------------------------------------------------------ #
    def _materialize_hits(self, page_url: str) -> List[Dict[str, Any]]:
        """
        Turn sniffer memory into the final list of dict hits.

        This mirrors the pattern of NetworkSniffer / JSSniffer:
          • 'page' always present
          • 'url', 'route', 'tag', 'kind'
          • 'meta' for extra info
        """
        hits: List[Dict[str, Any]] = []

        # 1) Nav events (history, hashchange, router_config, fiber_link, etc.)
        for nav in self._nav_events:
            hits.append(
                {
                    "page": page_url,
                    "url": nav.url,
                    "route": nav.pathname,
                    "tag": "react_route",
                    "kind": nav.kind,
                    "meta": {
                        "timestamp": nav.timestamp,
                    },
                }
            )

        # 2) Click events
        for click in self._click_events:
            hits.append(
                {
                    "page": page_url,
                    "url": click.url,
                    "route": click.pathname,
                    "tag": "react_link",
                    "kind": "click",
                    "meta": {
                        "text": click.text,
                        "timestamp": click.timestamp,
                    },
                }
            )

        # 3) Router routes (from config / fiber props)
        for r in self._router_routes:
            path = r.get("path") or ""
            meta = dict(r.get("meta") or {})
            meta["index"] = bool(r.get("index", False))
            hits.append(
                {
                    "page": page_url,
                    "url": path or page_url,
                    "route": path,
                    "tag": "react_route",
                    "kind": "router_config",
                    "meta": meta,
                }
            )

        # 4) Devtools info as its own hit
        if self._summary is not None:
            hits.append(
                {
                    "page": page_url,
                    "url": page_url,
                    "route": "",
                    "tag": "react_meta",
                    "kind": "react_devtools",
                    "meta": {
                        "hasReact": self._summary.has_react,
                        "rendererIds": self._summary.renderer_ids,
                        "timestamp": self._summary.timestamp,
                    },
                }
            )

        # 5) Optional aggregate summary hit
        if self.cfg.emit_summary_hit:
            summary_hit = self._build_summary_hit(page_url)
            if summary_hit is not None:
                hits.append(summary_hit)

        return hits

    def _build_summary_hit(self, page_url: str) -> Optional[Dict[str, Any]]:
        """
        Build a synthetic high-level summary hit aggregating counts and
        the most "interesting" routes.
        """
        if (
            not self._nav_events
            and not self._click_events
            and not self._summary
            and not self._router_routes
        ):
            return None

        # route frequency (from nav + router_routes)
        route_counts: Dict[str, int] = {}
        for nav in self._nav_events:
            if nav.pathname:
                route_counts[nav.pathname] = route_counts.get(nav.pathname, 0) + 1
        for r in self._router_routes:
            path = r.get("path") or ""
            if path:
                route_counts[path] = route_counts.get(path, 0) + 1

        top_routes = sorted(
            route_counts.items(),
            key=lambda kv: kv[1],
            reverse=True,
        )[:10]

        meta: Dict[str, Any] = {
            "nav_event_count": len(self._nav_events),
            "click_event_count": len(self._click_events),
            "router_route_count": len(self._router_routes),
            "unique_routes": len(self._routes_seen),
            "unique_urls": len(self._urls_seen),
            "top_routes": top_routes,
        }

        if self._summary is not None:
            meta.update(
                {
                    "hasReact": self._summary.has_react,
                    "rendererIds": self._summary.renderer_ids,
                    "react_devtools_timestamp": self._summary.timestamp,
                }
            )

        return {
            "page": page_url,
            "url": page_url,
            "route": "",
            "tag": "react_meta",
            "kind": "summary",
            "meta": meta,
        }


# ======================================================================
# DatabaseSniffer (Playwright-based DB / persistence sniffer)
# ======================================================================

class DatabaseSniffer:
    """
    Playwright-based sniffer for Data Persistence + Safe Link Extraction (ADVANCED / HARDENED).

    SAFE GUARANTEES:
      - Does NOT extract IndexedDB records (metadata only).
      - Does NOT return full backend configs; only shallow fingerprints + URL strings.
      - Does NOT store arbitrary HTML; only returns html snapshot + hits (URLs + metadata).

    Improvements:
      - High-ROI URL harvesting:
          * attribute whitelist beyond href/src (srcset, poster, data-src, data-href, etc.)
          * <source>/<track> scanning
          * CSS url(...) extraction from <style> + style=""
          * meta (og:video, twitter:player, etc.) URL capture
          * JSON-LD (application/ld+json) URL extraction with caps + seen-set
          * JS string-literal URL extraction from inline scripts with byte caps + yielding
      - Hardened against hangs:
          * circular protection and caps for JSON traversal
          * incremental harvesting (no giant concatenated buffers)
          * yields to event loop during heavy parse
    """

    # --- basic URL patterns (link-only) ---
    _ABS_URL_RE = re.compile(r"\b(?:https?|wss?)://[^\s\"'<>]+", re.IGNORECASE)
    _SCHEMELESS_RE = re.compile(r"(?<!:)\b//[^\s\"'<>]+", re.IGNORECASE)  # //cdn.example.com/x

    # CSS url(...) – handles url(x) url('x') url("x")
    _CSS_URL_RE = re.compile(r"url\(\s*(?:['\"])?([^'\"\)\s]+)(?:['\"])?\s*\)", re.IGNORECASE)

    # JS string literal URL-ish extraction (kept conservative)
    # - catches "https://..." 'wss://...' "//cdn..." "/api/v1" "./x" "../x"
    _JS_LIT_RE = re.compile(
        r"""(?:
            (?P<abs>(?:https?|wss?)://[^"'\\\s<>{}\[\]]+)
          | (?P<schemeless>//[^"'\\\s<>{}\[\]]+)
          | (?P<rel>
                (?:/|\./|\.\./)[^"'\\\s<>{}\[\]]+
            )
        )""",
        re.IGNORECASE | re.VERBOSE,
    )

    _ALLOWED_SCHEMES = {"http", "https", "ws", "wss"}

    # Attribute/value grabbing (we still parse with Playwright DOM, but keep regex fallback)
    _ATTR_PAIR_RE = re.compile(r"""([a-zA-Z0-9_\-:]+)\s*=\s*["']([^"']+)["']""")

    # ------------------------------------------------------------------ #
    # Config
    # ------------------------------------------------------------------ #
    @dataclass
    class Config:
        timeout: float = 10.0

        # --- Backwards compatible toggles (your pipeline expects these) ---
        enable_html_link_scan: bool = True              # legacy name
        enable_backend_link_scan: bool = True           # legacy name
        enable_network_capture: bool = True             # legacy name
        enable_backend_fingerprint: bool = True         # legacy name
        enable_indexeddb_dump: bool = True              # legacy name

        # --- New harvesting toggles (fine-grained) ---
        enable_dom_attribute_scan: bool = True
        enable_dom_style_scan: bool = True
        enable_dom_meta_scan: bool = True
        enable_jsonld_scan: bool = True
        enable_inline_script_string_scan: bool = True

        # --- IndexedDB metadata only ---
        max_idb_databases: int = 5
        max_idb_stores: int = 5

        # --- Backend fingerprint ---
        known_globals: Set[str] = field(default_factory=lambda: {
            "firebase", "_firebaseApp", "Supabase", "supabaseClient",
            "__FIREBASE_DEFAULTS__", "mongo", "Realm", "couchdb",
        })

        # --- Network capture caps (URL-only) ---
        max_network_urls: int = 400

        # --- Classification / filtering ---
        classify_links: bool = True
        allow_classes: Set[str] = field(default_factory=set)  # if non-empty, filter emitted links by class

        # --- Backend global scan caps (avoid expensive traversals) ---
        backend_scan_max_urls: int = 200
        backend_scan_max_keys_per_obj: int = 50
        backend_scan_max_array_items: int = 50
        backend_scan_depth: int = 2

        # --- DOM harvesting caps (avoid giant pages) ---
        max_dom_nodes: int = 4000
        max_attr_pairs: int = 12000

        # Only scan these attributes (high ROI)
        attr_whitelist: Set[str] = field(default_factory=lambda: {
            "href", "src", "srcset", "poster",
            "data-src", "data-href", "data-url", "data-srcset",
            "content", "value",  # meta/content + some forms
        })

        # --- CSS scanning caps ---
        max_style_tag_bytes: int = 400_000     # across all <style> tags
        max_inline_style_bytes: int = 200_000  # across all style="" attrs

        # --- JSON-LD caps ---
        max_jsonld_blocks: int = 30
        max_jsonld_bytes_per_block: int = 200_000
        json_scan_max_urls: int = 300
        json_scan_max_depth: int = 6
        json_scan_max_keys_per_obj: int = 100
        json_scan_max_array_items: int = 200

        # --- Inline script literal URL scan caps ---
        max_inline_script_blocks: int = 40
        max_inline_script_bytes_per_block: int = 200_000
        js_literal_max_urls: int = 400

        # --- Yielding / responsiveness ---
        yield_every_n_urls: int = 200

        @classmethod
        def from_kwargs(cls, **kwargs) -> "DatabaseSniffer.Config":
            """
            Backward/forward-compatible constructor:
            - ignores unknown keys instead of crashing your pipeline
            """
            allowed = {f.name for f in fields(cls)}
            filtered = {k: v for k, v in kwargs.items() if k in allowed}
            return cls(**filtered)

    # ------------------------------------------------------------------ #
    # Lifecycle
    # ------------------------------------------------------------------ #
    def __init__(self, config: Optional["DatabaseSniffer.Config"] = None, logger=None):
        self.cfg = config or self.Config()
        self.logger = logger or DEBUG_LOGGER
        self._log("DatabaseSniffer Initialized (hardened advanced link-only mode)", None)

    # ------------------------------------------------------------------ #
    # Logging helper
    # ------------------------------------------------------------------ #
    def _log(self, msg: str, log_list: Optional[List[str]]) -> None:
        full = f"[DatabaseSniffer] {msg}"
        try:
            if log_list is not None:
                log_list.append(full)
            if self.logger is not None:
                self.logger.log_message(full)
        except Exception:
            pass

    # ------------------------------------------------------------------ #
    # URL utilities
    # ------------------------------------------------------------------ #
    def _is_allowed_scheme(self, u: str) -> bool:
        try:
            return urlparse(u).scheme.lower() in self._ALLOWED_SCHEMES
        except Exception:
            return False

    def _normalize_candidate(self, base_url: str, raw: str) -> str:
        raw = (raw or "").strip()
        if not raw:
            return ""

        low = raw.lower()
        if low.startswith(("blob:", "data:", "javascript:", "mailto:", "tel:")):
            return ""

        # schemeless -> https
        if raw.startswith("//"):
            raw = "https:" + raw

        # relative -> absolute
        if raw.startswith("/") or raw.startswith("./") or raw.startswith("../"):
            raw = urljoin(base_url, raw)

        # canonicalize (your global helper)
        try:
            return _canonicalize_url(raw)  # noqa: F821
        except Exception:
            return raw

    def _classify_url(self, u: str) -> str:
        try:
            p = urlparse(u)
            path = (p.path or "").lower()
        except Exception:
            return "page"

        if any(path.endswith(ext) for ext in (".m3u8", ".mpd", ".ts", ".m4s", ".mp4", ".webm", ".mp3", ".aac", ".wav")):
            return "media"
        if any(path.endswith(ext) for ext in (".js", ".css", ".map")):
            return "asset"
        if any(seg in path for seg in ("/api/", "/graphql", "/v1/", "/v2/", "/rpc", "/rest")):
            return "api"
        if any(path.endswith(ext) for ext in (".json", ".xml")):
            return "data"
        return "page"

    # ------------------------------------------------------------------ #
    # Core add-hit helper
    # ------------------------------------------------------------------ #
    async def _add_link_hits_async(
        self,
        page_url: str,
        urls: List[str],
        hits: List[Dict[str, Any]],
        source: str,
        log: Optional[List[str]],
    ) -> None:
        if not urls:
            return

        # Optional filtering by class
        if self.cfg.classify_links and self.cfg.allow_classes:
            urls = [u for u in urls if self._classify_url(u) in self.cfg.allow_classes]
            if not urls:
                return

        self._log(f"Link scan ({source}) found {len(urls)} URLs", log)

        n = 0
        for u in urls:
            meta: Dict[str, Any] = {"url": u, "source": source}
            if self.cfg.classify_links:
                meta["class"] = self._classify_url(u)

            hits.append({
                "page": page_url,
                "url": u,
                "tag": "db_sniff",
                "kind": "content_link",
                "meta": meta,
            })

            n += 1
            if self.cfg.yield_every_n_urls and (n % self.cfg.yield_every_n_urls == 0):
                await asyncio.sleep(0)

    # ------------------------------------------------------------------ #
    # Text extraction primitives (safe)
    # ------------------------------------------------------------------ #
    def _extract_urls_from_text(self, base_url: str, text: str) -> List[str]:
        if not text:
            return []
        cands: List[str] = []
        cands += self._ABS_URL_RE.findall(text)
        cands += self._SCHEMELESS_RE.findall(text)

        seen: Set[str] = set()
        out: List[str] = []
        for raw in cands:
            u = self._normalize_candidate(base_url, raw)
            if not u:
                continue
            if not self._is_allowed_scheme(u):
                continue
            if u not in seen:
                seen.add(u)
                out.append(u)
        return out

    def _extract_css_urls(self, base_url: str, css_text: str) -> List[str]:
        if not css_text:
            return []
        out: List[str] = []
        seen: Set[str] = set()
        for raw in self._CSS_URL_RE.findall(css_text):
            u = self._normalize_candidate(base_url, raw)
            if not u or not self._is_allowed_scheme(u):
                continue
            if u not in seen:
                seen.add(u)
                out.append(u)
        return out

    def _extract_srcset_urls(self, base_url: str, srcset: str) -> List[str]:
        """
        srcset format: "url1 1x, url2 2x" or "url 480w, url 800w"
        We'll split commas, take first token in each chunk.
        """
        if not srcset:
            return []
        out: List[str] = []
        seen: Set[str] = set()
        for part in srcset.split(","):
            token = (part or "").strip().split()
            if not token:
                continue
            raw = token[0].strip()
            u = self._normalize_candidate(base_url, raw)
            if not u or not self._is_allowed_scheme(u):
                continue
            if u not in seen:
                seen.add(u)
                out.append(u)
        return out

    def _extract_js_string_literals(self, base_url: str, script_text: str, *, max_urls: int) -> List[str]:
        """
        Conservative scanning of inline JS for URL-ish string literals and relative endpoints.
        Uses caps to prevent runaway.
        """
        if not script_text:
            return []
        seen: Set[str] = set()
        out: List[str] = []
        for m in self._JS_LIT_RE.finditer(script_text):
            raw = m.group(0)
            u = self._normalize_candidate(base_url, raw)
            if not u or not self._is_allowed_scheme(u):
                continue
            if u in seen:
                continue
            seen.add(u)
            out.append(u)
            if len(out) >= max_urls:
                break
        return out

    def _extract_urls_from_json_value(
        self,
        base_url: str,
        val: Any,
        *,
        seen_ids: Set[int],
        out: List[str],
        max_urls: int,
        max_depth: int,
        max_keys: int,
        max_arr: int,
        depth: int = 0,
    ) -> None:
        """
        JSON traversal hardened:
          - seen_ids prevents circular loops
          - depth/keys/array caps
          - extracts URL strings only (absolute/ws/schemeless/relative)
        """
        if len(out) >= max_urls:
            return
        if depth > max_depth:
            return
        if val is None:
            return

        # Circular protection for containers
        if isinstance(val, (dict, list)):
            vid = id(val)
            if vid in seen_ids:
                return
            seen_ids.add(vid)

        if isinstance(val, str):
            # Pull any URLs inside the string
            for u in self._extract_urls_from_text(base_url, val):
                if len(out) >= max_urls:
                    break
                if u not in out:
                    out.append(u)

            # Also consider relative endpoints embedded as plain strings
            # (e.g., "/api/v1/foo")
            if len(out) < max_urls and val.startswith(("/", "./", "../")):
                u = self._normalize_candidate(base_url, val)
                if u and self._is_allowed_scheme(u) and u not in out:
                    out.append(u)
            return

        if isinstance(val, list):
            for item in val[:max_arr]:
                self._extract_urls_from_json_value(
                    base_url, item,
                    seen_ids=seen_ids, out=out,
                    max_urls=max_urls, max_depth=max_depth,
                    max_keys=max_keys, max_arr=max_arr,
                    depth=depth + 1,
                )
                if len(out) >= max_urls:
                    return
            return

        if isinstance(val, dict):
            # scan keys + values
            for k in list(val.keys())[:max_keys]:
                if len(out) >= max_urls:
                    return
                try:
                    self._extract_urls_from_json_value(
                        base_url, val.get(k),
                        seen_ids=seen_ids, out=out,
                        max_urls=max_urls, max_depth=max_depth,
                        max_keys=max_keys, max_arr=max_arr,
                        depth=depth + 1,
                    )
                except Exception:
                    continue

    def _extract_urls_from_json_text(self, base_url: str, json_text: str) -> List[str]:
        if not json_text:
            return []
        json_text = json_text.strip()
        if not json_text:
            return []

        try:
            data = json.loads(json_text)
        except Exception:
            # Sometimes JSON-LD has multiple objects without array; try a lightweight salvage:
            # If it fails, just do string URL extraction.
            return self._extract_urls_from_text(base_url, json_text)

        out: List[str] = []
        self._extract_urls_from_json_value(
            base_url,
            data,
            seen_ids=set(),
            out=out,
            max_urls=int(self.cfg.json_scan_max_urls),
            max_depth=int(self.cfg.json_scan_max_depth),
            max_keys=int(self.cfg.json_scan_max_keys_per_obj),
            max_arr=int(self.cfg.json_scan_max_array_items),
        )
        return out

    # ------------------------------------------------------------------ #
    # Network capture (URLs only)
    # ------------------------------------------------------------------ #
    def _add_url_to_bucket(self, bucket: Set[str], base_url: str, raw: str) -> None:
        u = self._normalize_candidate(base_url, raw)
        if u and self._is_allowed_scheme(u):
            bucket.add(u)

    async def _attach_network_collectors(self, page, page_url: str, net_urls: Set[str], log):
        def on_request(req):
            try:
                self._add_url_to_bucket(net_urls, page_url, req.url)
            except Exception:
                pass

        def on_response(resp):
            try:
                self._add_url_to_bucket(net_urls, page_url, resp.url)
                hdrs = getattr(resp, "headers", None) or {}
                for k in ("location", "link"):
                    v = hdrs.get(k)
                    if v:
                        for u in self._extract_urls_from_text(page_url, v):
                            net_urls.add(u)
            except Exception:
                pass

        page.on("request", on_request)
        page.on("response", on_response)

    # ------------------------------------------------------------------ #
    # DOM harvesting (advanced high ROI)
    # ------------------------------------------------------------------ #
    async def _dom_harvest_urls(self, page, page_url: str, log: Optional[List[str]]) -> Dict[str, List[str]]:
        """
        Uses Playwright page.evaluate to harvest:
          - whitelisted attribute values (href/src/srcset/poster/data-src/etc.)
          - inline style text (style="")
          - <style> tag contents
          - meta content for OG/twitter/etc.
          - JSON-LD blocks
          - inline script blocks (string literal extraction)
        Returns dict of buckets.
        """
        buckets: Dict[str, List[str]] = {
            "dom_attrs": [],
            "dom_srcset": [],
            "dom_css": [],
            "dom_meta": [],
            "jsonld": [],
            "inline_js": [],
        }

        # Pull DOM info in one go to reduce round-trips
        # Caps are applied inside JS to avoid huge payloads.
        js = r"""
        (cfg) => {
          const out = {
            attrs: [],
            srcsets: [],
            inlineStyles: [],
            styleTags: [],
            metaContents: [],
            jsonldBlocks: [],
            inlineScripts: [],
          };

          const MAX_NODES = cfg.maxNodes || 4000;
          const MAX_ATTRS = cfg.maxAttrs || 12000;
          const attrWhite = new Set(cfg.attrWhitelist || []);
          const maxStyleTagBytes = cfg.maxStyleTagBytes || 400000;
          const maxInlineStyleBytes = cfg.maxInlineStyleBytes || 200000;
          const maxJsonLdBlocks = cfg.maxJsonLdBlocks || 30;
          const maxJsonLdBytes = cfg.maxJsonLdBytes || 200000;
          const maxInlineScripts = cfg.maxInlineScripts || 40;
          const maxInlineScriptBytes = cfg.maxInlineScriptBytes || 200000;

          // --- element attribute scan ---
          let scannedNodes = 0;
          let scannedAttrs = 0;

          const els = Array.from(document.querySelectorAll('*'));
          for (const el of els) {
            scannedNodes++;
            if (scannedNodes > MAX_NODES) break;

            // srcset special
            const ss = el.getAttribute && el.getAttribute('srcset');
            if (ss) out.srcsets.push(ss);

            // inline style
            const st = el.getAttribute && el.getAttribute('style');
            if (st && out.inlineStyles.join('').length < maxInlineStyleBytes) out.inlineStyles.push(st);

            if (!el.attributes) continue;
            for (let i = 0; i < el.attributes.length; i++) {
              scannedAttrs++;
              if (scannedAttrs > MAX_ATTRS) break;
              const a = el.attributes[i];
              const name = (a.name || '').toLowerCase();
              if (!attrWhite.has(name)) continue;
              const v = a.value;
              if (typeof v === 'string' && v) out.attrs.push([name, v]);
            }
            if (scannedAttrs > MAX_ATTRS) break;
          }

          // --- style tags ---
          if (cfg.enableStyleTags) {
            const styles = Array.from(document.querySelectorAll('style'));
            let bytes = 0;
            for (const s of styles) {
              const t = s.textContent || '';
              if (!t) continue;
              const take = t.slice(0, Math.max(0, maxStyleTagBytes - bytes));
              if (!take) break;
              out.styleTags.push(take);
              bytes += take.length;
              if (bytes >= maxStyleTagBytes) break;
            }
          }

          // --- meta tags: OG/twitter/etc. use content attr ---
          if (cfg.enableMeta) {
            const metas = Array.from(document.querySelectorAll('meta'));
            for (const m of metas) {
              const prop = (m.getAttribute('property') || m.getAttribute('name') || '').toLowerCase();
              const content = m.getAttribute('content') || '';
              if (!content) continue;
              // keep high ROI meta names/properties
              if (
                prop.startsWith('og:') ||
                prop.startsWith('twitter:') ||
                prop.includes('video') ||
                prop.includes('player') ||
                prop.includes('stream') ||
                prop.includes('image')
              ) {
                out.metaContents.push(content);
              }
            }
          }

          // --- JSON-LD blocks ---
          if (cfg.enableJsonLd) {
            const scripts = Array.from(document.querySelectorAll('script[type="application/ld+json"]'));
            let n = 0;
            for (const sc of scripts) {
              if (n >= maxJsonLdBlocks) break;
              const t = (sc.textContent || '').trim();
              if (!t) continue;
              out.jsonldBlocks.push(t.slice(0, maxJsonLdBytes));
              n++;
            }
          }

          // --- inline scripts (string literals scan is done in python, but we pull text here) ---
          if (cfg.enableInlineScripts) {
            const scripts = Array.from(document.querySelectorAll('script:not([src])'));
            let n = 0;
            for (const sc of scripts) {
              if (n >= maxInlineScripts) break;
              const t = (sc.textContent || '');
              if (!t) continue;
              out.inlineScripts.push(t.slice(0, maxInlineScriptBytes));
              n++;
            }
          }

          return out;
        }
        """

        cfg = {
            "maxNodes": int(self.cfg.max_dom_nodes),
            "maxAttrs": int(self.cfg.max_attr_pairs),
            "attrWhitelist": sorted([a.lower() for a in (self.cfg.attr_whitelist or set())]),
            "enableStyleTags": bool(self.cfg.enable_dom_style_scan),
            "enableMeta": bool(self.cfg.enable_dom_meta_scan),
            "enableJsonLd": bool(self.cfg.enable_jsonld_scan),
            "enableInlineScripts": bool(self.cfg.enable_inline_script_string_scan),
            "maxStyleTagBytes": int(self.cfg.max_style_tag_bytes),
            "maxInlineStyleBytes": int(self.cfg.max_inline_style_bytes),
            "maxJsonLdBlocks": int(self.cfg.max_jsonld_blocks),
            "maxJsonLdBytes": int(self.cfg.max_jsonld_bytes_per_block),
            "maxInlineScripts": int(self.cfg.max_inline_script_blocks),
            "maxInlineScriptBytes": int(self.cfg.max_inline_script_bytes_per_block),
        }

        payload = None
        try:
            payload = await page.evaluate(js, cfg)
        except Exception as e:
            self._log(f"DOM harvest evaluate failed: {e}", log)
            return buckets

        # --- Attributes
        if self.cfg.enable_dom_attribute_scan and payload:
            attrs = payload.get("attrs") or []
            collected: List[str] = []
            collected_srcset: List[str] = []

            for name, val in attrs:
                nlow = (name or "").lower()
                if not isinstance(val, str) or not val.strip():
                    continue

                if nlow == "srcset":
                    collected_srcset.extend(self._extract_srcset_urls(page_url, val))
                else:
                    collected.extend(self._extract_urls_from_text(page_url, val))
                    # also allow relative endpoints in these attrs
                    if val.startswith(("/", "./", "../")):
                        u = self._normalize_candidate(page_url, val)
                        if u and self._is_allowed_scheme(u):
                            collected.append(u)

            # Handle also explicit srcset list harvested separately
            for ss in (payload.get("srcsets") or []):
                if isinstance(ss, str):
                    collected_srcset.extend(self._extract_srcset_urls(page_url, ss))

            buckets["dom_attrs"] = list(dict.fromkeys(collected))
            buckets["dom_srcset"] = list(dict.fromkeys(collected_srcset))

        # --- Inline styles + <style> tags
        if self.cfg.enable_dom_style_scan and payload:
            css_urls: List[str] = []
            for st in (payload.get("inlineStyles") or []):
                if isinstance(st, str):
                    css_urls.extend(self._extract_css_urls(page_url, st))
            for sty in (payload.get("styleTags") or []):
                if isinstance(sty, str):
                    css_urls.extend(self._extract_css_urls(page_url, sty))
            buckets["dom_css"] = list(dict.fromkeys(css_urls))

        # --- Meta tags
        if self.cfg.enable_dom_meta_scan and payload:
            meta_urls: List[str] = []
            for c in (payload.get("metaContents") or []):
                if isinstance(c, str):
                    meta_urls.extend(self._extract_urls_from_text(page_url, c))
                    if c.startswith(("/", "./", "../")):
                        u = self._normalize_candidate(page_url, c)
                        if u and self._is_allowed_scheme(u):
                            meta_urls.append(u)
            buckets["dom_meta"] = list(dict.fromkeys(meta_urls))

        # --- JSON-LD
        if self.cfg.enable_jsonld_scan and payload:
            jl_urls: List[str] = []
            for block in (payload.get("jsonldBlocks") or []):
                if isinstance(block, str) and block:
                    jl_urls.extend(self._extract_urls_from_json_text(page_url, block))
                    if len(jl_urls) >= int(self.cfg.json_scan_max_urls):
                        break
            buckets["jsonld"] = list(dict.fromkeys(jl_urls))[: int(self.cfg.json_scan_max_urls)]

        # --- Inline scripts string literal scan (incremental + yield)
        if self.cfg.enable_inline_script_string_scan and payload:
            js_urls: List[str] = []
            for block in (payload.get("inlineScripts") or []):
                if not isinstance(block, str) or not block:
                    continue
                js_urls.extend(self._extract_js_string_literals(page_url, block, max_urls=int(self.cfg.js_literal_max_urls)))
                if len(js_urls) >= int(self.cfg.js_literal_max_urls):
                    break
                # yield occasionally so Playwright can progress
                if len(js_urls) and (len(js_urls) % int(self.cfg.yield_every_n_urls or 200) == 0):
                    await asyncio.sleep(0)
            buckets["inline_js"] = list(dict.fromkeys(js_urls))[: int(self.cfg.js_literal_max_urls)]

        return buckets

    # ------------------------------------------------------------------ #
    # Public API (matches other sniffers)
    # ------------------------------------------------------------------ #
    async def sniff(
        self,
        context,              # Playwright BrowserContext
        page_url: str,
        timeout: float,
        log: List[str],
        extensions=None,      # signature compatibility; unused
    ) -> Tuple[str, List[Dict[str, Any]]]:
        if not context:
            self._log("No BrowserContext supplied; skipping.", log)
            return "", []

        tmo = float(timeout or self.cfg.timeout)
        hits: List[Dict[str, Any]] = []
        html: str = ""
        page = None

        self._log(f"Start DB sniff: {page_url}", log)

        # capture network URLs across the whole load
        net_urls: Set[str] = set()

        try:
            page = await context.new_page()

            if self.cfg.enable_network_capture:
                await self._attach_network_collectors(page, page_url, net_urls, log)

            # Navigate
            await page.goto(page_url, wait_until="domcontentloaded", timeout=int(tmo * 1000))
            await page.wait_for_timeout(800)

            # --- Backend fingerprint (window globals) ---
            backend_urls: List[str] = []
            if self.cfg.enable_backend_fingerprint:
                try:
                    fingerprints = await page.evaluate(
                        """
                        (globals) => {
                            const found = [];
                            try {
                                globals.forEach(g => {
                                    let val;
                                    try { val = window[g]; } catch (e) { val = undefined; }
                                    if (val !== undefined && val !== null) {
                                        const type = typeof val;
                                        let keys = [];
                                        if (type === 'object') {
                                            try { keys = Object.keys(val).slice(0, 5); } catch (e) {}
                                        }
                                        found.push({ name: g, type, keys });
                                    }
                                });
                            } catch (e) {}
                            return found;
                        }
                        """,
                        list(self.cfg.known_globals),
                    )
                    for fp in fingerprints or []:
                        if isinstance(fp, dict):
                            hits.append({
                                "page": page_url,
                                "url": page_url,
                                "tag": "db_sniff",
                                "kind": "db_config_detected",
                                "meta": fp,
                            })
                except Exception as e:
                    self._log(f"Backend fingerprint error on {page_url}: {e}", log)

                # --- Backend link-only scan with caps ---
                if self.cfg.enable_backend_link_scan:
                    try:
                        backend_urls = await page.evaluate(
                            """
                            (args) => {
                              const globals = args.globals || [];
                              const MAX_URLS = args.maxUrls || 200;
                              const MAX_KEYS = args.maxKeys || 50;
                              const MAX_ARR = args.maxArr || 50;
                              const MAX_DEPTH = args.maxDepth || 2;

                              const urls = [];
                              const seen = new Set();

                              const isUrl = (s) => typeof s === 'string' && /^(https?:\\/\\/|wss?:\\/\\/)/i.test(s);

                              const addUrl = (u) => {
                                if (!u || seen.has(u)) return;
                                if (isUrl(u)) { seen.add(u); urls.push(u); }
                              };

                              const scanValue = (v, depth) => {
                                if (urls.length >= MAX_URLS) return;
                                if (depth <= 0 || v == null) return;

                                if (typeof v === 'string') { addUrl(v); return; }

                                if (Array.isArray(v)) {
                                  for (const item of v.slice(0, MAX_ARR)) {
                                    scanValue(item, depth - 1);
                                    if (urls.length >= MAX_URLS) return;
                                  }
                                  return;
                                }

                                if (typeof v === 'object') {
                                  let keys = [];
                                  try { keys = Object.keys(v).slice(0, MAX_KEYS); } catch (e) { return; }
                                  for (const k of keys) {
                                    try { scanValue(v[k], depth - 1); } catch (e) {}
                                    if (urls.length >= MAX_URLS) return;
                                  }
                                }
                              };

                              for (const g of globals) {
                                let val;
                                try { val = window[g]; } catch (e) { continue; }
                                scanValue(val, MAX_DEPTH);
                                if (urls.length >= MAX_URLS) break;
                              }

                              return urls;
                            }
                            """,
                            {
                                "globals": list(self.cfg.known_globals),
                                "maxUrls": int(self.cfg.backend_scan_max_urls),
                                "maxKeys": int(self.cfg.backend_scan_max_keys_per_obj),
                                "maxArr": int(self.cfg.backend_scan_max_array_items),
                                "maxDepth": int(self.cfg.backend_scan_depth),
                            },
                        )
                        if not isinstance(backend_urls, list):
                            backend_urls = []
                    except Exception as e:
                        self._log(f"Backend link scan error on {page_url}: {e}", log)

            # Canonicalize backend urls (link-only)
            if backend_urls:
                out = []
                for u in backend_urls:
                    if isinstance(u, str):
                        uu = self._normalize_candidate(page_url, u)
                        if uu and self._is_allowed_scheme(uu):
                            out.append(uu)
                backend_urls = out

            # --- IndexedDB metadata (NO RECORD CONTENTS) ---
            if self.cfg.enable_indexeddb_dump:
                try:
                    idb_data = await self._dump_indexeddb(page, log)
                    for db in idb_data:
                        hits.append({
                            "page": page_url,
                            "url": page_url,
                            "tag": "db_sniff",
                            "kind": "indexeddb_dump",
                            "meta": db,
                        })
                except Exception as e:
                    self._log(f"IndexedDB dump error on {page_url}: {e}", log)

            # --- HTML snapshot ---
            try:
                html = await page.content()
            except Exception as e:
                self._log(f"Error getting HTML for {page_url}: {e}", log)

            # --- Advanced DOM harvesting (HIGH ROI) ---
            dom_buckets = {}
            if self.cfg.enable_html_link_scan:
                dom_buckets = await self._dom_harvest_urls(page, page_url, log)

            # --- Emit hits ---
            # 1) legacy “html scan” fallback: still worth keeping
            if self.cfg.enable_html_link_scan and html:
                html_links = self._extract_urls_from_text(page_url, html)
                await self._add_link_hits_async(page_url, html_links, hits, source="html_regex", log=log)

            # 2) advanced DOM buckets (attributes/srcset/css/meta/jsonld/inline_js)
            for k, urls in (dom_buckets or {}).items():
                if urls:
                    await self._add_link_hits_async(page_url, urls, hits, source=k, log=log)

            # 3) backend globals
            if backend_urls:
                await self._add_link_hits_async(page_url, backend_urls, hits, source="backend_globals", log=log)

            # 4) network URLs flush
            if self.cfg.enable_network_capture and net_urls:
                urls = list(net_urls)[: int(self.cfg.max_network_urls)]
                await self._add_link_hits_async(page_url, urls, hits, source="network", log=log)

        except Exception as e:
            self._log(f"Fatal error during DB sniff on {page_url}: {e}", log)
        finally:
            if page is not None:
                try:
                    await page.close()
                except Exception as e:
                    self._log(f"Error closing page for {page_url}: {e}", log)

        self._log(f"Finished DB sniff for {page_url}: hits={len(hits)}", log)
        return html or "", hits

    # ------------------------------------------------------------------ #
    # IndexedDB dumper (metadata-only; runs inside Playwright page)
    # ------------------------------------------------------------------ #
    async def _dump_indexeddb(self, page, log: Optional[List[str]]) -> List[Dict[str, Any]]:
        self._log("Attempting IndexedDB metadata dump (no records)...", log)

        script = """
        async (config) => {
            const { maxDbs, maxStores } = config;

            if (!window.indexedDB) {
                return [{ error: "IndexedDB not available in this context" }];
            }

            if (!window.indexedDB.databases) {
                return [{ error: "IndexedDB Enumeration API not supported in this browser context" }];
            }

            try {
                const dbs = await window.indexedDB.databases();
                const results = [];

                const targetDbs = dbs.slice(0, maxDbs);

                for (const dbInfo of targetDbs) {
                    if (!dbInfo || !dbInfo.name) continue;

                    const dbData = {
                        name: dbInfo.name,
                        version: dbInfo.version,
                        stores: []
                    };

                    const db = await new Promise((resolve) => {
                        try {
                            const req = window.indexedDB.open(dbInfo.name, dbInfo.version);
                            req.onsuccess = () => resolve(req.result);
                            req.onerror = () => resolve(null);
                            req.onblocked = () => resolve(null);
                        } catch (e) {
                            resolve(null);
                        }
                    });

                    if (!db) {
                        dbData.error = "Could not open DB (blocked or error)";
                        results.push(dbData);
                        continue;
                    }

                    const storeNames = Array.from(db.objectStoreNames || []).slice(0, maxStores);

                    if (storeNames.length > 0) {
                        try {
                            const tx = db.transaction(storeNames, 'readonly');

                            for (const storeName of storeNames) {
                                let approxCount = null;
                                try {
                                    const store = tx.objectStore(storeName);
                                    approxCount = await new Promise((resolve) => {
                                        try {
                                            const req = store.count();
                                            req.onsuccess = () => resolve(req.result ?? null);
                                            req.onerror = () => resolve(null);
                                        } catch (e) {
                                            resolve(null);
                                        }
                                    });
                                } catch (e) {
                                    // keep null
                                }

                                dbData.stores.push({
                                    name: storeName,
                                    approx_count: approxCount,
                                });
                            }
                        } catch (e) {
                            dbData.error = "Transaction failed: " + (e && e.message ? e.message : String(e || ""));
                        }
                    }

                    try { db.close(); } catch (_) {}
                    results.push(dbData);
                }

                return results;
            } catch (e) {
                return [{ error: "Global metadata dump error: " + (e && e.message ? e.message : String(e || "")) }];
            }
        }
        """

        try:
            args = {"maxDbs": int(self.cfg.max_idb_databases), "maxStores": int(self.cfg.max_idb_stores)}
            result = await page.evaluate(script, args)
            if not isinstance(result, list):
                result = []
            self._log(f"IndexedDB metadata dump complete. Found {len(result)} database entries.", log)
            return result
        except Exception as e:
            self._log(f"IndexedDB metadata script failed: {e}", log)
            return []

# ======================================================================
# InteractionSniffer (CDP-based Event & Overlay Analysis)
# ======================================================================

class InteractionSniffer:
    """
    Playwright + CDP sniffer for "Invisible" interactivity & UI barriers.

    Matches your other sniffers' contract:

        html, hits = await sniff(
            context,
            page_url,
            timeout,
            log,
            extensions=None,
        )

    hits schema (consistent with your suite):

        {
            "page": <page_url>,
            "url": <page_url or derived>,
            "tag": "interaction",
            "kind": "event_listener" | "overlay_detected" | "form_definition" | "summary",
            "meta": {...}
        }

    Key difference:
      • CDP can ask Chromium which DOM nodes have event listeners attached in memory,
        even if the HTML has no onclick=... and no href.

    Notes:
      • CDP requires Chromium. On Firefox/WebKit/Camoufox, we skip CDP gracefully.
      • Overlay + Form extraction are JS-based and work everywhere.
    """

    # ------------------------------------------------------------------ #
    # Config
    # ------------------------------------------------------------------ #
    @dataclass
    class Config:
        # generic controls
        timeout: float = 8.0
        max_hits: int = 250

        # small settle time after DOMContentLoaded
        wait_after_load_ms: int = 1000

        # ---------------- CDP: Event Listener Extraction ----------------
        enable_cdp_listeners: bool = True

        # only keep these listener types to reduce noise
        listener_types: Set[str] = field(default_factory=lambda: {
            "click", "mousedown", "mouseup",
            "submit",
            "keydown", "keyup",
            "touchstart", "touchend",
            "pointerdown", "pointerup",
        })

        # how many "nodes with relevant listeners" to emit
        max_listener_hits: int = 120

        # how many candidate nodes to inspect via CDP (upper bound)
        # (CDP calls are expensive; keep this modest)
        max_candidate_nodes: int = 500

        # CSS selector for candidate nodes (broad but bounded by max_candidate_nodes)
        candidate_selector: str = (
            "button, a, input, select, textarea, summary, details, label, "
            "[role='button'], [role='link'], [tabindex], [contenteditable='true'], "
            "div, span, li, svg"
        )

        # include capturing / passive info if available
        include_listener_flags: bool = True

        # Try to pull a short DOM snippet to help identify the element (safe bounded)
        include_outer_html_snippet: bool = True
        outer_html_max_chars: int = 280

        # ---------------- Overlay / Modal Detection (JS) ----------------
        enable_overlay_detection: bool = True
        min_z_index: int = 900
        coverage_threshold_percent: float = 50.0
        max_overlay_hits: int = 50

        # ---------------- Form Extraction (JS) ----------------
        enable_form_extraction: bool = True
        max_form_hits: int = 80
        max_inputs_per_form: int = 80

        # redact values for sensitive-ish inputs
        redact_input_types: Set[str] = field(default_factory=lambda: {
            "password",
        })

        # additionally redact if field name looks token-ish
        redact_name_regex: str = r"(csrf|token|auth|bearer|secret|key|session|jwt)"

        # emit aggregate summary hit
        emit_summary_hit: bool = True

    # ------------------------------------------------------------------ #
    # Internal memory dataclasses
    # ------------------------------------------------------------------ #
    @dataclass
    class ListenerMem:
        node_id: int
        node_name: str
        types: List[str]
        attributes: Dict[str, str]
        flags: Dict[str, Any] = field(default_factory=dict)
        outer_html: Optional[str] = None

    @dataclass
    class OverlayMem:
        tag_name: str
        id: str
        class_name: str
        z_index: int
        coverage: str
        text_preview: str

    @dataclass
    class FormMem:
        action: str
        method: str
        id: str
        class_name: str
        input_count: int
        inputs: List[Dict[str, Any]]

    # ------------------------------------------------------------------ #
    # Lifecycle
    # ------------------------------------------------------------------ #
    def __init__(self, config: Optional["InteractionSniffer.Config"] = None, logger=None):
        self.cfg = config or self.Config()
        self.logger = logger or DEBUG_LOGGER
        self._reset_memory()
        self._log("InteractionSniffer Initialized", None)

    def _reset_memory(self) -> None:
        self._listeners: List[InteractionSniffer.ListenerMem] = []
        self._overlays: List[InteractionSniffer.OverlayMem] = []
        self._forms: List[InteractionSniffer.FormMem] = []
        self._seen_fingerprints: Set[Tuple[Any, ...]] = set()

    # ------------------------------------------------------------------ #
    # Logging helper
    # ------------------------------------------------------------------ #
    def _log(self, msg: str, log_list: Optional[List[str]]) -> None:
        full = f"[InteractionSniffer] {msg}"
        try:
            if log_list is not None:
                log_list.append(full)
            if self.logger is not None:
                self.logger.log_message(full)
        except Exception:
            pass

    # ------------------------------------------------------------------ #
    # Public API (matches other sniffers)
    # ------------------------------------------------------------------ #
    async def sniff(
        self,
        context,              # Playwright BrowserContext
        page_url: str,
        timeout: float,
        log: List[str],
        extensions=None,      # unused; kept for signature compatibility
    ) -> Tuple[str, List[Dict[str, Any]]]:
        """
        Main entrypoint.

        Returns:
            (html, hits)
        """
        from playwright.async_api import TimeoutError as PWTimeoutError

        self._reset_memory()

        if not context:
            self._log("No BrowserContext supplied; skipping.", log)
            return "", []

        tmo = float(timeout or self.cfg.timeout)
        html: str = ""
        hits: List[Dict[str, Any]] = []
        page = None

        self._log(f"Start interaction sniff: {page_url} timeout={tmo}s", log)

        try:
            page = await context.new_page()
            await page.goto(page_url, wait_until="domcontentloaded", timeout=int(tmo * 1000))
            await page.wait_for_timeout(int(self.cfg.wait_after_load_ms))

            # 1) JS-based: forms + overlays (works on all browsers)
            if self.cfg.enable_form_extraction:
                await self._collect_forms(page, page_url, log)

            if self.cfg.enable_overlay_detection:
                await self._collect_overlays(page, page_url, log)

            # 2) CDP-based: event listeners (Chromium only)
            if self.cfg.enable_cdp_listeners:
                await self._collect_cdp_listeners(context, page, page_url, log)

            # HTML snapshot
            try:
                html = await page.content()
            except Exception as e:
                self._log(f"Error getting HTML for {page_url}: {e}", log)
                html = ""

            # materialize final hits
            hits = self._materialize_hits(page_url)

        except PWTimeoutError:
            self._log(f"Timeout while loading {page_url}", log)
        except Exception as e:
            self._log(f"Fatal error on {page_url}: {e}", log)
        finally:
            if page is not None:
                try:
                    await page.close()
                except Exception as e:
                    self._log(f"Error closing page for {page_url}: {e}", log)

        # global cap
        if len(hits) > self.cfg.max_hits:
            hits = hits[: self.cfg.max_hits]

        self._log(f"Finished interaction sniff for {page_url}: hits={len(hits)}", log)
        return html or "", hits

    # ------------------------------------------------------------------ #
    # JS: Forms
    # ------------------------------------------------------------------ #
    def _should_redact_field(self, name: str, input_type: str) -> bool:
        try:
            t = (input_type or "").lower().strip()
            if t in self.cfg.redact_input_types:
                return True
            n = (name or "").lower()
            if n and re.search(self.cfg.redact_name_regex, n, re.IGNORECASE):
                return True
        except Exception:
            pass
        return False

    async def _collect_forms(self, page, page_url: str, log: Optional[List[str]]) -> None:
        """
        Extract form structures; redact sensitive values.
        """
        try:
            forms = await page.evaluate(
                """
                (cfg) => {
                    const maxForms = cfg.maxForms;
                    const maxInputs = cfg.maxInputs;

                    const out = [];
                    const forms = Array.from(document.querySelectorAll('form')).slice(0, maxForms);

                    for (const f of forms) {
                        const inputs = [];
                        const els = Array.from(f.querySelectorAll('input, textarea, select, button'))
                                         .slice(0, maxInputs);

                        for (const i of els) {
                            inputs.push({
                                name: i.name || i.id || "",
                                type: (i.type || i.tagName || "").toLowerCase(),
                                value: (typeof i.value === "string" ? i.value : ""),
                                required: !!i.required,
                                disabled: !!i.disabled,
                                autocomplete: (i.autocomplete || "")
                            });
                        }

                        out.push({
                            action: f.action || "",
                            method: (f.method || "get").toLowerCase(),
                            id: f.id || "",
                            className: f.className || "",
                            input_count: inputs.length,
                            inputs: inputs
                        });
                    }

                    return out;
                }
                """,
                {
                    "maxForms": int(self.cfg.max_form_hits),
                    "maxInputs": int(self.cfg.max_inputs_per_form),
                },
            )

            if not isinstance(forms, list):
                forms = []

            # redact values safely in Python side (more flexible)
            for f in forms[: self.cfg.max_form_hits]:
                if not isinstance(f, dict):
                    continue
                inputs = f.get("inputs") or []
                if not isinstance(inputs, list):
                    inputs = []

                redacted_inputs: List[Dict[str, Any]] = []
                for inp in inputs[: self.cfg.max_inputs_per_form]:
                    if not isinstance(inp, dict):
                        continue
                    name = str(inp.get("name") or "")
                    itype = str(inp.get("type") or "")
                    val = str(inp.get("value") or "")
                    if self._should_redact_field(name, itype):
                        val = "[REDACTED]"
                    else:
                        # keep bounded; we do not want massive values
                        if len(val) > 200:
                            val = val[:200] + "…"

                    redacted_inputs.append(
                        {
                            "name": name,
                            "type": itype,
                            "value": val,
                            "required": bool(inp.get("required", False)),
                            "disabled": bool(inp.get("disabled", False)),
                            "autocomplete": str(inp.get("autocomplete") or ""),
                        }
                    )

                self._forms.append(
                    InteractionSniffer.FormMem(
                        action=str(f.get("action") or ""),
                        method=str(f.get("method") or "get"),
                        id=str(f.get("id") or ""),
                        class_name=str(f.get("className") or ""),
                        input_count=int(f.get("input_count") or len(redacted_inputs)),
                        inputs=redacted_inputs,
                    )
                )

            if self._forms:
                self._log(f"Extracted {len(self._forms)} form definitions", log)

        except Exception as e:
            self._log(f"Form extraction error: {e}", log)

    # ------------------------------------------------------------------ #
    # JS: Overlays / Modals
    # ------------------------------------------------------------------ #
    async def _collect_overlays(self, page, page_url: str, log: Optional[List[str]]) -> None:
        """
        Detect high z-index, fixed/absolute elements covering big viewport area.
        """
        try:
            overlays = await page.evaluate(
                """
                (config) => {
                    const { minZ, minCoverage, maxHits } = config;
                    const results = [];

                    const all = document.querySelectorAll('div, section, aside, iframe, dialog, [role="dialog"]');

                    const vw = Math.max(document.documentElement.clientWidth || 0, window.innerWidth || 0);
                    const vh = Math.max(document.documentElement.clientHeight || 0, window.innerHeight || 0);
                    const viewportArea = Math.max(1, vw * vh);

                    for (const el of all) {
                        if (results.length >= maxHits) break;

                        const style = window.getComputedStyle(el);
                        const z = parseInt(style.zIndex, 10);
                        const pos = style.position;
                        const vis = style.visibility;
                        const disp = style.display;
                        const opac = parseFloat(style.opacity || "1");

                        if (Number.isNaN(z)) continue;

                        if (
                            z >= minZ &&
                            vis !== 'hidden' && disp !== 'none' && opac > 0 &&
                            (pos === 'fixed' || pos === 'absolute')
                        ) {
                            const rect = el.getBoundingClientRect();
                            const area = Math.max(0, rect.width) * Math.max(0, rect.height);
                            if (area <= 0) continue;

                            const coveragePct = (area / viewportArea) * 100;
                            if (coveragePct >= minCoverage) {
                                results.push({
                                    tagName: el.tagName.toLowerCase(),
                                    id: el.id || "",
                                    className: (typeof el.className === "string" ? el.className : ""),
                                    zIndex: z,
                                    coverage: coveragePct.toFixed(1) + '%',
                                    textPreview: (el.innerText || "").trim().slice(0, 80)
                                });
                            }
                        }
                    }

                    return results;
                }
                """,
                {
                    "minZ": int(self.cfg.min_z_index),
                    "minCoverage": float(self.cfg.coverage_threshold_percent),
                    "maxHits": int(self.cfg.max_overlay_hits),
                },
            )

            if not isinstance(overlays, list):
                overlays = []

            for ov in overlays[: self.cfg.max_overlay_hits]:
                if not isinstance(ov, dict):
                    continue
                self._overlays.append(
                    InteractionSniffer.OverlayMem(
                        tag_name=str(ov.get("tagName") or ""),
                        id=str(ov.get("id") or ""),
                        class_name=str(ov.get("className") or ""),
                        z_index=int(ov.get("zIndex") or 0),
                        coverage=str(ov.get("coverage") or ""),
                        text_preview=str(ov.get("textPreview") or ""),
                    )
                )

            if self._overlays:
                self._log(f"Overlay detection: {len(self._overlays)} hits", log)

        except Exception as e:
            self._log(f"Overlay detection error: {e}", log)

    # ------------------------------------------------------------------ #
    # CDP: Event listeners (Chromium only)
    # ------------------------------------------------------------------ #
    async def _collect_cdp_listeners(self, context, page, page_url: str, log: Optional[List[str]]) -> None:
        """
        Use CDP DOMDebugger.getEventListeners to find nodes with in-memory listeners.

        Important:
          • Works only on Chromium.
          • We query candidates with a broad selector, then filter by actual listeners.
        """
        # Best-effort detection of browser type
        browser_name = "unknown"
        try:
            if getattr(context, "browser", None) and context.browser:
                browser_name = context.browser.browser_type.name
        except Exception:
            browser_name = "unknown"

        if browser_name != "chromium":
            self._log(f"Skipping CDP scan (browser is {browser_name}, need chromium)", log)
            return

        try:
            cdp = await context.new_cdp_session(page)
        except Exception as e:
            self._log(f"CDP session failed (non-critical): {e}", log)
            return

        found = 0
        inspected = 0

        try:
            # 1) Get document root
            doc = await cdp.send("DOM.getDocument", {"depth": 1, "pierce": True})
            root_node_id = (doc or {}).get("root", {}).get("nodeId")
            if not root_node_id:
                self._log("CDP: no DOM root nodeId", log)
                return

            # 2) Query candidate nodes
            sel = str(self.cfg.candidate_selector or "div,span,button,a,input")
            qs = await cdp.send("DOM.querySelectorAll", {"nodeId": root_node_id, "selector": sel})
            node_ids = (qs or {}).get("nodeIds", []) or []
            if not node_ids:
                self._log("CDP: no candidates matched selector", log)
                return

            node_ids = node_ids[: int(self.cfg.max_candidate_nodes)]

            # helper: flatten CDP attributes list into dict
            def _attr_list_to_dict(attr_list: List[str]) -> Dict[str, str]:
                try:
                    return dict(zip(attr_list[0::2], attr_list[1::2]))
                except Exception:
                    return {}

            # 3) For each candidate, resolve -> getEventListeners -> filter
            for nid in node_ids:
                if found >= int(self.cfg.max_listener_hits):
                    break

                inspected += 1

                try:
                    remote_obj = await cdp.send("DOM.resolveNode", {"nodeId": nid})
                    object_id = (remote_obj or {}).get("object", {}).get("objectId")
                    if not object_id:
                        continue

                    # Correct CDP method name is getEventListeners (plural)
                    listeners_resp = await cdp.send(
                        "DOMDebugger.getEventListeners",
                        {
                            "objectId": object_id,
                            "depth": 1,
                        },
                    )
                    listeners = (listeners_resp or {}).get("listeners", []) or []
                    if not listeners:
                        continue

                    # filter to relevant types
                    relevant = []
                    for l in listeners:
                        if not isinstance(l, dict):
                            continue
                        lt = str(l.get("type") or "")
                        if lt in self.cfg.listener_types:
                            relevant.append(l)

                    if not relevant:
                        continue

                    # attributes + nodeName
                    attrs_resp = await cdp.send("DOM.getAttributes", {"nodeId": nid})
                    attr_list = (attrs_resp or {}).get("attributes", []) or []
                    attr_dict = _attr_list_to_dict(attr_list)

                    desc = await cdp.send("DOM.describeNode", {"nodeId": nid})
                    node_name = ""
                    try:
                        node_name = str((desc or {}).get("node", {}).get("nodeName") or "")
                    except Exception:
                        node_name = ""

                    flags: Dict[str, Any] = {}
                    if self.cfg.include_listener_flags:
                        # Keep only small, non-explosive fields
                        flags = {
                            "count": len(relevant),
                            "capture": any(bool(r.get("useCapture")) for r in relevant),
                            "passive": any(bool(r.get("passive")) for r in relevant),
                            "once": any(bool(r.get("once")) for r in relevant),
                        }

                    outer_html = None
                    if self.cfg.include_outer_html_snippet:
                        try:
                            oh = await cdp.send("DOM.getOuterHTML", {"nodeId": nid})
                            outer_html = str((oh or {}).get("outerHTML") or "")
                            if outer_html and len(outer_html) > int(self.cfg.outer_html_max_chars):
                                outer_html = outer_html[: int(self.cfg.outer_html_max_chars)] + "…"
                        except Exception:
                            outer_html = None

                    # dedupe fingerprint (node + listener types + id/class)
                    fp = (
                        int(nid),
                        node_name,
                        tuple(sorted({str(r.get("type") or "") for r in relevant})),
                        attr_dict.get("id", ""),
                        attr_dict.get("class", ""),
                    )
                    if fp in self._seen_fingerprints:
                        continue
                    self._seen_fingerprints.add(fp)

                    self._listeners.append(
                        InteractionSniffer.ListenerMem(
                            node_id=int(nid),
                            node_name=node_name,
                            types=sorted({str(r.get("type") or "") for r in relevant}),
                            attributes=attr_dict,
                            flags=flags,
                            outer_html=outer_html,
                        )
                    )
                    found += 1

                except Exception:
                    continue

            self._log(
                f"CDP listener scan: inspected={inspected} candidates, found={found} interactive nodes",
                log,
            )

        except Exception as e:
            self._log(f"CDP listener scan failed: {e}", log)
        finally:
            try:
                await cdp.detach()
            except Exception:
                pass

    # ------------------------------------------------------------------ #
    # Memory -> Final hits
    # ------------------------------------------------------------------ #
    def _materialize_hits(self, page_url: str) -> List[Dict[str, Any]]:
        hits: List[Dict[str, Any]] = []

        # 1) Event listener hits
        for l in self._listeners:
            meta = {
                "nodeId": l.node_id,
                "nodeName": l.node_name,
                "types": list(l.types),
                "attributes": dict(l.attributes or {}),
                "flags": dict(l.flags or {}),
                "is_pure_js": True,  # indicates discovered via CDP memory, not HTML attrs
            }
            if l.outer_html:
                meta["outerHTML"] = l.outer_html

            hits.append(
                {
                    "page": page_url,
                    "url": page_url,
                    "tag": "interaction",
                    "kind": "event_listener",
                    "meta": meta,
                }
            )

        # 2) Overlay hits
        for ov in self._overlays:
            hits.append(
                {
                    "page": page_url,
                    "url": page_url,
                    "tag": "interaction",
                    "kind": "overlay_detected",
                    "meta": {
                        "tagName": ov.tag_name,
                        "id": ov.id,
                        "className": ov.class_name,
                        "zIndex": ov.z_index,
                        "coverage": ov.coverage,
                        "textPreview": ov.text_preview,
                    },
                }
            )

        # 3) Form definition hits
        for f in self._forms:
            hits.append(
                {
                    "page": page_url,
                    "url": (f.action or page_url),
                    "tag": "interaction",
                    "kind": "form_definition",
                    "meta": {
                        "action": f.action,
                        "method": f.method,
                        "id": f.id,
                        "class": f.class_name,
                        "input_count": f.input_count,
                        "inputs": f.inputs,
                    },
                }
            )

        # 4) Summary hit (optional)
        if self.cfg.emit_summary_hit:
            summary = self._build_summary_hit(page_url)
            if summary is not None:
                hits.append(summary)

        return hits

    def _build_summary_hit(self, page_url: str) -> Optional[Dict[str, Any]]:
        if not self._listeners and not self._overlays and not self._forms:
            return None

        # counts + quick highlights
        top_listener_types: Dict[str, int] = {}
        for l in self._listeners:
            for t in l.types:
                top_listener_types[t] = top_listener_types.get(t, 0) + 1

        top_types = sorted(top_listener_types.items(), key=lambda kv: kv[1], reverse=True)[:10]

        # overlay severity heuristic: max coverage / max z
        max_coverage = None
        max_z = None
        for ov in self._overlays:
            try:
                cov = float(str(ov.coverage).replace("%", ""))
                max_coverage = cov if max_coverage is None else max(max_coverage, cov)
            except Exception:
                pass
            try:
                max_z = ov.z_index if max_z is None else max(max_z, ov.z_index)
            except Exception:
                pass

        meta: Dict[str, Any] = {
            "listener_count": len(self._listeners),
            "overlay_count": len(self._overlays),
            "form_count": len(self._forms),
            "top_listener_types": top_types,
            "max_overlay_coverage_percent": max_coverage,
            "max_overlay_z_index": max_z,
        }

        return {
            "page": page_url,
            "url": page_url,
            "tag": "interaction",
            "kind": "summary",
            "meta": meta,
        }

# ======================================================================
# Database
# ======================================================================

DEFAULT_TIMEOUT_S = 10.0


@dataclass
class DatabaseConfig:
    """
    Configuration for sqlite connections.

    You can extend this later with:
      - pragmas
      - in-memory / shared-cache
      - WAL tuning
      - migrations folder, etc.
    """
    path: str = "link_corpus.db"
    timeout_s: float = DEFAULT_TIMEOUT_S
    check_same_thread: bool = False  # allow multi-thread access with our lock
    pragmas: Optional[dict[str, Any]] = None  # e.g. {"journal_mode":"WAL"}

    def normalized_path(self) -> str:
        return str(self.path or "link_corpus.db")


class DatabaseSubmanager:
    """
    A small sqlite manager intended to be shared across blocks.

    Responsibilities:
      - open/close a connection
      - install schema + perform light migrations
      - provide safe execute/fetch helpers
      - be thread-safe (single connection + RLock)

    Blocks should NOT talk to sqlite directly; use Stores instead.
    """

    def __init__(self, config: DatabaseConfig | None = None, logger=None):
        self.config = config or DatabaseConfig()
        self.logger = logger
        self._conn: Optional[sqlite3.Connection] = None
        self._lock = threading.RLock()
        self._schema_installed = False

    # ------------------------------------------------------------ #
    # Connection lifecycle
    # ------------------------------------------------------------ #
    def open(self) -> sqlite3.Connection:
        with self._lock:
            if self._conn:
                return self._conn

            db_path = self.config.normalized_path()
            existed = Path(db_path).exists()

            self._conn = sqlite3.connect(
                db_path,
                timeout=self.config.timeout_s,
                check_same_thread=self.config.check_same_thread,
            )
            self._conn.row_factory = sqlite3.Row

            self._apply_pragmas()
            # schema installation is store-driven (each store can call ensure_schema)
            if self.logger:
                self.logger.log_message(
                    f"[DB] {'Using existing' if existed else 'Created'} sqlite DB at {db_path}"
                )
            else:
                print(f"[DB] {'Using existing' if existed else 'Created'} sqlite DB at {db_path}")

            return self._conn

    def close(self) -> None:
        with self._lock:
            if self._conn:
                try:
                    self._conn.close()
                finally:
                    self._conn = None
                    self._schema_installed = False

    def connection(self) -> Optional[sqlite3.Connection]:
        return self._conn

    # ------------------------------------------------------------ #
    # Pragmas / schema / migrations
    # ------------------------------------------------------------ #
    def _apply_pragmas(self):
        if not self._conn:
            return
        pragmas = self.config.pragmas or {
            "journal_mode": "WAL",
            "synchronous": "NORMAL",
            "temp_store": "MEMORY",
            "foreign_keys": "ON",
        }
        cur = self._conn.cursor()
        for k, v in pragmas.items():
            try:
                cur.execute(f"PRAGMA {k}={v}")
            except Exception:
                # pragma failures should never crash the app
                pass
        self._conn.commit()

    def ensure_schema(self, ddl_statements: Sequence[str]) -> None:
        """
        Idempotent schema installer.

        Each Store passes its own DDL list.
        This allows many blocks to share one DB without collisions.
        """
        conn = self.open()
        with self._lock:
            cur = conn.cursor()
            for ddl in ddl_statements:
                cur.execute(ddl)
            conn.commit()
            self._schema_installed = True

    def ensure_columns(self, table: str, columns: dict[str, str]) -> None:
        """
        Micro-migration helper:
        Adds missing columns with ALTER TABLE.

        columns = {"seed_ok": "INTEGER DEFAULT 0", ...}
        """
        conn = self.open()
        with self._lock:
            cur = conn.cursor()
            try:
                cur.execute(f"PRAGMA table_info({table})")
                existing = {r["name"] for r in cur.fetchall()}
            except Exception:
                existing = set()

            for col, ddl in columns.items():
                if col not in existing:
                    try:
                        cur.execute(f"ALTER TABLE {table} ADD COLUMN {col} {ddl}")
                        if self.logger:
                            self.logger.log_message(f"[DB] Added column {table}.{col}")
                    except Exception as e:
                        if self.logger:
                            self.logger.log_message(f"[DB] Failed adding column {table}.{col}: {e}")
            conn.commit()

    # ------------------------------------------------------------ #
    # Query helpers
    # ------------------------------------------------------------ #
    def execute(self, sql: str, args: Sequence[Any] | None = None) -> None:
        conn = self.open()
        with self._lock:
            cur = conn.cursor()
            cur.execute(sql, args or [])
            conn.commit()

    def executemany(self, sql: str, rows: Iterable[Sequence[Any]]) -> None:
        conn = self.open()
        with self._lock:
            cur = conn.cursor()
            cur.executemany(sql, rows)
            conn.commit()

    def fetchone(self, sql: str, args: Sequence[Any] | None = None) -> Optional[sqlite3.Row]:
        conn = self.open()
        with self._lock:
            cur = conn.cursor()
            cur.execute(sql, args or [])
            return cur.fetchone()

    def fetchall(self, sql: str, args: Sequence[Any] | None = None) -> list[sqlite3.Row]:
        conn = self.open()
        with self._lock:
            cur = conn.cursor()
            cur.execute(sql, args or [])
            return cur.fetchall()

    def scalar(self, sql: str, args: Sequence[Any] | None = None) -> Any:
        row = self.fetchone(sql, args)
        if not row:
            return None
        return row[0]


# ======================================================================
# HLS
# ======================================================================

@dataclass
class HLSDownloadResult:
    """
    Result of an HLS capture.

    - stream_id: stable ID for this stream (hash of manifest URL)
    - manifest_url: original manifest URL (may be master or media playlist)
    - manifest_path: local path for the first manifest saved
    - variant_manifest_url: chosen variant playlist URL (if found)
    - variant_manifest_path: local path for variant manifest (if any)
    - segment_paths: list of local file paths for downloaded .ts segments
    """
    stream_id: str
    manifest_url: str
    manifest_path: str
    variant_manifest_url: Optional[str]
    variant_manifest_path: Optional[str]
    segment_paths: List[str]


class HLSSubManager:
    """
    Simple, environment-friendly HLS helper.

    Responsibilities:
      • Given a manifest URL (.m3u8), download it.
      • If it's a master playlist (#EXT-X-STREAM-INF), choose one variant.
      • Download that media playlist + up to N .ts segments.
      • Save everything under hls_cache/<stream_id>/...
      • Return paths + URLs; NO ffmpeg, NO transcoding.

    This is intentionally generic so other blocks can reuse it.
    """

    def __init__(
        self,
        root_dir: str | Path = "hls_cache",
        logger=None,
        max_segments: int = 200,
        max_total_bytes: int = 500 * 1024 * 1024,  # 500 MB safety cap
    ):
        self.root_dir = Path(root_dir)
        self.root_dir.mkdir(parents=True, exist_ok=True)
        self.logger = logger
        self.max_segments = max_segments
        self.max_total_bytes = max_total_bytes

    # ---- helpers -----------------------------------------------------

    def _log(self, msg: str):
        if self.logger and hasattr(self.logger, "log_message"):
            try:
                self.logger.log_message(msg)
                return
            except Exception:
                pass
        # Fallback – safe in background / tests
        print(msg)

    def _stream_id(self, manifest_url: str) -> str:
        h = hashlib.sha1(manifest_url.encode("utf-8", errors="ignore")).hexdigest()
        return h[:16]

    async def _fetch_text(
            self,
            session: Any,
            url: str,
            timeout: float,
            log: list[str],
    ) -> str:
        """
        Fetch text either via:
          • raw aiohttp.ClientSession (has .get)
          • HTTPSSubmanager (has .get_text)
        """
        # Path 1: HTTPSSubmanager-style wrapper (has get_text / get_bytes, but no .get)
        if hasattr(session, "get_text") and not hasattr(session, "get"):
            try:
                text = await session.get_text(url)
                if not text:
                    log.append(f"[HLS] Empty response for manifest {url}")
                return text or ""
            except Exception as e:
                log.append(f"[HLS] Error fetching manifest {url}: {e}")
                return ""

        # Path 2: plain aiohttp.ClientSession (has .get)
        try:
            async with session.get(
                    url,
                    timeout=aiohttp.ClientTimeout(total=timeout),
                    allow_redirects=True,
            ) as r:
                if r.status >= 400:
                    log.append(f"[HLS] HTTP {r.status} for manifest {url}")
                    return ""
                return await r.text(errors="ignore")
        except Exception as e:
            log.append(f"[HLS] Error fetching manifest {url}: {e}")
            return ""
    async def _download_binary(
        self,
        session: Any,
        url: str,
        path: Path,
        timeout: float,
        log: list[str],
        budget: dict,
    ) -> bool:
        """
        Download binary URL into path, respecting global byte budget.
        Works with either:
          • aiohttp.ClientSession
          • HTTPSSubmanager (get_bytes)
        Returns True if some bytes written.
        """
        # Path 1: HTTPSSubmanager-style client
        if hasattr(session, "get_bytes") and not hasattr(session, "get"):
            try:
                data = await session.get_bytes(url)
                if not data:
                    log.append(f"[HLS] Zero-length segment from {url}")
                    return False

                remaining = self.max_total_bytes - budget["bytes"]
                if remaining <= 0:
                    log.append(
                        "[HLS] Max_total_bytes reached; "
                        "stopping further segment downloads."
                    )
                    return False

                # Respect the global byte budget
                if len(data) > remaining:
                    log.append(
                        "[HLS] Truncating segment due to max_total_bytes limit."
                    )
                    data = data[:remaining]

                path.parent.mkdir(parents=True, exist_ok=True)
                with path.open("wb") as f:
                    f.write(data)

                written = len(data)
                budget["bytes"] += written
                if written == 0:
                    log.append(f"[HLS] Zero-length segment from {url}")
                    return False
                return True

            except Exception as e:
                log.append(f"[HLS] Error downloading segment {url}: {e}")
                return False

        # Path 2: aiohttp.ClientSession
        try:
            async with session.get(
                url,
                timeout=aiohttp.ClientTimeout(total=timeout),
                allow_redirects=True,
            ) as r:
                if r.status >= 400:
                    log.append(f"[HLS] Segment HTTP {r.status}: {url}")
                    return False

                path.parent.mkdir(parents=True, exist_ok=True)
                written = 0
                with path.open("wb") as f:
                    async for chunk in r.content.iter_chunked(256 * 1024):
                        if not chunk:
                            continue
                        if budget["bytes"] + len(chunk) > self.max_total_bytes:
                            log.append(
                                "[HLS] Max_total_bytes reached; "
                                "stopping further segment downloads."
                            )
                            break
                        f.write(chunk)
                        budget["bytes"] += len(chunk)
                        written += len(chunk)

                if written == 0:
                    log.append(f"[HLS] Zero-length segment from {url}")
                    return False
                return True

        except Exception as e:
            log.append(f"[HLS] Error downloading segment {url}: {e}")
            return False

    # ---- public API --------------------------------------------------

    async def capture_hls_stream(
        self,
        session: aiohttp.ClientSession,
        manifest_url: str,
        timeout: float,
        log: list[str],
    ) -> Optional[HLSDownloadResult]:
        """
        Best-effort HLS capture.

        Downloads:
          • The original manifest.
          • If it is a master playlist, the best BANDWIDTH variant.
          • Up to max_segments media segments from the chosen playlist.

        Returns HLSDownloadResult or None on total failure.
        """
        manifest_url = manifest_url.strip()
        if not manifest_url:
            return None

        stream_id = self._stream_id(manifest_url)
        stream_dir = self.root_dir / stream_id
        stream_dir.mkdir(parents=True, exist_ok=True)

        log.append(f"[HLS] Capturing HLS stream {manifest_url} -> {stream_dir}")

        # 1) Download original manifest
        master_text = await self._fetch_text(session, manifest_url, timeout, log)
        if not master_text.strip():
            log.append("[HLS] Empty master manifest; aborting.")
            return None

        master_path = stream_dir / "master.m3u8"
        master_path.write_text(master_text, encoding="utf-8", errors="ignore")

        # 2) Check for variants (#EXT-X-STREAM-INF)
        lines = [ln.strip() for ln in master_text.splitlines()]
        best_variant_url = None
        best_bandwidth = -1

        for idx, ln in enumerate(lines):
            if not ln.startswith("#EXT-X-STREAM-INF"):
                continue
            # Very small parser – looks for BANDWIDTH=12345
            bw = -1
            for part in ln.split(","):
                part = part.strip()
                if part.upper().startswith("BANDWIDTH="):
                    try:
                        bw = int(part.split("=", 1)[1].strip())
                    except ValueError:
                        bw = -1
                    break

            # Next non-comment line should be the URI
            uri = None
            if idx + 1 < len(lines):
                nxt = lines[idx + 1].strip()
                if nxt and not nxt.startswith("#"):
                    uri = nxt

            if uri:
                full = urljoin(manifest_url, uri)
                if bw > best_bandwidth:
                    best_bandwidth = bw
                    best_variant_url = full

        variant_text = None
        variant_path: Optional[Path] = None

        if best_variant_url:
            log.append(
                f"[HLS] Master playlist detected. Choosing variant "
                f"{best_variant_url} (BANDWIDTH={best_bandwidth})."
            )
            variant_text = await self._fetch_text(session, best_variant_url, timeout, log)
            if variant_text.strip():
                variant_path = stream_dir / "variant.m3u8"
                variant_path.write_text(variant_text, encoding="utf-8", errors="ignore")
            else:
                log.append("[HLS] Variant manifest empty; falling back to master for segments.")
        else:
            log.append("[HLS] No EXT-X-STREAM-INF found; treating master as media playlist.")

        media_text = variant_text or master_text
        media_url = best_variant_url or manifest_url

        # 3) Parse media playlist for segment URIs
        seg_urls: list[str] = []
        for ln in media_text.splitlines():
            ln = ln.strip()
            if not ln or ln.startswith("#"):
                continue
            # Non-comment lines in media playlist are segment URIs
            seg_urls.append(urljoin(media_url, ln))
            if len(seg_urls) >= self.max_segments:
                break

        if not seg_urls:
            log.append("[HLS] No segments found in media playlist.")
            return HLSDownloadResult(
                stream_id=stream_id,
                manifest_url=manifest_url,
                manifest_path=str(master_path),
                variant_manifest_url=best_variant_url,
                variant_manifest_path=str(variant_path) if variant_path else None,
                segment_paths=[],
            )

        # 4) Download segments with a global byte budget
        seg_paths: list[str] = []
        budget = {"bytes": 0}

        for idx, su in enumerate(seg_urls):
            seg_name = f"seg-{idx:05d}.ts"
            seg_path = stream_dir / seg_name
            ok = await self._download_binary(
                session, su, seg_path, timeout, log, budget
            )
            if ok:
                seg_paths.append(str(seg_path))
            if budget["bytes"] >= self.max_total_bytes:
                break

        log.append(
            f"[HLS] Downloaded {len(seg_paths)} segments "
            f"({budget['bytes'] / 1024 / 1024:.1f} MB) for stream_id={stream_id}."
        )

        return HLSDownloadResult(
            stream_id=stream_id,
            manifest_url=manifest_url,
            manifest_path=str(master_path),
            variant_manifest_url=best_variant_url,
            variant_manifest_path=str(variant_path) if variant_path else None,
            segment_paths=seg_paths,
        )

# ======================================================================
# HTTPS
# ======================================================================

@dataclass
class _HTTPResult:
    ok: bool
    status: Optional[int]
    headers: Dict[str, str]
    final_url: str
    body: bytes
    error: str = ""


class HTTPSSubmanager:
    """
    Industrial-grade shared HTTPS engine (aiohttp-only), with:
      - Freeze prevention: strict timeouts, redirect caps, early-exit for heavy MIME.
      - Secure Gateway: magic-byte verification, entropy heuristics, decompression bomb guard.
      - Optional domain reputation filter (local heuristics / denylist).
    """

    # --- Magic byte signatures (first bytes) ---
    _MAGIC_EXE = (b"MZ",)  # Windows PE
    _MAGIC_PDF = (b"%PDF",)
    _MAGIC_PNG = (b"\x89PNG\r\n\x1a\n",)
    _MAGIC_JPG = (b"\xff\xd8\xff",)
    _MAGIC_GIF = (b"GIF87a", b"GIF89a")
    _MAGIC_ZIP = (b"PK\x03\x04", b"PK\x05\x06", b"PK\x07\x08")

    # quick “script-like” / “text-like” types
    _TEXTLIKE_MIME_HINTS = (
        "text/",
        "application/json",
        "application/xml",
        "application/javascript",
        "application/x-javascript",
        "application/ecmascript",
        "application/x-ecmascript",
        "application/xhtml+xml",
        "application/x-www-form-urlencoded",
    )

    def __init__(
        self,
        user_agent: str = "Mozilla/5.0 PromptChat/LinkTracker",
        timeout: float = 6.0,
        retries: int = 2,
        backoff_base: float = 0.35,
        backoff_cap: float = 8.0,
        max_conn_per_host: int = 8,
        max_total_conn: int = 0,
        proxy: Optional[str] = None,
        proxy_pool: Optional[list] = None,
        verify: bool = True,
        ca_bundle: Optional[str] = None,

        # safety / “don’t melt”
        max_bytes: int = 4_000_000,
        max_html_chars: int = 600_000,
        respect_retry_after: bool = True,
        enable_cookies: bool = True,
        allow_redirects: bool = True,

        # ------------------ Freeze prevention ------------------
        max_redirects: int = 5,                # hard cap
        total_timeout_s: float = 15.0,         # DNS+connect+first byte+body, etc.
        connect_timeout_s: float = 5.0,
        sock_read_timeout_s: float = 7.0,      # overall socket-read budget
        chunk_timeout_s: float = 5.0,          # “silence” timeout between chunks
        chunk_size: int = 64 * 1024,

        # MIME early exit
        heavy_mime_hints: Tuple[str, ...] = ("video/", "audio/", "application/octet-stream"),
        heavy_snippet_cap: int = 1_000_000,    # if max_bytes > this and MIME is heavy => bail

        # ------------------ Secure Gateway ------------------
        enable_magic_byte_verification: bool = True,
        magic_pe_kill_mime_allow: Tuple[str, ...] = ("application/x-msdownload", "application/octet-stream"),
        magic_pe_kill_ext_block: Tuple[str, ...] = (".js", ".mjs", ".css", ".json", ".xml", ".txt", ".html", ".htm"),
        enable_entropy_filter: bool = True,
        entropy_sample_bytes: int = 64_000,    # only sample first N bytes of text
        entropy_threshold: float = 7.25,       # near 8 => very “random”
        min_printable_ratio: float = 0.75,     # text should mostly be printable
        enable_decompression_bomb_guard: bool = True,
        decompress_ratio_limit: float = 120.0, # uncompressed_bytes / compressed_bytes
        decompress_hard_cap_bytes: int = 12_000_000,  # absolute decoded cap during decompress

        # ------------------ Domain reputation (optional) ------------------
        enable_domain_reputation_filter: bool = False,
        domain_denylist: Optional[Tuple[str, ...]] = None,
        parked_domain_hints: Tuple[str, ...] = (
            "sedoparking", "parkingcrew", "bodis", "domainparking", "namebright",
            "dan.com", "hugedomains", "afternic", "parking", "buythisdomain"
        ),
    ):
        self.ua = user_agent
        self.timeout = float(timeout)
        self.retries = int(retries)
        self.backoff_base = float(backoff_base)
        self.backoff_cap = float(backoff_cap)

        self.max_conn_per_host = int(max_conn_per_host)
        self.max_total_conn = int(max_total_conn)

        self.proxy = proxy
        self.proxy_pool = proxy_pool or []

        self.verify = bool(verify)
        self.ca_bundle = ca_bundle

        self.max_bytes = int(max_bytes)
        self.max_html_chars = int(max_html_chars)
        self.respect_retry_after = bool(respect_retry_after)
        self.allow_redirects = bool(allow_redirects)

        # freeze prevention
        self.max_redirects = int(max_redirects)
        self.total_timeout_s = float(total_timeout_s)
        self.connect_timeout_s = float(connect_timeout_s)
        self.sock_read_timeout_s = float(sock_read_timeout_s)
        self.chunk_timeout_s = float(chunk_timeout_s)
        self.chunk_size = int(chunk_size)

        self.heavy_mime_hints = tuple(str(x).lower() for x in heavy_mime_hints)
        self.heavy_snippet_cap = int(heavy_snippet_cap)

        # secure gateway
        self.enable_magic_byte_verification = bool(enable_magic_byte_verification)
        self.magic_pe_kill_mime_allow = tuple(str(x).lower() for x in magic_pe_kill_mime_allow)
        self.magic_pe_kill_ext_block = tuple(str(x).lower() for x in magic_pe_kill_ext_block)

        self.enable_entropy_filter = bool(enable_entropy_filter)
        self.entropy_sample_bytes = int(entropy_sample_bytes)
        self.entropy_threshold = float(entropy_threshold)
        self.min_printable_ratio = float(min_printable_ratio)

        self.enable_decompression_bomb_guard = bool(enable_decompression_bomb_guard)
        self.decompress_ratio_limit = float(decompress_ratio_limit)
        self.decompress_hard_cap_bytes = int(decompress_hard_cap_bytes)

        # domain reputation
        self.enable_domain_reputation_filter = bool(enable_domain_reputation_filter)
        self.domain_denylist = tuple(d.lower() for d in (domain_denylist or ()))
        self.parked_domain_hints = tuple(x.lower() for x in parked_domain_hints)

        self.enable_cookies = bool(enable_cookies)

        self._session: Optional[aiohttp.ClientSession] = None
        self._connector: Optional[aiohttp.TCPConnector] = None
        self._ssl_context: Optional[ssl.SSLContext] = None

        self._host_sem: Dict[str, asyncio.Semaphore] = {}
        self._host_cooldown_until: Dict[str, float] = {}
        self._host_last_ok_url: Dict[str, str] = {}
        self._cooldown_lock = asyncio.Lock()

    # ------------------------------------------------------------- #
    # Context manager
    # ------------------------------------------------------------- #
    async def __aenter__(self):
        self._ssl_context = self._build_ssl_context()

        self._connector = aiohttp.TCPConnector(
            ssl=self._ssl_context,
            limit=(self.max_total_conn if self.max_total_conn > 0 else 0),
            limit_per_host=self.max_conn_per_host,
            ttl_dns_cache=300,
            enable_cleanup_closed=True,
            keepalive_timeout=30,
            happy_eyeballs_delay=0.25,
        )

        jar = aiohttp.CookieJar(unsafe=True) if self.enable_cookies else None
        base_headers = self._base_browser_headers()

        # IMPORTANT:
        # auto_decompress=False lets us enforce decompression ratio/caps ourselves.
        self._session = aiohttp.ClientSession(
            connector=self._connector,
            cookie_jar=jar,
            headers=base_headers,
            auto_decompress=False,
            trust_env=True,
        )
        return self

    async def __aexit__(self, exc_type, exc, tb):
        if self._session:
            await self._session.close()
        self._session = None
        self._connector = None
        self._ssl_context = None
        self._host_sem.clear()
        self._host_cooldown_until.clear()
        self._host_last_ok_url.clear()

    # ------------------------------------------------------------- #
    # SSL / TLS helpers
    # ------------------------------------------------------------- #
    def _build_ssl_context(self) -> Optional[ssl.SSLContext]:
        if self.verify and not self.ca_bundle:
            return None
        if self.verify:
            return ssl.create_default_context(cafile=self.ca_bundle if self.ca_bundle else None)
        ctx = ssl.create_default_context()
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
        return ctx

    # ------------------------------------------------------------- #
    # Host helpers
    # ------------------------------------------------------------- #
    def _host(self, url: str) -> str:
        try:
            return urlparse(url).netloc.lower()
        except Exception:
            return ""

    def _path(self, url: str) -> str:
        try:
            return urlparse(url).path or ""
        except Exception:
            return ""

    def _get_host_semaphore(self, host: str) -> asyncio.Semaphore:
        if not host:
            host = "_"
        return self._host_sem.setdefault(host, asyncio.Semaphore(self.max_conn_per_host))

    async def _respect_host_cooldown(self, host: str):
        if not host:
            return
        until = self._host_cooldown_until.get(host, 0.0)
        now = time.time()
        if until > now:
            await asyncio.sleep(min(5.0, until - now))

    async def _set_host_cooldown(self, host: str, seconds: float):
        if not host or seconds <= 0:
            return
        async with self._cooldown_lock:
            now = time.time()
            cur = self._host_cooldown_until.get(host, 0.0)
            self._host_cooldown_until[host] = max(cur, now + seconds)

    # ------------------------------------------------------------- #
    # Proxy + headers
    # ------------------------------------------------------------- #
    def _choose_proxy(self) -> Optional[str]:
        if self.proxy:
            return self.proxy
        if self.proxy_pool:
            return random.choice(self.proxy_pool)
        return None

    def _base_browser_headers(self) -> Dict[str, str]:
        return {
            "User-Agent": self.ua,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
            "Accept-Encoding": "gzip, deflate, br",
            "Connection": "keep-alive",
            "Upgrade-Insecure-Requests": "1",
            "DNT": "1",
            "Sec-Fetch-Dest": "document",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Site": "none",
            "Sec-Fetch-User": "?1",
        }

    def _per_request_headers(self, url: str) -> Dict[str, str]:
        host = self._host(url)
        last_ok = self._host_last_ok_url.get(host, "")
        h: Dict[str, str] = {}
        if last_ok:
            h["Referer"] = last_ok
            h["Sec-Fetch-Site"] = "same-origin"
        if random.random() < 0.10:
            h["Accept-Language"] = "en-US,en;q=0.8"
        return h

    # ------------------------------------------------------------- #
    # Retry policy
    # ------------------------------------------------------------- #
    def _is_retryable_status(self, status: int) -> bool:
        return status in (408, 425, 429, 500, 502, 503, 504)

    def _retry_delay(self, attempt: int, *, server_hint: Optional[float] = None) -> float:
        if server_hint is not None and server_hint > 0:
            return min(self.backoff_cap, float(server_hint))
        base = self.backoff_base * (2 ** attempt)
        jitter = random.uniform(0.0, base * 0.25)
        return min(self.backoff_cap, base + jitter)

    def _parse_retry_after(self, hdrs: Dict[str, str]) -> Optional[float]:
        ra = (hdrs.get("Retry-After") or hdrs.get("retry-after") or "").strip()
        if not ra:
            return None
        try:
            return float(ra)
        except Exception:
            return None

    # ------------------------------------------------------------- #
    # Domain reputation filter (optional)
    # ------------------------------------------------------------- #
    def _is_toxic_domain(self, host: str) -> bool:
        if not host:
            return False
        h = host.lower()

        # explicit denylist (exact or suffix match)
        for d in self.domain_denylist:
            if h == d or h.endswith("." + d):
                return True

        # cheap “parked” / “toxic” heuristics
        for hint in self.parked_domain_hints:
            if hint in h:
                return True

        # extremely short / weird netlocs can be junk in bulk crawls
        if len(h) <= 3 and "." not in h:
            return True

        return False

    # ------------------------------------------------------------- #
    # Secure Gateway helpers
    # ------------------------------------------------------------- #
    def _content_type(self, hdrs: Dict[str, str]) -> str:
        return (hdrs.get("Content-Type") or hdrs.get("content-type") or "").lower()

    def _content_encoding(self, hdrs: Dict[str, str]) -> str:
        return (hdrs.get("Content-Encoding") or hdrs.get("content-encoding") or "").lower()

    def _looks_textlike(self, ctype: str) -> bool:
        if not ctype:
            return False
        return any(h in ctype for h in self._TEXTLIKE_MIME_HINTS)

    def _should_early_exit_heavy(self, ctype: str, max_bytes: int) -> bool:
        if not ctype:
            return False
        if any(h in ctype for h in self.heavy_mime_hints) and max_bytes > self.heavy_snippet_cap:
            return True
        return False

    def _starts_with_any(self, data: bytes, sigs: Tuple[bytes, ...]) -> bool:
        for s in sigs:
            if data.startswith(s):
                return True
        return False

    def _magic_byte_violation(self, url: str, ctype: str, first: bytes) -> bool:
        """
        If a response is effectively a PE (MZ) but it "looks like" text/script,
        kill it early. This is deliberately conservative to avoid false positives.
        """
        if not first or len(first) < 2:
            return False
        if not self._starts_with_any(first, self._MAGIC_EXE):
            return False

        path = self._path(url).lower()

        # If file extension suggests text/script or page-like content -> suspicious
        if any(path.endswith(ext) for ext in self.magic_pe_kill_ext_block):
            return True

        # If content-type says textlike -> suspicious
        if self._looks_textlike(ctype):
            return True

        # If content-type is not in the small “allowed” list -> suspicious
        if ctype and not any(a in ctype for a in self.magic_pe_kill_mime_allow):
            return True

        return False

    def _shannon_entropy(self, data: bytes) -> float:
        """
        Shannon entropy in bits/byte on the given byte sample.
        """
        if not data:
            return 0.0
        # frequency
        counts = [0] * 256
        for b in data:
            counts[b] += 1
        n = float(len(data))
        ent = 0.0
        for c in counts:
            if c:
                p = c / n
                ent -= p * math.log2(p)
        return ent

    def _printable_ratio(self, data: bytes) -> float:
        if not data:
            return 1.0
        printable = 0
        for b in data:
            # allow common whitespace + ASCII printable
            if b in (9, 10, 13) or 32 <= b <= 126:
                printable += 1
        return printable / max(1, len(data))

    # ------------------------------------------------------------- #
    # Read + Decompress (bounded, timeouted, guarded)
    # ------------------------------------------------------------- #
    async def _read_bounded_secure(self, resp: aiohttp.ClientResponse, url: str, max_bytes: int) -> Tuple[bytes, str]:
        """
        Returns (body_bytes, error_string). error_string non-empty => treat as blocked/error.
        Notes:
          - Reads compressed bytes from the socket (auto_decompress=False).
          - If encoding gzip/deflate -> incremental decompress with ratio + cap checks.
          - Enforces per-chunk “silence” timeout to prevent slowloris/zombies.
          - Does magic-byte check on the *decompressed* first bytes (best signal).
          - Does entropy heuristic on text-like content (first N bytes).
        """
        hdrs = dict(resp.headers) if resp.headers else {}
        ctype = self._content_type(hdrs)
        enc = self._content_encoding(hdrs)

        # MIME-type early exit for heavy blobs
        if self._should_early_exit_heavy(ctype, max_bytes):
            return b"", "early_exit_heavy_mime"

        # incremental decompressor (gzip/deflate only; br is left as raw)
        decompressor = None
        if self.enable_decompression_bomb_guard:
            if "gzip" in enc:
                decompressor = zlib.decompressobj(16 + zlib.MAX_WBITS)  # gzip wrapper
            elif "deflate" in enc:
                decompressor = zlib.decompressobj()

        compressed_read = 0
        out = bytearray()
        first_probe_done = False
        entropy_probe = bytearray()

        it = resp.content.iter_chunked(self.chunk_size).__aiter__()

        while True:
            try:
                chunk = await asyncio.wait_for(it.__anext__(), timeout=self.chunk_timeout_s)
            except StopAsyncIteration:
                break
            except asyncio.TimeoutError:
                # chunk silence timeout: return what we have (do NOT freeze caller)
                break
            except Exception:
                break

            if not chunk:
                break

            compressed_read += len(chunk)

            # Decompress if we can; otherwise treat as plain bytes stream.
            produced = chunk
            if decompressor is not None:
                try:
                    produced = decompressor.decompress(chunk, self.decompress_hard_cap_bytes)
                except Exception:
                    return bytes(out), "decompress_error"

                # ratio guard (only meaningful if we have some compressed bytes)
                if compressed_read > 0:
                    ratio = (len(out) + len(produced)) / max(1, compressed_read)
                    if ratio > self.decompress_ratio_limit:
                        return bytes(out), "decompression_ratio_blocked"

                if (len(out) + len(produced)) > self.decompress_hard_cap_bytes:
                    return bytes(out), "decompression_hard_cap_blocked"

            # magic-byte verification on the first produced bytes
            if self.enable_magic_byte_verification and not first_probe_done:
                probe = produced[:16]
                first_probe_done = True
                if self._magic_byte_violation(url, ctype, probe):
                    try:
                        resp.close()
                    except Exception:
                        pass
                    return b"", "magic_byte_blocked"

            out.extend(produced)

            # entropy probe (only for text-like)
            if self.enable_entropy_filter and self._looks_textlike(ctype) and len(entropy_probe) < self.entropy_sample_bytes:
                take = produced[: max(0, self.entropy_sample_bytes - len(entropy_probe))]
                entropy_probe.extend(take)

            # bounded output read (caller budget)
            if len(out) >= max_bytes:
                try:
                    resp.close()  # early close to avoid lingering
                except Exception:
                    pass
                out = out[:max_bytes]
                break

        # flush decompressor
        if decompressor is not None:
            try:
                tail = decompressor.flush()
                if tail:
                    # enforce guards on flush too
                    if compressed_read > 0:
                        ratio = (len(out) + len(tail)) / max(1, compressed_read)
                        if ratio > self.decompress_ratio_limit:
                            return bytes(out), "decompression_ratio_blocked"
                    if (len(out) + len(tail)) > self.decompress_hard_cap_bytes:
                        return bytes(out), "decompression_hard_cap_blocked"

                    out.extend(tail)
                    if len(out) > max_bytes:
                        out = out[:max_bytes]
            except Exception:
                # ignore flush failures
                pass

        # entropy check (cheap heuristic; block only if strongly suspicious)
        if self.enable_entropy_filter and self._looks_textlike(ctype) and entropy_probe:
            ent = self._shannon_entropy(bytes(entropy_probe))
            pr = self._printable_ratio(bytes(entropy_probe))
            if ent >= self.entropy_threshold and pr < self.min_printable_ratio:
                return bytes(out), f"entropy_blocked(ent={ent:.2f},printable={pr:.2f})"

        return bytes(out), ""

    # ------------------------------------------------------------- #
    # Core request
    # ------------------------------------------------------------- #
    async def _request(
        self,
        method: str,
        url: str,
        *,
        want_body: bool,
        allow_redirects: Optional[bool] = None,
        headers: Optional[Dict[str, str]] = None,
        max_bytes: Optional[int] = None,
    ) -> _HTTPResult:
        if not self._session:
            raise RuntimeError("HTTPSSubmanager must be used in an async context (async with HTTPSSubmanager(...) as http).")

        method = (method or "GET").upper().strip()
        allow_redirects = self.allow_redirects if allow_redirects is None else bool(allow_redirects)
        max_bytes = self.max_bytes if max_bytes is None else int(max_bytes)

        host = self._host(url)

        # optional reputation filter
        if self.enable_domain_reputation_filter and self._is_toxic_domain(host):
            return _HTTPResult(False, None, {}, url, b"", error="domain_reputation_blocked")

        sem = self._get_host_semaphore(host)

        for attempt in range(self.retries + 1):
            await self._respect_host_cooldown(host)

            proxy = self._choose_proxy()
            req_headers: Dict[str, str] = {}
            req_headers.update(self._per_request_headers(url))
            if headers:
                req_headers.update(headers)

            try:
                async with sem:
                    timeout = ClientTimeout(
                        total=self.total_timeout_s,
                        connect=self.connect_timeout_s,
                        sock_read=self.sock_read_timeout_s,
                    )

                    async with self._session.request(
                        method,
                        url,
                        allow_redirects=allow_redirects,
                        max_redirects=self.max_redirects,
                        proxy=proxy,
                        timeout=timeout,
                        headers=req_headers,
                    ) as resp:

                        final_url = str(resp.url)
                        status = int(resp.status)
                        hdrs = dict(resp.headers) if resp.headers else {}

                        # cooldown on 429/503 with Retry-After
                        if self.respect_retry_after and status in (429, 503):
                            ra = self._parse_retry_after(hdrs)
                            if ra:
                                await self._set_host_cooldown(host, ra)

                        body = b""
                        err = ""

                        if want_body:
                            body, err = await self._read_bounded_secure(resp, url=final_url, max_bytes=max_bytes)
                            if err:
                                return _HTTPResult(False, status, hdrs, final_url, b"", error=err)

                        # last-ok for referer mimicry
                        if 200 <= status < 300:
                            self._host_last_ok_url[host] = final_url

                        # retryable statuses
                        if self._is_retryable_status(status) and attempt < self.retries:
                            server_hint = self._parse_retry_after(hdrs) if self.respect_retry_after else None
                            await asyncio.sleep(self._retry_delay(attempt, server_hint=server_hint))
                            continue

                        return _HTTPResult(
                            ok=(200 <= status < 300),
                            status=status,
                            headers=hdrs,
                            final_url=final_url,
                            body=body,
                            error="",
                        )

            except aiohttp.TooManyRedirects:
                return _HTTPResult(False, None, {}, url, b"", error="too_many_redirects")
            except (
                aiohttp.ClientConnectorError,
                aiohttp.ClientOSError,
                aiohttp.ServerDisconnectedError,
                aiohttp.ClientPayloadError,
                asyncio.TimeoutError,
                ssl.SSLError,
            ) as e:
                if attempt >= self.retries:
                    return _HTTPResult(False, None, {}, url, b"", error=str(e))
                await asyncio.sleep(self._retry_delay(attempt))
                continue
            except Exception as e:
                return _HTTPResult(False, None, {}, url, b"", error=str(e))

        return _HTTPResult(False, None, {}, url, b"", error="exhausted_retries")

    # ------------------------------------------------------------- #
    # Public helpers
    # ------------------------------------------------------------- #
    async def get_text(self, url: str) -> str:
        r = await self._request("GET", url, want_body=True)
        if not r.ok or not r.body:
            return ""
        try:
            txt = r.body.decode("utf-8", errors="ignore")
        except Exception:
            return ""
        if len(txt) > self.max_html_chars:
            txt = txt[: self.max_html_chars]
        return txt

    async def get_bytes(self, url: str) -> bytes:
        r = await self._request("GET", url, want_body=True)
        if not r.ok:
            return b""
        return r.body or b""

    async def head(self, url: str) -> Tuple[Optional[int], Dict[str, str]]:
        r = await self._request("HEAD", url, want_body=False, allow_redirects=True)
        if r.status is None:
            return None, {}
        return r.status, r.headers