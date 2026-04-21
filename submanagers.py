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
from html import unescape
from html.parser import HTMLParser
from pathlib import Path
import random  # For random delays
import json  # For JSON parsing in NetworkSniffer and JSSniffer
import xml.etree.ElementTree as ET

import aiohttp
from aiohttp import ClientTimeout
from bs4 import BeautifulSoup
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple, Sequence, Iterable
import asyncio, json, re, hashlib, time
from urllib.parse import urlparse, urlunparse, urlencode, parse_qsl, urljoin

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
    def _safe_parse_qsl(cls, query: Any) -> "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]":
        out: "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]" = []
        try:
            for k, v in cls.parse_qsl(cls._to_str(query), keep_blank_values=True):
                out.append((cls._to_str(k), cls._to_str(v)))
        except Exception:
            pass
        return out

    @classmethod
    def _safe_urlencode(cls, pairs: "NetworkSniffer.List[NetworkSniffer.Tuple[Any, Any]]") -> str:
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
        u = cls._to_str(url).strip()
        if not u:
            return ""
        try:
            p = cls._safe_urlparse(u)
            scheme = cls._to_str(p.scheme).lower()
            netloc = cls._to_str(p.netloc).lower()
            path = cls._to_str(p.path)
            params = cls._to_str(p.params)

            kept: "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]" = []
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
        max_json_hits: int = 220

        max_derived_per_manifest: int = 200
        max_manifests_to_expand: int = 10

        accept_unknown_streams: bool = True

        enable_auto_scroll: bool = True
        max_scroll_steps: int = 20
        scroll_step_delay_ms: int = 400
        scroll_back_to_top: bool = False

        goto_wait_until: str = "domcontentloaded"

        enable_host_allowlist: bool = False
        host_allow_substrings: "NetworkSniffer.Set[str]" = field(default_factory=set)

        enable_host_denylist: bool = False
        host_deny_substrings: "NetworkSniffer.Set[str]" = field(default_factory=set)

        video_extensions: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            ".mp4", ".webm", ".mkv", ".mov", ".avi", ".flv", ".wmv",
            ".m3u8", ".mpd", ".ts", ".3gp", ".m4v", ".f4v", ".ogv", ".m4s"
        })
        audio_extensions: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            ".mp3", ".m4a", ".aac", ".flac", ".ogg", ".opus", ".wav",
            ".weba", ".alac", ".aiff", ".wma"
        })
        image_extensions: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            ".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp", ".svg",
            ".avif", ".heic", ".heif", ".tiff"
        })
        junk_extensions: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            ".js", ".css", ".json", ".html", ".woff", ".woff2", ".ttf", ".map", ".vtt", ".srt"
        })

        video_prefixes: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {"video/"})
        audio_prefixes: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {"audio/"})
        image_prefixes: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {"image/"})
        hls_types: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "application/x-mpegurl", "application/vnd.apple.mpegurl"
        })
        dash_types: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "application/dash+xml", "application/vnd.mpeg.dash.mpd", "application/xml", "text/xml"
        })

        deny_content_substrings: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {"javascript", "css", "font/"})
        deny_resource_types: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {"stylesheet", "font"})

        video_stream_hints: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            ".m3u8", "manifest.mpd", "master.m3u8", "chunklist.m3u8",
            "videoplayback", "dash", "hls", "stream", "cdn",
            "seg-", "segment", "/seg/", "/segments/", "m4s"
        })
        audio_stream_hints: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "audio", "sound", "stream", ".mp3", ".m4a", ".aac",
            ".flac", ".ogg", ".opus", "weba"
        })

        ad_host_substrings: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "doubleclick", "googlesyndication", "adservice", "adserver",
            "adsystem", "adnxs", "tracking", "analytics", "metrics",
            "scorecardresearch", "pixel.", "trk.", "stats.", "ad."
        })
        ad_path_keywords: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "/ads/", "/adserver/", "/banner/", "/promo/", "/tracking/",
            "/click/", "/impression", "/pixel", "/sponsor/", "/advert/"
        })

        enable_json_sniff: bool = True
        json_url_hints: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "player", "manifest", "api", "metadata", "m3u8", "mpd",
            "playlist", "video", "audio", "graphql"
        })
        json_content_types: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "application/json", "text/json", "application/problem+json",
            "application/ld+json", "application/vnd.api+json"
        })
        json_loose_body_sniff: bool = True
        json_loose_max_kb: int = 384  # allow a bit more than 256 if you want
        json_accept_any_app_json: bool = True
        json_url_suffixes: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {".json"})
        json_url_patterns: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "/api/", "metadata", "manifest", "playlist", "player", "graphql"
        })
        json_body_max_kb: int = 256

        enable_graphql_sniff: bool = True
        graphql_endpoint_keywords: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {"/graphql"})
        graphql_max_body_kb: int = 256

        enable_header_url_mining: bool = True
        max_header_url_events: int = 250
        header_url_keys: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "location", "link", "content-location", "refresh"
        })

        enable_redirect_tracking: bool = True
        max_redirect_events: int = 200

        max_manifest_bytes: int = 512 * 1024
        prefer_master_manifests: bool = True

        enable_segment_heuristics: bool = True
        min_segment_bytes: int = 64 * 1024
        max_segment_bytes: int = 50 * 1024 * 1024
        accept_range_requests_as_media: bool = True

        enable_forensics: bool = True
        max_forensics_events: int = 250
        forensics_body_prefix_bytes: int = 8192
        forensics_hash_via_probe: bool = True
        forensics_probe_timeout_ms: int = 6000
        forensics_include_headers_subset: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "content-type", "content-length", "content-range", "accept-ranges",
            "etag", "last-modified", "cache-control", "expires",
            "server", "via", "x-cache", "cf-cache-status", "age",
            "location", "content-disposition",
        })
        forensics_include_request_headers_subset: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "referer", "origin", "range", "user-agent", "accept", "accept-language",
        })

        # ---------------- URL salvage ----------------
        enable_url_salvage: bool = True
        salvage_max_targets_total: int = 30
        salvage_max_targets_per_host: int = 8
        salvage_only_if_mediaish: bool = True
        salvage_only_if_suspect: bool = True
        salvage_suspect_statuses: "NetworkSniffer.Set[int]" = field(default_factory=lambda: {401, 403, 404, 410, 416, 429})
        salvage_min_score_to_probe: float = 2.0
        salvage_score_bonus_if_signed: float = 2.0
        salvage_score_bonus_if_mediaish: float = 1.0
        salvage_score_bonus_if_segmenty: float = 0.5
        salvage_probe_timeout_ms: int = 6500
        salvage_probe_concurrency: int = 6
        salvage_range_bytes: int = 8192
        salvage_log_level: str = "ok"  # "none" | "ok" | "all"
        salvage_record_non_200: bool = False
        salvage_emit_only_ok_variants_in_bundle: bool = True
        salvage_max_variants_per_url: int = 10
        salvage_max_query_simplify_variants: int = 4
        salvage_max_host_swap_variants: int = 6
        salvage_strip_query_keys_substrings: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "token", "expires", "exp", "sig", "signature", "policy", "key-pair-id",
            "x-amz-", "x-goog-", "x-ms-", "hdnts", "acl", "hmac",
            "cdn_hash", "hash", "auth", "authorization", "session",
        })
        salvage_origin_swaps: "NetworkSniffer.Dict[str, NetworkSniffer.Set[str]]" = field(default_factory=lambda: {
            "cf-hls-media.sndcdn.com": {"cf-media.sndcdn.com", "hls-media.sndcdn.com"},
            "media.sndcdn.com": {"cf-media.sndcdn.com"},
            "i1.sndcdn.com": {"i2.sndcdn.com", "i3.sndcdn.com", "i4.sndcdn.com"},
            "lh3.googleusercontent.com": {"lh4.googleusercontent.com", "lh5.googleusercontent.com", "lh6.googleusercontent.com"},
        })

        # ---------------- MSE sniff ----------------
        enable_mse_sniff: bool = True
        mse_max_events: int = 250
        mse_flush_interval_ms: int = 250
        mse_max_url_len: int = 2048
        mse_prefix_hex_bytes: int = 32
        mse_capture_fetch: bool = True
        mse_capture_xhr: bool = True
        mse_capture_media_src_assign: bool = True
        mse_emit_each_event_json: bool = False
        mse_mediaish_url_hints: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            ".m4s", ".mp4", ".ts", ".aac", ".m3u8", ".mpd", "dash", "hls", "segment", "seg", "chunk", "frag", "bytestream"
        })

        # ---------------- Binary Signature Sniffing ----------------
        enable_binary_signature_sniff: bool = True
        binary_sniff_only_if_unknown_kind: bool = True
        binary_sniff_prefix_bytes: int = 4096
        binary_sniff_timeout_ms: int = 6000
        binary_sniff_concurrency: int = 8
        binary_sniff_max_tasks: int = 80
        binary_suspect_extensions: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            ".php", ".bin", ".cgi", ".asp", ".aspx", ".jsp", ".do", ".action"
        })
        binary_suspect_content_types: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "application/octet-stream", "binary/octet-stream", "application/download", "application/x-download"
        })
        binary_sniff_url_hints: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "download", "media", "stream", "video", "audio", "file", "blob", "segment", "chunk"
        })

        # ---------------- NEW: Param Sniffer ----------------
        enable_param_sniff: bool = True
        param_max_events: int = 600
        param_max_queue: int = 2000
        param_flush_interval_ms: int = 250
        param_max_url_len: int = 2048
        param_max_key_len: int = 128
        param_max_val_len: int = 256
        param_capture_values: bool = False   # default FALSE (privacy)
        param_sample_rate: float = 1.0

        # ---------------- NEW: Bundle static scan (optional) ----------------
        enable_bundle_param_scan: bool = True
        bundle_scan_max_scripts: int = 15
        bundle_scan_range_bytes: int = 256 * 1024
        bundle_scan_timeout_ms: int = 7000
        bundle_scan_max_regex_hits: int = 250

        # ---------------- NEW: Correlation window ----------------
        correlate_window_ms: int = 1500
        correlate_max_per_key: int = 8

        # ---------------- Stronger candidate promotion ----------------
        enable_candidate_promotion: bool = True
        max_promoted_candidates: int = 120
        min_candidate_score: float = 2.5
        promote_probe_timeout_ms: int = 4500
        promote_probe_concurrency: int = 6
        promote_json_media_urls: bool = True
        promote_json_structured_candidates: bool = True
        promote_mse_candidates: bool = True
        promote_param_correlation: bool = True
        promote_bundle_scan_candidates: bool = True
        require_probe_for_weak_candidates: bool = False

    # ---------------------------- init ---------------------------- #
    def __init__(self, config: Optional["NetworkSniffer.Config"] = None, logger=None, http=None):
        self.cfg = config or self.Config()
        self.logger = logger if logger is not None else (globals().get("DEBUG_LOGGER", None) or self._FallbackLogger())
        self.http = http  # optional HTTPSSubmanager-like engine
        self._log("[NetworkSniffer] Initialized (ParamSniff + BundleScan + Correlate + MSE + BinarySig + Salvage) [hard str-safe]", None)
        try:
            self.cfg.video_stream_hints.add("cf-hls-media.sndcdn.com")
            self.cfg.audio_stream_hints.add(".m3u8")
        except Exception:
            pass

    # ---------------------------- logging ---------------------------- #
    def _log(self, msg: Any, log_list: Optional["NetworkSniffer.List[str]"]) -> None:
        s = self._to_str(msg)
        try:
            if log_list is not None:
                log_list.append(s)
            if self.logger is not None:
                self.logger.log_message(s)
        except Exception:
            pass

    # ---------------------------- helpers ---------------------------- #
    def _extract_urls_from_text(self, s: Any) -> "NetworkSniffer.List[str]":
        s = self._to_str(s)
        if not s:
            return []
        rx = self.re.compile(r"\b(?:https?|wss?)://[^\s\"'<>]+", self.re.IGNORECASE)
        out: "NetworkSniffer.List[str]" = []
        seen: "NetworkSniffer.Set[str]" = set()
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

    def _classify_by_extension(self, path: str) -> "NetworkSniffer.Optional[str]":
        p = (path or "").lower()
        if any(p.endswith(ext) for ext in self.cfg.video_extensions):
            return "video"
        if any(p.endswith(ext) for ext in self.cfg.audio_extensions):
            return "audio"
        if any(p.endswith(ext) for ext in self.cfg.image_extensions):
            return "image"
        return None

    def _classify_by_content_type(self, ctype: str) -> "NetworkSniffer.Optional[str]":
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

    def _classify_by_stream_hint(self, url_lower: str) -> "NetworkSniffer.Optional[str]":
        if any(h in url_lower for h in self.cfg.video_stream_hints):
            return "video"
        if any(h in url_lower for h in self.cfg.audio_stream_hints):
            return "audio"
        return None

    def _matches_json_pattern(self, url_lower: str) -> bool:
        return any(pat in url_lower for pat in self.cfg.json_url_patterns)

    def _should_sniff_json(self, url_lower: str, ctype: str, content_length: "NetworkSniffer.Optional[int]") -> bool:
        if not self.cfg.enable_json_sniff:
            return False

        ct = (ctype or "").lower().split(";")[0].strip()

        # Size gate (use loose max if enabled)
        if content_length is None:
            return False
        max_bytes = int((self.cfg.json_loose_max_kb if getattr(self.cfg, "json_loose_body_sniff",
                                                               True) else self.cfg.json_body_max_kb)) * 1024
        if content_length > max_bytes:
            return False

        # Fast accept: any application/json-like
        if getattr(self.cfg, "json_accept_any_app_json", True):
            if ct in (self.cfg.json_content_types or set()):
                return True

        # Otherwise score signals
        score = 0.0

        # hinty content-type
        if "json" in ct:
            score += 2.0

        # URL hints
        if any(h in url_lower for h in (self.cfg.json_url_hints or set())):
            score += 1.5
        if any(pat in url_lower for pat in (self.cfg.json_url_patterns or set())):
            score += 2.0
        if any(url_lower.endswith(suf) for suf in (getattr(self.cfg, "json_url_suffixes", {".json"}) or set())):
            score += 1.0

        # If it *might* carry media metadata
        if any(h in url_lower for h in ("pixabay", "video", "videos", "media", "asset", "cdn")):
            score += 1.0

        return score >= 2.0

    def _iter_urls_in_json(self, obj: "NetworkSniffer.Any", *, limit: int = 2500):
        """
        Yield string values that look like URLs from a nested JSON structure.
        Hard limits to avoid huge recursion.
        """
        seen = 0
        stack = [obj]
        while stack and seen < limit:
            cur = stack.pop()
            if cur is None:
                continue
            if isinstance(cur, str):
                s = cur.strip()
                if s.startswith(("http://", "https://", "wss://", "ws://")):
                    yield s
                    seen += 1
                continue
            if isinstance(cur, dict):
                for v in cur.values():
                    stack.append(v)
                continue
            if isinstance(cur, (list, tuple)):
                for v in cur:
                    stack.append(v)
                continue

    def _emit_media_url(self, url: str, *, tag: str, kind_hint: "NetworkSniffer.Optional[str]",
                        found_items: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]",
                        seen_network: "NetworkSniffer.Set[str]",
                        max_items: int):
        cu = self._canonicalize_url(url)
        if not cu or cu in seen_network:
            return
        if not self._host_allowed(cu):
            return

        ul = cu.lower()
        p = self._safe_urlparse(cu)
        path = self._to_str(p.path).lower()

        kind = (
                self._classify_by_extension(path)
                or self._classify_by_stream_hint(ul)
                or kind_hint
        )
        if kind not in ("video", "audio", "image"):
            return

        if len(found_items) < max_items:
            found_items.append({
                "url": cu,
                "text": f"[JSON→URL {kind.capitalize()}]",
                "tag": tag,
                "kind": kind,
                "content_type": "?",
                "size": "?",
            })
        seen_network.add(cu)

    def _looks_like_graphql_endpoint(self, url_lower: str) -> bool:
        return any(k in url_lower for k in self.cfg.graphql_endpoint_keywords)

    def _is_allowed_by_extensions(self, url: str, extensions: "NetworkSniffer.Optional[NetworkSniffer.Set[str]]", kind: "NetworkSniffer.Optional[str]") -> bool:
        if not extensions:
            return True
        parsed = self._safe_urlparse(url)
        path = self._to_str(parsed.path).lower()
        if any(path.endswith(ext.lower()) for ext in extensions):
            return True
        if self.cfg.accept_unknown_streams and kind in ("video", "audio"):
            return True
        return False

    def _is_manifest(self, url: str, ctype: str) -> "NetworkSniffer.Optional[str]":
        ul = (url or "").lower()
        ct = (ctype or "").lower()
        if ul.endswith(".m3u8") or ct in self.cfg.hls_types:
            return "hls"
        if ul.endswith(".mpd") or ct in self.cfg.dash_types:
            return "dash"
        return None

    def _looks_like_segment(self, url_lower: str, ctype: str, content_length: "NetworkSniffer.Optional[int]", headers: "NetworkSniffer.Dict[str, str]") -> "NetworkSniffer.Optional[str]":
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

    def _parse_hls_manifest(self, manifest_text: Any, base_url: str) -> "NetworkSniffer.List[str]":
        txt = self._to_str(manifest_text)
        out: "NetworkSniffer.List[str]" = []
        seen: "NetworkSniffer.Set[str]" = set()
        for m in self._HLS_LINE_RE.finditer(txt or ""):
            line = (m.group(1) or "").strip()
            if not line:
                continue
            full = self._canonicalize_url(self._safe_urljoin(base_url, line))
            if full and full not in seen:
                seen.add(full)
                out.append(full)
        return out

    def _parse_mpd_manifest(self, manifest_text: Any, base_url: str) -> "NetworkSniffer.List[str]":
        txt = self._to_str(manifest_text)
        out: "NetworkSniffer.List[str]" = []
        seen: "NetworkSniffer.Set[str]" = set()

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

    async def _expand_manifest(self, response, manifest_kind: str, url: str, log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]") -> "NetworkSniffer.List[str]":
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
    async def _auto_scroll(self, page, tmo: float, log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]") -> None:
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
    def _normalize_item(self, it: "NetworkSniffer.Dict[str, Any]") -> "NetworkSniffer.Dict[str, str]":
        return {
            "url": self._to_str(it.get("url")),
            "text": self._to_str(it.get("text")),
            "tag": self._to_str(it.get("tag") or "network_sniff"),
            "kind": self._to_str(it.get("kind") or "unknown"),
            "content_type": self._to_str(it.get("content_type") or "?"),
            "size": self._to_str(it.get("size") or "?"),
            "score": self._to_str(it.get("score") if it.get("score") is not None else ""),
            "confidence": self._to_str(it.get("confidence") or ""),
            "evidence": self._to_str(it.get("evidence") or ""),
        }

    # ============================== URL salvage (unchanged core) ============================== #
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
        if kl in ("sig", "signature", "token", "auth", "authorization", "expires", "exp", "policy"):
            return True
        if kl.startswith(("x-amz-", "x-goog-", "x-ms-")):
            return True
        return False

    def _signaturey_value(self, v: str) -> bool:
        vv = (v or "").strip()
        if not vv:
            return False
        if vv.isdigit() and len(vv) in (10, 13):
            return True
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

    def _build_query_variants(self, url: str) -> "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]":
        out: "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]" = []
        try:
            p = self._safe_urlparse(url)
            if not p.scheme or not p.netloc:
                return out

            pairs = self._safe_parse_qsl(p.query)
            if not pairs:
                return out

            kept1: "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]" = []
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

            kept2: "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]" = []
            for k, v in pairs:
                ks = self._to_str(k)
                vs = self._to_str(v)
                if len(ks) <= 16 and len(vs) <= 64 and not self._signaturey_key(ks) and not self._signaturey_value(vs):
                    kept2.append((ks, vs))
            if kept2 and kept2 != pairs:
                q2 = self._safe_urlencode(kept2)
                u2 = self._safe_urlunparse((p.scheme, p.netloc, p.path, p.params, q2, ""))
                out.append((u2, "query_keep_simple"))

            u3 = self._safe_urlunparse((p.scheme, p.netloc, p.path, p.params, "", ""))
            out.append((u3, "path_only"))
        except Exception:
            pass

        seen: "NetworkSniffer.Set[str]" = set()
        uniq: "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]" = []
        for u, k in out:
            cu = self._canonicalize_url(u)
            if not cu or cu in seen:
                continue
            seen.add(cu)
            uniq.append((cu, k))
            if len(uniq) >= int(self.cfg.salvage_max_query_simplify_variants):
                break
        return uniq

    def _programmatic_host_swaps(self, host: str) -> "NetworkSniffer.Set[str]":
        h = (host or "").strip().lower()
        if not h:
            return set()

        out: "NetworkSniffer.Set[str]" = set()

        m = self.re.match(r"^(i)(\d+)\.(.+)$", h)
        if m:
            base = m.group(1)
            n = int(m.group(2))
            rest = m.group(3)
            for nn in range(max(1, n - 1), min(9, n + 4) + 1):
                if nn != n:
                    out.add(f"{base}{nn}.{rest}")

        if h.startswith("cf-"):
            out.add(h[len("cf-"):])
        else:
            out.add("cf-" + h)

        if h.startswith("cdn."):
            out.add(h[len("cdn."):])
        else:
            out.add("cdn." + h)

        return {x for x in out if x and x != h}

    def _origin_swap_variants(self, url: str) -> "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]":
        out: "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]" = []
        try:
            p = self._safe_urlparse(url)
            host = self._to_str(p.netloc).lower()
            if not host:
                return out

            for ah in (self.cfg.salvage_origin_swaps.get(host) or set()):
                ahs = self._to_str(ah).strip().lower()
                if ahs and ahs != host:
                    out.append((self._safe_urlunparse((p.scheme, ahs, p.path, p.params, p.query, p.fragment)), "origin_swap_static"))

            for ahs in self._programmatic_host_swaps(host):
                out.append((self._safe_urlunparse((p.scheme, ahs, p.path, p.params, p.query, p.fragment)), "origin_swap_rule"))
        except Exception:
            pass

        seen: "NetworkSniffer.Set[str]" = set()
        uniq: "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]" = []
        for u, k in out:
            cu = self._canonicalize_url(u)
            if not cu or cu in seen:
                continue
            seen.add(cu)
            uniq.append((cu, k))
            if len(uniq) >= int(self.cfg.salvage_max_host_swap_variants):
                break
        return uniq

    def _salvage_score(self, url: str, *, status: "NetworkSniffer.Optional[int]", kind: "NetworkSniffer.Optional[str]") -> float:
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

    def _salvage_should_target(self, url: str, *, status: "NetworkSniffer.Optional[int]", kind: "NetworkSniffer.Optional[str]") -> bool:
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

    def _salvage_log(self, msg: str, log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]", *, level: str):
        lvl = (self.cfg.salvage_log_level or "ok").lower()
        if lvl == "none":
            return
        if lvl == "ok" and level != "ok":
            return
        self._log(msg, log)

    async def _probe_url(self, api_ctx, url: str, req_headers: "NetworkSniffer.Dict[str, str]", *, timeout_ms: int) -> "NetworkSniffer.Dict[str, Any]":
        url = self._to_str(url)
        result = {
            "url": url, "ok": False, "status": None, "final_url": url,
            "content_type": None, "content_length": None, "hash_prefix_sha256": None,
            "method": None, "error": "",
        }

        # --- Engine path ---
        if self.http:
            try:
                status, hdrs = await self.http.head(url)
                result.update({
                    "method": "ENGINE_HEAD+PREFIX_GET",
                    "status": status,
                    "content_type": hdrs.get("Content-Type") or hdrs.get("content-type"),
                    "content_length": hdrs.get("Content-Length") or hdrs.get("content-length")
                })
                prefix = await self.http.get_prefix(url, size=int(self.cfg.salvage_range_bytes), timeout_ms=timeout_ms)
                if prefix:
                    result["hash_prefix_sha256"] = self.hashlib.sha256(prefix).hexdigest()
                if status and 200 <= status < 300:
                    result["ok"] = True
                return result
            except Exception as e:
                self._log(f"[NetworkSniffer] Engine probe failed, trying fallback: {e}", None)

        # --- Playwright fallback ---
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
                result["hash_prefix_sha256"] = self.hashlib.sha256(b[: int(self.cfg.salvage_range_bytes)]).hexdigest()
            if result["status"] in (200, 206):
                result["ok"] = True
        except Exception as e:
            result["error"] = f"pw_fallback_failed:{e}"

        return result

    async def _salvage_one(self, api_ctx, observed_url: str, req_headers_subset: "NetworkSniffer.Dict[str, str]", *,
                          log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]", observed_status: "NetworkSniffer.Optional[int]", observed_kind: "NetworkSniffer.Optional[str]") -> "NetworkSniffer.Dict[str, Any]":
        observed = self._canonicalize_url(observed_url)
        if not observed:
            return {"observed_url": self._to_str(observed_url), "variants": [], "ok_variants": []}

        variants: "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]" = []
        variants.extend(self._build_query_variants(observed))
        variants.extend(self._origin_swap_variants(observed))

        for (u, k) in list(variants)[:3]:
            for (u2, k2) in self._origin_swap_variants(u):
                variants.append((u2, f"{k}+{k2}"))

        seen: "NetworkSniffer.Set[str]" = {observed}
        uniq: "NetworkSniffer.List[NetworkSniffer.Tuple[str, str]]" = []
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

        out_variants: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        ok_variants: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        tmo = int(self.cfg.salvage_probe_timeout_ms)

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
                break
            else:
                if self.cfg.salvage_record_non_200:
                    self._salvage_log(
                        f"[NetworkSniffer] Salvage miss: {observed} -> {u} ({pr.get('status')})",
                        log, level="all"
                    )

        variants_emit = ok_variants if self.cfg.salvage_emit_only_ok_variants_in_bundle else out_variants
        return {"observed_url": observed, "variants": variants_emit, "ok_variants": ok_variants}

    # ============================== forensics helpers ============================== #
    def _pick_headers_subset(self, headers_lc: "NetworkSniffer.Dict[str, str]", allow: "NetworkSniffer.Set[str]") -> "NetworkSniffer.Dict[str, str]":
        out: "NetworkSniffer.Dict[str, str]" = {}
        for k in (allow or set()):
            kk = self._to_str(k).lower()
            v = headers_lc.get(kk)
            if v:
                out[kk] = self._to_str(v)
        return out

    def _hash_post_data(self, post_data: Any, max_bytes: int = 4096) -> "NetworkSniffer.Dict[str, Any]":
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

    async def _hash_body_prefix_via_probe(self, api_ctx, url: str, req_headers_subset: "NetworkSniffer.Dict[str, str]", *,
                                          timeout_ms: int, prefix_bytes: int) -> "NetworkSniffer.Optional[str]":
        if self.http:
            try:
                prefix = await self.http.get_prefix(self._to_str(url), size=int(prefix_bytes), timeout_ms=timeout_ms)
                return self.hashlib.sha256(prefix).hexdigest() if prefix else None
            except Exception:
                pass

        if api_ctx is None:
            return None
        try:
            h = {self._to_str(k): self._to_str(v) for k, v in (req_headers_subset or {}).items() if k and v}
            h["Range"] = f"bytes=0-{max(0, int(prefix_bytes) - 1)}"
            resp = await api_ctx.get(self._to_str(url), headers=h, timeout=timeout_ms)
            b = await resp.body()
            return self.hashlib.sha256(b[:prefix_bytes]).hexdigest() if b else None
        except Exception:
            return None

    # ============================== Binary signature sniffing ============================== #
    def _ext_of(self, url: str) -> str:
        try:
            p = self._safe_urlparse(url)
            path = self._to_str(p.path).lower()
            i = path.rfind(".")
            if i == -1:
                return ""
            ext = path[i:]
            if len(ext) > 10:
                return ""
            return ext
        except Exception:
            return ""

    def _is_binary_suspect(self, url: str, *, ctype: str, resource_type: str, content_length: "NetworkSniffer.Optional[int]") -> bool:
        if not self.cfg.enable_binary_signature_sniff:
            return False
        if not self._host_allowed(url):
            return False
        if url.startswith("blob:"):
            return False

        ul = (url or "").lower()
        ext = self._ext_of(url)

        suspect_ext = (ext in (self.cfg.binary_suspect_extensions or set())) or (ext == "")
        hinty_url = any(h in ul for h in (self.cfg.binary_sniff_url_hints or set()))

        ct = (ctype or "").lower().split(";")[0].strip()
        suspect_ct = ct in (self.cfg.binary_suspect_content_types or set())

        if content_length is not None and content_length < 2048 and not (suspect_ext and hinty_url):
            return False

        if "text/html" in ct and not hinty_url:
            return False

        if self._deny_by_resource_type(resource_type):
            return False

        return bool(suspect_ext or suspect_ct or hinty_url)

    async def _get_prefix_bytes(self, api_ctx, url: str, req_headers_subset: "NetworkSniffer.Dict[str, str]", *,
                               timeout_ms: int, prefix_bytes: int) -> "NetworkSniffer.Optional[bytes]":
        url = self._to_str(url)
        if self.http:
            try:
                b = await self.http.get_prefix(url, size=int(prefix_bytes), timeout_ms=timeout_ms)
                return bytes(b) if b else None
            except Exception:
                pass

        if api_ctx is None:
            return None
        try:
            h = {self._to_str(k): self._to_str(v) for k, v in (req_headers_subset or {}).items() if k and v}
            h["Range"] = f"bytes=0-{max(0, int(prefix_bytes) - 1)}"
            resp = await api_ctx.get(url, headers=h, timeout=timeout_ms)
            b = await resp.body()
            return bytes(b) if b else None
        except Exception:
            return None

    def _guess_kind_from_magic(self, b: "NetworkSniffer.Optional[bytes]") -> "NetworkSniffer.Tuple[NetworkSniffer.Optional[str], NetworkSniffer.Optional[str], str]":
        if not b:
            return None, None, "no_bytes"

        bb = bytes(b[: max(64, min(len(b), 4096))])

        # images
        if bb.startswith(b"\x89PNG\r\n\x1a\n"):
            return "image", "image/png", "magic:png"
        if bb[:3] == b"\xFF\xD8\xFF":
            return "image", "image/jpeg", "magic:jpg"
        if bb.startswith(b"GIF87a") or bb.startswith(b"GIF89a"):
            return "image", "image/gif", "magic:gif"
        if bb.startswith(b"RIFF") and b"WEBP" in bb[8:16]:
            return "image", "image/webp", "magic:webp"

        # mp4/fmp4 or early moof/mdat
        if len(bb) >= 12 and bb[4:8] == b"ftyp":
            return "video", "video/mp4", "magic:mp4_ftyp"
        if b"moof" in bb[:64] or b"mdat" in bb[:64]:
            return "video", "video/mp4", "magic:mp4_moof_mdat"

        # MPEG-TS
        if bb and bb[0] == 0x47:
            return "video", "video/mp2t", "magic:mpegts"

        # EBML (webm/mkv)
        if bb.startswith(b"\x1A\x45\xDF\xA3"):
            return "video", "video/webm", "magic:ebml_webm"

        # audio
        if bb.startswith(b"ID3"):
            return "audio", "audio/mpeg", "magic:mp3_id3"
        if len(bb) >= 2 and bb[0] == 0xFF and (bb[1] & 0xE0) == 0xE0:
            return "audio", "audio/mpeg", "magic:mp3_framesync"
        if len(bb) >= 2 and bb[0] == 0xFF and (bb[1] & 0xF6) == 0xF0:
            return "audio", "audio/aac", "magic:aac_adts"
        if bb.startswith(b"OggS"):
            return "audio", "audio/ogg", "magic:ogg"
        if bb.startswith(b"fLaC"):
            return "audio", "audio/flac", "magic:flac"
        if bb.startswith(b"RIFF") and b"WAVE" in bb[8:16]:
            return "audio", "audio/wav", "magic:wav"

        return None, None, "magic:unknown"

    # ============================== MSE sniff bridge ============================== #
    def _mse_init_script(self, cfg: "NetworkSniffer.Dict[str, Any]") -> str:
        safe_cfg = {
            "maxQueue": int(cfg.get("maxQueue", 2000)),
            "maxUrlLen": int(cfg.get("maxUrlLen", 2048)),
            "prefixHexBytes": int(cfg.get("prefixHexBytes", 32)),
            "flushIntervalMs": int(cfg.get("flushIntervalMs", 250)),
            "captureFetch": bool(cfg.get("captureFetch", True)),
            "captureXHR": bool(cfg.get("captureXHR", True)),
            "captureMediaSrcAssign": bool(cfg.get("captureMediaSrcAssign", True)),
            "mediaishHints": list(cfg.get("mediaishHints", [])),
        }
        cfg_json = self.json.dumps(safe_cfg)
        return f"""
(() => {{
  try {{
    const NS = (window.__NS_MSE = window.__NS_MSE || {{}});
    if (NS.__installed) return;
    NS.__installed = true;

    const DEFAULTS = {{
      maxQueue: 2000,
      maxUrlLen: 2048,
      prefixHexBytes: 32,
      flushIntervalMs: 250,
      captureFetch: true,
      captureXHR: true,
      captureMediaSrcAssign: true,
      mediaishHints: [
        ".m4s",".mp4",".ts",".aac",".m3u8",".mpd","dash","hls","segment","seg","chunk","frag","bytestream"
      ]
    }};

    const EMBEDDED = {cfg_json};
    NS.cfg = Object.assign(DEFAULTS, (NS.cfg || {{}}), (EMBEDDED || {{}}));
    NS.q = NS.q || [];
    NS.stats = NS.stats || {{dropped:0, pushed:0, flushed:0, errs:0}};

    function nowMs(){{ return Date.now(); }}
    function trunc(s, n){{ s = (s == null ? "" : String(s)); return s.length > n ? s.slice(0, n) : s; }}
    function safeUrl(u){{ return trunc(u, NS.cfg.maxUrlLen); }}

    function isMediaishUrl(u){{
      try {{
        const s = String(u || "").toLowerCase();
        for (const h of (NS.cfg.mediaishHints||[])) {{ if (s.includes(h)) return true; }}
        return false;
      }} catch(e) {{ return false; }}
    }}

    function hexPrefixFromU8(u8, maxBytes){{
      try {{
        const n = Math.min(u8.byteLength || 0, maxBytes|0);
        let out = "";
        for (let i=0;i<n;i++) {{
          const b = u8[i] & 0xFF;
          out += (b<16 ? "0" : "") + b.toString(16);
        }}
        return out;
      }} catch(e) {{ return ""; }}
    }}

    function pushEvt(evt){{
      try {{
        if (!evt || typeof evt !== "object") return;
        evt.ts = evt.ts || nowMs();
        if (evt.url) evt.url = safeUrl(evt.url);
        if (NS.q.length >= (NS.cfg.maxQueue|0)) {{
          NS.q.shift();
          NS.stats.dropped++;
        }}
        NS.q.push(evt);
        NS.stats.pushed++;
      }} catch(e) {{
        NS.stats.errs++;
      }}
    }}

    function flush(){{
      try {{
        const fn = window.__ns_mse_push;
        if (typeof fn !== "function") return;
        if (!NS.q.length) return;
        const batch = NS.q.splice(0, 100);
        NS.stats.flushed += batch.length;
        fn(batch);
      }} catch(e) {{
        NS.stats.errs++;
      }}
    }}

    setInterval(flush, Math.max(50, NS.cfg.flushIntervalMs|0));

    const MS = window.MediaSource;
    if (MS && MS.prototype) {{
      const origAddSB = MS.prototype.addSourceBuffer;
      if (typeof origAddSB === "function") {{
        MS.prototype.addSourceBuffer = function(mime){{
          const msId = (this.__ns_ms_id = this.__ns_ms_id || ("ms_" + Math.random().toString(16).slice(2)));
          pushEvt({{event:"mse_addSourceBuffer", ms_id: msId, mime: trunc(mime, 200)}});
          const sb = origAddSB.apply(this, arguments);

          try {{
            if (sb && !sb.__ns_wrapped) {{
              sb.__ns_wrapped = true;
              sb.__ns_mime = trunc(mime, 200);
              const origAppend = sb.appendBuffer;

              if (typeof origAppend === "function") {{
                sb.appendBuffer = function(buf){{
                  try {{
                    const u8 = buf instanceof ArrayBuffer ? new Uint8Array(buf) :
                              (ArrayBuffer.isView(buf) ? new Uint8Array(buf.buffer, buf.byteOffset, buf.byteLength) : null);
                    const byteLen = u8 ? (u8.byteLength||0) : (buf && buf.byteLength ? buf.byteLength : null);
                    const hex = u8 ? hexPrefixFromU8(u8, NS.cfg.prefixHexBytes|0) : "";
                    pushEvt({{
                      event:"mse_appendBuffer",
                      ms_id: msId,
                      mime: sb.__ns_mime || "",
                      byteLength: byteLen,
                      prefix_hex: hex
                    }});
                  }} catch(e) {{}}
                  return origAppend.apply(this, arguments);
                }};
              }}
            }}
          }} catch(e) {{}}

          return sb;
        }};
      }}
    }}

    try {{
      const origCreate = URL.createObjectURL;
      if (typeof origCreate === "function") {{
        URL.createObjectURL = function(obj){{
          const out = origCreate.apply(this, arguments);
          try {{
            if (obj && window.MediaSource && obj instanceof window.MediaSource) {{
              const msId = (obj.__ns_ms_id = obj.__ns_ms_id || ("ms_" + Math.random().toString(16).slice(2)));
              pushEvt({{event:"mse_createObjectURL", ms_id: msId, blob_url: safeUrl(out)}});
            }}
          }} catch(e) {{}}
          return out;
        }};
      }}
    }} catch(e) {{}}

    if (NS.cfg.captureMediaSrcAssign) {{
      try {{
        const proto = HTMLMediaElement && HTMLMediaElement.prototype;
        if (proto) {{
          const desc = Object.getOwnPropertyDescriptor(proto, "src");
          if (desc && desc.set) {{
            Object.defineProperty(proto, "src", {{
              get: desc.get,
              set: function(v){{
                try {{
                  const s = String(v||"");
                  if (s.startsWith("blob:")) {{
                    pushEvt({{event:"media_src_set", tag:"prop", blob_url: safeUrl(s)}});
                  }}
                }} catch(e) {{}}
                return desc.set.call(this, v);
              }}
            }});
          }}

          const origSetAttr = Element.prototype.setAttribute;
          Element.prototype.setAttribute = function(k, v){{
            try {{
              if (this && (this instanceof HTMLMediaElement) && String(k||"").toLowerCase() === "src") {{
                const s = String(v||"");
                if (s.startsWith("blob:")) pushEvt({{event:"media_src_set", tag:"attr", blob_url: safeUrl(s)}});
              }}
            }} catch(e) {{}}
            return origSetAttr.apply(this, arguments);
          }};
        }}
      }} catch(e) {{}}
    }}

    if (NS.cfg.captureFetch && typeof window.fetch === "function") {{
      const origFetch = window.fetch;
      window.fetch = async function(input, init){{
        const url = (typeof input === "string" ? input : (input && input.url ? input.url : ""));
        const u = safeUrl(url);
        const mediaish = isMediaishUrl(u);

        try {{
          const resp = await origFetch.apply(this, arguments);
          try {{
            if (mediaish) {{
              const ct = resp && resp.headers ? resp.headers.get("content-type") : null;
              const cl = resp && resp.headers ? resp.headers.get("content-length") : null;
              pushEvt({{event:"fetch_resp", url:u, status: resp ? resp.status : null, content_type: trunc(ct,120), content_length: trunc(cl,30)}});
            }}
          }} catch(e) {{}}
          return resp;
        }} catch(e) {{
          try {{
            if (mediaish) pushEvt({{event:"fetch_err", url:u, error: trunc(e && e.message ? e.message : String(e), 200)}});
          }} catch(_e) {{}}
          throw e;
        }}
      }};
    }}

    if (NS.cfg.captureXHR && window.XMLHttpRequest) {{
      const X = window.XMLHttpRequest;
      const origOpen = X.prototype.open;
      const origSend = X.prototype.send;

      X.prototype.open = function(method, url){{
        try {{
          this.__ns_xhr_url = safeUrl(url);
          this.__ns_xhr_method = trunc(method, 16);
        }} catch(e) {{}}
        return origOpen.apply(this, arguments);
      }};

      X.prototype.send = function(body){{
        try {{
          const u = this.__ns_xhr_url || "";
          const mediaish = isMediaishUrl(u);
          if (mediaish) {{
            const self = this;
            const onLoad = function(){{
              try {{
                const ct = self.getResponseHeader ? self.getResponseHeader("content-type") : null;
                const cl = self.getResponseHeader ? self.getResponseHeader("content-length") : null;
                pushEvt({{event:"xhr_resp", url:u, status: self.status, content_type: trunc(ct,120), content_length: trunc(cl,30), responseType: trunc(self.responseType, 20)}});
              }} catch(e) {{}}
            }};
            self.addEventListener("load", onLoad);
            self.addEventListener("error", () => pushEvt({{event:"xhr_err", url:u}}));
          }}
        }} catch(e) {{}}
        return origSend.apply(this, arguments);
      }};
    }}

  }} catch (e) {{
    try {{ (window.__NS_MSE = window.__NS_MSE || {{}}).stats = {{errs:999}}; }} catch(_e) {{}}
  }}
}})();
"""

    async def _install_mse_bridge(self, page, mse_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]", *, log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]"):
        if not self.cfg.enable_mse_sniff:
            return

        max_events = int(self.cfg.mse_max_events)

        async def _binding(source, payload):
            try:
                if payload is None:
                    return
                batch = payload if isinstance(payload, list) else [payload]
                for ev in batch:
                    if len(mse_events) >= max_events:
                        return
                    if isinstance(ev, dict):
                        mse_events.append(ev)
                    else:
                        mse_events.append({"event": "mse_raw", "raw": self._to_str(ev)})
            except Exception as e:
                self._log(f"[NetworkSniffer][MSE] binding error: {e}", log)

        try:
            await page.expose_binding("__ns_mse_push", _binding)
        except Exception as e:
            self._log(f"[NetworkSniffer][MSE] expose_binding failed: {e}", log)
            return

        cfg = {
            "maxQueue": max(100, int(self.cfg.mse_max_events) * 8),
            "maxUrlLen": int(self.cfg.mse_max_url_len),
            "prefixHexBytes": int(self.cfg.mse_prefix_hex_bytes),
            "flushIntervalMs": int(self.cfg.mse_flush_interval_ms),
            "captureFetch": bool(self.cfg.mse_capture_fetch),
            "captureXHR": bool(self.cfg.mse_capture_xhr),
            "captureMediaSrcAssign": bool(self.cfg.mse_capture_media_src_assign),
            "mediaishHints": list(self.cfg.mse_mediaish_url_hints or []),
        }

        try:
            script = self._mse_init_script(cfg)
            await page.add_init_script(script=script)
        except TypeError:
            try:
                await page.add_init_script(script)
            except Exception as e:
                self._log(f"[NetworkSniffer][MSE] init_script failed: {e}", log)
        except Exception as e:
            self._log(f"[NetworkSniffer][MSE] init_script failed: {e}", log)

    # ============================== NEW: Param Sniffer bridge ============================== #
    def _param_init_script(self, cfg: "NetworkSniffer.Dict[str, Any]") -> str:
        # Use your exact patch, with cfg injected safely.
        safe_cfg = {
            "maxQueue": int(cfg.get("maxQueue", 2000)),
            "flushIntervalMs": int(cfg.get("flushIntervalMs", 250)),
            "maxUrlLen": int(cfg.get("maxUrlLen", 2048)),
            "maxKeyLen": int(cfg.get("maxKeyLen", 128)),
            "maxValLen": int(cfg.get("maxValLen", 256)),
            "captureValues": bool(cfg.get("captureValues", False)),
            "sampleRate": float(cfg.get("sampleRate", 1.0)),
        }
        cfg_json = self.json.dumps(safe_cfg)
        return f"""
(() => {{
  try {{
    const NS = (window.__NS_PARAMS = window.__NS_PARAMS || {{}});
    if (NS.__installed) return;
    NS.__installed = true;

    NS.q = NS.q || [];
    NS.stats = NS.stats || {{ dropped: 0, pushed: 0, flushed: 0, errs: 0 }};
    NS.cfg = Object.assign({{
      maxQueue: 2000,
      flushIntervalMs: 250,
      maxUrlLen: 2048,
      maxKeyLen: 128,
      maxValLen: 256,
      captureValues: false,
      sampleRate: 1.0
    }}, NS.cfg || {{}}, {cfg_json});

    function nowMs(){{ return Date.now(); }}
    function trunc(s,n){{ s = (s==null ? "" : String(s)); return s.length>n ? s.slice(0,n) : s; }}
    function safeUrl(u){{ return trunc(u, NS.cfg.maxUrlLen|0); }}
    function rand(){{ return Math.random(); }}

    function pushEvt(evt){{
      try{{
        if (!evt || typeof evt !== "object") return;
        if ((NS.cfg.sampleRate||1) < 1.0 && rand() > (NS.cfg.sampleRate||1)) return;
        evt.ts = evt.ts || nowMs();
        if (evt.url) evt.url = safeUrl(evt.url);
        if (evt.key) evt.key = trunc(evt.key, NS.cfg.maxKeyLen|0);
        if (evt.value && !NS.cfg.captureValues) delete evt.value;
        if (evt.value) evt.value = trunc(evt.value, NS.cfg.maxValLen|0);
        if (NS.q.length >= (NS.cfg.maxQueue|0)) {{ NS.q.shift(); NS.stats.dropped++; }}
        NS.q.push(evt); NS.stats.pushed++;
      }} catch(e) {{ NS.stats.errs++; }}
    }}

    function flush(){{
      try{{
        const fn = window.__ns_param_push;
        if (typeof fn !== "function") return;
        if (!NS.q.length) return;
        const batch = NS.q.splice(0, 150);
        NS.stats.flushed += batch.length;
        fn(batch);
      }} catch(e) {{ NS.stats.errs++; }}
    }}
    setInterval(flush, Math.max(50, NS.cfg.flushIntervalMs|0));

    // ---- URLSearchParams hooks ----
    const USP = window.URLSearchParams && window.URLSearchParams.prototype;
    if (USP){{
      const ogGet = USP.get;
      const ogHas = USP.has;
      const ogGetAll = USP.getAll;

      if (typeof ogGet === "function"){{
        USP.get = function(k){{
          try{{
            const key = String(k||"");
            const val = ogGet.apply(this, arguments);
            pushEvt({{ event:"usp_get", key, value: val, url: safeUrl(location && location.href) }});
          }} catch(e){{}}
          return ogGet.apply(this, arguments);
        }};
      }}
      if (typeof ogHas === "function"){{
        USP.has = function(k){{
          try{{
            const key = String(k||"");
            const out = ogHas.apply(this, arguments);
            pushEvt({{ event:"usp_has", key, present: !!out, url: safeUrl(location && location.href) }});
          }} catch(e){{}}
          return ogHas.apply(this, arguments);
        }};
      }}
      if (typeof ogGetAll === "function"){{
        USP.getAll = function(k){{
          try{{
            const key = String(k||"");
            const out = ogGetAll.apply(this, arguments);
            pushEvt({{ event:"usp_getAll", key, count: (out && out.length)||0, url: safeUrl(location && location.href) }});
          }} catch(e){{}}
          return ogGetAll.apply(this, arguments);
        }};
      }}
    }}

    // ---- navigation hooks ----
    function recordNav(u, how){{
      try{{
        const s = safeUrl(u || "");
        if (!s) return;
        pushEvt({{ event:"nav", how, url: s }});
      }} catch(e){{}}
    }}

    const H = window.history;
    if (H && typeof H.pushState === "function"){{
      const og = H.pushState;
      H.pushState = function(state, title, url){{
        try {{ recordNav(url, "pushState"); }} catch(e){{}}
        return og.apply(this, arguments);
      }};
    }}
    if (H && typeof H.replaceState === "function"){{
      const og = H.replaceState;
      H.replaceState = function(state, title, url){{
        try {{ recordNav(url, "replaceState"); }} catch(e){{}}
        return og.apply(this, arguments);
      }};
    }}

    try{{
      const L = window.location;
      if (L && typeof L.assign === "function"){{
        const og = L.assign.bind(L);
        L.assign = function(url){{ recordNav(url, "location.assign"); return og(url); }};
      }}
      if (L && typeof L.replace === "function"){{
        const og = L.replace.bind(L);
        L.replace = function(url){{ recordNav(url, "location.replace"); return og(url); }};
      }}
    }} catch(e){{}}

  }} catch(e) {{}}
}})();
"""

    async def _install_param_bridge(self, page, param_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]", *, log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]"):
        if not self.cfg.enable_param_sniff:
            return

        max_events = int(self.cfg.param_max_events)

        async def _binding(source, payload):
            try:
                if payload is None:
                    return
                batch = payload if isinstance(payload, list) else [payload]
                for ev in batch:
                    if len(param_events) >= max_events:
                        return
                    if isinstance(ev, dict):
                        param_events.append(ev)
                    else:
                        param_events.append({"event": "param_raw", "raw": self._to_str(ev)})
            except Exception as e:
                self._log(f"[NetworkSniffer][PARAM] binding error: {e}", log)

        try:
            await page.expose_binding("__ns_param_push", _binding)
        except Exception as e:
            self._log(f"[NetworkSniffer][PARAM] expose_binding failed: {e}", log)
            return

        cfg = {
            "maxQueue": int(self.cfg.param_max_queue),
            "flushIntervalMs": int(self.cfg.param_flush_interval_ms),
            "maxUrlLen": int(self.cfg.param_max_url_len),
            "maxKeyLen": int(self.cfg.param_max_key_len),
            "maxValLen": int(self.cfg.param_max_val_len),
            "captureValues": bool(self.cfg.param_capture_values),
            "sampleRate": float(self.cfg.param_sample_rate),
        }

        try:
            script = self._param_init_script(cfg)
            await page.add_init_script(script=script)
        except TypeError:
            try:
                await page.add_init_script(script)
            except Exception as e:
                self._log(f"[NetworkSniffer][PARAM] init_script failed: {e}", log)
        except Exception as e:
            self._log(f"[NetworkSniffer][PARAM] init_script failed: {e}", log)

    # ============================== NEW: Bundle static scan ============================== #
    def _extract_script_srcs_from_html(self, html: str, base_url: str) -> "NetworkSniffer.List[str]":
        html = self._to_str(html)
        if not html:
            return []
        rx = self.re.compile(r"<script[^>]+src\s*=\s*['\"]([^'\"]+)['\"][^>]*>", self.re.I)
        out: "NetworkSniffer.List[str]" = []
        seen: "NetworkSniffer.Set[str]" = set()
        for m in rx.finditer(html):
            src = self._to_str(m.group(1)).strip()
            if not src:
                continue
            full = self._canonicalize_url(self._safe_urljoin(base_url, src))
            if full and full not in seen:
                seen.add(full)
                out.append(full)
        return out

    def _bundle_param_regexes(self) -> "NetworkSniffer.List[NetworkSniffer.Tuple[str, Any]]":
        # returns list of (name, compiled_regex)
        return [
            ("usp_get_literal", self.re.compile(r'URLSearchParams\\([^)]*\\)\\.get\\(["\']([a-zA-Z0-9_\\-]{{1,64}})["\']\\)', self.re.I)),
            ("dot_get_literal", self.re.compile(r'\\.get\\(["\']([a-zA-Z0-9_\\-]{{1,64}})["\']\\)', self.re.I)),
            ("query_key_like", self.re.compile(r'[?&]([a-zA-Z0-9_\\-]{{1,64}})=', self.re.I)),
            ("api_path", self.re.compile(r'(/api/[a-zA-Z0-9_/-]{3,80})', self.re.I)),
            ("next_data", self.re.compile(r'__NEXT_DATA__', self.re.I)),
            ("nuxt", self.re.compile(r'__NUXT__', self.re.I)),
        ]

    async def _fetch_text_prefix(self, api_ctx, url: str, *, timeout_ms: int, max_bytes: int) -> str:
        url = self._to_str(url)
        if not api_ctx:
            return ""
        try:
            h = {"Range": f"bytes=0-{max(0, int(max_bytes)-1)}"}
            resp = await api_ctx.get(url, headers=h, timeout=timeout_ms)
            b = await resp.body()
            if not b:
                return ""
            # decode as text-ish; bundles are usually utf-8
            try:
                return b.decode("utf-8", "ignore")
            except Exception:
                try:
                    return b.decode("latin-1", "ignore")
                except Exception:
                    return ""
        except Exception:
            return ""

    async def _bundle_param_scan(self, api_ctx, script_urls: "NetworkSniffer.List[str]", *, log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]") -> "NetworkSniffer.Dict[str, Any]":
        if not self.cfg.enable_bundle_param_scan or not api_ctx:
            return {"enabled": False, "scripts_scanned": 0, "hits": []}

        max_scripts = max(0, int(self.cfg.bundle_scan_max_scripts))
        max_bytes = max(8192, int(self.cfg.bundle_scan_range_bytes))
        timeout_ms = max(1000, int(self.cfg.bundle_scan_timeout_ms))
        max_hits = max(1, int(self.cfg.bundle_scan_max_regex_hits))

        rx_list = self._bundle_param_regexes()
        hits: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []

        # small dedupe
        seen_scripts: "NetworkSniffer.Set[str]" = set()
        picked: "NetworkSniffer.List[str]" = []
        for u in (script_urls or []):
            cu = self._canonicalize_url(u)
            if not cu or cu in seen_scripts:
                continue
            if not self._host_allowed(cu):
                continue
            seen_scripts.add(cu)
            picked.append(cu)
            if len(picked) >= max_scripts:
                break

        sem = self.asyncio.Semaphore(6)

        async def scan_one(u: str):
            async with sem:
                txt = await self._fetch_text_prefix(api_ctx, u, timeout_ms=timeout_ms, max_bytes=max_bytes)
                if not txt:
                    return
                for name, rx in rx_list:
                    for m in rx.finditer(txt):
                        if len(hits) >= max_hits:
                            return
                        g1 = self._to_str(m.group(1)) if m.groups() else self._to_str(m.group(0))
                        hits.append({
                            "script": u,
                            "pattern": name,
                            "hit": g1[:200],
                        })

        await self.asyncio.gather(*[scan_one(u) for u in picked], return_exceptions=True)

        self._log(f"[NetworkSniffer][BUNDLE] scanned={len(picked)} hits={len(hits)}", log)
        return {"enabled": True, "scripts_scanned": len(picked), "hits": hits}

    # ============================== Correlation helpers ============================== #
    def _ms_now(self) -> int:
        try:
            return int(self.time.time() * 1000.0)
        except Exception:
            return 0

    def _postprocess_param_events(self, param_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]") -> "NetworkSniffer.Dict[str, Any]":
        counts: "NetworkSniffer.Dict[str, int]" = {}
        nav_urls: "NetworkSniffer.List[str]" = []
        seen_nav: "NetworkSniffer.Set[str]" = set()

        for ev in (param_events or []):
            try:
                et = self._to_str(ev.get("event"))
                if et.startswith("usp_"):
                    k = self._to_str(ev.get("key"))
                    if k:
                        counts[k] = counts.get(k, 0) + 1
                if et == "nav":
                    u = self._to_str(ev.get("url"))
                    if u and u not in seen_nav:
                        seen_nav.add(u)
                        nav_urls.append(u)
            except Exception:
                pass

        # top keys
        top = sorted(counts.items(), key=lambda kv: kv[1], reverse=True)[:80]
        return {
            "counts": counts,
            "top_keys": [{"key": k, "reads": v} for (k, v) in top],
            "nav_urls": nav_urls[:200],
            "total_events": len(param_events or []),
        }

    def _correlate_params_to_endpoints(
        self,
        param_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]",
        resp_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]",
        *,
        window_ms: int,
        max_per_key: int
    ) -> "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]":
        """
        Correlate param reads -> network URLs observed shortly after.
        This is a heuristic report, not a guarantee of causality.
        """
        if not param_events or not resp_events:
            return []

        # Normalize + sort by ts (ms)
        pe = []
        for ev in param_events:
            et = self._to_str(ev.get("event"))
            if not et.startswith("usp_"):
                continue
            k = self._to_str(ev.get("key"))
            ts = ev.get("ts")
            try:
                ts = int(ts) if ts is not None else None
            except Exception:
                ts = None
            if k and ts is not None:
                pe.append((ts, k, et, self._to_str(ev.get("url"))))
        pe.sort(key=lambda t: t[0])

        re_ = []
        for ev in resp_events:
            ts = ev.get("ts")
            try:
                ts = int(ts) if ts is not None else None
            except Exception:
                ts = None
            u = self._to_str(ev.get("url"))
            kind = self._to_str(ev.get("kind") or ev.get("type") or "resp")
            if u and ts is not None:
                re_.append((ts, u, kind))
        re_.sort(key=lambda t: t[0])

        # two-pointer window
        out: "NetworkSniffer.Dict[str, NetworkSniffer.Dict[str, Any]]" = {}
        j = 0

        for (ts, key, et, src_url) in pe:
            if key not in out:
                out[key] = {
                    "param_key": key,
                    "reads": 0,
                    "first_seen_url": src_url,
                    "first_seen_ts": ts,
                    "endpoints": {},  # url -> count
                }
            out[key]["reads"] += 1

            # advance j to first resp >= ts
            while j < len(re_) and re_[j][0] < ts:
                j += 1

            # collect within window
            jj = j
            while jj < len(re_) and (re_[jj][0] - ts) <= window_ms:
                u = re_[jj][1]
                # avoid correlating the page URL itself too much; still keep if meaningful
                out[key]["endpoints"][u] = out[key]["endpoints"].get(u, 0) + 1
                jj += 1

        # format
        reports: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        for k, info in out.items():
            eps = info["endpoints"]
            top_eps = sorted(eps.items(), key=lambda kv: kv[1], reverse=True)[:max_per_key]
            reports.append({
                "param_key": k,
                "reads": int(info.get("reads", 0)),
                "first_seen_url": info.get("first_seen_url"),
                "likely_triggers": [{"type": "resp", "url": u, "count": c} for (u, c) in top_eps],
            })

        # keep only keys with something to show
        reports = [r for r in reports if r.get("likely_triggers")]
        reports.sort(key=lambda r: int(r.get("reads", 0)), reverse=True)
        return reports[:200]


    # ============================== Stronger promotion helpers ============================== #
    _MEDIA_KEYWORDS = {
        "video", "videos", "audio", "media", "stream", "streams", "src", "source", "sources",
        "file", "files", "play", "playback", "playlist", "manifest", "download", "cdn",
        "dash", "hls", "mp4", "webm", "m3u8", "mpd", "poster", "thumb", "thumbnail",
    }

    def _looks_like_media_key(self, key: Any) -> bool:
        k = self._to_str(key).strip().lower()
        if not k:
            return False
        return any(tok in k for tok in self._MEDIA_KEYWORDS)

    def _kind_from_key_name(self, key: Any) -> "NetworkSniffer.Optional[str]":
        k = self._to_str(key).strip().lower()
        if not k:
            return None
        if any(x in k for x in ("audio", "sound", "track", "mp3", "aac", "opus", "ogg", "m4a", "wav")):
            return "audio"
        if any(x in k for x in ("poster", "thumb", "thumbnail", "preview_image", "previewimage", "cover")):
            return "image"
        if any(x in k for x in ("video", "stream", "manifest", "playlist", "dash", "hls", "mp4", "webm", "m3u8", "mpd", "playback")):
            return "video"
        return None

    def _is_urlish_candidate(self, value: Any, *, parent_key: str = "") -> bool:
        s = self._to_str(value).strip()
        if not s:
            return False
        sl = s.lower()
        if s.startswith(("http://", "https://", "ws://", "wss://", "//", "/")):
            return True
        if any(sl.endswith(ext) for ext in (
            ".mp4", ".m4v", ".webm", ".mkv", ".mov", ".avi", ".ts", ".m4s", ".m3u8", ".mpd",
            ".mp3", ".m4a", ".aac", ".ogg", ".opus", ".wav",
            ".jpg", ".jpeg", ".png", ".gif", ".webp", ".avif",
        )):
            return True
        if any(h in sl for h in (
            "videoplayback", "manifest", "playlist", "chunklist", "master.m3u8", "index.m3u8", ".m3u8", ".mpd",
            "/segment", "/seg/", "segment-", "chunk-", "bytestream", "init.mp4", "moov", "transcode", "cdn",
        )):
            return True
        return self._looks_like_media_key(parent_key)

    def _extract_candidate_urls_from_obj(
        self,
        obj: Any,
        *,
        base_url: str,
        limit: int = 1200,
    ) -> "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]":
        out: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        stack: "NetworkSniffer.List[NetworkSniffer.Tuple[Any, str, int]]" = [(obj, "", 0)]
        seen: "NetworkSniffer.Set[str]" = set()

        while stack and len(out) < limit:
            cur, parent_key, depth = stack.pop()
            if depth > 10 or cur is None:
                continue

            if isinstance(cur, dict):
                for k, v in cur.items():
                    stack.append((v, self._to_str(k), depth + 1))
                continue

            if isinstance(cur, (list, tuple)):
                for v in cur:
                    stack.append((v, parent_key, depth + 1))
                continue

            s = self._to_str(cur).strip()
            if not s:
                continue
            if len(s) > 4096:
                continue
            if not self._is_urlish_candidate(s, parent_key=parent_key):
                continue

            full = s
            if s.startswith("//"):
                full = "https:" + s
            elif not s.startswith(("http://", "https://", "ws://", "wss://")):
                full = self._safe_urljoin(base_url, s)

            cu = self._canonicalize_url(full)
            if not cu or cu in seen:
                continue
            seen.add(cu)

            out.append({
                "url": cu,
                "parent_key": parent_key,
                "kind_hint": self._kind_from_key_name(parent_key),
            })

        return out

    def _score_promoted_candidate(
        self,
        *,
        url: str,
        source: str,
        parent_key: str = "",
        kind_hint: "NetworkSniffer.Optional[str]" = None,
        content_type: str = "",
        count: int = 1,
        event_name: str = "",
    ) -> "NetworkSniffer.Tuple[float, NetworkSniffer.Optional[str], str]":
        cu = self._canonicalize_url(url)
        if not cu:
            return 0.0, None, "empty"

        p = self._safe_urlparse(cu)
        path = self._to_str(p.path).lower()
        netloc = self._to_str(p.netloc).lower()
        ul = cu.lower()
        if self._looks_like_ad(netloc, path):
            return -100.0, None, "ad"
        if not self._host_allowed(cu):
            return -100.0, None, "host_blocked"

        kind = (
            kind_hint
            or self._classify_by_extension(path)
            or self._classify_by_content_type(content_type)
            or self._classify_by_stream_hint(ul)
        )

        score = 0.0
        reason_parts = [source]

        if kind:
            score += 2.0
            reason_parts.append(f"kind:{kind}")
        if self._is_manifest(cu, content_type):
            score += 3.0
            reason_parts.append("manifest")
        if self._looks_like_segment(ul, content_type, None, {}):
            score += 1.5
            reason_parts.append("segment")
        if self._looks_like_media_key(parent_key):
            score += 1.5
            reason_parts.append(f"key:{parent_key}")
        if source == "mse":
            score += 3.0
        elif source == "param_corr":
            score += 2.5
        elif source == "bundle":
            score += 1.75
        elif source == "json":
            score += 1.25
        if event_name:
            el = event_name.lower()
            if any(x in el for x in ("append", "source", "xhr_resp", "fetch_resp", "media_src", "video")):
                score += 1.25
                reason_parts.append(f"event:{el[:24]}")
        if count > 1:
            score += min(3.0, (count - 1) * 0.5)
            reason_parts.append(f"count:{count}")

        if any(h in ul for h in ("master.m3u8", "chunklist.m3u8", "index.m3u8", "manifest", "playlist", "videoplayback")):
            score += 1.5
            reason_parts.append("url_hint")

        return score, kind, "|".join(reason_parts)

    def _score_existing_item(self, item: "NetworkSniffer.Dict[str, Any]") -> float:
        tag = self._to_str(item.get("tag")).lower()
        kind = self._to_str(item.get("kind")).lower()
        ct = self._to_str(item.get("content_type")).lower()
        score = 0.0
        if tag == "binary_sig_sniff":
            score += 9.0
        elif tag == "network_sniff":
            score += 7.0
        elif "promoted" in tag:
            try:
                return float(item.get("score") or 0.0)
            except Exception:
                score += 4.0
        if kind == "video":
            score += 2.0
        elif kind == "audio":
            score += 1.5
        elif kind == "image":
            score += 0.5
        if ct.startswith("video/") or ct in self.cfg.hls_types or ct in self.cfg.dash_types:
            score += 2.0
        elif ct.startswith("audio/"):
            score += 1.0
        return score

    def _item_rank_tuple(self, item: "NetworkSniffer.Dict[str, Any]") -> "NetworkSniffer.Tuple[float, int, int, int]":
        try:
            score = float(item.get("score") if item.get("score") is not None else self._score_existing_item(item))
        except Exception:
            score = self._score_existing_item(item)
        kind = self._to_str(item.get("kind")).lower()
        tag = self._to_str(item.get("tag")).lower()
        kind_rank = 3 if kind == "video" else 2 if kind == "audio" else 1 if kind == "image" else 0
        tag_rank = 3 if tag == "binary_sig_sniff" else 2 if tag == "network_sniff" else 1 if "promoted" in tag else 0
        ctype_rank = 1 if self._to_str(item.get("content_type")).lower().startswith(("video/", "audio/")) else 0
        return (score, kind_rank, tag_rank, ctype_rank)

    def _upsert_promoted_candidate(
        self,
        bucket: "NetworkSniffer.Dict[str, NetworkSniffer.Dict[str, Any]]",
        *,
        url: str,
        source: str,
        parent_key: str = "",
        kind_hint: "NetworkSniffer.Optional[str]" = None,
        content_type: str = "",
        count: int = 1,
        event_name: str = "",
        size: Any = "?",
    ) -> None:
        score, kind, reason = self._score_promoted_candidate(
            url=url,
            source=source,
            parent_key=parent_key,
            kind_hint=kind_hint,
            content_type=content_type,
            count=count,
            event_name=event_name,
        )
        if score < float(self.cfg.min_candidate_score):
            return
        cu = self._canonicalize_url(url)
        if not cu:
            return
        existing = bucket.get(cu)
        confidence = "strong" if score >= 6.5 else "medium" if score >= 4.0 else "weak"
        item = {
            "url": cu,
            "text": f"[Promoted {((kind or kind_hint or 'media').capitalize())}] {source}",
            "tag": f"promoted_{source}",
            "kind": kind or kind_hint or "unknown",
            "content_type": content_type or "?",
            "size": self._to_str(size or "?"),
            "score": round(float(score), 3),
            "confidence": confidence,
            "evidence": reason,
        }
        if existing is None or self._item_rank_tuple(item) > self._item_rank_tuple(existing):
            bucket[cu] = item

    async def _verify_promoted_candidates(
        self,
        api_ctx,
        promoted_by_url: "NetworkSniffer.Dict[str, NetworkSniffer.Dict[str, Any]]",
        request_evidence: "NetworkSniffer.Dict[str, NetworkSniffer.Dict[str, Any]]",
        *,
        extensions: "NetworkSniffer.Optional[NetworkSniffer.Set[str]]",
        log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]",
    ) -> None:
        if not promoted_by_url:
            return
        if api_ctx is None and self.http is None:
            return

        top = sorted(promoted_by_url.values(), key=self._item_rank_tuple, reverse=True)[: int(self.cfg.max_promoted_candidates)]
        sem = self.asyncio.Semaphore(max(1, int(self.cfg.promote_probe_concurrency)))

        async def one(item: "NetworkSniffer.Dict[str, Any]"):
            async with sem:
                u = self._to_str(item.get("url"))
                ev = request_evidence.get(u) or request_evidence.get(self._canonicalize_url(u)) or {}
                req_hdrs = ev.get("headers_subset") or {}
                try:
                    pr = await self._probe_url(api_ctx, u, req_hdrs, timeout_ms=int(self.cfg.promote_probe_timeout_ms))
                except Exception as e:
                    self._log(f"[NetworkSniffer] promote probe failed for {u}: {e}", log)
                    return

                status = pr.get("status")
                pct = self._to_str(pr.get("content_type") or item.get("content_type") or "")
                if pct:
                    item["content_type"] = pct
                if pr.get("content_length"):
                    item["size"] = self._to_str(pr.get("content_length"))

                if status in (200, 206):
                    item["score"] = round(float(item.get("score") or 0.0) + 2.5, 3)
                    item["confidence"] = "medium" if item.get("confidence") == "weak" else item.get("confidence") or "medium"

                kind2 = self._classify_by_content_type(pct)
                if kind2:
                    item["kind"] = kind2
                    item["score"] = round(float(item.get("score") or 0.0) + 1.0, 3)

                need_prefix = (item.get("kind") in (None, "", "unknown")) or (not kind2)
                if need_prefix:
                    prefix = await self._get_prefix_bytes(
                        api_ctx,
                        u,
                        req_hdrs,
                        timeout_ms=int(self.cfg.promote_probe_timeout_ms),
                        prefix_bytes=int(self.cfg.binary_sniff_prefix_bytes),
                    )
                    kind_magic, ctype_magic, detail = self._guess_kind_from_magic(prefix)
                    if kind_magic:
                        item["kind"] = kind_magic
                        item["content_type"] = ctype_magic or item.get("content_type") or "?"
                        item["tag"] = "promoted_magic"
                        item["evidence"] = self._to_str(item.get("evidence") or "") + f"|magic:{detail}"
                        item["score"] = round(float(item.get("score") or 0.0) + 4.0, 3)
                        item["confidence"] = "strong"

                if not self._is_allowed_by_extensions(u, extensions, self._to_str(item.get("kind")) or None):
                    item["drop_me"] = True
                elif (item.get("kind") in (None, "", "unknown")) and bool(self.cfg.require_probe_for_weak_candidates):
                    item["drop_me"] = True

        await self.asyncio.gather(*[one(it) for it in top], return_exceptions=True)
        for k in list(promoted_by_url.keys()):
            if promoted_by_url[k].get("drop_me"):
                promoted_by_url.pop(k, None)

    async def _promote_secondary_candidates(
        self,
        api_ctx,
        *,
        canonical_page_url: str,
        json_hits: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]",
        mse_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]",
        correlation_reports: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]",
        bundle_scan: "NetworkSniffer.Dict[str, Any]",
        request_evidence: "NetworkSniffer.Dict[str, NetworkSniffer.Dict[str, Any]]",
        extensions: "NetworkSniffer.Optional[NetworkSniffer.Set[str]]",
        log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]",
    ) -> "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]":
        promoted_by_url: "NetworkSniffer.Dict[str, NetworkSniffer.Dict[str, Any]]" = {}

        if self.cfg.promote_json_media_urls or self.cfg.promote_json_structured_candidates:
            for hit in json_hits:
                base_url = self._to_str(hit.get("url") or canonical_page_url)
                data = hit.get("json")
                if not data:
                    continue
                candidates = self._extract_candidate_urls_from_obj(data, base_url=base_url, limit=300)
                for cand in candidates:
                    self._upsert_promoted_candidate(
                        promoted_by_url,
                        url=cand.get("url") or "",
                        source="json",
                        parent_key=self._to_str(cand.get("parent_key") or ""),
                        kind_hint=cand.get("kind_hint"),
                    )

        if self.cfg.promote_mse_candidates and mse_events:
            url_counts: "NetworkSniffer.Dict[str, int]" = {}
            meta: "NetworkSniffer.Dict[str, NetworkSniffer.Dict[str, Any]]" = {}
            for ev in mse_events:
                if not isinstance(ev, dict):
                    continue
                u = self._to_str(ev.get("url") or ev.get("src") or ev.get("request_url") or ev.get("mediaUrl"))
                if not u:
                    continue
                cu = self._canonicalize_url(u)
                if not cu:
                    continue
                url_counts[cu] = url_counts.get(cu, 0) + 1
                if cu not in meta:
                    meta[cu] = {
                        "event_name": self._to_str(ev.get("event") or ev.get("type") or "mse"),
                        "content_type": self._to_str(ev.get("content_type") or ""),
                    }
            for cu, cnt in url_counts.items():
                mm = meta.get(cu) or {}
                self._upsert_promoted_candidate(
                    promoted_by_url,
                    url=cu,
                    source="mse",
                    parent_key="mse",
                    kind_hint=None,
                    content_type=self._to_str(mm.get("content_type") or ""),
                    count=cnt,
                    event_name=self._to_str(mm.get("event_name") or "mse"),
                )

        if self.cfg.promote_param_correlation and correlation_reports:
            for rep in correlation_reports:
                pkey = self._to_str(rep.get("param_key") or "")
                reads = int(rep.get("reads") or 0)
                for trg in (rep.get("likely_triggers") or []):
                    if not isinstance(trg, dict):
                        continue
                    u = self._to_str(trg.get("url") or "")
                    cnt = int(trg.get("count") or 1)
                    self._upsert_promoted_candidate(
                        promoted_by_url,
                        url=u,
                        source="param_corr",
                        parent_key=pkey,
                        kind_hint=self._kind_from_key_name(pkey),
                        count=max(reads, cnt),
                        event_name=self._to_str(trg.get("type") or "resp"),
                    )

        if self.cfg.promote_bundle_scan_candidates and bundle_scan:
            for hit in (bundle_scan.get("hits") or []):
                if not isinstance(hit, dict):
                    continue
                raw = self._to_str(hit.get("hit") or "")
                if not raw:
                    continue
                pat = self._to_str(hit.get("pattern") or "bundle")
                if raw.startswith("/"):
                    raw = self._safe_urljoin(canonical_page_url, raw)
                elif not raw.startswith(("http://", "https://", "ws://", "wss://")):
                    continue
                self._upsert_promoted_candidate(
                    promoted_by_url,
                    url=raw,
                    source="bundle",
                    parent_key=pat,
                    kind_hint=self._kind_from_key_name(pat),
                )

        await self._verify_promoted_candidates(
            api_ctx,
            promoted_by_url,
            request_evidence,
            extensions=extensions,
            log=log,
        )

        items = list(promoted_by_url.values())
        items.sort(key=self._item_rank_tuple, reverse=True)
        return items[: int(self.cfg.max_promoted_candidates)]

    def _dedupe_and_rank_items(self, items: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]") -> "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]":
        best: "NetworkSniffer.Dict[str, NetworkSniffer.Dict[str, Any]]" = {}
        ordered: "NetworkSniffer.List[str]" = []
        for item in items:
            if not isinstance(item, dict):
                continue
            cu = self._canonicalize_url(item.get("url"))
            if not cu:
                continue
            item = dict(item)
            item["url"] = cu
            if cu not in best:
                best[cu] = item
                ordered.append(cu)
            else:
                if self._item_rank_tuple(item) > self._item_rank_tuple(best[cu]):
                    best[cu] = item
        out = [best[u] for u in ordered]
        out.sort(key=self._item_rank_tuple, reverse=True)
        return out

    # ------------------ NEW helper: emit any useful URL ------------------ #
    def _emit_linkish_url(
            self,
            url: Any,
            *,
            bucket: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]",
            seen: "NetworkSniffer.Set[str]",
            tag: str,
            text: str = "",
            kind_hint: "NetworkSniffer.Optional[str]" = None,
            content_type: str = "?",
            size: Any = "?",
            extensions: "NetworkSniffer.Optional[NetworkSniffer.Set[str]]" = None,
            evidence: str = "",
            score: Any = None,
            confidence: str = "",
    ) -> None:
        cu = self._canonicalize_url(url)
        if not cu or cu in seen:
            return
        if not self._host_allowed(cu):
            return

        p = self._safe_urlparse(cu)
        path = self._to_str(getattr(p, "path", "")).lower()
        netloc = self._to_str(getattr(p, "netloc", "")).lower()
        ul = cu.lower()
        ct = self._to_str(content_type or "")

        if self._looks_like_ad(netloc, path):
            return

        docish_tags = {
            "a", "area", "form", "iframe", "frame", "link", "meta",
            "redirect", "dom_href", "dom_src", "json_url", "mse_url",
            "param_url", "network_link", "network_doc"
        }

        # Keep HTML/page-style links for docish tags, but still block obvious junk for other kinds.
        if self._is_junk_by_extension(path) and tag not in docish_tags and not self._is_mediaish_url(cu):
            return

        if self._deny_by_content_type(ct) and tag not in docish_tags:
            # still allow actual media-ish or stream-hinted URLs through
            if not (
                    self._classify_by_content_type(ct)
                    or self._classify_by_stream_hint(ul)
                    or self._is_mediaish_url(cu)
            ):
                return

        kind = (
                kind_hint
                or self._classify_by_extension(path)
                or self._classify_by_content_type(ct)
                or self._classify_by_stream_hint(ul)
        )

        if tag in {"a", "area", "form", "iframe", "frame", "link", "meta", "redirect", "dom_href",
                   "dom_src"} and not kind:
            kind = "page"

        if not self._is_allowed_by_extensions(cu, extensions, None if kind in (None, "page", "unknown") else kind):
            return

        bucket.append({
            "url": cu,
            "text": self._to_str(text or "[Link]"),
            "tag": self._to_str(tag or "network_link"),
            "kind": self._to_str(kind or "unknown"),
            "content_type": self._to_str(ct or "?"),
            "size": self._to_str(size if size not in (None, "") else "?"),
            "score": self._to_str(score if score is not None else ""),
            "confidence": self._to_str(confidence or ""),
            "evidence": self._to_str(evidence or ""),
        })
        seen.add(cu)

    # ------------------ NEW helper: harvest DOM links directly ------------------ #
    async def _collect_dom_linkish_items(
            self,
            page,
            base_url: str,
            *,
            bucket: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]",
            seen: "NetworkSniffer.Set[str]",
            extensions: "NetworkSniffer.Optional[NetworkSniffer.Set[str]]" = None,
            log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]" = None,
    ) -> None:
        try:
            raw_items = await page.evaluate(
                """
                () => {
                  const out = [];
                  const seen = new Set();

                  const push = (u, t, tag, kind) => {
                    try {
                      u = String(u || "").trim();
                      if (!u) return;
                      const lu = u.toLowerCase();
                      if (
                        lu === "#" ||
                        lu.startsWith("javascript:") ||
                        lu.startsWith("mailto:") ||
                        lu.startsWith("tel:") ||
                        lu.startsWith("data:")
                      ) return;

                      const key = `${tag}|${u}`;
                      if (seen.has(key)) return;
                      seen.add(key);

                      out.push({
                        url: u,
                        text: String(t || "").trim().slice(0, 220),
                        tag: String(tag || "dom_href"),
                        kind: String(kind || "")
                      });
                    } catch (_) {}
                  };

                  for (const el of document.querySelectorAll("a[href], area[href]")) {
                    push(
                      el.getAttribute("href"),
                      el.innerText || el.textContent || el.getAttribute("title") || el.getAttribute("aria-label") || "",
                      (el.tagName || "").toLowerCase(),
                      "page"
                    );
                  }

                  for (const el of document.querySelectorAll("link[href]")) {
                    const rel = (el.getAttribute("rel") || "").toLowerCase();
                    push(
                      el.getAttribute("href"),
                      rel || el.getAttribute("title") || "",
                      "link",
                      rel.includes("icon") ? "image" : (rel.includes("preload") || rel.includes("prefetch") ? "asset" : "page")
                    );
                  }

                  for (const el of document.querySelectorAll("iframe[src], frame[src]")) {
                    push(el.getAttribute("src"), el.getAttribute("title") || "", (el.tagName || "").toLowerCase(), "page");
                  }

                  for (const el of document.querySelectorAll("form[action]")) {
                    push(el.getAttribute("action"), el.getAttribute("id") || el.getAttribute("name") || "", "form", "page");
                  }

                  for (const el of document.querySelectorAll("img[src], source[src], video[src], audio[src], track[src], embed[src]")) {
                    const tag = (el.tagName || "").toLowerCase();
                    let kind = "";
                    if (tag === "img") kind = "image";
                    else if (tag === "audio" || tag === "track") kind = "audio";
                    else if (tag === "video" || tag === "source" || tag === "embed") kind = "video";
                    push(el.getAttribute("src"), el.getAttribute("title") || el.getAttribute("alt") || "", tag, kind);
                  }

                  for (const el of document.querySelectorAll("object[data]")) {
                    push(el.getAttribute("data"), el.getAttribute("title") || "", "object", "asset");
                  }

                  for (const el of document.querySelectorAll("meta[content]")) {
                    const p = (el.getAttribute("property") || el.getAttribute("name") || "").toLowerCase();
                    if (
                      p.includes("og:video") ||
                      p.includes("og:image") ||
                      p.includes("twitter:image") ||
                      p.includes("twitter:player") ||
                      p.includes("og:url") ||
                      p === "canonical"
                    ) {
                      push(el.getAttribute("content"), p, "meta", p.includes("image") ? "image" : (p.includes("video") || p.includes("player") ? "video" : "page"));
                    }
                  }

                  // dataset / inline attr salvage for JS-heavy sites
                  for (const el of document.querySelectorAll("[data-href], [data-url], [data-src], [data-video], [onclick]")) {
                    push(el.getAttribute("data-href"), "", "dom_href", "page");
                    push(el.getAttribute("data-url"), "", "dom_href", "page");
                    push(el.getAttribute("data-src"), "", "dom_src", "asset");
                    push(el.getAttribute("data-video"), "", "dom_src", "video");

                    const onclick = el.getAttribute("onclick") || "";
                    const m = onclick.match(/https?:\\/\\/[^"'\\s<>]+/ig);
                    if (m) {
                      for (const u of m) push(u, "", "onclick", "page");
                    }
                  }

                  return out.slice(0, 4000);
                }
                """
            ) or []
        except Exception as e:
            self._log(f"[NetworkSniffer] DOM link harvest failed: {e}", log)
            return

        added = 0
        for item in raw_items:
            if not isinstance(item, dict):
                continue
            raw = self._to_str(item.get("url"))
            if not raw:
                continue
            full = self._safe_urljoin(base_url, raw)
            self._emit_linkish_url(
                full,
                bucket=bucket,
                seen=seen,
                tag=self._to_str(item.get("tag") or "dom_href"),
                text=self._to_str(item.get("text") or "[DOM Link]"),
                kind_hint=(self._to_str(item.get("kind")) or None),
                content_type="?",
                size="?",
                extensions=extensions,
                evidence="dom-harvest",
            )
            added += 1

        self._log(f"[NetworkSniffer] DOM link harvest added {added} candidate link(s).", log)

    # ============================== sniff ============================== #
    async def sniff(
            self,
            context,
            page_url: str,
            *,
            timeout: "NetworkSniffer.Optional[float]" = None,
            log: "NetworkSniffer.Optional[NetworkSniffer.List[str]]" = None,
            extensions: "NetworkSniffer.Optional[NetworkSniffer.Set[str]]" = None,
    ):
        if context is None:
            self._log("[NetworkSniffer] No Playwright context; skipping sniff.", log)
            return "", [], []

        tmo = float(timeout if timeout is not None else self.cfg.timeout)
        self.cfg.timeout = tmo
        canonical_page_url = self._canonicalize_url(page_url)

        found_items: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        derived_items: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        page_link_items: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        json_hits: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []

        seen_network: "NetworkSniffer.Set[str]" = set()
        seen_derived: "NetworkSniffer.Set[str]" = set()
        seen_page_links: "NetworkSniffer.Set[str]" = set()
        seen_mse_urls: "NetworkSniffer.Set[str]" = set()
        seen_binary_sig: "NetworkSniffer.Set[str]" = set()

        blob_placeholders: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        req_types: "NetworkSniffer.Dict[str, str]" = {}

        request_evidence: "NetworkSniffer.Dict[str, NetworkSniffer.Dict[str, Any]]" = {}
        redirect_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        seen_redirect: "NetworkSniffer.Set[str]" = set()

        forensics: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        seen_forensics: "NetworkSniffer.Set[str]" = set()

        salvage_info: "NetworkSniffer.Dict[str, NetworkSniffer.Dict[str, Any]]" = {}
        salvage_host_counts: "NetworkSniffer.Dict[str, int]" = {}
        salvage_bundles: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []

        mse_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        param_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []

        resp_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []

        script_urls: "NetworkSniffer.List[str]" = []
        seen_scripts: "NetworkSniffer.Set[str]" = set()

        binary_tasks: "NetworkSniffer.List[NetworkSniffer.asyncio.Task]" = []
        binary_sem = self.asyncio.Semaphore(int(self.cfg.binary_sniff_concurrency))

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

        manifests_to_expand: "NetworkSniffer.List[NetworkSniffer.Tuple[Any, str, str]]" = []
        promoted_items: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        corr: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        bundle_scan: "NetworkSniffer.Dict[str, Any]" = {"enabled": False, "scripts_scanned": 0, "hits": []}

        self._log(f"[NetworkSniffer] Start sniff: {canonical_page_url} (timeout={tmo}s)", log)

        if self.cfg.enable_mse_sniff:
            await self._install_mse_bridge(page, mse_events, log=log)
        if self.cfg.enable_param_sniff:
            await self._install_param_bridge(page, param_events, log=log)

        def _parse_content_length(headers_lc: "NetworkSniffer.Dict[str, str]") -> "NetworkSniffer.Optional[int]":
            try:
                raw = self._to_str(headers_lc.get("content-length") or "").strip()
                if not raw:
                    return None
                return int(raw.split(",", 1)[0].strip())
            except Exception:
                return None

        def handle_request(req):
            try:
                rurl = self._to_str(getattr(req, "url", None))
                req_types[rurl] = self._to_str(getattr(req, "resource_type", None))
            except Exception:
                pass

            try:
                if self.cfg.enable_forensics:
                    url = self._to_str(getattr(req, "url", None))
                    if url and url not in request_evidence:
                        try:
                            rh_raw = getattr(req, "headers", None) or {}
                            rh_lc = {self._to_str(k).lower(): self._to_str(v) for k, v in rh_raw.items()}
                        except Exception:
                            rh_lc = {}
                        req_hdr_subset = self._pick_headers_subset(rh_lc,
                                                                   self.cfg.forensics_include_request_headers_subset)

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

            try:
                rt = self._to_str(getattr(req, "resource_type", None))
                if rt == "script":
                    u = self._canonicalize_url(self._to_str(getattr(req, "url", None)))
                    if u and u not in seen_scripts and self._host_allowed(u):
                        seen_scripts.add(u)
                        script_urls.append(u)
            except Exception:
                pass

            try:
                if self.cfg.enable_graphql_sniff and self._to_str(getattr(req, "method", "")).upper() == "POST":
                    url_lower = self._to_str(getattr(req, "url", None)).lower()
                    if self._looks_like_graphql_endpoint(url_lower):
                        body = self._to_str(getattr(req, "post_data", None) or "")
                        if body and len(body) <= int(self.cfg.graphql_max_body_kb) * 1024:
                            try:
                                gql_payload = self.json.loads(body)
                            except Exception:
                                gql_payload = None

                            if gql_payload is not None:
                                payloads = gql_payload if isinstance(gql_payload, list) else [gql_payload]
                                for pay in payloads:
                                    if not isinstance(pay, dict):
                                        continue
                                    if len(json_hits) >= max_json:
                                        break

                                    op_name = pay.get("operationName")
                                    vars_obj = pay.get("variables")
                                    query = pay.get("query") or ""
                                    is_introspection = isinstance(query, str) and (
                                                "__schema" in query or "__type" in query)
                                    var_keys = list(vars_obj.keys()) if isinstance(vars_obj, dict) else None

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

        async def handle_response(response):
            try:
                raw_url = self._to_str(getattr(response, "url", None))
                canonical_url = self._canonicalize_url(raw_url)
                if not canonical_url or not self._host_allowed(canonical_url):
                    return

                try:
                    hdrs_raw = getattr(response, "headers", None) or {}
                    headers = {self._to_str(k).lower(): self._to_str(v) for k, v in hdrs_raw.items()}
                except Exception:
                    headers = {}

                status = getattr(response, "status", None)
                resource_type = self._to_str(req_types.get(raw_url) or req_types.get(canonical_url) or "")
                content_type = self._to_str(headers.get("content-type") or "")
                content_length = _parse_content_length(headers)

                if len(resp_events) < 4000:
                    resp_events.append({
                        "ts": self.time.time(),
                        "url": canonical_url,
                        "status": status,
                        "content_type": content_type,
                        "resource_type": resource_type,
                    })

                parsed = self._safe_urlparse(canonical_url)
                path = self._to_str(getattr(parsed, "path", "")).lower()
                netloc = self._to_str(getattr(parsed, "netloc", "")).lower()
                url_lower = canonical_url.lower()

                if self._looks_like_ad(netloc, path):
                    return

                kind = (
                        self._classify_by_content_type(content_type)
                        or self._classify_by_extension(path)
                        or self._classify_by_stream_hint(url_lower)
                )

                manifest_kind = self._is_manifest(canonical_url, content_type)
                seg_kind = self._looks_like_segment(url_lower, content_type, content_length, headers)
                if not kind and seg_kind:
                    kind = seg_kind

                # Redirect / location mining
                location = self._to_str(headers.get("location") or "").strip()
                if location:
                    dest = self._canonicalize_url(self._safe_urljoin(canonical_url, location))
                    if dest and dest not in seen_redirect:
                        seen_redirect.add(dest)
                        redirect_events.append({
                            "from": canonical_url,
                            "to": dest,
                            "status": status,
                        })
                        self._emit_linkish_url(
                            dest,
                            bucket=page_link_items,
                            seen=seen_page_links,
                            tag="redirect",
                            text="[Redirect]",
                            kind_hint="page",
                            content_type="?",
                            size="?",
                            extensions=extensions,
                            evidence=f"redirect:{status}",
                        )

                # Emit useful response URL even if it is not classic media.
                if not self._deny_by_resource_type(resource_type):
                    tag = "network_sniff" if kind in ("video", "audio",
                                                      "image") or manifest_kind or seg_kind else "network_link"
                    label = (
                        f"[Network {kind.capitalize()}]" if kind in ("video", "audio", "image")
                        else ("[Network Manifest]" if manifest_kind else "[Network Link]")
                    )
                    self._emit_linkish_url(
                        canonical_url,
                        bucket=(found_items if tag == "network_sniff" else page_link_items),
                        seen=(seen_network if tag == "network_sniff" else seen_page_links),
                        tag=tag,
                        text=label,
                        kind_hint=(kind or ("video" if manifest_kind else None)),
                        content_type=content_type,
                        size=content_length if content_length is not None else "?",
                        extensions=extensions,
                        evidence=f"response:{status}:{resource_type or 'unknown'}",
                    )

                if manifest_kind and len(manifests_to_expand) < max_manifests:
                    manifests_to_expand.append((response, manifest_kind, canonical_url))

                # JSON body sniff
                if self._should_sniff_json(url_lower, content_type, content_length):
                    body_text = ""
                    try:
                        body_text = self._to_str(await response.text())
                    except Exception:
                        body_text = ""

                    data = None
                    if body_text:
                        try:
                            data = self.json.loads(body_text)
                        except Exception:
                            data = None

                    if data is not None and len(json_hits) < max_json:
                        json_hits.append({
                            "url": canonical_url,
                            "json": data,
                            "source_page": canonical_page_url,
                        })

                        for u in self._iter_urls_in_json(data, limit=2500):
                            self._emit_linkish_url(
                                u,
                                bucket=page_link_items,
                                seen=seen_page_links,
                                tag="json_url",
                                text="[JSON URL]",
                                kind_hint=None,
                                content_type="?",
                                size="?",
                                extensions=extensions,
                                evidence="json-body",
                            )

                # Forensics bundle
                try:
                    if self.cfg.enable_forensics:
                        req_ev = request_evidence.get(raw_url) or request_evidence.get(canonical_url) or {}
                        req_hdr_subset = req_ev.get("headers_subset") or {}
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
                            "status": status,
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
                except Exception:
                    pass

                # Salvage targeting
                try:
                    if self.cfg.enable_url_salvage:
                        if self._salvage_should_target(canonical_url, status=status, kind=kind):
                            host = self._to_str(self._safe_urlparse(canonical_url).netloc).lower()
                            if host:
                                cnt = salvage_host_counts.get(host, 0)
                                if cnt < int(self.cfg.salvage_max_targets_per_host):
                                    score = self._salvage_score(canonical_url, status=status, kind=kind)
                                    prev = salvage_info.get(canonical_url)
                                    if (prev is None) or (float(prev.get("score", 0.0)) < score):
                                        salvage_info[canonical_url] = {
                                            "url": canonical_url,
                                            "score": score,
                                            "status": status,
                                            "kind": kind,
                                        }
                                        salvage_host_counts[host] = salvage_host_counts.get(host, 0) + 1
                except Exception:
                    pass

            except Exception as e:
                self._log(
                    f"[NetworkSniffer][handle_response] Error processing {self._to_str(getattr(response, 'url', None))}: {self._to_str(e)}",
                    log
                )

        page.on("response", handle_response)

        try:
            nav_modes = []
            for mode in (wait_mode, "commit", "domcontentloaded", "load"):
                mode = self._to_str(mode or "").strip() or "domcontentloaded"
                if mode not in nav_modes:
                    nav_modes.append(mode)

            sniff_goto_timeout = max(15000, int(tmo * 1000))
            navigated = False
            for mode in nav_modes:
                try:
                    await page.goto(canonical_page_url, wait_until=mode, timeout=sniff_goto_timeout)
                    navigated = True
                    if mode != wait_mode:
                        self._log(f"[NetworkSniffer] goto recovered using wait_until={mode} on {canonical_page_url}",
                                  log)
                    break
                except Exception as e:
                    self._log(f"[NetworkSniffer] goto timeout on {canonical_page_url} (wait_until={mode}): {e}", log)

            await self._auto_scroll(page, tmo, log)
            await page.wait_for_timeout(int(tmo * 1000 * 0.2))

            if self.cfg.enable_param_sniff:
                try:
                    await page.wait_for_timeout(max(80, int(self.cfg.param_flush_interval_ms)))
                except Exception:
                    pass

            try:
                html = await page.content()
            except Exception as e:
                self._log(f"[NetworkSniffer] page.content failed on {canonical_page_url}: {e}", log)
                html = ""

            # Direct DOM link harvest so plain page links finally get returned.
            await self._collect_dom_linkish_items(
                page,
                canonical_page_url,
                bucket=page_link_items,
                seen=seen_page_links,
                extensions=extensions,
                log=log,
            )

            # Also mine any raw absolute URLs visible in the HTML snapshot.
            try:
                for u in self._extract_urls_from_text(html)[:500]:
                    self._emit_linkish_url(
                        u,
                        bucket=page_link_items,
                        seen=seen_page_links,
                        tag="html_url",
                        text="[HTML URL]",
                        kind_hint=None,
                        content_type="?",
                        size="?",
                        extensions=extensions,
                        evidence="html-regex",
                    )
            except Exception:
                pass

            # Expand manifests
            for resp, manifest_kind, manifest_url in manifests_to_expand[:max_manifests]:
                try:
                    derived = await self._expand_manifest(resp, manifest_kind, manifest_url, log)
                except Exception as e:
                    self._log(f"[NetworkSniffer] Manifest expansion failed for {manifest_url}: {e}", log)
                    derived = []

                for du in derived[:max_derived_per_manifest]:
                    self._emit_linkish_url(
                        du,
                        bucket=derived_items,
                        seen=seen_derived,
                        tag=f"{manifest_kind}_derived",
                        text=f"[{manifest_kind.upper()} Derived]",
                        kind_hint="video",
                        content_type="?",
                        size="?",
                        extensions=extensions,
                        evidence=f"{manifest_kind}-expand",
                    )

            # Salvage probing
            if self.cfg.enable_url_salvage and salvage_info:
                top_salvage = sorted(
                    salvage_info.values(),
                    key=lambda x: float(x.get("score", 0.0)),
                    reverse=True,
                )[: int(self.cfg.salvage_max_targets_total)]

                for s in top_salvage:
                    try:
                        ev = request_evidence.get(s.get("url")) or {}
                        req_hdrs = ev.get("headers_subset") or {}
                        bundle = await self._salvage_one(
                            api_ctx,
                            s.get("url"),
                            req_hdrs,
                            log=log,
                            observed_status=s.get("status"),
                            observed_kind=s.get("kind"),
                        )
                        if bundle:
                            salvage_bundles.append(bundle)
                            for okv in bundle.get("ok_variants") or []:
                                self._emit_linkish_url(
                                    okv.get("url"),
                                    bucket=derived_items,
                                    seen=seen_derived,
                                    tag="salvaged",
                                    text="[Salvaged URL]",
                                    kind_hint=s.get("kind"),
                                    content_type=okv.get("content_type") or "?",
                                    size=okv.get("content_length") or "?",
                                    extensions=extensions,
                                    evidence=self._to_str(okv.get("variant_kind") or "salvage"),
                                )
                    except Exception as e:
                        self._log(f"[NetworkSniffer] Salvage failed for {s.get('url')}: {e}", log)

            # Param-to-endpoint correlation
            if self.cfg.enable_param_sniff:
                try:
                    corr = self._correlate_params_to_endpoints(
                        param_events,
                        resp_events,
                        window_ms=int(self.cfg.correlate_window_ms),
                        max_per_key=int(self.cfg.correlate_max_per_key),
                    )
                    if corr and len(json_hits) < max_json:
                        json_hits.append({
                            "url": canonical_page_url,
                            "json": {"param_endpoint_correlation": {
                                "window_ms": int(self.cfg.correlate_window_ms),
                                "items": corr[:250],
                            }},
                            "source_page": canonical_page_url,
                        })
                except Exception as e:
                    self._log(f"[NetworkSniffer] param correlation failed: {e}", log)
                    corr = []

            # Bundle scan
            if self.cfg.enable_bundle_param_scan and api_ctx is not None and script_urls:
                try:
                    bundle_scan = await self._bundle_param_scan(api_ctx, script_urls, log=log)
                    if len(json_hits) < max_json:
                        json_hits.append({
                            "url": canonical_page_url,
                            "json": {"bundle_param_scan": bundle_scan},
                            "source_page": canonical_page_url,
                        })
                except Exception as e:
                    self._log(f"[NetworkSniffer] bundle scan failed: {e}", log)

            # Candidate promotion still kept
            if self.cfg.enable_candidate_promotion:
                try:
                    promoted_items = await self._promote_secondary_candidates(
                        api_ctx,
                        canonical_page_url=canonical_page_url,
                        json_hits=json_hits,
                        mse_events=mse_events,
                        correlation_reports=corr,
                        bundle_scan=bundle_scan,
                        request_evidence=request_evidence,
                        extensions=extensions,
                        log=log,
                    )
                except Exception as e:
                    self._log(f"[NetworkSniffer] Candidate promotion failed: {e}", log)
                    promoted_items = []

            # Secondary harvesting from all the side-channels
            try:
                for hit in json_hits:
                    for u in self._iter_urls_in_json(hit.get("json") or {}, limit=2500):
                        self._emit_linkish_url(
                            u,
                            bucket=page_link_items,
                            seen=seen_page_links,
                            tag="json_url",
                            text="[JSON URL]",
                            kind_hint=None,
                            content_type="?",
                            size="?",
                            extensions=extensions,
                            evidence="json-hit",
                        )
            except Exception:
                pass

            try:
                for ev in redirect_events:
                    self._emit_linkish_url(
                        ev.get("to"),
                        bucket=page_link_items,
                        seen=seen_page_links,
                        tag="redirect",
                        text="[Redirect]",
                        kind_hint="page",
                        content_type="?",
                        size="?",
                        extensions=extensions,
                        evidence=f"redirect:{ev.get('status')}",
                    )
            except Exception:
                pass

            try:
                for ev in mse_events:
                    u = self._to_str(ev.get("url") or ev.get("src") or ev.get("request_url") or ev.get("mediaUrl"))
                    if not u:
                        continue
                    self._emit_linkish_url(
                        u,
                        bucket=page_link_items,
                        seen=seen_page_links,
                        tag="mse_url",
                        text="[MSE URL]",
                        kind_hint=None,
                        content_type=self._to_str(ev.get("content_type") or ""),
                        size="?",
                        extensions=extensions,
                        evidence=self._to_str(ev.get("event") or ev.get("type") or "mse"),
                    )
            except Exception:
                pass

            try:
                for ev in param_events:
                    for u in self._iter_urls_in_json(ev, limit=20):
                        self._emit_linkish_url(
                            u,
                            bucket=page_link_items,
                            seen=seen_page_links,
                            tag="param_url",
                            text="[Param URL]",
                            kind_hint=None,
                            content_type="?",
                            size="?",
                            extensions=extensions,
                            evidence="param-event",
                        )
            except Exception:
                pass

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

        except Exception as e:
            self._log(f"[NetworkSniffer] Unexpected error during sniff for {canonical_page_url}: {e}", log)

        finally:
            try:
                # make sure we don't leave probe tasks behind
                if binary_tasks:
                    done, pending = await self.asyncio.wait(binary_tasks, timeout=max(0.1, min(2.0, tmo * 0.25)))
                    for task in pending:
                        try:
                            task.cancel()
                        except Exception:
                            pass
                    if pending:
                        await self.asyncio.gather(*pending, return_exceptions=True)
            except Exception:
                pass

            try:
                await self.asyncio.wait_for(page.close(), timeout=3.0)
            except Exception:
                pass

        merged_items_any = found_items + derived_items + promoted_items + blob_placeholders + page_link_items
        merged_items_any = self._dedupe_and_rank_items([it for it in merged_items_any if it.get("url")])
        merged_items = [self._normalize_item(it) for it in merged_items_any if it.get("url")]

        summary = (
            f"[NetworkSniffer] Finished sniff for {canonical_page_url}: "
            f"media={len(found_items)} derived={len(derived_items)} promoted={len(promoted_items)} "
            f"blob={len(blob_placeholders)} page_links={len(page_link_items)} "
            f"json_hits={len(json_hits)} forensics={len(forensics)} salvage={len(salvage_bundles)} "
            f"mse={len(mse_events)} param_events={len(param_events)} scripts={len(script_urls)} "
            f"binary_sig_tasks={len(binary_tasks)} "
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

    Key design points:
      - NEVER passes timeout= to page.evaluate/page.content/page.close (older PW compat)
      - All timeouts enforced via asyncio.wait_for wrappers
      - Multi-pass, budgeted scanning to avoid reverse-image / heavy pages wedging you
      - Watchdog hard-cap for the entire sniff run (returns partials)
      - Uses staged "cheap -> medium -> heavy" passes and skips expensive passes if time is low
      - Can return partial HTML/links if later passes hang or the page is too heavy
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
        evaluate_timeout_s: float = 2.5          # per evaluate call
        content_timeout_s: float = 2.0           # page.content() budget
        close_timeout_s: float = 1.2             # page.close budget
        watchdog_multiplier: float = 1.25        # whole sniff hard-cap multiplier

        # newly emphasized anti-stall controls
        max_nav_timeout_s: float = 30
        preflight_timeout_s: float = 1.25
        pass_guard_s: float = 2.2
        min_seconds_reserved_for_close: float = 0.60
        min_seconds_reserved_for_content: float = 0.75
        skip_heavy_if_remaining_below_s: float = 2.0
        skip_clicks_if_remaining_below_s: float = 2.8
        degrade_on_large_dom: bool = True
        large_dom_threshold: int = 3500
        max_pending_requests_hint: int = 24

        max_items_soft_limit: int = 1800         # browser-side cap before returning to Python

        # Shadow DOM traversal caps
        shadow_host_soft_limit: int = 250        # how many potential shadow hosts to inspect
        max_dom_nodes_scanned: int = 9000        # global cap for scanned elements

        # Script scanning caps
        enable_script_scan: bool = True
        script_soft_limit: int = 60              # number of <script> tags to inspect
        max_script_chars: int = 60_000           # truncate per-script text
        enable_json_parse_in_scripts: bool = True
        max_json_parse_chars: int = 90_000       # cap JSON.parse text length

        # Optional click simulation
        enable_click_simulation: bool = False
        max_click_targets: int = 6
        click_timeout_ms: int = 10500
        click_target_selectors: List[str] = field(default_factory=lambda: [
            "button", "[role=button]", "[onclick]", "div[role=link]", "span[role=link]"
        ])

        # ------------------ Webpack module scan (safe/off by default) -- #
        enable_webpack_scan: bool = False
        webpack_module_soft_limit: int = 120
        max_webpack_fn_chars: int = 70_000
        webpack_url_regex: str = r"(https?:\/\/[^\s'\"`]+|\/api\/[a-zA-Z0-9_\/\-\?\=&]+)"
        webpack_api_hints: Set[str] = field(default_factory=lambda: {
            "/api/", "/graphql", "/auth", "/login", "/logout", "/stream",
            ".m3u8", ".mpd", "/cdn/", "/v1/", "/v2/"
        })

        # ------------------ “long lost content” scans ------------------ #
        enable_perf_entries: bool = True
        max_perf_entries: int = 500

        enable_meta_scan: bool = True
        enable_link_rel_scan: bool = True
        enable_srcset_scan: bool = True

        # NOTE: computedStyle can be EXPENSIVE on huge pages.
        enable_css_url_scan: bool = True
        enable_computed_style_bg_scan: bool = False
        computed_style_bg_budget: int = 350
        max_style_chars: int = 80_000

        enable_storage_scan: bool = True
        max_storage_keys: int = 90
        max_storage_chars: int = 90_000

        enable_spa_state_scan: bool = True
        max_spa_json_chars: int = 120_000
        spa_state_keys: List[str] = field(default_factory=lambda: [
            "__NEXT_DATA__", "__NUXT__", "__NUXT_DATA__", "__APOLLO_STATE__",
            "__INITIAL_STATE__", "__PRELOADED_STATE__", "__SSR_STATE__",
            "REDUX_STATE", "INITIAL_REDUX_STATE",
        ])

        # Optional runtime collectors mentioned elsewhere in your codebase
        enable_runtime_url_ring: bool = True
        runtime_ring_soft_limit: int = 300
        enable_mutation_url_ring: bool = True
        mutation_ring_soft_limit: int = 250
        enable_hydration_scan: bool = True
        enable_worker_scan: bool = True
        enable_sw_scan: bool = True
        enable_webrtc_scan: bool = True

        selectors: List[str] = field(default_factory=lambda: [
            "a[href]",
            "video[src]", "video source[src]", "source[src]",
            "audio[src]", "audio source[src]",
            "img[src]", "img[srcset]",
            "iframe[src]", "embed[src]",
            "link[href]",
            "meta[content]",
        ])

        junk_prefixes: Set[str] = field(default_factory=lambda: {
            "blob:", "javascript:", "data:"
        })

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

        data_url_keys: Set[str] = field(default_factory=lambda: {
            "data-href", "data-url", "data-src", "data-srcset",
            "data-video", "data-video-url", "data-poster",
            "data-file", "data-stream", "data-mp4", "data-m3u8", "data-mpd",
            "data-audio", "data-audio-url", "data-image", "data-media-url"
        })

        onclick_url_regexes: List[str] = field(default_factory=lambda: [
            r"""['\"]((?:https?:)?//[^'\"]+)['\"]""",
            r"""location\.href\s*=\s*['\"]([^'\"]+)['\"]""",
            r"""window\.open\(\s*['\"]([^'\"]+)['\"]""",
            r"""window\.location\.assign\(\s*['\"]([^'\"]+)['\"]\)""",
            r"""window\.location\.replace\(\s*['\"]([^'\"]+)['\"]\)""",
            r"""decodeURIComponent\s*\(\s*['\"]([^'\"]+)['\"]\)""",
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

    # ------------------------- logging ------------------------- #

    def _log(self, msg: str, log_list: Optional[List[str]]) -> None:
        full = f"[JSSniffer] {msg}"
        try:
            if log_list is not None:
                log_list.append(full)
            if self.logger is not None:
                self.logger.log_message(full)
        except Exception:
            pass

    # ------------------------- PW-safe wrappers ------------------------- #

    async def _pw_eval(self, page, script: str, arg: dict, log: Optional[List[str]]) -> dict:
        try:
            return await asyncio.wait_for(page.evaluate(script, arg), timeout=self.cfg.evaluate_timeout_s)
        except asyncio.TimeoutError:
            raise TimeoutError(f"page.evaluate exceeded {self.cfg.evaluate_timeout_s}s")
        except Exception as e:
            raise RuntimeError(f"page.evaluate failed: {e}")

    async def _pw_content(self, page, log: Optional[List[str]]) -> str:
        try:
            return await asyncio.wait_for(page.content(), timeout=self.cfg.content_timeout_s)
        except asyncio.TimeoutError:
            raise TimeoutError(f"page.content exceeded {self.cfg.content_timeout_s}s")
        except Exception as e:
            raise RuntimeError(f"page.content failed: {e}")

    async def _pw_close(self, page, log: Optional[List[str]]) -> None:
        try:
            await asyncio.wait_for(page.close(), timeout=self.cfg.close_timeout_s)
        except Exception:
            return None

    # ------------------------- URL helpers ------------------------- #

    def _is_junk_url(self, url: str) -> bool:
        if not url:
            return True
        u = url.lower().strip()
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
        if kind in ("video", "audio"):
            return True
        return False

    def _normalize_link(self, url: str, text: str, tag: str) -> Dict[str, str]:
        return {"url": url, "text": text or "", "tag": tag or "a"}

    def _fix_common_escapes(self, url: str) -> str:
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

    def _canonicalize_local(self, url: str) -> str:
        try:
            return _canonicalize_url(self._fix_common_escapes(url))
        except Exception:
            try:
                return self._fix_common_escapes(url)
            except Exception:
                return url

    def _dedupe_links(self, items: List[Dict[str, str]], *, limit: Optional[int] = None) -> List[Dict[str, str]]:
        out: List[Dict[str, str]] = []
        seen: Set[str] = set()
        max_n = int(limit or self.cfg.max_links)
        for item in items:
            try:
                raw_url = str((item or {}).get("url") or "").strip()
            except Exception:
                raw_url = ""
            if not raw_url:
                continue
            u = self._canonicalize_local(raw_url)
            if not u or self._is_junk_url(u) or u in seen:
                continue
            kind = self._classify_kind(u)
            if not self._is_allowed_by_extensions(u, None, kind):
                continue
            seen.add(u)
            out.append({
                "url": u,
                "text": str((item or {}).get("text") or "")[:400],
                "tag": str((item or {}).get("tag") or "a")[:80],
            })
            if len(out) >= max_n:
                break
        return out

    def _deadline(self, started: float, hard_cap: float) -> float:
        return started + hard_cap

    def _remaining(self, started: float, hard_cap: float) -> float:
        return self._deadline(started, hard_cap) - time.monotonic()

    def _budget_low_for_heavy(self, started: float, hard_cap: float) -> bool:
        return self._remaining(started, hard_cap) < float(self.cfg.skip_heavy_if_remaining_below_s)

    def _budget_low_for_clicks(self, started: float, hard_cap: float) -> bool:
        return self._remaining(started, hard_cap) < float(self.cfg.skip_clicks_if_remaining_below_s)

    async def _safe_wait(self, coro, *, timeout_s: float, label: str, log: Optional[List[str]], default=None):
        try:
            return await asyncio.wait_for(coro, timeout=max(0.05, timeout_s))
        except asyncio.TimeoutError:
            self._log(f"{label} timed out after {timeout_s:.2f}s", log)
            return default
        except Exception as e:
            self._log(f"{label} failed: {e}", log)
            return default

    async def _get_dom_metrics(self, page, log: Optional[List[str]]) -> Dict[str, Any]:
        script = r"""
        () => {
          try {
            const all = document.querySelectorAll('*');
            const scripts = document.scripts ? document.scripts.length : 0;
            const links = document.links ? document.links.length : 0;
            return {
              nodeCount: all ? all.length : 0,
              scriptCount: scripts,
              linkCount: links,
              readyState: document.readyState || '',
              title: document.title || '',
            };
          } catch (e) {
            return { nodeCount: 0, scriptCount: 0, linkCount: 0, error: String(e || '') };
          }
        }
        """
        try:
            return await asyncio.wait_for(page.evaluate(script), timeout=min(self.cfg.preflight_timeout_s, self.cfg.evaluate_timeout_s))
        except Exception as e:
            self._log(f"DOM metrics probe failed: {e}", log)
            return {"nodeCount": 0, "scriptCount": 0, "linkCount": 0}

    async def _maybe_block_resources(self, page, log: Optional[List[str]]) -> None:
        if not self.cfg.block_resource_types:
            return
        blocked = {str(x).strip().lower() for x in (self.cfg.blocked_types or set()) if str(x).strip()}
        if not blocked:
            return

        async def _route(route):
            try:
                req = route.request
                rt = str(getattr(req, "resource_type", "") or "").lower()
                if rt in blocked:
                    await route.abort()
                    return
            except Exception:
                pass
            try:
                await route.continue_()
            except Exception:
                pass

        try:
            await page.route("**/*", _route)
            self._log(f"Resource blocking enabled for types={sorted(blocked)}", log)
        except Exception as e:
            self._log(f"Failed to enable route blocking: {e}", log)

    # ------------------------- auto-scroll ------------------------- #

    async def _auto_scroll(self, page, tmo: float, log: Optional[List[str]]) -> None:
        if not self.cfg.enable_auto_scroll:
            return

        try:
            max_steps = max(1, int(self.cfg.max_scroll_steps))
            step_delay = max(60, int(self.cfg.scroll_step_delay_ms))
            max_total_ms = int(tmo * 1000 * 0.65)
            used_ms = 0

            self._log(f"Auto-scroll enabled: steps={max_steps}, step_delay={step_delay}ms", log)

            last_height = 0
            try:
                last_height = await asyncio.wait_for(
                    page.evaluate("() => document.scrollingElement ? document.scrollingElement.scrollHeight : (document.body ? document.body.scrollHeight : 0)"),
                    timeout=self.cfg.evaluate_timeout_s,
                )
            except Exception as e:
                self._log(f"Auto-scroll: initial height read failed: {e}", log)
                return

            for i in range(max_steps):
                if used_ms >= max_total_ms:
                    self._log("Auto-scroll: reached time budget; stopping.", log)
                    break

                try:
                    await asyncio.wait_for(
                        page.evaluate("() => window.scrollBy(0, window.innerHeight);"),
                        timeout=self.cfg.evaluate_timeout_s,
                    )
                except Exception as e:
                    self._log(f"Auto-scroll: scrollBy failed: {e}", log)
                    break

                await page.wait_for_timeout(step_delay)
                used_ms += step_delay

                try:
                    new_height = await asyncio.wait_for(
                        page.evaluate("() => document.scrollingElement ? document.scrollingElement.scrollHeight : (document.body ? document.body.scrollHeight : 0)"),
                        timeout=self.cfg.evaluate_timeout_s,
                    )
                except Exception as e:
                    self._log(f"Auto-scroll: height read failed: {e}", log)
                    break

                self._log(f"Auto-scroll step {i+1}/{max_steps}: height {last_height} -> {new_height}", log)

                if int(new_height or 0) <= int(last_height or 0):
                    self._log("Auto-scroll: no further height growth; stopping.", log)
                    break
                last_height = new_height

            if self.cfg.scroll_back_to_top:
                try:
                    await asyncio.wait_for(
                        page.evaluate("() => window.scrollTo(0, 0);"),
                        timeout=self.cfg.evaluate_timeout_s,
                    )
                except Exception:
                    pass

        except Exception as e:
            self._log(f"Auto-scroll error: {e}", log)

    # ------------------------- staged JS passes ------------------------- #

    _JS_PASS_CHEAP = r'''
    (args) => {
      const {
        baseUrl, selectors, dataKeys, onclickRegexes, maxItems,
        maxDomNodes, includeShadow, shadowHostLimit,
        enableMeta, enableRelLinks, enableSrcset,
        enablePerf, maxPerf
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
        try { u = normalizeUrlRaw(String(u).trim()); return new URL(u, baseUrl).href; }
        catch { return String(u).trim(); }
      }

      function labelOf(el) {
        try {
          const txt = (el.innerText || el.textContent || el.getAttribute('aria-label') || el.getAttribute('title') || '').trim();
          return txt.slice(0, 240);
        } catch { return ''; }
      }

      function push(el, url, tag) {
        if (out.length >= maxItems) return false;
        url = absUrl(url);
        if (!url || url.startsWith('blob:') || url.startsWith('javascript:') || url.startsWith('data:') || seen.has(url)) return true;
        seen.add(url);
        out.push({ url, text: labelOf(el), tag: tag || (el && el.tagName ? String(el.tagName).toLowerCase() : 'dom') });
        return out.length < maxItems;
      }

      function scanNode(root) {
        let nodes = [];
        try {
          nodes = root.querySelectorAll(selectors.join(','));
        } catch {}
        const lim = Math.min(nodes.length || 0, maxDomNodes);
        for (let i = 0; i < lim; i++) {
          const el = nodes[i];
          try {
            const tag = (el.tagName || '').toLowerCase();
            const href = el.getAttribute && (el.getAttribute('href') || el.getAttribute('src') || el.getAttribute('content'));
            if (href && !push(el, href, tag)) return;
            if (enableSrcset && el.getAttribute) {
              const srcset = el.getAttribute('srcset') || '';
              if (srcset) {
                for (const part of String(srcset).split(',')) {
                  const url = String(part || '').trim().split(/\s+/)[0];
                  if (url && !push(el, url, tag + ':srcset')) return;
                }
              }
            }
            if (el.getAttribute) {
              for (const k of dataKeys) {
                const v = el.getAttribute(k);
                if (v && !push(el, v, tag + ':' + k)) return;
              }
              const onclick = el.getAttribute('onclick') || '';
              if (onclick) {
                for (const rxSrc of onclickRegexes) {
                  let rx = null;
                  try { rx = new RegExp(rxSrc, 'ig'); } catch {}
                  if (!rx) continue;
                  let m;
                  while ((m = rx.exec(onclick)) !== null) {
                    const u = m && m[1] ? m[1] : (m && m[0] ? m[0] : '');
                    if (u && !push(el, u, tag + ':onclick')) return;
                  }
                }
              }
            }
          } catch {}
        }
      }

      scanNode(document);

      if (includeShadow) {
        try {
          const all = Array.from(document.querySelectorAll('*')).slice(0, shadowHostLimit);
          for (const host of all) {
            if (out.length >= maxItems) break;
            try {
              if (host && host.shadowRoot) scanNode(host.shadowRoot);
            } catch {}
          }
        } catch {}
      }

      if (enableMeta) {
        try {
          const metas = Array.from(document.querySelectorAll('meta[content]')).slice(0, 200);
          for (const el of metas) {
            if (out.length >= maxItems) break;
            const v = el.getAttribute('content');
            if (!v) continue;
            if (/https?:\/\//i.test(v) || /^\//.test(v)) {
              if (!push(el, v, 'meta')) break;
            }
          }
        } catch {}
      }

      if (enableRelLinks) {
        try {
          const rels = Array.from(document.querySelectorAll('link[href]')).slice(0, 200);
          for (const el of rels) {
            if (out.length >= maxItems) break;
            const v = el.getAttribute('href');
            if (v && !push(el, v, 'link')) break;
          }
        } catch {}
      }

      if (enablePerf && typeof performance !== 'undefined' && performance.getEntries) {
        try {
          const perf = performance.getEntries().slice(0, maxPerf);
          for (const e of perf) {
            if (out.length >= maxItems) break;
            try {
              if (e && e.name && (String(e.name).startsWith('http://') || String(e.name).startsWith('https://') || String(e.name).startsWith('/'))) {
                if (!push(document.documentElement || document.body || document, e.name, 'perf')) break;
              }
            } catch {}
          }
        } catch {}
      }

      return { items: out, capped: out.length >= maxItems, stage: 'cheap' };
    }
    '''

    _JS_PASS_MEDIUM = r'''
    (args) => {
      const {
        baseUrl, maxItems, maxStyleChars,
        enableCssUrls, enableStorage, maxStorageKeys, maxStorageChars,
        enableSpa, maxSpaChars, spaKeys,
        enableScriptScan, scriptLimit, maxScriptChars,
        enableJsonParse, maxJsonParseChars, scriptJsonHints
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
        try { u = normalizeUrlRaw(String(u).trim()); return new URL(u, baseUrl).href; }
        catch { return String(u).trim(); }
      }

      function push(url, text, tag) {
        if (out.length >= maxItems) return false;
        url = absUrl(url);
        if (!url || url.startsWith('blob:') || url.startsWith('javascript:') || url.startsWith('data:') || seen.has(url)) return true;
        seen.add(url);
        out.push({ url, text: String(text || '').slice(0, 240), tag: tag || 'js' });
        return out.length < maxItems;
      }

      function extractUrlsFromText(s, tag) {
        try {
          s = String(s || '');
          if (!s) return;
          const rx = /(https?:\/\/[^\s'"`<>]+|\/[A-Za-z0-9_\-\.\/\?\=&%#]{3,})/ig;
          let m;
          while ((m = rx.exec(s)) !== null) {
            const u = m && m[1] ? m[1] : (m && m[0] ? m[0] : '');
            if (!u) continue;
            if (!push(u, '', tag)) return;
          }
        } catch {}
      }

      if (enableCssUrls) {
        try {
          const styles = Array.from(document.querySelectorAll('style,[style]')).slice(0, 180);
          for (const el of styles) {
            if (out.length >= maxItems) break;
            let txt = '';
            try { txt = el.tagName && el.tagName.toLowerCase() === 'style' ? (el.textContent || '') : (el.getAttribute('style') || ''); } catch {}
            if (!txt) continue;
            if (txt.length > maxStyleChars) txt = txt.slice(0, maxStyleChars);
            extractUrlsFromText(txt, 'css');
          }
        } catch {}
      }

      if (enableStorage) {
        try {
          let seenKeys = 0;
          const buckets = [window.localStorage, window.sessionStorage];
          for (const store of buckets) {
            if (!store) continue;
            const lim = Math.min(store.length || 0, maxStorageKeys);
            for (let i = 0; i < lim; i++) {
              if (out.length >= maxItems) break;
              let k = '', v = '';
              try { k = String(store.key(i) || ''); } catch {}
              try { v = String(store.getItem(k) || ''); } catch {}
              if (!k && !v) continue;
              if (v.length > maxStorageChars) v = v.slice(0, maxStorageChars);
              extractUrlsFromText(v, 'storage');
              seenKeys += 1;
            }
          }
        } catch {}
      }

      if (enableSpa) {
        try {
          for (const k of spaKeys) {
            if (out.length >= maxItems) break;
            let val = null;
            try { val = window[k]; } catch {}
            if (val == null) continue;
            let s = '';
            try { s = JSON.stringify(val); } catch { try { s = String(val); } catch {} }
            if (!s) continue;
            if (s.length > maxSpaChars) s = s.slice(0, maxSpaChars);
            extractUrlsFromText(s, 'spa-state');
          }
        } catch {}
      }

      if (enableScriptScan) {
        try {
          const scripts = Array.from(document.scripts || []).slice(0, scriptLimit);
          for (const el of scripts) {
            if (out.length >= maxItems) break;
            try {
              const src = el.getAttribute && el.getAttribute('src');
              if (src && !push(src, '', 'script:src')) break;
            } catch {}
            let txt = '';
            try { txt = String(el.textContent || ''); } catch {}
            if (!txt) continue;
            if (txt.length > maxScriptChars) txt = txt.slice(0, maxScriptChars);
            extractUrlsFromText(txt, 'script');

            if (enableJsonParse) {
              try {
                const low = txt.toLowerCase();
                let hinted = false;
                for (const hint of scriptJsonHints) {
                  if (low.includes(String(hint).toLowerCase())) { hinted = true; break; }
                }
                if (!hinted) continue;
                const m = txt.match(/\{[\s\S]{20,}\}|\[[\s\S]{20,}\]/);
                if (!m) continue;
                let chunk = String(m[0] || '');
                if (chunk.length > maxJsonParseChars) chunk = chunk.slice(0, maxJsonParseChars);
                extractUrlsFromText(chunk, 'script-json');
              } catch {}
            }
          }
        } catch {}
      }

      return { items: out, capped: out.length >= maxItems, stage: 'medium' };
    }
    '''

    _JS_PASS_HEAVY = r'''
    (args) => {
      const {
        baseUrl, maxItems,
        enableComputedBg, computedBgBudget,
        enableWebpack, webpackLimit, maxWebpackFnChars, webpackUrlRegex, webpackApiHints,
        maxDomNodes
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
        try { u = normalizeUrlRaw(String(u).trim()); return new URL(u, baseUrl).href; }
        catch { return String(u).trim(); }
      }

      function push(url, text, tag) {
        if (out.length >= maxItems) return false;
        url = absUrl(url);
        if (!url || url.startsWith('blob:') || url.startsWith('javascript:') || url.startsWith('data:') || seen.has(url)) return true;
        seen.add(url);
        out.push({ url, text: String(text || '').slice(0, 240), tag: tag || 'js-heavy' });
        return out.length < maxItems;
      }

      function extractUrlsFromText(s, tag) {
        try {
          s = String(s || '');
          if (!s) return;
          const rx = /(https?:\/\/[^\s'"`<>]+|\/[A-Za-z0-9_\-\.\/\?\=&%#]{3,})/ig;
          let m;
          while ((m = rx.exec(s)) !== null) {
            const u = m && m[1] ? m[1] : (m && m[0] ? m[0] : '');
            if (!u) continue;
            if (!push(u, '', tag)) return;
          }
        } catch {}
      }

      if (enableComputedBg && typeof getComputedStyle === 'function') {
        try {
          const els = Array.from(document.querySelectorAll('*')).slice(0, Math.min(maxDomNodes, computedBgBudget));
          for (const el of els) {
            if (out.length >= maxItems) break;
            let bg = '';
            try { bg = String(getComputedStyle(el).backgroundImage || ''); } catch {}
            if (!bg || bg === 'none') continue;
            extractUrlsFromText(bg, 'computed-style');
          }
        } catch {}
      }

      if (enableWebpack) {
        try {
          let req = null;
          try {
            req = (window.__webpack_require__ || null);
          } catch {}
          if (req && req.c) {
            let modules = [];
            try { modules = Object.values(req.c || {}); } catch {}
            if (modules.length > webpackLimit) modules = modules.slice(0, webpackLimit);

            let rx = null;
            try { rx = new RegExp(webpackUrlRegex, 'ig'); } catch {}
            if (rx) {
              for (const mod of modules) {
                if (out.length >= maxItems) break;
                let src = '';
                try {
                  let fn = null;
                  if (mod && typeof mod.toString === 'function') fn = mod;
                  else if (mod && mod.exports && typeof mod.exports.toString === 'function') fn = mod.exports;
                  if (!fn) continue;
                  src = String(fn.toString() || '');
                } catch { continue; }

                if (!src) continue;
                if (src.length > maxWebpackFnChars) src = src.slice(0, maxWebpackFnChars);
                rx.lastIndex = 0;
                let m;
                while ((m = rx.exec(src)) !== null) {
                  const candidate = m && m[0] ? m[0] : '';
                  if (!candidate) continue;
                  const low = candidate.toLowerCase();
                  let ok = false;
                  for (const hint of webpackApiHints) {
                    if (low.includes(String(hint).toLowerCase())) { ok = true; break; }
                  }
                  if (!ok) continue;
                  if (!push(candidate, '', 'webpack')) break;
                }
              }
            }
          }
        } catch {}
      }

      return { items: out, capped: out.length >= maxItems, stage: 'heavy' };
    }
    '''

    async def _collect_runtime_url_events(self, page, canonical_page_url: str, runtime_hits: List[Dict[str, str]], log: Optional[List[str]]) -> None:
        if not self.cfg.enable_runtime_url_ring:
            return
        script = r'''
        () => {
          try {
            const buf = Array.isArray(window.__jsSnifferRuntimeUrls) ? window.__jsSnifferRuntimeUrls : [];
            return buf.slice(0, 500);
          } catch (e) {
            return [];
          }
        }
        '''
        result = await self._safe_wait(page.evaluate(script), timeout_s=min(self.cfg.evaluate_timeout_s, 1.0), label="runtime-url-ring", log=log, default=[])
        if not isinstance(result, list):
            return
        for u in result[: self.cfg.runtime_ring_soft_limit]:
            try:
                su = self._canonicalize_local(str(u or "").strip())
                if su and not self._is_junk_url(su):
                    runtime_hits.append({"url": su, "text": "", "tag": "runtime-url"})
            except Exception:
                pass

    async def _collect_mutation_url_events(self, page, canonical_page_url: str, runtime_hits: List[Dict[str, str]], log: Optional[List[str]]) -> None:
        if not self.cfg.enable_mutation_url_ring:
            return
        script = r'''
        () => {
          try {
            const buf = Array.isArray(window.__jsSnifferMutationUrls) ? window.__jsSnifferMutationUrls : [];
            return buf.slice(0, 500);
          } catch (e) {
            return [];
          }
        }
        '''
        result = await self._safe_wait(page.evaluate(script), timeout_s=min(self.cfg.evaluate_timeout_s, 1.0), label="mutation-url-ring", log=log, default=[])
        if not isinstance(result, list):
            return
        for u in result[: self.cfg.mutation_ring_soft_limit]:
            try:
                su = self._canonicalize_local(str(u or "").strip())
                if su and not self._is_junk_url(su):
                    runtime_hits.append({"url": su, "text": "", "tag": "mutation-url"})
            except Exception:
                pass

    async def _collect_hydration_state(self, page, canonical_page_url: str, runtime_hits: List[Dict[str, str]], log: Optional[List[str]]) -> None:
        if not self.cfg.enable_hydration_scan:
            return
        script = r'''
        () => {
          const keys = ['__NEXT_DATA__','__NUXT__','__NUXT_DATA__','__APOLLO_STATE__','__INITIAL_STATE__','__PRELOADED_STATE__','__SSR_STATE__','REDUX_STATE','INITIAL_REDUX_STATE'];
          const out = [];
          function walk(v, depth) {
            if (depth > 3 || out.length > 200) return;
            if (v == null) return;
            if (typeof v === 'string') {
              out.push(v);
              return;
            }
            if (Array.isArray(v)) {
              for (const x of v.slice(0, 40)) walk(x, depth + 1);
              return;
            }
            if (typeof v === 'object') {
              for (const k of Object.keys(v).slice(0, 60)) {
                try { walk(v[k], depth + 1); } catch {}
              }
            }
          }
          try {
            for (const k of keys) {
              try { if (window[k] != null) walk(window[k], 0); } catch {}
            }
          } catch {}
          return out;
        }
        '''
        vals = await self._safe_wait(page.evaluate(script), timeout_s=min(self.cfg.evaluate_timeout_s, 1.25), label="hydration-state", log=log, default=[])
        if not isinstance(vals, list):
            return
        rx = re.compile(r"(https?:\/\/[^\s'\"`<>]+|\/[A-Za-z0-9_\-\.\/\?\=&%#]{3,})", re.I)
        for s in vals[:200]:
            try:
                text = str(s or "")
            except Exception:
                continue
            for m in rx.findall(text):
                try:
                    u = self._canonicalize_local(m)
                    if u and not self._is_junk_url(u):
                        runtime_hits.append({"url": u, "text": "", "tag": "hydration"})
                except Exception:
                    pass

    async def _collect_worker_events(self, page, canonical_page_url: str, runtime_hits: List[Dict[str, str]], log: Optional[List[str]]) -> None:
        if not self.cfg.enable_worker_scan:
            return
        script = r"""
        () => {
          try {
            const out = [];
            const ss = Array.from(document.querySelectorAll('script[src], link[rel="modulepreload"][href]')).slice(0, 120);
            for (const el of ss) {
              const v = el.getAttribute('src') || el.getAttribute('href') || '';
              if (v) out.push(v);
            }
            return out;
          } catch (e) {
            return [];
          }
        }
        """
        vals = await self._safe_wait(page.evaluate(script), timeout_s=min(self.cfg.evaluate_timeout_s, 1.0), label="worker-scan", log=log, default=[])
        if not isinstance(vals, list):
            return
        for s in vals[:100]:
            try:
                u = self._canonicalize_local(str(s or "").strip())
                if u and not self._is_junk_url(u):
                    runtime_hits.append({"url": u, "text": "", "tag": "worker-related"})
            except Exception:
                pass

    async def _collect_sw_events(self, page, canonical_page_url: str, runtime_hits: List[Dict[str, str]], log: Optional[List[str]]) -> None:
        if not self.cfg.enable_sw_scan:
            return
        script = r"""
        async () => {
          try {
            if (!('serviceWorker' in navigator)) return [];
            const regs = await navigator.serviceWorker.getRegistrations();
            const out = [];
            for (const reg of regs || []) {
              try { if (reg.scope) out.push(reg.scope); } catch {}
              try { if (reg.active && reg.active.scriptURL) out.push(reg.active.scriptURL); } catch {}
              try { if (reg.waiting && reg.waiting.scriptURL) out.push(reg.waiting.scriptURL); } catch {}
              try { if (reg.installing && reg.installing.scriptURL) out.push(reg.installing.scriptURL); } catch {}
            }
            return out;
          } catch (e) {
            return [];
          }
        }
        """
        vals = await self._safe_wait(page.evaluate(script), timeout_s=min(self.cfg.evaluate_timeout_s, 1.6), label="service-worker-scan", log=log, default=[])
        if not isinstance(vals, list):
            return
        for s in vals[:60]:
            try:
                u = self._canonicalize_local(str(s or "").strip())
                if u and not self._is_junk_url(u):
                    runtime_hits.append({"url": u, "text": "", "tag": "service-worker"})
            except Exception:
                pass

    async def _collect_css_url_events(self, page, canonical_page_url: str, runtime_hits: List[Dict[str, str]], log: Optional[List[str]]) -> None:
        if not self.cfg.enable_css_url_scan:
            return
        script = r"""
        () => {
          try {
            const out = [];
            const rx = /url\((['"]?)(.*?)\1\)/ig;
            const nodes = Array.from(document.querySelectorAll('style,[style]')).slice(0, 150);
            for (const el of nodes) {
              let txt = '';
              try { txt = el.tagName && el.tagName.toLowerCase() === 'style' ? (el.textContent || '') : (el.getAttribute('style') || ''); } catch {}
              if (!txt) continue;
              let m;
              while ((m = rx.exec(txt)) !== null) {
                const u = m && m[2] ? m[2] : '';
                if (u) out.push(u);
              }
            }
            return out;
          } catch (e) {
            return [];
          }
        }
        """
        vals = await self._safe_wait(page.evaluate(script), timeout_s=min(self.cfg.evaluate_timeout_s, 1.1), label="css-url-events", log=log, default=[])
        if not isinstance(vals, list):
            return
        for s in vals[:120]:
            try:
                u = self._canonicalize_local(str(s or "").strip())
                if u and not self._is_junk_url(u):
                    runtime_hits.append({"url": u, "text": "", "tag": "css-runtime"})
            except Exception:
                pass

    async def _collect_webrtc_events(self, page, canonical_page_url: str, runtime_hits: List[Dict[str, str]], log: Optional[List[str]]) -> None:
        if not self.cfg.enable_webrtc_scan:
            return
        # intentionally light: detect config/ICE URL hints, not active peer intervention
        script = r"""
        () => {
          try {
            const out = [];
            const keys = ['__rtcConfig', '__webrtcConfig', '__iceServers'];
            for (const k of keys) {
              try {
                const v = window[k];
                if (!v) continue;
                out.push(JSON.stringify(v));
              } catch {}
            }
            return out;
          } catch (e) {
            return [];
          }
        }
        """
        vals = await self._safe_wait(page.evaluate(script), timeout_s=min(self.cfg.evaluate_timeout_s, 1.0), label="webrtc-events", log=log, default=[])
        if not isinstance(vals, list):
            return
        rx = re.compile(r"((?:stun|turn|turns):[^\s'\"`<>]+|https?:\/\/[^\s'\"`<>]+)", re.I)
        for s in vals[:60]:
            try:
                text = str(s or "")
            except Exception:
                continue
            for m in rx.findall(text):
                runtime_hits.append({"url": str(m), "text": "", "tag": "webrtc"})

    async def _collect_json_parse_events(self, page, canonical_page_url: str, runtime_hits: List[Dict[str, str]], log: Optional[List[str]]) -> None:
        # lightweight placeholder that reads optional hook buffers if page instrumentation created them elsewhere
        script = r"""
        () => {
          try {
            const buf = Array.isArray(window.__jsonParseUrlHits) ? window.__jsonParseUrlHits : [];
            return buf.slice(0, 250);
          } catch (e) {
            return [];
          }
        }
        """
        vals = await self._safe_wait(page.evaluate(script), timeout_s=min(self.cfg.evaluate_timeout_s, 0.9), label="json-parse-events", log=log, default=[])
        if not isinstance(vals, list):
            return
        for s in vals[:120]:
            try:
                u = self._canonicalize_local(str(s or "").strip())
                if u and not self._is_junk_url(u):
                    runtime_hits.append({"url": u, "text": "", "tag": "json-parse"})
            except Exception:
                pass

    async def _maybe_simulate_clicks(self, page, started: float, hard_cap: float, log: Optional[List[str]]) -> None:
        if not self.cfg.enable_click_simulation:
            return
        if self._budget_low_for_clicks(started, hard_cap):
            self._log("Skipping click simulation due to low remaining budget.", log)
            return

        selector = ", ".join(self.cfg.click_target_selectors or [])
        script = r"""
        (sel) => {
          try {
            const els = Array.from(document.querySelectorAll(sel)).slice(0, 30);
            return els.map((el, idx) => ({
              idx,
              selector: sel,
              text: String((el.innerText || el.textContent || el.getAttribute('aria-label') || '').trim()).slice(0, 140),
              visible: !!(el.offsetWidth || el.offsetHeight || (el.getClientRects && el.getClientRects().length)),
            }));
          } catch (e) {
            return [];
          }
        }
        """
        candidates = await self._safe_wait(page.evaluate(script, selector), timeout_s=min(self.cfg.evaluate_timeout_s, 1.0), label="click-candidate-scan", log=log, default=[])
        if not isinstance(candidates, list) or not candidates:
            return

        clicked = 0
        for idx, _entry in enumerate(candidates):
            if clicked >= int(self.cfg.max_click_targets):
                break
            if self._budget_low_for_clicks(started, hard_cap):
                break
            try:
                loc = page.locator(selector).nth(idx)
                await self._safe_wait(loc.click(timeout=int(self.cfg.click_timeout_ms)), timeout_s=max(0.5, self.cfg.click_timeout_ms / 1000.0 + 0.6), label=f"click[{idx}]", log=log, default=None)
                try:
                    await page.wait_for_timeout(int(self.cfg.click_timeout_ms // 3 or 250))
                except Exception:
                    pass
                clicked += 1
            except Exception as e:
                self._log(f"Click simulation failed for candidate {idx}: {e}", log)

        if clicked:
            self._log(f"Click simulation completed for {clicked} target(s).", log)

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
        self.cfg.timeout = tmo
        canonical_page_url = self._canonicalize_local(page_url)

        html: str = ""
        links: List[Dict[str, str]] = []
        seen_urls_in_js: Set[str] = set()
        runtime_hits: List[Dict[str, str]] = []
        page = await context.new_page()

        hard_cap = max(3.0, tmo * float(self.cfg.watchdog_multiplier))
        started = time.monotonic()

        async def _run() -> Tuple[str, List[Dict[str, str]]]:
            nonlocal html, links, seen_urls_in_js, runtime_hits

            try:
                try:
                    page.set_default_timeout(int(max(1.0, min(tmo, self.cfg.max_nav_timeout_s)) * 1000))
                    page.set_default_navigation_timeout(int(max(2.0, min(max(tmo, 5.0), self.cfg.max_nav_timeout_s)) * 1000))
                except Exception:
                    pass

                await self._maybe_block_resources(page, log)

                nav_wait = max(1.0, min(tmo + 1.0, self.cfg.max_nav_timeout_s))
                goto_result = await self._safe_wait(
                    page.goto(canonical_page_url, wait_until=self.cfg.goto_wait_until),
                    timeout_s=nav_wait,
                    label="page.goto",
                    log=log,
                    default=None,
                )
                if goto_result is None:
                    self._log("Navigation returned no response/partial state; continuing with partial page state.", log)

                if self.cfg.wait_after_goto_ms > 0:
                    try:
                        await page.wait_for_timeout(int(self.cfg.wait_after_goto_ms))
                    except Exception:
                        pass

                dom_metrics = await self._get_dom_metrics(page, log)
                node_count = int((dom_metrics or {}).get("nodeCount") or 0)
                script_count = int((dom_metrics or {}).get("scriptCount") or 0)
                self._log(f"DOM preflight: nodes={node_count}, scripts={script_count}, ready={dom_metrics.get('readyState','')}", log)

                local_cfg = dict(
                    baseUrl=canonical_page_url,
                    selectors=list(self.cfg.selectors),
                    includeShadow=bool(self.cfg.include_shadow_dom),
                    dataKeys=list(self.cfg.data_url_keys),
                    onclickRegexes=list(self.cfg.onclick_url_regexes),
                    redirectHints=list(self.cfg.redirect_hints),
                    scriptJsonHints=list(self.cfg.script_json_hints),
                    maxItems=int(self.cfg.max_items_soft_limit),
                    maxDomNodes=int(self.cfg.max_dom_nodes_scanned),
                    shadowHostLimit=int(self.cfg.shadow_host_soft_limit),
                    enableMeta=bool(self.cfg.enable_meta_scan),
                    enableRelLinks=bool(self.cfg.enable_link_rel_scan),
                    enablePerf=bool(self.cfg.enable_perf_entries),
                    maxPerf=int(self.cfg.max_perf_entries),
                    enableCssUrls=bool(self.cfg.enable_css_url_scan),
                    enableComputedBg=bool(self.cfg.enable_computed_style_bg_scan),
                    computedBgBudget=int(self.cfg.computed_style_bg_budget),
                    maxStyleChars=int(self.cfg.max_style_chars),
                    enableSrcset=bool(self.cfg.enable_srcset_scan),
                    enableScriptScan=bool(self.cfg.enable_script_scan),
                    scriptLimit=int(self.cfg.script_soft_limit),
                    maxScriptChars=int(self.cfg.max_script_chars),
                    enableJsonParse=bool(self.cfg.enable_json_parse_in_scripts),
                    maxJsonParseChars=int(self.cfg.max_json_parse_chars),
                    enableStorage=bool(self.cfg.enable_storage_scan),
                    maxStorageKeys=int(self.cfg.max_storage_keys),
                    maxStorageChars=int(self.cfg.max_storage_chars),
                    enableSpa=bool(self.cfg.enable_spa_state_scan),
                    maxSpaChars=int(self.cfg.max_spa_json_chars),
                    spaKeys=list(self.cfg.spa_state_keys),
                    enableWebpack=bool(self.cfg.enable_webpack_scan),
                    webpackLimit=int(self.cfg.webpack_module_soft_limit),
                    maxWebpackFnChars=int(self.cfg.max_webpack_fn_chars),
                    webpackUrlRegex=str(self.cfg.webpack_url_regex),
                    webpackApiHints=list(self.cfg.webpack_api_hints),
                )

                # fast pass always
                cheap = await self._safe_wait(
                    self._pw_eval(page, self._JS_PASS_CHEAP, local_cfg, log),
                    timeout_s=min(self.cfg.pass_guard_s, max(0.8, self._remaining(started, hard_cap) - self.cfg.min_seconds_reserved_for_close)),
                    label="cheap-js-pass",
                    log=log,
                    default={"items": [], "capped": False, "stage": "cheap"},
                )
                if isinstance(cheap, dict):
                    links.extend(list(cheap.get("items") or []))
                    self._log(f"Cheap pass returned {len(cheap.get('items') or [])} items.", log)

                # auto-scroll only if page is not already huge and time is available
                if self.cfg.enable_auto_scroll and not self._budget_low_for_heavy(started, hard_cap):
                    if (not self.cfg.degrade_on_large_dom) or node_count < self.cfg.large_dom_threshold:
                        await self._auto_scroll(page, min(1.8, max(0.75, self._remaining(started, hard_cap) * 0.35)), log)

                # medium pass unless page/budget suggests we should degrade
                degrade = bool(self.cfg.degrade_on_large_dom and node_count >= self.cfg.large_dom_threshold)
                if degrade:
                    self._log(f"Large DOM detected ({node_count}); downgrading heavy scans.", log)
                if not degrade and not self._budget_low_for_heavy(started, hard_cap):
                    medium = await self._safe_wait(
                        self._pw_eval(page, self._JS_PASS_MEDIUM, local_cfg, log),
                        timeout_s=min(self.cfg.pass_guard_s, max(0.9, self._remaining(started, hard_cap) - self.cfg.min_seconds_reserved_for_close)),
                        label="medium-js-pass",
                        log=log,
                        default={"items": [], "capped": False, "stage": "medium"},
                    )
                    if isinstance(medium, dict):
                        links.extend(list(medium.get("items") or []))
                        self._log(f"Medium pass returned {len(medium.get('items') or [])} items.", log)
                else:
                    self._log("Skipping medium/heavier JS pass due to low budget or degraded mode.", log)

                # optional click simulation before runtime collectors
                await self._maybe_simulate_clicks(page, started, hard_cap, log)

                # runtime collectors are cheapish and often useful
                await self._collect_json_parse_events(page, canonical_page_url, runtime_hits, log)
                await self._collect_hydration_state(page, canonical_page_url, runtime_hits, log)
                await self._collect_runtime_url_events(page, canonical_page_url, runtime_hits, log)
                await self._collect_mutation_url_events(page, canonical_page_url, runtime_hits, log)
                await self._collect_worker_events(page, canonical_page_url, runtime_hits, log)
                await self._collect_sw_events(page, canonical_page_url, runtime_hits, log)
                await self._collect_css_url_events(page, canonical_page_url, runtime_hits, log)
                await self._collect_webrtc_events(page, canonical_page_url, runtime_hits, log)

                # heavy pass is last and only if time remains
                if (not degrade) and (not self._budget_low_for_heavy(started, hard_cap)):
                    heavy = await self._safe_wait(
                        self._pw_eval(page, self._JS_PASS_HEAVY, local_cfg, log),
                        timeout_s=min(self.cfg.pass_guard_s, max(0.8, self._remaining(started, hard_cap) - self.cfg.min_seconds_reserved_for_close)),
                        label="heavy-js-pass",
                        log=log,
                        default={"items": [], "capped": False, "stage": "heavy"},
                    )
                    if isinstance(heavy, dict):
                        links.extend(list(heavy.get("items") or []))
                        self._log(f"Heavy pass returned {len(heavy.get('items') or [])} items.", log)
                else:
                    self._log("Skipping heavy JS pass due to low remaining budget or degraded mode.", log)

                # html fetch near the end but reserve time for it
                if self._remaining(started, hard_cap) > self.cfg.min_seconds_reserved_for_content:
                    try:
                        html = await self._pw_content(page, log)
                    except Exception as e:
                        self._log(f"Failed to get page content: {e}", log)
                        html = ""
                else:
                    self._log("Skipping page.content due to low remaining budget.", log)
                    html = ""

            except Exception as e:
                self._log(f"Unexpected error during JS sniff: {e}", log)
            finally:
                try:
                    await self._pw_close(page, log)
                except Exception as e:
                    self._log(f"Failed to close page: {e}", log)

            merged = self._dedupe_links(links + runtime_hits, limit=self.cfg.max_links)
            self._log(f"Finished JS sniff for {canonical_page_url}: links={len(merged)}, elapsed={time.monotonic() - started:.2f}s", log)
            return html, merged

        try:
            return await asyncio.wait_for(_run(), timeout=hard_cap)
        except asyncio.TimeoutError:
            self._log(f"Whole-run watchdog fired at {hard_cap:.2f}s; returning partial results.", log)
            merged = self._dedupe_links(links + runtime_hits, limit=self.cfg.max_links)
            try:
                await self._pw_close(page, log)
            except Exception:
                pass
            return html, merged


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

    NEW (added in this rewrite):
      - Worker/SharedWorker/Worklet visibility + postMessage URL hints (bounded)
      - Service Worker registration + ready scope/script logging
      - CSS URL mining: <link rel=preconnect/prefetch/preload> + CSS url(...) via insertRule/setProperty
      - WebRTC ICE visibility: RTCPeerConnection + iceServers (stun/turn) + basic state signals
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

        # --- runtime URL hooks (URL-only) ---
        enable_runtime_url_hooks: bool = True
        max_runtime_url_events: int = 500
        runtime_url_keywords: Set[str] = field(default_factory=lambda: {
            "api", "graphql", "manifest", "playlist", "m3u8", "mpd", "stream", "vod", "hls", "dash"
        })

        # --- mutation observer (URL-only) ---
        enable_mutation_observer: bool = True
        mutation_observer_ms: int = 1500
        max_mutation_url_events: int = 400

        # --- response header mining (URL-only) ---
        enable_response_header_mining: bool = True
        max_header_url_events: int = 200

        # --- JSON.parse hook ---
        enable_json_parse_sniff: bool = True
        json_parse_max_bytes: int = 64 * 1024  # max source string length
        json_parse_keywords: Set[str] = field(default_factory=lambda: {
            "manifest", "playlist", "m3u8", "mpd", "stream",
            "video", "audio", "hls", "dash", "api", "graphql", "next"
        })
        json_parse_store_parsed: bool = True

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

        # ---------------- NEW: Worker / SharedWorker / Worklet ----------------
        enable_worker_sniff: bool = True
        max_worker_events: int = 400
        worker_message_max_bytes: int = 4096

        # ---------------- NEW: Service Worker ----------------
        enable_service_worker_sniff: bool = True
        max_sw_events: int = 200

        # ---------------- NEW: CSS URL mining + <link rel=...> hints ----------------
        enable_css_url_sniff: bool = True
        max_css_url_events: int = 600
        css_url_max_len: int = 2048

        # ---------------- NEW: WebRTC ICE visibility ----------------
        enable_webrtc_sniff: bool = True
        max_webrtc_events: int = 200

    def __init__(self, config: Optional["RuntimeSniffer.Config"] = None, logger=None):
        self.cfg = config or self.Config()
        self.logger = logger or DEBUG_LOGGER
        self._log("RuntimeSniffer Initialized (full+workers+css+webrtc)", None)

        # keep your prior special hints
        try:
            self.cfg.json_body_url_hints.update({
                "api-v2.soundcloud.com/tracks",
                "api-v2.soundcloud.com/media",
                "client_id="
            })
        except Exception:
            pass

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

    # =====================================================================
    # Runtime URL hooks (fetch/xhr/ws/eventsource/beacon) - URL-only ring buf
    # =====================================================================

    async def _inject_runtime_url_hooks(self, context: "BrowserContext", log: Optional[List[str]]) -> None:
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
            self._log("Injected runtime URL hooks.", log)
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

    # =====================================================================
    # MutationObserver URL collector (href/src/data-*)
    # =====================================================================

    async def _inject_mutation_observer(self, context: "BrowserContext", log: Optional[List[str]]) -> None:
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

    # =====================================================================
    # Response header mining (Location/Link)
    # =====================================================================

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

    # =====================================================================
    # JSON.parse hook
    # =====================================================================

    async def _inject_json_parse_hook(self, context: "BrowserContext", log: Optional[List[str]]) -> None:
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
            self._log("Injected JSON.parse hook.", log)
        except Exception as e:
            self._log(f"Failed to inject JSON.parse hook: {e}", log)

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

    # =====================================================================
    # Hydration globals
    # =====================================================================

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

    # =====================================================================
    # Console sniff
    # =====================================================================

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

    # =====================================================================
    # WebSocket sniff
    # =====================================================================

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

    # =====================================================================
    # Request body sniff (page.route)
    # =====================================================================

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

    # =====================================================================
    # MediaSource / MSE hook
    # =====================================================================

    async def _inject_mediasource_script(self, context: "BrowserContext", log: Optional[List[str]]) -> None:
        if not self.cfg.enable_mediasource_sniff:
            return

        try:
            await context.add_init_script(
                """
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
                      try {
                        if (obj instanceof MediaSource) {
                          logMedia('createObjectURL', { url, mediaSourceType: 'MediaSource' });
                        }
                      } catch {}
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
                """
            )
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

    # =====================================================================
    # Media events (video/audio listeners, optional autoplay muted)
    # =====================================================================

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
                {"autoPlay": auto_play},
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

    # =====================================================================
    # Perf entries
    # =====================================================================

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
                regex_str,
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

    # =====================================================================
    # Storage sniff (localStorage/sessionStorage)
    # =====================================================================

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
                max_bytes,
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

    # =====================================================================
    # NEW: Worker / SharedWorker / Worklet hooks (+ postMessage URL hints)
    # =====================================================================

    async def _inject_worker_sniffer(self, context: "BrowserContext", log: Optional[List[str]]) -> None:
        if not self.cfg.enable_worker_sniff:
            return

        max_events = int(self.cfg.max_worker_events)
        max_msg = int(self.cfg.worker_message_max_bytes)

        try:
            await context.add_init_script(
                f"""
                (() => {{
                  try {{
                    const STORE = "__workerEvents";
                    const MAX = {max_events};
                    const MAX_MSG = {max_msg};

                    const out = [];
                    const seen = new Set();

                    function abs(u) {{
                      try {{ return new URL(String(u), location.href).href; }}
                      catch {{ return String(u || ""); }}
                    }}

                    function push(kind, payload) {{
                      try {{
                        const key = kind + "|" + JSON.stringify(payload || {{}});
                        if (seen.has(key)) return;
                        seen.add(key);
                        out.push(Object.assign({{ ts: Date.now(), kind }}, payload || {{}}));
                        if (out.length > MAX) out.shift();
                        window[STORE] = out;
                      }} catch (e) {{}}
                    }}

                    function extractUrls(s) {{
                      try {{
                        if (!s) return [];
                        s = String(s);
                        if (s.length > MAX_MSG) return [];
                        const rx = /\\b(?:https?|wss?):\\/\\/[^\\s"'<>]+/ig;
                        const m = s.match(rx) || [];
                        const out2 = [];
                        const set2 = new Set();
                        for (const u of m) {{
                          if (!set2.has(u)) {{ set2.add(u); out2.push(u); }}
                          if (out2.length >= 50) break;
                        }}
                        return out2;
                      }} catch (e) {{ return []; }}
                    }}

                    // Worker
                    try {{
                      const OrigWorker = window.Worker;
                      if (typeof OrigWorker === "function") {{
                        window.Worker = function(url, opts) {{
                          try {{ push("worker:new", {{ url: abs(url), hasOptions: !!opts }}); }} catch (e) {{}}
                          const w = new OrigWorker(url, opts);
                          try {{
                            const origPM = w.postMessage;
                            if (typeof origPM === "function") {{
                              w.postMessage = function(msg) {{
                                try {{
                                  if (typeof msg === "string") {{
                                    const urls = extractUrls(msg);
                                    if (urls.length) push("worker:postMessage", {{
                                      to: "worker",
                                      urls,
                                      preview: msg.slice(0, 512)
                                    }});
                                  }}
                                }} catch (e) {{}}
                                return origPM.apply(this, arguments);
                              }};
                            }}
                          }} catch (e) {{}}
                          return w;
                        }};
                        window.Worker.prototype = OrigWorker.prototype;
                      }}
                    }} catch (e) {{}}

                    // SharedWorker
                    try {{
                      const OrigShared = window.SharedWorker;
                      if (typeof OrigShared === "function") {{
                        window.SharedWorker = function(url, nameOrOpts) {{
                          try {{ push("sharedworker:new", {{ url: abs(url) }}); }} catch (e) {{}}
                          const sw = new OrigShared(url, nameOrOpts);
                          try {{
                            const p = sw && sw.port;
                            if (p && typeof p.postMessage === "function") {{
                              const origPM = p.postMessage;
                              p.postMessage = function(msg) {{
                                try {{
                                  if (typeof msg === "string") {{
                                    const urls = extractUrls(msg);
                                    if (urls.length) push("sharedworker:postMessage", {{
                                      to: "sharedworker",
                                      urls,
                                      preview: msg.slice(0, 512)
                                    }});
                                  }}
                                }} catch (e) {{}}
                                return origPM.apply(this, arguments);
                              }};
                            }}
                          }} catch (e) {{}}
                          return sw;
                        }};
                        window.SharedWorker.prototype = OrigShared.prototype;
                      }}
                    }} catch (e) {{}}

                    // Worklets: AudioWorklet.addModule(url)
                    try {{
                      // In many browsers: (new AudioContext()).audioWorklet.addModule(...)
                      const AC = window.AudioContext || window.webkitAudioContext;
                      if (typeof AC === "function" && AC.prototype) {{
                        const desc = Object.getOwnPropertyDescriptor(AC.prototype, "audioWorklet");
                        if (desc && typeof desc.get === "function") {{
                          const origGet = desc.get;
                          Object.defineProperty(AC.prototype, "audioWorklet", {{
                            get() {{
                              const aw = origGet.call(this);
                              try {{
                                if (aw && typeof aw.addModule === "function" && !aw.___sniffWrapped) {{
                                  const origAdd = aw.addModule.bind(aw);
                                  aw.addModule = function(url, options) {{
                                    try {{ push("audioWorklet:addModule", {{ url: abs(url) }}); }} catch (e) {{}}
                                    return origAdd(url, options);
                                  }};
                                  aw.___sniffWrapped = true;
                                }}
                              }} catch (e) {{}}
                              return aw;
                            }}
                          }});
                        }}
                      }}
                    }} catch (e) {{}}

                  }} catch (e) {{
                    try {{ console.log("[RuntimeSniffer] worker hook init error:", e); }} catch (_) {{}}
                  }}
                }})();
                """
            )
            self._log("Injected Worker/SharedWorker/Worklet hooks.", log)
        except Exception as e:
            self._log(f"Failed to inject worker hooks: {e}", log)

    async def _collect_worker_events(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_worker_sniff:
            return
        try:
            events = await page.evaluate(
                "() => Array.isArray(window.__workerEvents) ? window.__workerEvents : []"
            ) or []
        except Exception as e:
            self._log(f"Error reading __workerEvents: {e}", log)
            return
        if not events:
            return

        runtime_hits.append({
            "url": canonical_page_url,
            "json": {"worker_events": events[: int(self.cfg.max_worker_events)]},
            "source_page": canonical_page_url,
        })
        self._log(f"Worker events captured: {len(events)}", log)

    # =====================================================================
    # NEW: Service Worker register + ready
    # =====================================================================

    async def _inject_service_worker_sniffer(self, context: "BrowserContext", log: Optional[List[str]]) -> None:
        if not self.cfg.enable_service_worker_sniff:
            return

        max_events = int(self.cfg.max_sw_events)
        try:
            await context.add_init_script(
                f"""
                (() => {{
                  try {{
                    const STORE = "__swEvents";
                    const MAX = {max_events};
                    const out = [];
                    const seen = new Set();

                    function abs(u) {{
                      try {{ return new URL(String(u), location.href).href; }}
                      catch {{ return String(u || ""); }}
                    }}

                    function push(kind, payload) {{
                      try {{
                        const key = kind + "|" + JSON.stringify(payload || {{}});
                        if (seen.has(key)) return;
                        seen.add(key);
                        out.push(Object.assign({{ ts: Date.now(), kind }}, payload || {{}}));
                        if (out.length > MAX) out.shift();
                        window[STORE] = out;
                      }} catch (e) {{}}
                    }}

                    const sw = navigator && navigator.serviceWorker;
                    if (!sw) return;

                    // wrap register(scriptURL)
                    try {{
                      const origReg = sw.register && sw.register.bind(sw);
                      if (typeof origReg === "function") {{
                        sw.register = function(scriptURL, options) {{
                          try {{
                            push("sw:register", {{
                              scriptURL: abs(scriptURL),
                              scope: (options && options.scope) ? abs(options.scope) : null
                            }});
                          }} catch (e) {{}}
                          return origReg(scriptURL, options);
                        }};
                      }}
                    }} catch (e) {{}}

                    // observe ready promise resolution
                    try {{
                      const p = sw.ready;
                      if (p && typeof p.then === "function") {{
                        p.then((reg) => {{
                          try {{
                            const scope = reg && reg.scope ? String(reg.scope) : null;
                            const active = reg && reg.active;
                            const scriptURL = active && active.scriptURL ? String(active.scriptURL) : null;
                            push("sw:ready", {{
                              scope: scope ? abs(scope) : null,
                              scriptURL: scriptURL ? abs(scriptURL) : null
                            }});
                          }} catch (e) {{}}
                        }}).catch(() => {{}});
                      }}
                    }} catch (e) {{}}

                  }} catch (e) {{
                    try {{ console.log("[RuntimeSniffer] service worker init error:", e); }} catch (_) {{}}
                  }}
                }})();
                """
            )
            self._log("Injected Service Worker hooks (register/ready).", log)
        except Exception as e:
            self._log(f"Failed to inject Service Worker hooks: {e}", log)

    async def _collect_sw_events(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_service_worker_sniff:
            return
        try:
            events = await page.evaluate(
                "() => Array.isArray(window.__swEvents) ? window.__swEvents : []"
            ) or []
        except Exception as e:
            self._log(f"Error reading __swEvents: {e}", log)
            return
        if not events:
            return

        runtime_hits.append({
            "url": canonical_page_url,
            "json": {"service_worker_events": events[: int(self.cfg.max_sw_events)]},
            "source_page": canonical_page_url,
        })
        self._log(f"Service Worker events captured: {len(events)}", log)

    # =====================================================================
    # NEW: CSS URL mining + <link rel=preconnect/prefetch/preload> hints
    # =====================================================================

    async def _inject_css_url_sniffer(self, context: "BrowserContext", log: Optional[List[str]]) -> None:
        if not self.cfg.enable_css_url_sniff:
            return

        max_events = int(self.cfg.max_css_url_events)
        max_len = int(self.cfg.css_url_max_len)

        try:
            await context.add_init_script(
                f"""
                (() => {{
                  try {{
                    const STORE = "__cssUrlEvents";
                    const MAX = {max_events};
                    const MAXLEN = {max_len};
                    const out = [];
                    const seen = new Set();

                    function abs(u) {{
                      try {{ return new URL(String(u), location.href).href; }}
                      catch {{ return String(u || ""); }}
                    }}

                    function push(kind, url, extra) {{
                      try {{
                        if (!url) return;
                        url = String(url);
                        if (url.length > MAXLEN) return;
                        const u = abs(url);
                        const low = u.toLowerCase();
                        if (low.startsWith("blob:") || low.startsWith("data:") || low.startsWith("javascript:")) return;
                        const key = kind + "|" + u;
                        if (seen.has(key)) return;
                        seen.add(key);
                        out.push(Object.assign({{ ts: Date.now(), kind, url: u }}, extra || {{}}));
                        if (out.length > MAX) out.shift();
                        window[STORE] = out;
                      }} catch (e) {{}}
                    }}

                    function extractCssUrls(txt) {{
                      try {{
                        if (!txt) return [];
                        txt = String(txt);
                        if (txt.length > 20000) txt = txt.slice(0, 20000);
                        const rx = /url\\(\\s*(['"]?)([^'")]+)\\1\\s*\\)/ig;
                        const out2 = [];
                        const set2 = new Set();
                        let m;
                        while ((m = rx.exec(txt)) !== null) {{
                          const u = m[2];
                          if (!u) continue;
                          if (set2.has(u)) continue;
                          set2.add(u);
                          out2.push(u);
                          if (out2.length >= 50) break;
                        }}
                        return out2;
                      }} catch (e) {{ return []; }}
                    }}

                    // initial scan of <link rel=... href> hints
                    function scanLinkHints() {{
                      try {{
                        const rels = new Set(["preconnect","prefetch","preload","dns-prefetch","modulepreload"]);
                        const links = document.querySelectorAll ? document.querySelectorAll("link[rel][href]") : [];
                        for (const el of links) {{
                          const rel = (el.getAttribute("rel") || "").toLowerCase().trim();
                          if (!rels.has(rel)) continue;
                          const href = el.getAttribute("href");
                          if (href) push("linkhint:"+rel, href);
                        }}
                      }} catch (e) {{}}
                    }}

                    if (document.readyState === "loading") {{
                      document.addEventListener("DOMContentLoaded", scanLinkHints, {{ once: true }});
                    }} else {{
                      scanLinkHints();
                    }}

                    // Hook CSSStyleSheet.insertRule
                    try {{
                      const origIns = CSSStyleSheet && CSSStyleSheet.prototype && CSSStyleSheet.prototype.insertRule;
                      if (typeof origIns === "function") {{
                        CSSStyleSheet.prototype.insertRule = function(rule, index) {{
                          try {{
                            const urls = extractCssUrls(rule);
                            for (const u of urls) push("css:insertRule", u);
                          }} catch (e) {{}}
                          return origIns.apply(this, arguments);
                        }};
                      }}
                    }} catch (e) {{}}

                    // Hook style.setProperty
                    try {{
                      const origSP = CSSStyleDeclaration && CSSStyleDeclaration.prototype && CSSStyleDeclaration.prototype.setProperty;
                      if (typeof origSP === "function") {{
                        CSSStyleDeclaration.prototype.setProperty = function(name, value, priority) {{
                          try {{
                            const urls = extractCssUrls(value);
                            for (const u of urls) push("css:setProperty", u, {{ prop: String(name || "") }});
                          }} catch (e) {{}}
                          return origSP.apply(this, arguments);
                        }};
                      }}
                    }} catch (e) {{}}

                  }} catch (e) {{
                    try {{ console.log("[RuntimeSniffer] css init error:", e); }} catch (_) {{}}
                  }}
                }})();
                """
            )
            self._log("Injected CSS URL sniffer + link-hints.", log)
        except Exception as e:
            self._log(f"Failed to inject CSS URL sniffer: {e}", log)

    async def _collect_css_url_events(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_css_url_sniff:
            return
        try:
            events = await page.evaluate(
                "() => Array.isArray(window.__cssUrlEvents) ? window.__cssUrlEvents : []"
            ) or []
        except Exception as e:
            self._log(f"Error reading __cssUrlEvents: {e}", log)
            return
        if not events:
            return

        runtime_hits.append({
            "url": canonical_page_url,
            "json": {"css_url_events": events[: int(self.cfg.max_css_url_events)]},
            "source_page": canonical_page_url,
        })
        self._log(f"CSS URL events captured: {len(events)}", log)

    # =====================================================================
    # NEW: WebRTC ICE visibility (RTCPeerConnection + iceServers)
    # =====================================================================

    async def _inject_webrtc_sniffer(self, context: "BrowserContext", log: Optional[List[str]]) -> None:
        if not self.cfg.enable_webrtc_sniff:
            return

        max_events = int(self.cfg.max_webrtc_events)

        try:
            await context.add_init_script(
                f"""
                (() => {{
                  try {{
                    const STORE = "__webrtcEvents";
                    const MAX = {max_events};
                    const out = [];
                    const seen = new Set();

                    function push(kind, payload) {{
                      try {{
                        const key = kind + "|" + JSON.stringify(payload || {{}});
                        if (seen.has(key)) return;
                        seen.add(key);
                        out.push(Object.assign({{ ts: Date.now(), kind }}, payload || {{}}));
                        if (out.length > MAX) out.shift();
                        window[STORE] = out;
                      }} catch (e) {{}}
                    }}

                    function normIceServers(cfg) {{
                      try {{
                        const ics = (cfg && cfg.iceServers) ? cfg.iceServers : [];
                        const out2 = [];
                        for (const s of (ics || [])) {{
                          if (!s) continue;
                          let urls = s.urls || s.url;
                          if (!urls) continue;
                          if (!Array.isArray(urls)) urls = [urls];
                          for (const u of urls) {{
                            const us = String(u || "");
                            if (!us) continue;
                            if (/^(stun:|turn:|turns:)/i.test(us)) out2.push(us);
                          }}
                        }}
                        return out2.slice(0, 30);
                      }} catch (e) {{ return []; }}
                    }}

                    const OrigPC = window.RTCPeerConnection || window.webkitRTCPeerConnection;
                    if (typeof OrigPC !== "function") return;

                    function WrappedPC(cfg, constraints) {{
                      try {{
                        const ice = normIceServers(cfg);
                        push("webrtc:pc", {{ iceServers: ice }});
                      }} catch (e) {{}}

                      const pc = new OrigPC(cfg, constraints);

                      try {{
                        pc.addEventListener("icecandidate", (ev) => {{
                          try {{
                            const c = ev && ev.candidate && ev.candidate.candidate;
                            if (c && /\\b(?:stun|turn|udp|tcp)\\b/i.test(c)) {{
                              push("webrtc:icecandidate", {{ preview: String(c).slice(0, 300) }});
                            }}
                          }} catch (e) {{}}
                        }});
                      }} catch (e) {{}}

                      try {{
                        pc.addEventListener("connectionstatechange", () => {{
                          try {{ push("webrtc:connectionstate", {{ state: String(pc.connectionState || "") }}); }} catch (e) {{}}
                        }});
                      }} catch (e) {{}}

                      try {{
                        pc.addEventListener("iceconnectionstatechange", () => {{
                          try {{ push("webrtc:iceconnectionstate", {{ state: String(pc.iceConnectionState || "") }}); }} catch (e) {{}}
                        }});
                      }} catch (e) {{}}

                      // optional: timing signals
                      try {{
                        const origOffer = pc.createOffer && pc.createOffer.bind(pc);
                        if (typeof origOffer === "function") {{
                          pc.createOffer = function() {{
                            push("webrtc:createOffer", {{}});
                            return origOffer.apply(this, arguments);
                          }};
                        }}
                      }} catch (e) {{}}

                      try {{
                        const origSRD = pc.setRemoteDescription && pc.setRemoteDescription.bind(pc);
                        if (typeof origSRD === "function") {{
                          pc.setRemoteDescription = function(desc) {{
                            try {{
                              const t = desc && desc.type ? String(desc.type) : null;
                              push("webrtc:setRemoteDescription", {{ type: t }});
                            }} catch (e) {{}}
                            return origSRD.apply(this, arguments);
                          }};
                        }}
                      }} catch (e) {{}}

                      try {{
                        const origSLD = pc.setLocalDescription && pc.setLocalDescription.bind(pc);
                        if (typeof origSLD === "function") {{
                          pc.setLocalDescription = function(desc) {{
                            try {{
                              const t = desc && desc.type ? String(desc.type) : null;
                              push("webrtc:setLocalDescription", {{ type: t }});
                            }} catch (e) {{}}
                            return origSLD.apply(this, arguments);
                          }};
                        }}
                      }} catch (e) {{}}

                      return pc;
                    }}

                    WrappedPC.prototype = OrigPC.prototype;
                    if (window.RTCPeerConnection) window.RTCPeerConnection = WrappedPC;
                    if (window.webkitRTCPeerConnection) window.webkitRTCPeerConnection = WrappedPC;

                  }} catch (e) {{
                    try {{ console.log("[RuntimeSniffer] webrtc init error:", e); }} catch (_) {{}}
                  }}
                }})();
                """
            )
            self._log("Injected WebRTC sniffer (RTCPeerConnection).", log)
        except Exception as e:
            self._log(f"Failed to inject WebRTC sniffer: {e}", log)

    async def _collect_webrtc_events(
        self,
        page: "Page",
        canonical_page_url: str,
        runtime_hits: List[Dict[str, Any]],
        log: Optional[List[str]],
    ) -> None:
        if not self.cfg.enable_webrtc_sniff:
            return
        try:
            events = await page.evaluate(
                "() => Array.isArray(window.__webrtcEvents) ? window.__webrtcEvents : []"
            ) or []
        except Exception as e:
            self._log(f"Error reading __webrtcEvents: {e}", log)
            return
        if not events:
            return

        runtime_hits.append({
            "url": canonical_page_url,
            "json": {"webrtc_events": events[: int(self.cfg.max_webrtc_events)]},
            "source_page": canonical_page_url,
        })
        self._log(f"WebRTC events captured: {len(events)}", log)

    # ------------------------------ NEW: link promotion helpers ------------------------------ #

    def _push_link_hit(
            self,
            out: List[Dict[str, Any]],
            seen: Set[str],
            *,
            url: Any,
            source_page: str,
            tag: str,
            meta: Optional[Dict[str, Any]] = None,
    ) -> None:
        try:
            u = _canonicalize_url(str(url or "").strip())
        except Exception:
            u = str(url or "").strip()

        if not u:
            return

        low = u.lower()
        if low.startswith(("blob:", "data:", "javascript:", "mailto:", "tel:")):
            return

        key = f"{tag}|{u}"
        if key in seen:
            return
        seen.add(key)

        out.append({
            "url": u,
            "tag": tag,
            "source_page": source_page,
            "json": meta or {},
        })

    def _deep_collect_urls(self, obj: Any, *, limit: int = 2500) -> List[str]:
        out: List[str] = []
        seen: Set[str] = set()
        stack: List[Any] = [obj]

        while stack and len(out) < limit:
            cur = stack.pop()
            if cur is None:
                continue

            if isinstance(cur, str):
                s = cur.strip()
                if s.startswith(("http://", "https://", "ws://", "wss://")):
                    cu = _canonicalize_url(s)
                    if cu and cu not in seen:
                        seen.add(cu)
                        out.append(cu)
                else:
                    for u in self._extract_urls_from_text(s):
                        cu = _canonicalize_url(u)
                        if cu and cu not in seen:
                            seen.add(cu)
                            out.append(cu)
                continue

            if isinstance(cur, dict):
                stack.extend(cur.values())
                continue

            if isinstance(cur, (list, tuple, set)):
                stack.extend(list(cur))
                continue

        return out

    async def _collect_dom_linkish_hits(
            self,
            page: "Page",
            canonical_page_url: str,
            out: List[Dict[str, Any]],
            seen: Set[str],
            log: Optional[List[str]],
    ) -> None:
        try:
            items = await page.evaluate(
                """
                () => {
                  const out = [];
                  const seen = new Set();

                  function push(url, tag, text) {
                    try {
                      url = String(url || "").trim();
                      if (!url) return;
                      const low = url.toLowerCase();
                      if (
                        low === "#" ||
                        low.startsWith("javascript:") ||
                        low.startsWith("mailto:") ||
                        low.startsWith("tel:") ||
                        low.startsWith("data:")
                      ) return;

                      const key = `${tag}|${url}`;
                      if (seen.has(key)) return;
                      seen.add(key);
                      out.push({
                        url,
                        tag,
                        text: String(text || "").trim().slice(0, 200)
                      });
                    } catch (_) {}
                  }

                  for (const el of document.querySelectorAll("a[href], area[href]")) {
                    push(
                      el.getAttribute("href"),
                      (el.tagName || "").toLowerCase(),
                      el.innerText || el.textContent || el.getAttribute("title") || el.getAttribute("aria-label") || ""
                    );
                  }

                  for (const el of document.querySelectorAll("iframe[src], frame[src], img[src], video[src], audio[src], source[src], embed[src]")) {
                    push(
                      el.getAttribute("src"),
                      (el.tagName || "").toLowerCase(),
                      el.getAttribute("title") || el.getAttribute("alt") || ""
                    );
                  }

                  for (const el of document.querySelectorAll("form[action]")) {
                    push(
                      el.getAttribute("action"),
                      "form",
                      el.getAttribute("name") || el.getAttribute("id") || ""
                    );
                  }

                  for (const el of document.querySelectorAll("link[href]")) {
                    push(
                      el.getAttribute("href"),
                      "link",
                      el.getAttribute("rel") || ""
                    );
                  }

                  for (const el of document.querySelectorAll("meta[content]")) {
                    const p = (el.getAttribute("property") || el.getAttribute("name") || "").toLowerCase();
                    if (
                      p.includes("og:url") ||
                      p.includes("og:image") ||
                      p.includes("og:video") ||
                      p.includes("twitter:image") ||
                      p.includes("twitter:player") ||
                      p === "canonical"
                    ) {
                      push(el.getAttribute("content"), "meta", p);
                    }
                  }

                  for (const el of document.querySelectorAll("[data-href], [data-url], [data-src], [data-video], [onclick]")) {
                    push(el.getAttribute("data-href"), "data-href", "");
                    push(el.getAttribute("data-url"), "data-url", "");
                    push(el.getAttribute("data-src"), "data-src", "");
                    push(el.getAttribute("data-video"), "data-video", "");

                    const onclick = el.getAttribute("onclick") || "";
                    const matches = onclick.match(/https?:\\/\\/[^"'\\s<>]+/ig) || [];
                    for (const u of matches) push(u, "onclick", "");
                  }

                  return out.slice(0, 4000);
                }
                """
            ) or []
        except Exception as e:
            self._log(f"DOM link harvest failed: {e}", log)
            return

        added = 0
        for it in items:
            if not isinstance(it, dict):
                continue
            raw = str(it.get("url") or "").strip()
            if not raw:
                continue
            full = urljoin(canonical_page_url, raw)

            before = len(out)
            self._push_link_hit(
                out,
                seen,
                url=full,
                source_page=canonical_page_url,
                tag=str(it.get("tag") or "dom"),
                meta={"text": str(it.get("text") or ""), "reason": "dom-harvest"},
            )
            if len(out) > before:
                added += 1

        self._log(f"DOM link harvest added {added} link(s).", log)

    def _promote_runtime_hits_to_links(
            self,
            runtime_hits: List[Dict[str, Any]],
            canonical_page_url: str,
            out: List[Dict[str, Any]],
            seen: Set[str],
    ) -> None:
        for hit in runtime_hits:
            if not isinstance(hit, dict):
                continue

            # 1) direct top-level url
            top_url = str(hit.get("url") or "").strip()
            if top_url and top_url != canonical_page_url:
                self._push_link_hit(
                    out,
                    seen,
                    url=top_url,
                    source_page=canonical_page_url,
                    tag=str(hit.get("tag") or "runtime"),
                    meta={"reason": "top-level-runtime-hit"},
                )

            # 2) nested payload urls
            payload = hit.get("json")
            for u in self._deep_collect_urls(payload, limit=250):
                self._push_link_hit(
                    out,
                    seen,
                    url=u,
                    source_page=canonical_page_url,
                    tag="runtime_nested",
                    meta={"reason": "nested-runtime-url"},
                )

            # 3) special-case response header miner shape:
            #    {"url": resp.url, "json": {"header": k, "url": u}}
            if isinstance(payload, dict):
                nested_u = str(payload.get("url") or "").strip()
                if nested_u and nested_u != top_url:
                    self._push_link_hit(
                        out,
                        seen,
                        url=nested_u,
                        source_page=canonical_page_url,
                        tag=str(payload.get("header") or "runtime_header"),
                        meta={"reason": "promoted-nested-url"},
                    )
    # =====================================================================
    # Main entry
    # =====================================================================

    # =====================================================================
    # Main entry
    # =====================================================================

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
        self.cfg.timeout = tmo
        canonical_page_url = _canonicalize_url(page_url)

        runtime_hits: List[Dict[str, Any]] = []
        promoted_links: List[Dict[str, Any]] = []
        seen_links: Set[str] = set()

        # ------------------------------------------------------------
        # Context-level hooks (MUST run before new_page / navigation)
        # ------------------------------------------------------------
        await self._inject_mediasource_script(context, log)
        await self._inject_json_parse_hook(context, log)
        await self._inject_runtime_url_hooks(context, log)
        await self._inject_mutation_observer(context, log)

        # NEW: workers/sw/css/webrtc
        await self._inject_worker_sniffer(context, log)
        await self._inject_service_worker_sniffer(context, log)
        await self._inject_css_url_sniffer(context, log)
        await self._inject_webrtc_sniffer(context, log)

        page: Page = await context.new_page()
        html: str = ""
        wait_mode = getattr(self.cfg, "goto_wait_until", "domcontentloaded")
        goto_timeout_ms = max(35000, int(tmo * 1000))

        # Attach page-level hooks BEFORE navigation
        self._attach_console_sniffer(page, runtime_hits, canonical_page_url, log)
        self._attach_websocket_sniffer(page, runtime_hits, canonical_page_url, log)
        if self.cfg.enable_response_header_mining:
            self._attach_response_header_miner(page, runtime_hits, canonical_page_url, log)
        await self._attach_request_body_sniffer(page, runtime_hits, canonical_page_url, log)

        self._log(f"Start runtime sniff: {canonical_page_url} timeout={tmo}s", log)

        try:
            nav_modes: List[str] = []
            for mode in (wait_mode, "commit", "domcontentloaded", "load"):
                mode = str(mode or "").strip() or "domcontentloaded"
                if mode not in nav_modes:
                    nav_modes.append(mode)

            for mode in nav_modes:
                try:
                    await page.goto(
                        canonical_page_url,
                        wait_until=mode,
                        timeout=goto_timeout_ms,
                    )
                    if mode != wait_mode:
                        self._log(f"goto recovered using wait_until={mode}", log)
                    break
                except Exception as e:
                    self._log(f"goto timeout on {canonical_page_url} (wait_until={mode}): {e}", log)

            # Let page settle a bit
            await page.wait_for_timeout(int(tmo * 1000 * 0.2))

            # Best-effort "play" poke
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

            # runtime URL hook ring buffer
            await self._collect_runtime_url_events(page, canonical_page_url, runtime_hits, log)

            # mutation observer URL ring buffer
            await self._collect_mutation_url_events(page, canonical_page_url, runtime_hits, log)

            # NEW collectors: worker/sw/css/webrtc
            await self._collect_worker_events(page, canonical_page_url, runtime_hits, log)
            await self._collect_sw_events(page, canonical_page_url, runtime_hits, log)
            await self._collect_css_url_events(page, canonical_page_url, runtime_hits, log)
            await self._collect_webrtc_events(page, canonical_page_url, runtime_hits, log)

            try:
                html = await page.content()
            except Exception as e:
                self._log(f"Failed to get page content: {e}", log)
                html = ""

            # NEW: direct DOM href/src/action/meta harvest
            await self._collect_dom_linkish_hits(
                page,
                canonical_page_url,
                promoted_links,
                seen_links,
                log,
            )

            # NEW: raw absolute URL harvest from HTML snapshot
            try:
                for u in self._extract_urls_from_text(html)[:500]:
                    self._push_link_hit(
                        promoted_links,
                        seen_links,
                        url=u,
                        source_page=canonical_page_url,
                        tag="html_url",
                        meta={"reason": "html-regex"},
                    )
            except Exception:
                pass

            # NEW: flatten runtime hits into real top-level links
            self._promote_runtime_hits_to_links(
                runtime_hits,
                canonical_page_url,
                promoted_links,
                seen_links,
            )

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

        merged_hits: List[Dict[str, Any]] = []
        seen_merged: Set[str] = set()

        # Keep original rich runtime hits first
        for hit in runtime_hits:
            if not isinstance(hit, dict):
                continue
            key = f"orig|{str(hit.get('url') or '')}|{str(hit.get('json') or '')[:256]}"
            if key in seen_merged:
                continue
            seen_merged.add(key)
            merged_hits.append(hit)

        # Then append promoted real links
        for hit in promoted_links:
            if not isinstance(hit, dict):
                continue
            key = f"link|{str(hit.get('tag') or '')}|{str(hit.get('url') or '')}"
            if key in seen_merged:
                continue
            seen_merged.add(key)
            merged_hits.append(hit)

        self._log(
            f"Finished runtime sniff for {canonical_page_url}: raw_hits={len(runtime_hits)} promoted_links={len(promoted_links)} total={len(merged_hits)}",
            log,
        )
        return html, merged_hits
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
    # NEW helpers: URL promotion / normalization
    # ------------------------------------------------------------------ #
    def _extract_urls_from_text(self, s: str) -> List[str]:
        import re

        if not s:
            return []
        rx = re.compile(r"\b(?:https?|wss?)://[^\s\"'<>]+", re.IGNORECASE)
        out: List[str] = []
        seen: Set[str] = set()
        for m in rx.findall(s):
            if m not in seen:
                seen.add(m)
                out.append(m)
        return out

    def _absolutize_url(self, page_url: str, raw_url: str) -> str:
        from urllib.parse import urljoin

        raw = str(raw_url or "").strip()
        if not raw:
            return ""
        if raw.startswith(("javascript:", "mailto:", "tel:", "data:")):
            return ""
        try:
            return urljoin(page_url, raw)
        except Exception:
            return raw

    def _route_from_url(self, url: str) -> str:
        from urllib.parse import urlparse

        try:
            return str(urlparse(url).path or "")
        except Exception:
            return ""

    def _normalize_hit_urls(self, page_url: str, hits: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        out: List[Dict[str, Any]] = []
        for hit in hits or []:
            if not isinstance(hit, dict):
                continue

            h = dict(hit)
            raw_url = str(h.get("url") or "").strip()
            raw_route = str(h.get("route") or "").strip()

            candidate = raw_url or raw_route or page_url
            abs_url = self._absolutize_url(page_url, candidate) or candidate or page_url
            route = raw_route or self._route_from_url(abs_url)

            h["url"] = abs_url
            h["route"] = route
            out.append(h)
        return out

    def _dedupe_hits(self, hits: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        out: List[Dict[str, Any]] = []
        seen: Set[Tuple[str, str, str]] = set()

        for hit in hits or []:
            if not isinstance(hit, dict):
                continue
            key = (
                str(hit.get("tag") or ""),
                str(hit.get("kind") or ""),
                str(hit.get("url") or ""),
            )
            if key in seen:
                continue
            seen.add(key)
            out.append(hit)
        return out

    async def _collect_dom_link_hits(self, page, page_url: str, log: List[str]) -> List[Dict[str, Any]]:
        dom_hits: List[Dict[str, Any]] = []

        try:
            raw_items = await page.evaluate(
                """
                () => {
                  const out = [];
                  const seen = new Set();

                  function push(url, kind, text) {
                    try {
                      url = String(url || "").trim();
                      if (!url) return;
                      const low = url.toLowerCase();
                      if (
                        low === "#" ||
                        low.startsWith("javascript:") ||
                        low.startsWith("mailto:") ||
                        low.startsWith("tel:") ||
                        low.startsWith("data:")
                      ) return;

                      const key = `${kind}|${url}`;
                      if (seen.has(key)) return;
                      seen.add(key);

                      out.push({
                        url,
                        kind,
                        text: String(text || "").trim().slice(0, 200)
                      });
                    } catch (_) {}
                  }

                  for (const el of document.querySelectorAll("a[href], area[href]")) {
                    push(
                      el.getAttribute("href"),
                      "dom_href",
                      el.innerText || el.textContent || el.getAttribute("title") || el.getAttribute("aria-label") || ""
                    );
                  }

                  for (const el of document.querySelectorAll("iframe[src], frame[src], img[src], video[src], audio[src], source[src], embed[src]")) {
                    push(
                      el.getAttribute("src"),
                      "dom_src",
                      el.getAttribute("title") || el.getAttribute("alt") || ""
                    );
                  }

                  for (const el of document.querySelectorAll("form[action]")) {
                    push(
                      el.getAttribute("action"),
                      "dom_action",
                      el.getAttribute("name") || el.getAttribute("id") || ""
                    );
                  }

                  for (const el of document.querySelectorAll("link[href]")) {
                    push(
                      el.getAttribute("href"),
                      "dom_link_tag",
                      el.getAttribute("rel") || ""
                    );
                  }

                  for (const el of document.querySelectorAll("meta[content]")) {
                    const p = (el.getAttribute("property") || el.getAttribute("name") || "").toLowerCase();
                    if (
                      p.includes("og:url") ||
                      p.includes("og:image") ||
                      p.includes("og:video") ||
                      p.includes("twitter:image") ||
                      p.includes("twitter:player") ||
                      p === "canonical"
                    ) {
                      push(el.getAttribute("content"), "dom_meta", p);
                    }
                  }

                  for (const el of document.querySelectorAll("[data-href], [data-url], [data-src], [data-video], [onclick]")) {
                    push(el.getAttribute("data-href"), "dom_data_href", "");
                    push(el.getAttribute("data-url"), "dom_data_url", "");
                    push(el.getAttribute("data-src"), "dom_data_src", "");
                    push(el.getAttribute("data-video"), "dom_data_video", "");

                    const onclick = el.getAttribute("onclick") || "";
                    const matches = onclick.match(/https?:\\/\\/[^"'\\s<>]+/ig) || [];
                    for (const u of matches) push(u, "dom_onclick", "");
                  }

                  return out.slice(0, 4000);
                }
                """
            ) or []
        except Exception as e:
            self._log(f"DOM link harvest error on {page_url}: {e}", log)
            return dom_hits

        for item in raw_items:
            if not isinstance(item, dict):
                continue

            raw = str(item.get("url") or "").strip()
            if not raw:
                continue

            full = self._absolutize_url(page_url, raw)
            if not full:
                continue

            dom_hits.append(
                {
                    "page": page_url,
                    "url": full,
                    "route": self._route_from_url(full),
                    "tag": "react_link",
                    "kind": str(item.get("kind") or "dom_link"),
                    "meta": {
                        "text": str(item.get("text") or ""),
                        "source": "dom_harvest",
                    },
                }
            )

        self._log(f"DOM link harvest found {len(dom_hits)} link(s) on {page_url}", log)
        return dom_hits

    def _collect_html_url_hits(self, page_url: str, html: str) -> List[Dict[str, Any]]:
        hits: List[Dict[str, Any]] = []

        for u in self._extract_urls_from_text(html)[:500]:
            full = self._absolutize_url(page_url, u)
            if not full:
                continue
            hits.append(
                {
                    "page": page_url,
                    "url": full,
                    "route": self._route_from_url(full),
                    "tag": "react_link",
                    "kind": "html_url",
                    "meta": {
                        "source": "html_regex",
                    },
                }
            )

        return hits

    # ------------------------------------------------------------------ #
    # Public API (matches other sniffers)
    # ------------------------------------------------------------------ #
    async def sniff(
            self,
            context,  # Playwright BrowserContext
            page_url: str,
            timeout: float,
            log: List[str],
            extensions=None,  # kept for signature compatibility; usually unused
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
        self.cfg.timeout = timeout

        try:
            page = await context.new_page()

            # Install instrumentation BEFORE first navigation so early SPA boot is captured
            try:
                await self._install_instrumentation(page, page_url, log)
            except Exception as e:
                self._log(f"Pre-navigation instrumentation error on {page_url}: {e}", log)

            nav_modes: List[str] = []
            for mode in ("domcontentloaded", "commit", "load"):
                if mode not in nav_modes:
                    nav_modes.append(mode)

            loaded = False
            for mode in nav_modes:
                try:
                    await page.goto(
                        page_url,
                        wait_until=mode,
                        timeout=max(15000, int(timeout * 1000)),
                    )
                    loaded = True
                    if mode != "domcontentloaded":
                        self._log(f"goto recovered using wait_until={mode} for {page_url}", log)
                    break
                except PWTimeoutError:
                    self._log(f"Timeout while loading {page_url} with wait_until={mode}", log)
                except Exception as e:
                    self._log(f"Error loading {page_url} with wait_until={mode}: {e}", log)

            # Give React / SPA some time to bootstrap & navigate
            await page.wait_for_timeout(self.cfg.wait_after_load_ms)

            # Grab HTML
            try:
                html = await page.content()
            except Exception as e:
                self._log(f"Error getting HTML for {page_url}: {e}", log)

            # Extract JS / React instrumentation hits into memory
            try:
                raw_hits = await self._collect_raw_hits(page, page_url, log)
                self._ingest_raw_hits(raw_hits, page_url, log)
                hits = self._materialize_hits(page_url)
            except Exception as e:
                self._log(f"Error collecting instrumentation hits for {page_url}: {e}", log)

            # NEW: direct DOM link harvest
            try:
                dom_hits = await self._collect_dom_link_hits(page, page_url, log)
                hits.extend(dom_hits)
            except Exception as e:
                self._log(f"Error collecting DOM links for {page_url}: {e}", log)

            # NEW: raw absolute URLs from HTML snapshot
            try:
                html_hits = self._collect_html_url_hits(page_url, html or "")
                hits.extend(html_hits)
            except Exception as e:
                self._log(f"Error collecting HTML URLs for {page_url}: {e}", log)

            # Normalize relative routes/URLs into absolute URLs
            hits = self._normalize_hit_urls(page_url, hits)

            # Dedupe final output
            hits = self._dedupe_hits(hits)

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
        if low.startswith(("blob:", "data:", "javascript:", "mailto:", "tel:", "#")):
            return ""

        # schemeless -> https
        if raw.startswith("//"):
            raw = "https:" + raw

        try:
            parsed = urlparse(raw)
            has_scheme = bool(parsed.scheme)
        except Exception:
            has_scheme = False

        # relative / query-only / bare path -> absolute
        if not has_scheme:
            if raw.startswith(("/", "./", "../", "?")):
                raw = urljoin(base_url, raw)
            elif " " not in raw and ("/" in raw or "." in raw):
                raw = urljoin(base_url, raw)
            else:
                return ""

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
                    collected.extend(self._extract_value_urls(page_url, val, direct=True))

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
                    meta_urls.extend(self._extract_value_urls(page_url, c, direct=True))
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

    def _dedupe_hits(self, hits: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        out: List[Dict[str, Any]] = []
        seen: Set[Tuple[str, str, str, str]] = set()

        for hit in hits or []:
            if not isinstance(hit, dict):
                continue

            meta = hit.get("meta") or {}
            source = str(meta.get("source") or "")
            key = (
                str(hit.get("tag") or ""),
                str(hit.get("kind") or ""),
                str(hit.get("url") or ""),
                source,
            )
            if key in seen:
                continue
            seen.add(key)
            out.append(hit)

        return out
    def _extract_value_urls(self, base_url: str, value: str, *, direct: bool = False) -> List[str]:
        """
        Extract URLs from a single DOM/backend value.

        direct=True is for href/src/action/content-like fields where the whole value
        may itself be a relative URL such as:
          "watch"
          "api/v1/items"
          "?page=2"
          "./video.mp4"
        """
        raw = (value or "").strip()
        if not raw:
            return []

        seen: Set[str] = set()
        out: List[str] = []

        def add_candidate(candidate: str) -> None:
            try:
                u = self._normalize_candidate(base_url, candidate)
            except Exception:
                u = ""
            if not u or not self._is_allowed_scheme(u):
                return
            if u in seen:
                return
            seen.add(u)
            out.append(u)

        # absolute / schemeless URLs embedded in text
        for u in self._extract_urls_from_text(base_url, raw):
            add_candidate(u)

        if direct:
            low = raw.lower()

            if not low.startswith(("blob:", "data:", "javascript:", "mailto:", "tel:", "#")):
                # explicit relative/query/schemeless
                if raw.startswith(("//", "/", "./", "../", "?")):
                    add_candidate(raw)

                # bare relative path/file/endpoint
                elif " " not in raw:
                    if (
                            "/" in raw
                            or "." in raw
                            or raw.lower().startswith(("api", "graphql", "rest", "rpc", "v1/", "v2/"))
                    ):
                        add_candidate(raw)

        return out
    # ------------------------------------------------------------------ #
    # Public API (matches other sniffers)
    # ------------------------------------------------------------------ #
    async def sniff(
            self,
            context,  # Playwright BrowserContext
            page_url: str,
            timeout: float,
            log: List[str],
            extensions=None,  # signature compatibility; unused
    ) -> Tuple[str, List[Dict[str, Any]]]:
        if not context:
            self._log("No BrowserContext supplied; skipping.", log)
            return "", []

        tmo = float(timeout or self.cfg.timeout)
        self.cfg.timeout = tmo
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

            # Navigate with small fallback ladder
            nav_modes: List[str] = []
            for mode in ("domcontentloaded", "commit", "load"):
                if mode not in nav_modes:
                    nav_modes.append(mode)

            loaded = False
            for mode in nav_modes:
                try:
                    await page.goto(
                        page_url,
                        wait_until=mode,
                        timeout=max(15000, int(tmo * 1000)),
                    )
                    loaded = True
                    if mode != "domcontentloaded":
                        self._log(f"goto recovered using wait_until={mode} for {page_url}", log)
                    break
                except Exception as e:
                    self._log(f"goto timeout/error on {page_url} (wait_until={mode}): {e}", log)

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
            # 1) legacy regex scan
            if self.cfg.enable_html_link_scan and html:
                html_links = self._extract_urls_from_text(page_url, html)
                await self._add_link_hits_async(page_url, html_links, hits, source="html_regex", log=log)

            # 2) advanced DOM buckets
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

            # final dedupe
            hits = self._dedupe_hits(hits)

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
# InteractionSniffer (bounded / fail-fast rewrite)
# ======================================================================

class InteractionSniffer:
    """
    Bounded Playwright + CDP sniffer for interactivity, overlays, barriers, forms,
    and accessible controls.

    Contract:
        html, hits = await sniff(
            context,
            page_url,
            timeout,
            log,
            extensions=None,
        )

    hits schema:
        {
            "page": <page_url>,
            "url": <page_url or derived>,
            "tag": "interaction",
            "kind": "...",
            "meta": {...}
        }
    """

    @dataclass
    class Config:
        timeout: float = 6.0
        max_hits: int = 180
        wait_after_load_ms: int = 400

        # hard budgets
        hard_total_budget_s: float = 6.5
        goto_timeout_ms: int = 3500
        per_eval_timeout_s: float = 1.6
        per_cdp_timeout_s: float = 1.5
        per_action_settle_ms: int = 250

        # adaptive gates
        min_budget_for_cdp_s: float = 1.8
        min_budget_for_ax_s: float = 1.2
        min_budget_for_dynamic_s: float = 1.6
        min_budget_for_post_phase_s: float = 0.8

        # dynamic simulation
        enable_dynamic_simulation: bool = True
        sim_scroll_steps: int = 1
        sim_scroll_delay_ms: int = 180
        sim_click_targets: int = 1
        sim_click_timeout_ms: int = 1200
        cta_text_hints: List[str] = field(default_factory=lambda: [
            "accept", "agree", "continue", "close", "ok", "okay", "got it",
            "play", "watch", "enter", "allow", "next", "submit",
            "sign in", "log in", "login", "sign up", "register",
            "open", "view", "show",
        ])

        # CDP listeners
        enable_cdp_listeners: bool = True
        listener_types: Set[str] = field(default_factory=lambda: {
            "click", "mousedown", "mouseup", "submit",
            "keydown", "keyup", "touchstart", "touchend",
            "pointerdown", "pointerup",
        })
        max_listener_hits: int = 64
        max_candidate_nodes: int = 160
        candidate_selector: str = (
            "button, a, input, select, textarea, summary, details, label, "
            "[role='button'], [role='link'], [tabindex], [contenteditable='true']"
        )

        # overlays / blockers / barriers
        enable_overlay_detection: bool = True
        min_z_index: int = 900
        coverage_threshold_percent: float = 45.0
        max_overlay_hits: int = 20
        detect_scroll_lock: bool = True
        overlay_keywords: List[str] = field(default_factory=lambda: [
            "cookie", "consent", "subscribe", "sign in", "log in",
            "disable adblock", "adblock", "enable javascript", "paywall",
            "verify you are human", "captcha", "hcaptcha", "recaptcha",
        ])

        enable_hit_test_blockers: bool = True
        hit_test_grid: int = 2
        max_hit_test_hits: int = 12

        enable_ui_barrier_scan: bool = True
        max_barrier_hits: int = 16

        # forms
        enable_form_extraction: bool = True
        max_form_hits: int = 24
        max_inputs_per_form: int = 32
        redact_input_types: Set[str] = field(default_factory=lambda: {"password"})
        redact_name_regex: str = r"(csrf|token|auth|bearer|secret|key|session|jwt)"
        emit_summary_hit: bool = True

        enable_dom_link_extraction: bool = True
        max_link_hits: int = 72
        max_html_regex_link_hits: int = 180


        # AX / accessibility
        enable_ax_tree_scan: bool = True
        ax_roles: Set[str] = field(default_factory=lambda: {
            "button", "link", "checkbox", "textbox", "combobox", "menuitem"
        })
        max_ax_hits: int = 40

        # page gating
        skip_asset_paths: bool = True
        skip_challenge_pages: bool = True
        asset_exts: Set[str] = field(default_factory=lambda: {
            ".js", ".css", ".map", ".json", ".xml", ".svg", ".png", ".jpg", ".jpeg",
            ".gif", ".ico", ".woff", ".woff2", ".ttf", ".eot", ".webp", ".avif"
        })
        asset_path_hints: Set[str] = field(default_factory=lambda: {
            "/assets/", "/thumbnails/", "/logos/", "/favicons/", "/fonts/",
            "/css/", "/js/", "/libraries/", "/cms-uploads/", "/translations/"
        })
        challenge_hints: Set[str] = field(default_factory=lambda: {
            "/cdn-cgi/", "captcha", "recaptcha", "hcaptcha", "turnstile",
            "cloudflare", "challenge-platform", "verify you are human",
        })

    def __init__(self, config: Optional["InteractionSniffer.Config"] = None, logger=None):
        self.cfg = config or self.Config()
        self.logger = logger or DEBUG_LOGGER
        self._reset_memory()
        self._log("InteractionSniffer Initialized", None)

    # ------------------------------------------------------------------ #
    # memory / logging
    # ------------------------------------------------------------------ #

    def _reset_memory(self) -> None:
        self._hits: List[Dict[str, Any]] = []
        self._seen: Set[Tuple[Any, ...]] = set()

    def _log(self, msg: str, log_list: Optional[List[str]]) -> None:
        full = f"[InteractionSniffer] {msg}"
        try:
            if log_list is not None:
                log_list.append(full)
            if self.logger is not None:
                self.logger.log_message(full)  # type: ignore[attr-defined]
        except Exception:
            pass

    def _emit_hit(self, page_url: str, kind: str, meta: Dict[str, Any], *, url: Optional[str] = None) -> None:
        u = url or page_url
        fp = (
            kind,
            str(u),
            str(meta.get("selector_hint") or ""),
            str(meta.get("phase") or ""),
            str(meta.get("evidence") or meta.get("text_preview") or meta.get("role") or ""),
        )
        if fp in self._seen:
            return
        self._seen.add(fp)
        self._hits.append({
            "page": page_url,
            "url": u,
            "tag": "interaction",
            "kind": kind,
            "meta": meta,
        })

    # ------------------------------------------------------------------ #
    # helpers
    # ------------------------------------------------------------------ #

    async def _safe_eval(self, page, script: str, arg: Any, log: Optional[List[str]]) -> Any:
        try:
            return await asyncio.wait_for(page.evaluate(script, arg), timeout=self.cfg.per_eval_timeout_s)
        except Exception as e:
            self._log(f"page.evaluate failed/timeout: {e}", log)
            return None

    async def _cdp_send(self, cdp, method: str, params: Optional[Dict[str, Any]], log: Optional[List[str]]) -> Any:
        try:
            return await asyncio.wait_for(cdp.send(method, params or {}), timeout=self.cfg.per_cdp_timeout_s)
        except Exception as e:
            msg = str(e)
            if method == "DOM.pushNodesByBackendIdsToFrontend" and "Document needs to be requested first" in msg:
                return None
            self._log(f"CDP send {method} failed/timeout: {e}", log)
            return None

    def _canon_url(self, u: str) -> str:
        return (u or "").strip()

    def _remaining_budget(self, deadline: float) -> float:
        return max(0.0, deadline - time.monotonic())

    def _url_profile(self, page_url: str) -> Dict[str, Any]:
        low = (page_url or "").strip().lower()

        is_valid = low.startswith("http://") or low.startswith("https://")

        parsed = urlparse(low) if is_valid else None
        path = parsed.path or "" if parsed else ""
        host = parsed.netloc or "" if parsed else ""

        asset_ext = any(path.endswith(ext) for ext in self.cfg.asset_exts)
        asset_hint = any(h in path for h in self.cfg.asset_path_hints)
        challenge = any(h in low for h in self.cfg.challenge_hints)

        return {
            "is_valid": is_valid,
            "host": host,
            "path": path,
            "is_asset_like": bool(asset_ext or asset_hint),
            "is_challenge_like": bool(challenge),
        }

    def _should_skip_dynamic(self, profile: Dict[str, Any]) -> bool:
        return bool(profile.get("is_asset_like") or profile.get("is_challenge_like"))

    def _is_html_response(self, response) -> bool:
        try:
            ctype = (response.headers.get("content-type") or "").lower()
        except Exception:
            ctype = ""
        if not ctype:
            return True
        return ("text/html" in ctype) or ("application/xhtml" in ctype)

    async def _cheap_dom_probe(self, page, log: Optional[List[str]]) -> Dict[str, Any]:
        probe = await self._safe_eval(
            page,
            """
            () => {
                try {
                    const nodes = document.querySelectorAll("*").length;
                    const scripts = document.scripts ? document.scripts.length : 0;
                    const title = (document.title || "").trim().slice(0, 120);
                    const bodyText = ((document.body && document.body.innerText) || "").trim();
                    const textLen = bodyText.length;
                    const buttons = document.querySelectorAll("button, [role='button'], a[role='button']").length;
                    const forms = document.querySelectorAll("form").length;
                    const links = document.links ? document.links.length : 0;
                    return {
                        ok: true,
                        ready: document.readyState || "",
                        nodes,
                        scripts,
                        title,
                        textLen,
                        buttons,
                        forms,
                        links,
                        bodySample: bodyText.slice(0, 220),
                    };
                } catch (e) {
                    return { ok: false, error: String(e || "") };
                }
            }
            """,
            None,
            log,
        )
        return probe if isinstance(probe, dict) else {"ok": False}

    def _extract_urls_from_text(self, s: str) -> List[str]:
        if not s:
            return []
        rx = re.compile(r"\b(?:https?|wss?)://[^\s\"'<>]+", re.IGNORECASE)
        out: List[str] = []
        seen: Set[str] = set()
        for u in rx.findall(s):
            if u not in seen:
                seen.add(u)
                out.append(u)
        return out

    def _absolutize_url(self, base_url: str, raw_url: str) -> str:
        raw = str(raw_url or "").strip()
        if not raw:
            return ""

        low = raw.lower()
        if low.startswith(("javascript:", "mailto:", "tel:", "data:", "blob:", "#")):
            return ""

        try:
            return urljoin(base_url, raw)
        except Exception:
            return raw

    async def _collect_dom_link_hits(self, page, page_url: str, log: Optional[List[str]], *, phase: str) -> None:
        if not getattr(self.cfg, "enable_dom_link_extraction", True):
            return

        payload = await self._safe_eval(
            page,
            """
            (cfg) => {
                const out = [];
                const seen = new Set();
                const maxHits = cfg.maxHits || 72;

                function push(url, kind, text, selector) {
                    try {
                        url = String(url || "").trim();
                        if (!url) return;

                        const low = url.toLowerCase();
                        if (
                            low === "#" ||
                            low.startsWith("javascript:") ||
                            low.startsWith("mailto:") ||
                            low.startsWith("tel:") ||
                            low.startsWith("data:") ||
                            low.startsWith("blob:")
                        ) return;

                        const key = `${kind}|${url}|${selector || ""}`;
                        if (seen.has(key)) return;
                        seen.add(key);

                        out.push({
                            url,
                            kind,
                            text: String(text || "").trim().slice(0, 140),
                            selector: String(selector || "").trim().slice(0, 120),
                        });
                    } catch (_) {}
                }

                function selOf(el) {
                    try {
                        if (!el) return "";
                        if (el.id) return `#${CSS.escape(el.id)}`;
                        const cls = (typeof el.className === "string" ? el.className : "");
                        const c1 = cls.split(/\\s+/).filter(Boolean)[0];
                        if (c1) return `${el.tagName.toLowerCase()}.${CSS.escape(c1)}`;
                        return el.tagName.toLowerCase();
                    } catch {
                        return "";
                    }
                }

                // href/action/src-style values
                const linkish = Array.from(document.querySelectorAll(
                    "a[href], area[href], iframe[src], frame[src], form[action], link[href], img[src], video[src], audio[src], source[src], embed[src]"
                )).slice(0, 600);

                for (const el of linkish) {
                    if (out.length >= maxHits) break;
                    const tag = (el.tagName || "").toLowerCase();

                    if ((tag === "a" || tag === "area") && el.getAttribute("href")) {
                        push(el.getAttribute("href"), "dom_href", el.innerText || el.textContent || el.getAttribute("title") || "", selOf(el));
                        continue;
                    }
                    if (tag === "form" && el.getAttribute("action")) {
                        push(el.getAttribute("action"), "dom_action", el.getAttribute("name") || el.getAttribute("id") || "", selOf(el));
                        continue;
                    }
                    if (el.getAttribute("src")) {
                        push(el.getAttribute("src"), "dom_src", el.getAttribute("alt") || el.getAttribute("title") || "", selOf(el));
                        continue;
                    }
                    if (el.getAttribute("href")) {
                        push(el.getAttribute("href"), "dom_link_tag", el.getAttribute("rel") || "", selOf(el));
                        continue;
                    }
                }

                // meta URLs
                const metas = Array.from(document.querySelectorAll("meta[content]")).slice(0, 120);
                for (const m of metas) {
                    if (out.length >= maxHits) break;
                    const p = (m.getAttribute("property") || m.getAttribute("name") || "").toLowerCase();
                    if (
                        p.includes("og:url") ||
                        p.includes("og:image") ||
                        p.includes("og:video") ||
                        p.includes("twitter:image") ||
                        p.includes("twitter:player") ||
                        p === "canonical"
                    ) {
                        push(m.getAttribute("content"), "dom_meta", p, "meta");
                    }
                }

                // data-* and onclick URLs
                const extras = Array.from(document.querySelectorAll("[data-href], [data-url], [data-src], [data-action], [onclick]")).slice(0, 400);
                for (const el of extras) {
                    if (out.length >= maxHits) break;
                    push(el.getAttribute("data-href"), "dom_data_href", "", selOf(el));
                    push(el.getAttribute("data-url"), "dom_data_url", "", selOf(el));
                    push(el.getAttribute("data-src"), "dom_data_src", "", selOf(el));
                    push(el.getAttribute("data-action"), "dom_data_action", "", selOf(el));

                    const onclick = el.getAttribute("onclick") || "";
                    const matches = onclick.match(/https?:\\/\\/[^"'\\s<>]+/ig) || [];
                    for (const u of matches) {
                        if (out.length >= maxHits) break;
                        push(u, "dom_onclick", "", selOf(el));
                    }
                }

                return out.slice(0, maxHits);
            }
            """,
            {"maxHits": int(getattr(self.cfg, "max_link_hits", 72))},
            log,
        )

        if not isinstance(payload, list):
            return

        added = 0
        for item in payload[: int(getattr(self.cfg, "max_link_hits", 72))]:
            if not isinstance(item, dict):
                continue

            raw = str(item.get("url") or "").strip()
            full = self._absolutize_url(page_url, raw)
            if not full:
                continue

            self._emit_hit(
                page_url,
                "derived_link",
                {
                    "phase": phase,
                    "source": str(item.get("kind") or "dom_link"),
                    "selector_hint": str(item.get("selector") or ""),
                    "text_preview": str(item.get("text") or ""),
                    "evidence": "dom_link_harvest",
                },
                url=full,
            )
            added += 1

        if added:
            self._log(f"[{phase}] DOM links: +{added}", log)
    # ------------------------------------------------------------------ #
    # public API
    # ------------------------------------------------------------------ #

    async def sniff(
            self,
            context,
            page_url: str,
            timeout: float,
            log: List[str],
            extensions=None,
    ) -> Tuple[str, List[Dict[str, Any]]]:
        from playwright.async_api import TimeoutError as PWTimeoutError
        self.cfg.timeout = timeout
        self._reset_memory()
        html = ""

        if not context:
            self._log("No BrowserContext supplied; skipping.", log)
            return "", []

        profile = self._url_profile(page_url)
        if not profile["is_valid"]:
            self._log(f"Skipping invalid URL: {page_url}", log)
            return "", []

        deadline = time.monotonic() + min(
            float(self.cfg.hard_total_budget_s),
            max(1.0, float(timeout or self.cfg.timeout))
        )

        self._log(
            f"Start interaction sniff: {page_url} timeout={float(timeout or self.cfg.timeout):.1f}s "
            f"budget={self._remaining_budget(deadline):.1f}s",
            log,
        )

        if self.cfg.skip_asset_paths and profile["is_asset_like"]:
            self._emit_hit(
                page_url,
                "skip_asset_page",
                {
                    "reason": "asset_like_path",
                    "path": profile["path"],
                    "host": profile["host"],
                },
            )
            self._log(f"Fast-skip asset-like page: {page_url}", log)
            return "", self._hits[: self.cfg.max_hits]

        page = None
        try:
            page = await context.new_page()

            nav_modes: List[str] = []
            for mode in ("domcontentloaded", "commit", "load"):
                if mode not in nav_modes:
                    nav_modes.append(mode)

            response = None
            goto_base_timeout = min(
                int(self.cfg.goto_timeout_ms),
                max(900, int(self._remaining_budget(deadline) * 1000) - 200),
            )

            for mode in nav_modes:
                try:
                    response = await page.goto(
                        page_url,
                        wait_until=mode,
                        timeout=max(900, goto_base_timeout),
                    )
                    if mode != "domcontentloaded":
                        self._log(f"goto recovered using wait_until={mode} for {page_url}", log)
                    break
                except PWTimeoutError:
                    self._log(f"Timeout while loading {page_url} with wait_until={mode}", log)
                except Exception as e:
                    self._log(f"goto error on {page_url} (wait_until={mode}): {e}", log)

            if response is not None and not self._is_html_response(response):
                try:
                    ctype = (response.headers.get("content-type") or "")
                except Exception:
                    ctype = ""
                self._emit_hit(
                    page_url,
                    "non_html_response",
                    {"content_type": ctype, "status": getattr(response, "status", None)},
                )
                self._log(f"Skipping non-HTML response for {page_url}: {ctype}", log)
                return "", self._hits[: self.cfg.max_hits]

            if self._remaining_budget(deadline) <= 0.15:
                return "", self._hits[: self.cfg.max_hits]

            await page.wait_for_timeout(
                min(
                    int(self.cfg.wait_after_load_ms),
                    max(50, int(self._remaining_budget(deadline) * 250)),
                )
            )

            probe = await self._cheap_dom_probe(page, log)
            if probe.get("ok"):
                self._emit_hit(page_url, "dom_probe", probe)
                self._log(
                    f"DOM probe: nodes={probe.get('nodes')} scripts={probe.get('scripts')} "
                    f"buttons={probe.get('buttons')} forms={probe.get('forms')} textLen={probe.get('textLen')}",
                    log,
                )

            if not probe.get("ok", False):
                self._log("DOM probe failed; returning partial hits.", log)
                return "", self._hits[: self.cfg.max_hits]

            degraded = bool(
                profile["is_challenge_like"] or
                int(probe.get("nodes") or 0) <= 6 or
                int(probe.get("textLen") or 0) <= 40
            )

            await self._collect_phase(page, page_url, log, phase="pre", deadline=deadline)

            if (
                    self.cfg.enable_cdp_listeners
                    and not degraded
                    and self._remaining_budget(deadline) >= self.cfg.min_budget_for_cdp_s
            ):
                await self._collect_cdp_listeners(context, page, page_url, log, deadline=deadline)

            if (
                    self.cfg.enable_ax_tree_scan
                    and not degraded
                    and self._remaining_budget(deadline) >= self.cfg.min_budget_for_ax_s
            ):
                await self._collect_ax_tree(context, page, page_url, log, deadline=deadline)

            if (
                    self.cfg.enable_dynamic_simulation
                    and not degraded
                    and not self._should_skip_dynamic(profile)
                    and self._remaining_budget(deadline) >= self.cfg.min_budget_for_dynamic_s
            ):
                await self._simulate_and_rescan(context, page, page_url, log, deadline=deadline)

            if self._remaining_budget(deadline) > 0.20:
                try:
                    html = await asyncio.wait_for(page.content(), timeout=min(1.0, self._remaining_budget(deadline)))
                except Exception as e:
                    self._log(f"Error getting HTML for {page_url}: {e}", log)
                    html = ""

            # final raw URL harvest from html snapshot
            if html:
                added = 0
                for u in self._extract_urls_from_text(html)[: int(getattr(self.cfg, "max_html_regex_link_hits", 180))]:
                    self._emit_hit(
                        page_url,
                        "derived_link",
                        {
                            "phase": "html",
                            "source": "html_regex",
                            "selector_hint": "",
                            "text_preview": "",
                            "evidence": "html_regex",
                        },
                        url=u,
                    )
                    added += 1
                if added:
                    self._log(f"[html] Regex links: +{added}", log)

        except PWTimeoutError:
            self._log(f"Timeout while loading {page_url}", log)
        except Exception as e:
            msg = str(e)
            if (
                    "ERR_NAME_NOT_RESOLVED" in msg
                    or "Cannot navigate to invalid URL" in msg
                    or "ERR_INVALID_URL" in msg
            ):
                self._emit_hit(page_url, "navigation_error", {"error": msg[:240], "fatal": True})
                self._log(f"Fatal navigation failure on {page_url}: {e}", log)
            else:
                self._emit_hit(page_url, "sniff_error", {"error": msg[:240]})
                self._log(f"Fatal error on {page_url}: {e}", log)
        finally:
            if page is not None:
                try:
                    await asyncio.wait_for(page.close(), timeout=2.0)
                except Exception as e:
                    self._log(f"Error closing page for {page_url}: {e}", log)

        hits = self._hits[: self.cfg.max_hits]
        self._log(f"Finished interaction sniff for {page_url}: hits={len(hits)}", log)
        return html or "", hits

    # ------------------------------------------------------------------ #
    # collectors
    # ------------------------------------------------------------------ #

    async def _collect_phase(self, page, page_url: str, log: Optional[List[str]], *, phase: str,
                             deadline: float) -> None:
        if self._remaining_budget(deadline) <= 0.15:
            return

        if getattr(self.cfg, "enable_dom_link_extraction", True) and self._remaining_budget(deadline) > 0.20:
            await self._collect_dom_link_hits(page, page_url, log, phase=phase)

        if self.cfg.enable_form_extraction and self._remaining_budget(deadline) > 0.25:
            await self._collect_forms(page, page_url, log, phase=phase)

        if self.cfg.enable_overlay_detection and self._remaining_budget(deadline) > 0.25:
            await self._collect_overlays(page, page_url, log, phase=phase)

        if self.cfg.enable_ui_barrier_scan and self._remaining_budget(deadline) > 0.20:
            await self._collect_ui_barriers(page, page_url, log, phase=phase)

        if self.cfg.enable_hit_test_blockers and self._remaining_budget(deadline) > 0.20:
            await self._collect_hit_test_blockers(page, page_url, log, phase=phase)

    async def _collect_forms(self, page, page_url: str, log: Optional[List[str]], *, phase: str) -> None:
        payload = await self._safe_eval(
            page,
            """
            (cfg) => {
                const out = [];
                const forms = Array.from(document.querySelectorAll("form")).slice(0, cfg.maxForms);

                for (const f of forms) {
                    const inputs = [];
                    const els = Array.from(f.querySelectorAll("input, textarea, select, button")).slice(0, cfg.maxInputs);
                    for (const i of els) {
                        inputs.push({
                            name: i.name || i.id || "",
                            type: (i.type || i.tagName || "").toLowerCase(),
                            required: !!i.required,
                            disabled: !!i.disabled,
                            placeholder: i.placeholder || "",
                            autocomplete: i.autocomplete || "",
                        });
                    }
                    out.push({
                        action: f.action || "",
                        method: (f.method || "get").toLowerCase(),
                        id: f.id || "",
                        className: (typeof f.className === "string" ? f.className : ""),
                        input_count: inputs.length,
                        inputs
                    });
                }
                return out;
            }
            """,
            {"maxForms": int(self.cfg.max_form_hits), "maxInputs": int(self.cfg.max_inputs_per_form)},
            log,
        )

        if not isinstance(payload, list):
            return

        for form in payload[: self.cfg.max_form_hits]:
            if not isinstance(form, dict):
                continue

            inputs = []
            for inp in (form.get("inputs") or [])[: self.cfg.max_inputs_per_form]:
                if not isinstance(inp, dict):
                    continue
                name = str(inp.get("name") or "")
                typ = str(inp.get("type") or "")
                if typ in self.cfg.redact_input_types or re.search(self.cfg.redact_name_regex, name, re.I):
                    value = "[REDACTED]"
                else:
                    value = ""
                inputs.append({
                    "name": name,
                    "type": typ,
                    "value": value,
                    "required": bool(inp.get("required", False)),
                    "disabled": bool(inp.get("disabled", False)),
                    "placeholder": str(inp.get("placeholder") or ""),
                    "autocomplete": str(inp.get("autocomplete") or ""),
                })

            self._emit_hit(
                page_url,
                "form",
                {
                    "phase": phase,
                    "action": str(form.get("action") or ""),
                    "method": str(form.get("method") or "get"),
                    "id": str(form.get("id") or ""),
                    "class_name": str(form.get("className") or ""),
                    "input_count": int(form.get("input_count") or len(inputs)),
                    "inputs": inputs,
                },
            )

        if payload:
            self._log(f"[{phase}] Extracted {len(payload)} form definitions", log)

    async def _collect_overlays(self, page, page_url: str, log: Optional[List[str]], *, phase: str) -> None:
        payload = await self._safe_eval(
            page,
            """
            (config) => {
                const { minZ, minCoverage, maxHits, detectScrollLock, keywords } = config;
                const results = [];

                const vw = Math.max(document.documentElement.clientWidth || 0, window.innerWidth || 0);
                const vh = Math.max(document.documentElement.clientHeight || 0, window.innerHeight || 0);
                const viewportArea = Math.max(1, vw * vh);

                const bodyOv = (() => { try { return getComputedStyle(document.body).overflow || ""; } catch { return ""; } })();
                const htmlOv = (() => { try { return getComputedStyle(document.documentElement).overflow || ""; } catch { return ""; } })();

                function hasKeyword(txt){
                  const t = String(txt || "").toLowerCase();
                  for (const k of (keywords || [])) {
                    if (k && t.includes(String(k).toLowerCase())) return true;
                  }
                  return false;
                }

                const nodes = Array.from(document.querySelectorAll("div, section, aside, iframe, dialog, [role='dialog'], [aria-modal='true']")).slice(0, 250);

                for (const el of nodes) {
                    if (results.length >= maxHits) break;
                    const style = getComputedStyle(el);
                    const zRaw = style.zIndex;
                    const z = parseInt(zRaw, 10);
                    if (Number.isNaN(z)) continue;

                    const rect = el.getBoundingClientRect();
                    const area = Math.max(0, rect.width) * Math.max(0, rect.height);
                    if (area <= 0) continue;
                    const coveragePct = (area / viewportArea) * 100;

                    const isOverlayLike =
                        (z >= minZ) &&
                        style.visibility !== "hidden" &&
                        style.display !== "none" &&
                        (style.position === "fixed" || style.position === "absolute") &&
                        coveragePct >= minCoverage;

                    if (!isOverlayLike) continue;

                    const txt = (el.innerText || "").trim();
                    results.push({
                        tagName: el.tagName.toLowerCase(),
                        id: el.id || "",
                        className: (typeof el.className === "string" ? el.className : ""),
                        zIndex: z,
                        coverage: coveragePct.toFixed(1) + "%",
                        textPreview: txt.slice(0, 80),
                        pointerEvents: style.pointerEvents || "",
                        opacity: parseFloat(style.opacity || "1"),
                        position: style.position || "",
                        scrollLock: detectScrollLock ? ((bodyOv === "hidden") || (htmlOv === "hidden")) : false,
                        keywordHit: hasKeyword(txt),
                    });
                }

                return { overlays: results, bodyOverflow: bodyOv, htmlOverflow: htmlOv };
            }
            """,
            {
                "minZ": int(self.cfg.min_z_index),
                "minCoverage": float(self.cfg.coverage_threshold_percent),
                "maxHits": int(self.cfg.max_overlay_hits),
                "detectScrollLock": bool(self.cfg.detect_scroll_lock),
                "keywords": list(self.cfg.overlay_keywords),
            },
            log,
        )

        if not isinstance(payload, dict):
            return

        overlays = payload.get("overlays") or []
        if not isinstance(overlays, list):
            return

        for ov in overlays[: self.cfg.max_overlay_hits]:
            if not isinstance(ov, dict):
                continue
            self._emit_hit(
                page_url,
                "overlay",
                {
                    "phase": phase,
                    "tag_name": str(ov.get("tagName") or ""),
                    "id": str(ov.get("id") or ""),
                    "class_name": str(ov.get("className") or ""),
                    "z_index": int(ov.get("zIndex") or 0),
                    "coverage": str(ov.get("coverage") or ""),
                    "text_preview": str(ov.get("textPreview") or ""),
                    "pointer_events": str(ov.get("pointerEvents") or ""),
                    "opacity": float(ov.get("opacity") or 1.0),
                    "position": str(ov.get("position") or ""),
                    "keyword_hit": bool(ov.get("keywordHit", False)),
                    "scroll_lock": bool(ov.get("scrollLock", False)),
                },
            )

        if overlays:
            self._log(f"[{phase}] Overlay detection: +{len(overlays)}", log)

    async def _collect_ui_barriers(self, page, page_url: str, log: Optional[List[str]], *, phase: str) -> None:
        payload = await self._safe_eval(
            page,
            """
            (cfg) => {
                const out = [];
                const maxHits = cfg.maxHits;

                function push(type, evidence, selector){
                    if (out.length >= maxHits) return;
                    out.push({type, evidence, selector: selector || ""});
                }

                const bodyText = (() => {
                    try { return ((document.body && document.body.innerText) || "").toLowerCase(); }
                    catch { return ""; }
                })();

                const ifr = Array.from(document.querySelectorAll("iframe[src], script[src]")).slice(0, 200);
                for (const el of ifr) {
                    if (out.length >= maxHits) break;
                    const src = String(el.getAttribute("src") || "").toLowerCase();
                    if (!src) continue;
                    if (src.includes("recaptcha") || src.includes("hcaptcha") || src.includes("captcha") || src.includes("turnstile")) {
                        push("captcha", src, el.tagName.toLowerCase());
                    }
                    if (src.includes("/cdn-cgi/") || src.includes("cloudflare")) {
                        push("cloudflare_challenge", src, el.tagName.toLowerCase());
                    }
                }

                const keywords = [
                    ["paywall", ["subscribe", "subscription", "continue reading"]],
                    ["cookie_consent", ["cookie", "consent", "privacy choices"]],
                    ["adblock", ["disable adblock", "ad blocker", "turn off adblock"]],
                    ["bot_check", ["verify you are human", "unusual traffic", "bot detection"]],
                ];

                for (const [typ, ks] of keywords) {
                    for (const k of ks) {
                        if (bodyText.includes(k)) {
                            push(String(typ), `keyword:${k}`, "bodyText");
                            break;
                        }
                    }
                }

                const selPairs = [
                    ["captcha", "[data-sitekey], .h-captcha, .g-recaptcha, iframe[title*='captcha' i]"],
                    ["cloudflare_challenge", "#challenge-form, .cf-challenge, iframe[src*='cdn-cgi' i]"],
                    ["consent", "[id*='consent' i], [class*='consent' i], [id*='cookie' i], [class*='cookie' i]"],
                ];

                for (const [typ, sel] of selPairs) {
                    if (out.length >= maxHits) break;
                    let hit = null;
                    try { hit = document.querySelector(sel); } catch {}
                    if (hit) push(String(typ), `selector:${sel}`, sel);
                }

                return out;
            }
            """,
            {"maxHits": int(self.cfg.max_barrier_hits)},
            log,
        )

        if not isinstance(payload, list):
            return

        for item in payload[: self.cfg.max_barrier_hits]:
            if not isinstance(item, dict):
                continue
            self._emit_hit(
                page_url,
                "barrier",
                {
                    "phase": phase,
                    "barrier_type": str(item.get("type") or "unknown"),
                    "evidence": str(item.get("evidence") or ""),
                    "selector_hint": str(item.get("selector") or ""),
                },
            )

        if payload:
            self._log(f"[{phase}] UI barriers: +{len(payload)}", log)

    async def _collect_hit_test_blockers(self, page, page_url: str, log: Optional[List[str]], *, phase: str) -> None:
        payload = await self._safe_eval(
            page,
            """
            (cfg) => {
                const grid = Math.max(2, cfg.grid|0);
                const maxHits = cfg.maxHits|0;
                const vw = Math.max(document.documentElement.clientWidth||0, window.innerWidth||0);
                const vh = Math.max(document.documentElement.clientHeight||0, window.innerHeight||0);

                const pts = [];
                for (let gy=0; gy<grid; gy++){
                    for (let gx=0; gx<grid; gx++){
                        const x = Math.floor((gx+1) * vw / (grid+1));
                        const y = Math.floor((gy+1) * vh / (grid+1));
                        pts.push([x,y]);
                    }
                }
                pts.push([Math.floor(vw/2), Math.floor(vh/2)]);

                function safeOuter(el){
                    try { return (el && el.outerHTML ? String(el.outerHTML).slice(0, 220) : ""); } catch { return ""; }
                }

                function infoAt(x,y){
                    let el = null;
                    try { el = document.elementFromPoint(x,y); } catch { el = null; }
                    if (!el) return null;
                    let st = null;
                    try { st = getComputedStyle(el); } catch { st = null; }
                    let rect = {x:0,y:0,w:0,h:0};
                    try { const r = el.getBoundingClientRect(); rect = {x:r.x,y:r.y,w:r.width,h:r.height}; } catch {}
                    const txt = (() => { try { return (el.innerText||"").trim().slice(0,80); } catch { return ""; } })();
                    return {
                        point: [x,y],
                        tagName: (el.tagName||"").toLowerCase(),
                        id: el.id||"",
                        className: (typeof el.className==="string" ? el.className : ""),
                        pointerEvents: st ? (st.pointerEvents||"") : "",
                        opacity: st ? parseFloat(st.opacity||"1") : 1.0,
                        zIndex: st ? (st.zIndex||"") : "",
                        position: st ? (st.position||"") : "",
                        rect,
                        textPreview: txt,
                        outerHTML: safeOuter(el),
                    };
                }

                const out = [];
                const seen = new Set();

                for (const [x,y] of pts){
                    if (out.length >= maxHits) break;
                    const it = infoAt(x,y);
                    if (!it) continue;

                    const fp = `${it.tagName}#${it.id}.${it.className}|${it.pointerEvents}|${it.position}|${it.zIndex}`;
                    if (seen.has(fp)) continue;
                    seen.add(fp);

                    const area = Math.max(0, it.rect.w) * Math.max(0, it.rect.h);
                    const viewportArea = Math.max(1, vw*vh);
                    const coverPct = (area / viewportArea) * 100;

                    const isBlocker = (it.pointerEvents !== "none") && (
                        (it.position === "fixed") || (coverPct >= 20) || (it.tagName === "dialog")
                    );

                    if (isBlocker) out.push({...it, coveragePct: coverPct.toFixed(1)});
                }

                return out;
            }
            """,
            {"grid": int(self.cfg.hit_test_grid), "maxHits": int(self.cfg.max_hit_test_hits)},
            log,
        )

        if not isinstance(payload, list):
            return

        for item in payload[: self.cfg.max_hit_test_hits]:
            if not isinstance(item, dict):
                continue
            self._emit_hit(
                page_url,
                "hit_test_blocker",
                {
                    "phase": phase,
                    "point": item.get("point") or [0, 0],
                    "tag_name": str(item.get("tagName") or ""),
                    "id": str(item.get("id") or ""),
                    "class_name": str(item.get("className") or ""),
                    "pointer_events": str(item.get("pointerEvents") or ""),
                    "opacity": float(item.get("opacity") or 1.0),
                    "z_index": str(item.get("zIndex") or ""),
                    "position": str(item.get("position") or ""),
                    "rect": dict(item.get("rect") or {}),
                    "text_preview": str(item.get("textPreview") or ""),
                    "outer_html": str(item.get("outerHTML") or ""),
                    "coverage_pct": str(item.get("coveragePct") or ""),
                },
            )

        if payload:
            self._log(f"[{phase}] Hit-test blockers: +{len(payload)}", log)

    async def _collect_cdp_listeners(self, context, page, page_url: str, log: Optional[List[str]], *, deadline: float) -> None:
        browser_name = "unknown"
        try:
            if getattr(context, "browser", None) and context.browser:
                browser_name = context.browser.browser_type.name
        except Exception:
            browser_name = "unknown"

        if browser_name != "chromium":
            self._log(f"Skipping CDP scan (browser is {browser_name}, need chromium)", log)
            return

        if self._remaining_budget(deadline) < self.cfg.min_budget_for_cdp_s:
            return

        try:
            cdp = await context.new_cdp_session(page)
        except Exception as e:
            self._log(f"CDP session failed (non-critical): {e}", log)
            return

        found = 0
        inspected = 0

        try:
            doc = await self._cdp_send(cdp, "DOM.getDocument", {"depth": 1, "pierce": True}, log)
            root_node_id = (doc or {}).get("root", {}).get("nodeId")
            if not root_node_id:
                return

            qs = await self._cdp_send(cdp, "DOM.querySelectorAll", {
                "nodeId": root_node_id,
                "selector": str(self.cfg.candidate_selector),
            }, log)
            node_ids = (qs or {}).get("nodeIds", []) or []
            node_ids = node_ids[: int(self.cfg.max_candidate_nodes)]

            def attrs_to_dict(attr_list: List[str]) -> Dict[str, str]:
                try:
                    return dict(zip(attr_list[0::2], attr_list[1::2]))
                except Exception:
                    return {}

            for nid in node_ids:
                if self._remaining_budget(deadline) < 0.35:
                    break
                if found >= int(self.cfg.max_listener_hits):
                    break

                inspected += 1

                remote_obj = await self._cdp_send(cdp, "DOM.resolveNode", {"nodeId": nid}, log)
                object_id = (remote_obj or {}).get("object", {}).get("objectId")
                if not object_id:
                    continue

                listeners_resp = await self._cdp_send(
                    cdp,
                    "DOMDebugger.getEventListeners",
                    {"objectId": object_id, "depth": 1},
                    log,
                )
                listeners = (listeners_resp or {}).get("listeners", []) or []
                if not listeners:
                    continue

                relevant = []
                for l in listeners:
                    if not isinstance(l, dict):
                        continue
                    lt = str(l.get("type") or "")
                    if lt in self.cfg.listener_types:
                        relevant.append(l)
                if not relevant:
                    continue

                attrs_resp = await self._cdp_send(cdp, "DOM.getAttributes", {"nodeId": nid}, log)
                attr_dict = attrs_to_dict((attrs_resp or {}).get("attributes", []) or [])

                desc = await self._cdp_send(cdp, "DOM.describeNode", {"nodeId": nid}, log)
                node_name = str((desc or {}).get("node", {}).get("nodeName") or "").lower()

                self._emit_hit(
                    page_url,
                    "listener",
                    {
                        "node_id": int(nid),
                        "node_name": node_name,
                        "listener_types": sorted({str(r.get("type") or "") for r in relevant}),
                        "attributes": attr_dict,
                        "flags": {
                            "count": len(relevant),
                            "capture": any(bool(r.get("useCapture")) for r in relevant),
                            "passive": any(bool(r.get("passive")) for r in relevant),
                            "once": any(bool(r.get("once")) for r in relevant),
                        },
                    },
                )
                found += 1

            self._log(f"CDP listener scan: inspected={inspected} found={found}", log)
        finally:
            try:
                await cdp.detach()
            except Exception:
                pass

    async def _collect_ax_tree(self, context, page, page_url: str, log: Optional[List[str]], *, deadline: float) -> None:
        if self._remaining_budget(deadline) < self.cfg.min_budget_for_ax_s:
            return

        browser_name = "unknown"
        try:
            if getattr(context, "browser", None) and context.browser:
                browser_name = context.browser.browser_type.name
        except Exception:
            browser_name = "unknown"

        if browser_name == "chromium":
            try:
                cdp = await context.new_cdp_session(page)
                try:
                    await self._cdp_send(cdp, "Accessibility.enable", {}, log)
                    ax = await self._cdp_send(cdp, "Accessibility.getFullAXTree", {}, log)
                    nodes = (ax or {}).get("nodes", []) or []
                    kept = 0

                    def prop(node: Dict[str, Any], key: str) -> str:
                        v = node.get(key)
                        if isinstance(v, dict) and "value" in v:
                            return str(v.get("value") or "")
                        return str(v or "")

                    for n in nodes:
                        if self._remaining_budget(deadline) < 0.25:
                            break
                        if kept >= int(self.cfg.max_ax_hits):
                            break
                        if not isinstance(n, dict):
                            continue

                        role = prop(n, "role").lower()
                        if role and role not in self.cfg.ax_roles:
                            continue

                        self._emit_hit(
                            page_url,
                            "ax_node",
                            {
                                "role": role or "unknown",
                                "name": prop(n, "name"),
                                "value": prop(n, "value"),
                                "selector_hint": "ax_tree",
                                "source": "cdp",
                            },
                        )
                        kept += 1

                    self._log(f"AX tree (CDP): kept={kept}", log)
                    return
                finally:
                    try:
                        await cdp.detach()
                    except Exception:
                        pass
            except Exception as e:
                self._log(f"AX tree via CDP failed; fallback: {e}", log)

        try:
            snap = await asyncio.wait_for(page.accessibility.snapshot(), timeout=min(self.cfg.per_eval_timeout_s, self._remaining_budget(deadline)))
            q = [snap] if isinstance(snap, dict) else []
            kept = 0
            while q and kept < int(self.cfg.max_ax_hits) and self._remaining_budget(deadline) > 0.2:
                cur = q.pop(0)
                if not isinstance(cur, dict):
                    continue
                role = str(cur.get("role") or "").lower()
                if role in self.cfg.ax_roles:
                    self._emit_hit(
                        page_url,
                        "ax_node",
                        {
                            "role": role,
                            "name": str(cur.get("name") or ""),
                            "value": str(cur.get("value") or ""),
                            "disabled": bool(cur.get("disabled", False)),
                            "focused": bool(cur.get("focused", False)),
                            "selector_hint": "ax_snapshot",
                            "source": "playwright",
                        },
                    )
                    kept += 1

                children = cur.get("children") or []
                if isinstance(children, list):
                    q.extend(children)

            if kept:
                self._log(f"AX snapshot (Playwright): kept={kept}", log)
        except Exception as e:
            self._log(f"AX snapshot failed: {e}", log)

    async def _pick_click_targets(self, page, log: Optional[List[str]]) -> List[Dict[str, Any]]:
        payload = await self._safe_eval(
            page,
            """
            (cfg) => {
                const hints = (cfg.hints || []).map(s => String(s||"").toLowerCase());
                const max = cfg.max|0;

                function isVisible(el){
                    try {
                        const st = getComputedStyle(el);
                        if (st.display === "none" || st.visibility === "hidden" || parseFloat(st.opacity||"1") <= 0) return false;
                        const r = el.getBoundingClientRect();
                        if (r.width <= 2 || r.height <= 2) return false;
                        const vw = Math.max(document.documentElement.clientWidth||0, window.innerWidth||0);
                        const vh = Math.max(document.documentElement.clientHeight||0, window.innerHeight||0);
                        if (r.bottom < 0 || r.right < 0) return false;
                        if (r.top > vh || r.left > vw) return false;
                        return true;
                    } catch { return false; }
                }

                function textOf(el){
                    try { return (el.innerText || el.textContent || el.value || "").trim().slice(0, 90); }
                    catch { return ""; }
                }

                function selectorOf(el){
                    try {
                        if (el.id) return `#${CSS.escape(el.id)}`;
                        const cls = (typeof el.className === "string" ? el.className : "");
                        const c1 = cls.split(/\\s+/).filter(Boolean)[0];
                        if (c1) return `${el.tagName.toLowerCase()}.${CSS.escape(c1)}`;
                        return el.tagName.toLowerCase();
                    } catch { return ""; }
                }

                const sel = "button, [role='button'], a[role='button'], input[type='button'], input[type='submit'], [onclick]";
                const cands = Array.from(document.querySelectorAll(sel)).slice(0, 100);

                const out = [];
                for (const el of cands){
                    if (!isVisible(el)) continue;
                    const t = textOf(el);
                    const tl = t.toLowerCase();
                    let score = 0;
                    let reason = [];
                    if (t) score += 0.2;
                    for (const h of hints){
                        if (h && tl.includes(h)) {
                            score += 1.0;
                            reason.push(`text:${h}`);
                            break;
                        }
                    }
                    if (el.tagName.toLowerCase() === "button") {
                        score += 0.2;
                        reason.push("button");
                    }
                    if (el.getAttribute("aria-label")) {
                        score += 0.1;
                        reason.push("aria-label");
                    }
                    const selector = selectorOf(el);
                    if (!selector) continue;
                    out.push({selector, text: t, score, reason: reason.join(",")});
                }

                out.sort((a,b) => b.score - a.score);
                return out.slice(0, max);
            }
            """,
            {"hints": self.cfg.cta_text_hints, "max": 4},
            log,
        )
        return payload if isinstance(payload, list) else []

    async def _simulate_and_rescan(self, context, page, page_url: str, log: Optional[List[str]], *, deadline: float) -> None:
        if self._remaining_budget(deadline) < self.cfg.min_budget_for_dynamic_s:
            return

        # One short scroll only
        try:
            await page.evaluate("() => window.scrollBy(0, Math.max(160, window.innerHeight * 0.6));")
            await page.wait_for_timeout(int(self.cfg.sim_scroll_delay_ms))
        except Exception:
            pass

        if self._remaining_budget(deadline) >= self.cfg.min_budget_for_post_phase_s:
            await self._collect_phase(page, page_url, log, phase="post_scroll", deadline=deadline)

        if self._remaining_budget(deadline) < 0.9:
            self._log("Dynamic sim: not enough budget left for click phase.", log)
            return

        targets = await self._pick_click_targets(page, log)
        if not targets:
            self._log("Dynamic sim: no click targets selected.", log)
            return

        clicks_done = 0
        for t in targets[: int(self.cfg.sim_click_targets)]:
            if self._remaining_budget(deadline) < 0.8:
                break

            selector = str(t.get("selector") or "")
            if not selector:
                continue

            try:
                handle = await page.query_selector(selector)
                if not handle:
                    continue
                await handle.scroll_into_view_if_needed(timeout=700)
                await handle.click(timeout=int(self.cfg.sim_click_timeout_ms))
                clicks_done += 1
                self._emit_hit(
                    page_url,
                    "interaction_action",
                    {
                        "phase": f"post_click_{clicks_done}",
                        "action": "click",
                        "selector_hint": selector,
                        "reason": str(t.get("reason") or ""),
                        "text_preview": str(t.get("text") or ""),
                    },
                )
                await page.wait_for_timeout(int(self.cfg.per_action_settle_ms))

                if self._remaining_budget(deadline) >= self.cfg.min_budget_for_post_phase_s:
                    await self._collect_phase(page, page_url, log, phase=f"post_click_{clicks_done}", deadline=deadline)
            except Exception:
                continue

        self._log(f"Dynamic sim: scroll_steps={self.cfg.sim_scroll_steps} clicks={clicks_done}", log)

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


@dataclass
class _LinkIntel:
    url: str
    canonical_url: str
    host: str
    path: str
    source: str
    parent: str = ""
    score: float = 0.0
    hits: int = 0
    first_seen: float = field(default_factory=time.time)
    last_seen: float = field(default_factory=time.time)
    content_type: str = ""
    status: Optional[int] = None
    kind: str = "unknown"
    tokens: Tuple[str, ...] = field(default_factory=tuple)
    evidence: Tuple[str, ...] = field(default_factory=tuple)


@dataclass
class _GuidanceBundle:
    seed_url: str
    canonical_seed: str
    referer: Optional[str]
    accept: Optional[str]
    candidates: List[Dict[str, Any]]


@dataclass
class _PastLinkState:
    canonical_url: str
    first_seen: float = field(default_factory=time.time)
    last_seen: float = field(default_factory=time.time)
    last_success: float = 0.0
    last_status: Optional[int] = None
    last_error: str = ""
    hits: int = 0
    successes: int = 0
    failures: int = 0
    consecutive_failures: int = 0
    timeout_hits: int = 0
    deep_parses: int = 0
    deep_parse_skips: int = 0
    memo_hits: int = 0
    cooldown_until: float = 0.0
    body_cooldown_until: float = 0.0
    parse_cooldown_until: float = 0.0
    latency_ema_ms: float = 0.0
    last_fingerprint: str = ""
    same_fingerprint_hits: int = 0
    last_child_digest: str = ""
    same_child_digest_hits: int = 0
    consecutive_zero_child_parses: int = 0
    last_parse_mode: str = ""


@dataclass
class _ResponseMemo:
    fingerprint: str
    final_url: str
    status: Optional[int]
    content_type: str
    extracted_urls: Tuple[str, ...] = field(default_factory=tuple)
    mode: str = "full"
    hits: int = 0
    first_seen: float = field(default_factory=time.time)
    last_seen: float = field(default_factory=time.time)


class _PastLinkGuard:
    """
    Learns which exact URLs are runtime traps.

    Main idea:
    - repeated request failures become cheap
    - repeated giant/same-body parses downgrade from full -> light -> skip
    - repeated pages that produce the same exact child set get parse-cooled down
    - body-level penalties do not have to block HEAD requests forever
    """

    _HARD_ERRORS = {
        "chunk_timeout",
        "decompression_failed",
        "decompression_ratio_blocked",
        "decompression_hard_cap_blocked",
        "magic_byte_blocked",
        "entropy_blocked",
    }

    def __init__(self, *, max_entries: int = 8192):
        self.max_entries = int(max(256, max_entries))
        self._states: Dict[str, _PastLinkState] = {}

    def clear(self) -> None:
        self._states.clear()

    def _get(self, canonical_url: str) -> _PastLinkState:
        state = self._states.get(canonical_url)
        if state is None:
            state = _PastLinkState(canonical_url=canonical_url)
            self._states[canonical_url] = state
            self._prune_if_needed()
        return state

    def _prune_if_needed(self) -> None:
        if len(self._states) <= self.max_entries:
            return
        drop_n = max(32, len(self._states) - self.max_entries)
        oldest = sorted(self._states.items(), key=lambda kv: kv[1].last_seen)[:drop_n]
        for key, _ in oldest:
            self._states.pop(key, None)

    def allow_request(self, canonical_url: str, *, method: str = "GET", want_body: bool = True) -> Tuple[bool, str]:
        if not canonical_url:
            return True, ""
        state = self._states.get(canonical_url)
        if not state:
            return True, ""

        now = time.time()
        state.last_seen = now

        if state.cooldown_until > now:
            return False, f"url_cooldown:{round(state.cooldown_until - now, 2)}"

        if want_body and method.upper() != "HEAD" and state.body_cooldown_until > now:
            return False, f"body_cooldown:{round(state.body_cooldown_until - now, 2)}"

        return True, ""

    def note_success(self, canonical_url: str, *, status: Optional[int], elapsed_ms: float) -> None:
        if not canonical_url:
            return
        state = self._get(canonical_url)
        now = time.time()
        state.last_seen = now
        state.last_success = now
        state.last_status = status
        state.last_error = ""
        state.hits += 1
        state.successes += 1
        state.consecutive_failures = 0
        state.cooldown_until = 0.0
        state.body_cooldown_until = 0.0
        if elapsed_ms > 0:
            if state.latency_ema_ms <= 0:
                state.latency_ema_ms = float(elapsed_ms)
            else:
                state.latency_ema_ms = (state.latency_ema_ms * 0.82) + (float(elapsed_ms) * 0.18)

    def note_failure(self, canonical_url: str, *, error: str, status: Optional[int] = None, want_body: bool = True) -> None:
        if not canonical_url:
            return

        state = self._get(canonical_url)
        now = time.time()
        err = str(error or "request_failed")

        state.last_seen = now
        state.last_status = status
        state.last_error = err
        state.hits += 1
        state.failures += 1
        state.consecutive_failures += 1
        if "timeout" in err:
            state.timeout_hits += 1

        penalty = 0.0
        body_penalty = 0.0

        if status in {404, 410}:
            penalty = 240.0
        elif status in {401, 403, 416, 429}:
            penalty = 90.0
        elif err in self._HARD_ERRORS:
            body_penalty = 300.0 if want_body else 120.0
        elif err.startswith("body_cooldown"):
            body_penalty = 30.0
        elif "timeout" in err:
            body_penalty = min(180.0, 25.0 * state.timeout_hits)
        elif state.consecutive_failures >= 3:
            penalty = min(180.0, 15.0 * (state.consecutive_failures - 2))

        if penalty > 0.0:
            state.cooldown_until = max(state.cooldown_until, now + penalty)
        if body_penalty > 0.0:
            state.body_cooldown_until = max(state.body_cooldown_until, now + body_penalty)

    def select_parse_mode(
        self,
        canonical_url: str,
        *,
        fingerprint: str,
        body_size: int,
        content_type: str,
    ) -> str:
        if not canonical_url:
            return "full"

        state = self._get(canonical_url)
        now = time.time()
        state.last_seen = now

        if state.parse_cooldown_until > now:
            state.deep_parse_skips += 1
            return "skip"

        if fingerprint and state.last_fingerprint == fingerprint:
            state.same_fingerprint_hits += 1
        else:
            state.last_fingerprint = fingerprint
            state.same_fingerprint_hits = 1
            state.same_child_digest_hits = 0
            state.consecutive_zero_child_parses = 0

        ct = (content_type or "").lower()
        is_htmlish = ("html" in ct) or ("xml" in ct) or (not ct)
        large = body_size >= 250_000
        huge = body_size >= 700_000
        giant = body_size >= 1_500_000

        if state.same_fingerprint_hits >= 4 and (large or huge):
            state.deep_parse_skips += 1
            state.parse_cooldown_until = max(state.parse_cooldown_until, now + 240.0)
            return "skip"

        if state.same_fingerprint_hits >= 3 and huge:
            state.deep_parse_skips += 1
            state.parse_cooldown_until = max(state.parse_cooldown_until, now + 120.0)
            return "light"

        if giant:
            return "light"

        if large and is_htmlish and state.deep_parses >= 1 and state.same_fingerprint_hits >= 2:
            return "light"

        if state.latency_ema_ms >= 4500 and large:
            return "light"

        return "full"

    def note_parse(self, canonical_url: str, *, mode: str, extracted_urls: Optional[Iterable[str]] = None) -> None:
        if not canonical_url:
            return

        state = self._get(canonical_url)
        now = time.time()
        state.last_seen = now
        state.last_parse_mode = str(mode or "")

        if mode == "skip":
            state.deep_parse_skips += 1
            return
        if mode == "memo":
            state.memo_hits += 1
            return

        state.deep_parses += 1

        urls = [str(u).strip() for u in (extracted_urls or ()) if str(u).strip()]
        if not urls:
            state.consecutive_zero_child_parses += 1
            if state.consecutive_zero_child_parses >= 2:
                state.parse_cooldown_until = max(state.parse_cooldown_until, now + min(180.0, 30.0 * state.consecutive_zero_child_parses))
            return

        state.consecutive_zero_child_parses = 0
        digest = hashlib.sha1("\n".join(sorted(set(urls))[:256]).encode("utf-8", errors="ignore")).hexdigest()
        if digest and digest == state.last_child_digest:
            state.same_child_digest_hits += 1
        else:
            state.last_child_digest = digest
            state.same_child_digest_hits = 1

        if state.same_child_digest_hits >= 3:
            state.parse_cooldown_until = max(state.parse_cooldown_until, now + 180.0)


class _ResponseMemoStore:
    """
    Caches extraction work for repeated identical bodies/final URLs.
    """

    def __init__(self, *, max_entries: int = 2048, max_urls_per_entry: int = 300):
        self.max_entries = int(max(64, max_entries))
        self.max_urls_per_entry = int(max(8, max_urls_per_entry))
        self._items: Dict[str, _ResponseMemo] = {}

    def clear(self) -> None:
        self._items.clear()

    def make_fingerprint(
        self,
        *,
        final_url: str,
        status: Optional[int],
        content_type: str,
        body: bytes,
    ) -> str:
        h = hashlib.sha1()
        h.update((final_url or "").encode("utf-8", errors="ignore"))
        h.update(b"\0")
        h.update(str(status).encode("ascii", errors="ignore"))
        h.update(b"\0")
        h.update((content_type or "").lower().encode("utf-8", errors="ignore"))
        h.update(b"\0")
        h.update(str(len(body)).encode("ascii", errors="ignore"))
        if body:
            h.update(body[:131072])
        return h.hexdigest()

    def get(self, fingerprint: str) -> Optional[_ResponseMemo]:
        item = self._items.get(fingerprint)
        if item is None:
            return None
        item.hits += 1
        item.last_seen = time.time()
        return item

    def remember(
        self,
        *,
        fingerprint: str,
        final_url: str,
        status: Optional[int],
        content_type: str,
        extracted_urls: Iterable[str],
        mode: str,
    ) -> _ResponseMemo:
        now = time.time()
        urls: List[str] = []
        seen: Set[str] = set()
        for raw in extracted_urls:
            s = str(raw or "").strip()
            if not s or s in seen:
                continue
            seen.add(s)
            urls.append(s)
            if len(urls) >= self.max_urls_per_entry:
                break

        item = self._items.get(fingerprint)
        if item is None:
            item = _ResponseMemo(
                fingerprint=fingerprint,
                final_url=final_url,
                status=status,
                content_type=content_type,
                extracted_urls=tuple(urls),
                mode=mode,
                hits=1,
                first_seen=now,
                last_seen=now,
            )
            self._items[fingerprint] = item
            self._prune_if_needed()
            return item

        item.final_url = final_url or item.final_url
        item.status = status if status is not None else item.status
        item.content_type = content_type or item.content_type
        if urls:
            merged = list(item.extracted_urls)
            for u in urls:
                if u not in merged:
                    merged.append(u)
            item.extracted_urls = tuple(merged[: self.max_urls_per_entry])
        item.mode = mode or item.mode
        item.hits += 1
        item.last_seen = now
        return item

    def _prune_if_needed(self) -> None:
        if len(self._items) <= self.max_entries:
            return
        drop_n = max(16, len(self._items) - self.max_entries)
        oldest = sorted(self._items.items(), key=lambda kv: kv[1].last_seen)[:drop_n]
        for key, _ in oldest:
            self._items.pop(key, None)


class _RelationBudget:
    def __init__(self, *, max_parents: int = 2500, max_children_per_parent: int = 192, max_referers_per_host: int = 64):
        self.max_parents = int(max(32, max_parents))
        self.max_children_per_parent = int(max(8, max_children_per_parent))
        self.max_referers_per_host = int(max(8, max_referers_per_host))

    def add_child(self, mapping: Dict[str, Set[str]], parent: str, child: str, *, intel: Dict[str, _LinkIntel]) -> None:
        if not parent or not child or parent == child:
            return
        bucket = mapping.setdefault(parent, set())
        bucket.add(child)
        if len(bucket) > self.max_children_per_parent:
            ranked = sorted(
                bucket,
                key=lambda u: (
                    getattr(intel.get(u), "score", 0.0),
                    getattr(intel.get(u), "hits", 0),
                    getattr(intel.get(u), "last_seen", 0.0),
                ),
                reverse=True,
            )
            mapping[parent] = set(ranked[: self.max_children_per_parent])
        if len(mapping) > self.max_parents:
            ranked_parents = sorted(
                mapping.items(),
                key=lambda kv: max((getattr(intel.get(u), "last_seen", 0.0) for u in kv[1]), default=0.0),
                reverse=True,
            )
            keep = dict(ranked_parents[: self.max_parents])
            mapping.clear()
            mapping.update(keep)

    def add_referer(self, host_buckets: Dict[str, Dict[str, float]], host: str, referer: str, weight: float) -> None:
        if not host or not referer:
            return
        bucket = host_buckets.setdefault(host, {})
        bucket[referer] = float(bucket.get(referer, 0.0)) + float(weight)
        if len(bucket) > self.max_referers_per_host:
            ranked = sorted(bucket.items(), key=lambda kv: kv[1], reverse=True)[: self.max_referers_per_host]
            host_buckets[host] = dict(ranked)


class HTTPSSubmanager:
    """
    Industrial-grade shared HTTPS engine (aiohttp-only), now with built-in link intelligence:
      - keeps the existing request surface used by the rest of the codebase
      - learns from redirects, HTML, text payloads, Link/Location headers, and prior success
      - scores related URLs by similarity and can guide follow-up fetches automatically
      - improves per-request headers (referer / accept) using its own observed context

    Small internal additions in this rewrite:
      - per-request coalescing for identical in-flight fetches
      - stronger body/parse cooldowns for repeated trap links
      - same-child-set detection so giant pages stop being reparsed forever
      - slightly stricter canonicalization and HTML extraction caps
    """

    _MAGIC_EXE = (b"MZ",)
    _MAGIC_PDF = (b"%PDF",)
    _MAGIC_PNG = (b"\x89PNG\r\n\x1a\n",)
    _MAGIC_JPG = (b"\xff\xd8\xff",)
    _MAGIC_GIF = (b"GIF87a", b"GIF89a")
    _MAGIC_ZIP = (b"PK\x03\x04", b"PK\x05\x06", b"PK\x07\x08")

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

    _TRACKING_QS = {
        "utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
        "utm_id", "utm_name", "utm_reader", "utm_viz_id",
        "gclid", "dclid", "gbraid", "wbraid", "fbclid", "msclkid", "ttclid", "twclid", "yclid",
        "mc_cid", "mc_eid", "ref", "referrer",
    }

    _URL_RE = re.compile(r"\bhttps?://[^\s\"'<>]+", re.I)
    _HTML_ATTR_RE = re.compile(
        r"(?:href|src|data-src|data-href|poster|content)=[\"']([^\"']+)[\"']",
        re.I,
    )
    _TOKEN_RE = re.compile(r"[a-z0-9]{2,}", re.I)

    _ASSETISH_HINTS = (
        ".m3u8", ".mpd", ".m4s", ".mp4", ".webm", ".ts", ".mkv", ".jpg", ".jpeg", ".png", ".gif",
        "manifest", "playlist", "stream", "segment", "chunk", "frag", "download", "media", "video", "audio",
        "cdn", "playback", "thumb", "poster", "graphql", "api",
    )

    _MEDIA_ACCEPTS = {
        "video": "video/*,application/vnd.apple.mpegurl,application/dash+xml;q=0.9,*/*;q=0.5",
        "audio": "audio/*,application/octet-stream;q=0.8,*/*;q=0.5",
        "image": "image/avif,image/webp,image/apng,image/*,*/*;q=0.5",
        "json": "application/json,text/plain,*/*",
        "html": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "generic": "*/*",
    }

    _RETRYABLE_STATUS = {408, 409, 425, 429, 500, 502, 503, 504}
    _MAX_INTEL_URLS = 6000

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
        max_redirects: int = 5,
        total_timeout_s: float = 15.0,
        connect_timeout_s: float = 5.0,
        sock_read_timeout_s: float = 7.0,
        chunk_timeout_s: float = 5.0,
        chunk_size: int = 64 * 1024,

        # MIME early exit
        heavy_mime_hints: Tuple[str, ...] = ("video/", "audio/", "application/octet-stream"),
        heavy_snippet_cap: int = 1_000_000,

        # ------------------ Secure Gateway ------------------
        enable_magic_byte_verification: bool = True,
        magic_pe_kill_mime_allow: Tuple[str, ...] = ("application/x-msdownload", "application/octet-stream"),
        magic_pe_kill_ext_block: Tuple[str, ...] = (".js", ".mjs", ".css", ".json", ".xml", ".txt", ".html", ".htm"),
        enable_entropy_filter: bool = True,
        entropy_sample_bytes: int = 64_000,
        entropy_threshold: float = 7.25,
        min_printable_ratio: float = 0.75,
        enable_decompression_bomb_guard: bool = True,
        decompress_ratio_limit: float = 120.0,
        decompress_hard_cap_bytes: int = 12_000_000,

        # ------------------ Domain reputation (optional) ------------------
        enable_domain_reputation_filter: bool = False,
        domain_denylist: Optional[Tuple[str, ...]] = None,
        parked_domain_hints: Tuple[str, ...] = (
            "sedoparking", "parkingcrew", "bodis", "domainparking", "namebright",
            "dan.com", "hugedomains", "afternic", "parking", "buythisdomain",
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
        self.enable_cookies = bool(enable_cookies)
        self.allow_redirects = bool(allow_redirects)
        self.max_redirects = int(max_redirects)
        self.total_timeout_s = float(total_timeout_s)
        self.connect_timeout_s = float(connect_timeout_s)
        self.sock_read_timeout_s = float(sock_read_timeout_s)
        self.chunk_timeout_s = float(chunk_timeout_s)
        self.chunk_size = int(chunk_size)
        self.heavy_mime_hints = tuple(str(x).lower() for x in heavy_mime_hints)
        self.heavy_snippet_cap = int(heavy_snippet_cap)
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
        self.enable_domain_reputation_filter = bool(enable_domain_reputation_filter)
        self.domain_denylist = tuple((domain_denylist or ()))
        self.parked_domain_hints = tuple(x.lower() for x in parked_domain_hints)

        self._session: Optional[aiohttp.ClientSession] = None
        self._connector: Optional[aiohttp.TCPConnector] = None
        self._ssl_context: Optional[ssl.SSLContext] = None
        self._host_sem: Dict[str, asyncio.Semaphore] = {}
        self._host_cooldown_until: Dict[str, float] = {}
        self._host_last_ok_url: Dict[str, str] = {}
        self._cooldown_lock = asyncio.Lock()

        # intelligence / self-guidance
        self._intel_by_url: Dict[str, _LinkIntel] = {}
        self._children_by_parent: Dict[str, Set[str]] = {}
        self._seed_to_candidates: Dict[str, Set[str]] = {}
        self._host_accept_bias: Dict[str, str] = {}
        self._host_referers: Dict[str, Dict[str, float]] = {}
        self._intel_lock = asyncio.Lock()

        # runtime helpers for long-lived sniffers
        self._past_link_guard = _PastLinkGuard()
        self._response_memo = _ResponseMemoStore()
        self._relation_budget = _RelationBudget()

        # identical in-flight request coalescing
        self._inflight: Dict[str, asyncio.Task] = {}
        self._inflight_lock = asyncio.Lock()

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
        self._session = aiohttp.ClientSession(
            connector=self._connector,
            cookie_jar=jar,
            headers=self._base_browser_headers(),
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
        self._host_accept_bias.clear()
        self._host_referers.clear()
        self._past_link_guard.clear()
        self._response_memo.clear()
        async with self._inflight_lock:
            self._inflight.clear()

    # ------------------------------------------------------------------
    # Public additions for sniffers / trackers (optional, no caller changes required)
    # ------------------------------------------------------------------

    async def register_sniffer_candidates(
        self,
        page_url: str,
        items: Sequence[Dict[str, Any]],
        *,
        source: str = "sniffer",
    ) -> None:
        seed = self._canonicalize_url(page_url)
        if not seed or not items:
            return
        for item in items:
            if not isinstance(item, dict):
                continue
            url = self._canonicalize_url(str(item.get("url") or ""))
            if not url:
                continue
            kind = self._classify_url_kind(url, str(item.get("content_type") or ""))
            score = 2.0 + self._score_url_similarity(seed, url)
            if kind in ("video", "audio", "image", "manifest", "json"):
                score += 1.0
            await self._remember_candidate(
                url=url,
                source=source,
                parent=seed,
                score=score,
                kind=kind,
                content_type=str(item.get("content_type") or ""),
                evidence=(str(item.get("tag") or source), str(item.get("kind") or kind)),
            )

    async def get_guidance(self, seed_url: str, *, limit: int = 24) -> Dict[str, Any]:
        bundle = await self._build_guidance_bundle(seed_url, limit=limit)
        return {
            "seed_url": bundle.seed_url,
            "canonical_seed": bundle.canonical_seed,
            "referer": bundle.referer,
            "accept": bundle.accept,
            "candidates": bundle.candidates,
        }

    async def head(self, url: str, *, allow_redirects: Optional[bool] = None, headers: Optional[Dict[str, str]] = None) -> Tuple[Optional[int], Dict[str, str]]:
        r = await self._request("HEAD", url, want_body=False, allow_redirects=allow_redirects, headers=headers)
        return r.status, r.headers

    async def get_bytes(
        self,
        url: str,
        *,
        allow_redirects: Optional[bool] = None,
        headers: Optional[Dict[str, str]] = None,
        max_bytes: Optional[int] = None,
    ) -> bytes:
        r = await self._request("GET", url, want_body=True, allow_redirects=allow_redirects, headers=headers, max_bytes=max_bytes)
        return bytes(r.body or b"") if r.ok else b""

    async def get_text(
        self,
        url: str,
        *,
        allow_redirects: Optional[bool] = None,
        headers: Optional[Dict[str, str]] = None,
        max_bytes: Optional[int] = None,
    ) -> str:
        raw = await self.get_bytes(url, allow_redirects=allow_redirects, headers=headers, max_bytes=max_bytes)
        if not raw:
            return ""
        return self._decode_body(raw)

    async def get_prefix(
        self,
        url: str,
        *,
        size: int = 8192,
        timeout_ms: Optional[int] = None,
        headers: Optional[Dict[str, str]] = None,
        allow_redirects: bool = True,
    ) -> bytes:
        url = str(url or "")
        size = max(0, int(size))
        if not url or size <= 0:
            return b""
        h = dict(headers or {})
        if not any(k.lower() == "range" for k in h):
            h["Range"] = f"bytes=0-{max(0, size - 1)}"

        async def _do() -> bytes:
            r = await self._request("GET", url, want_body=True, allow_redirects=allow_redirects, headers=h, max_bytes=size)
            if not r.ok or not r.body:
                return b""
            return bytes(r.body[:size])

        if timeout_ms and timeout_ms > 0:
            try:
                return await asyncio.wait_for(_do(), timeout=float(timeout_ms) / 1000.0)
            except Exception:
                return b""
        try:
            return await _do()
        except Exception:
            return b""

    async def probe(
        self,
        url: str,
        *,
        range_bytes: int = 8192,
        timeout_ms: Optional[int] = None,
        headers: Optional[Dict[str, str]] = None,
        allow_redirects: bool = True,
        hash_algo: str = "sha256",
    ) -> Dict[str, Any]:
        url = str(url or "")
        out: Dict[str, Any] = {
            "url": url,
            "ok": False,
            "status": None,
            "final_url": url,
            "content_type": None,
            "content_length": None,
            "hash_prefix": None,
            "hash_algo": hash_algo,
            "error": "",
        }
        if not url:
            out["error"] = "empty_url"
            return out

        try:
            status, hdrs = await self.head(url)
            out["status"] = status
            out["content_type"] = hdrs.get("Content-Type") or hdrs.get("content-type") or None
            out["content_length"] = hdrs.get("Content-Length") or hdrs.get("content-length") or None
        except Exception as e:
            out["error"] = f"head_failed:{e}"

        try:
            prefix = await self.get_prefix(
                url,
                size=int(range_bytes),
                timeout_ms=timeout_ms,
                headers=headers,
                allow_redirects=allow_redirects,
            )
            if prefix:
                algo = (hash_algo or "sha256").lower()
                if algo == "sha1":
                    out["hash_prefix"] = hashlib.sha1(prefix).hexdigest()
                elif algo == "md5":
                    out["hash_prefix"] = hashlib.md5(prefix).hexdigest()
                else:
                    out["hash_prefix"] = hashlib.sha256(prefix).hexdigest()
        except Exception as e:
            if not out["error"]:
                out["error"] = f"prefix_failed:{e}"

        out["ok"] = bool(out.get("status") and 200 <= int(out["status"]) < 300)
        return out

    # ------------------------------------------------------------------
    # Core request path
    # ------------------------------------------------------------------

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
        method = (method or "GET").upper().strip()
        allow_redirects = self.allow_redirects if allow_redirects is None else bool(allow_redirects)
        max_bytes = self.max_bytes if max_bytes is None else int(max_bytes)

        key = self._request_coalesce_key(
            method=method,
            url=url,
            want_body=want_body,
            allow_redirects=allow_redirects,
            headers=headers,
            max_bytes=max_bytes,
        )

        # Coalesce only body-bearing GET requests or HEADs with the same request shape.
        async with self._inflight_lock:
            existing = self._inflight.get(key)
            if existing is not None:
                try:
                    return await existing
                except Exception as e:
                    return _HTTPResult(False, None, {}, str(url or ""), b"", error=str(e) or "request_failed")

            task = asyncio.create_task(
                self._request_uncached(
                    method,
                    url,
                    want_body=want_body,
                    allow_redirects=allow_redirects,
                    headers=headers,
                    max_bytes=max_bytes,
                )
            )
            self._inflight[key] = task

        try:
            return await task
        finally:
            async with self._inflight_lock:
                if self._inflight.get(key) is task:
                    self._inflight.pop(key, None)

    async def _request_uncached(
        self,
        method: str,
        url: str,
        *,
        want_body: bool,
        allow_redirects: bool,
        headers: Optional[Dict[str, str]],
        max_bytes: int,
    ) -> _HTTPResult:
        if not self._session:
            raise RuntimeError("HTTPSSubmanager must be used in an async context (async with HTTPSSubmanager(...) as http).")

        host = self._host(url)
        canonical_req = self._canonicalize_url(url)

        if self.enable_domain_reputation_filter and self._is_toxic_domain(host):
            return _HTTPResult(False, None, {}, str(url or ""), b"", error="domain_reputation_blocked")

        allowed, reason = self._past_link_guard.allow_request(canonical_req or str(url or ""), method=method, want_body=want_body)
        if not allowed:
            return _HTTPResult(False, None, {}, str(url or ""), b"", error=reason)

        sem = self._get_host_semaphore(host)
        last_exc = ""

        for attempt in range(self.retries + 1):
            await self._respect_host_cooldown(host)
            proxy = self._choose_proxy()
            req_headers: Dict[str, str] = {}
            req_headers.update(self._per_request_headers(url))
            if headers:
                req_headers.update(headers)

            started = time.perf_counter()
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
                        final_canonical = self._canonicalize_url(final_url) or canonical_req or str(url or "")
                        status = int(resp.status)
                        hdrs = dict(resp.headers) if resp.headers else {}

                        if self.respect_retry_after and status in (429, 503):
                            ra = self._parse_retry_after(hdrs)
                            if ra:
                                await self._set_host_cooldown(host, ra)

                        body = b""
                        err = ""
                        if want_body:
                            body, err = await self._read_bounded_secure(resp, url=final_url, max_bytes=max_bytes)
                            if err:
                                self._past_link_guard.note_failure(final_canonical, error=err, status=status, want_body=True)
                                await self._learn_from_response(
                                    requested_url=str(url or ""),
                                    final_url=final_url,
                                    status=status,
                                    headers=hdrs,
                                    body=b"",
                                    request_headers=req_headers,
                                )
                                return _HTTPResult(False, status, hdrs, final_url, b"", error=err)

                        elapsed_ms = max(0.0, (time.perf_counter() - started) * 1000.0)
                        if 200 <= status < 300:
                            self._host_last_ok_url[host] = final_url
                            self._past_link_guard.note_success(final_canonical, status=status, elapsed_ms=elapsed_ms)
                        else:
                            self._past_link_guard.note_failure(final_canonical, error=f"http_status:{status}", status=status, want_body=want_body)

                        await self._learn_from_response(
                            requested_url=str(url or ""),
                            final_url=final_url,
                            status=status,
                            headers=hdrs,
                            body=body,
                            request_headers=req_headers,
                        )

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
            except asyncio.TimeoutError:
                last_exc = "timeout"
                self._past_link_guard.note_failure(canonical_req or str(url or ""), error=last_exc, want_body=want_body)
            except aiohttp.ClientError as e:
                last_exc = f"client_error:{e}"
                self._past_link_guard.note_failure(canonical_req or str(url or ""), error=last_exc, want_body=want_body)
            except Exception as e:
                last_exc = str(e)
                self._past_link_guard.note_failure(canonical_req or str(url or ""), error=last_exc, want_body=want_body)

            if attempt < self.retries:
                await asyncio.sleep(self._retry_delay(attempt))

        return _HTTPResult(False, None, {}, str(url or ""), b"", error=last_exc or "request_failed")

    # ------------------------------------------------------------------
    # Link intelligence / self-guidance
    # ------------------------------------------------------------------

    async def _learn_from_response(
        self,
        *,
        requested_url: str,
        final_url: str,
        status: Optional[int],
        headers: Dict[str, str],
        body: bytes,
        request_headers: Dict[str, str],
    ) -> None:
        req_c = self._canonicalize_url(requested_url)
        fin_c = self._canonicalize_url(final_url)
        if not req_c and not fin_c:
            return

        seed = fin_c or req_c
        ctype = self._header_get(headers, "content-type")
        kind = self._classify_url_kind(seed, ctype)

        base_score = 1.0
        if status and 200 <= status < 300:
            base_score += 1.5
        if req_c and fin_c and req_c != fin_c:
            base_score += 0.5

        await self._remember_candidate(
            url=seed,
            source="response_final",
            parent=req_c,
            score=base_score,
            kind=kind,
            status=status,
            content_type=ctype,
            evidence=(f"status:{status}",),
        )

        location = self._header_get(headers, "location")
        if location:
            loc_abs = self._canonicalize_url(urljoin(final_url or requested_url, location))
            if loc_abs:
                await self._remember_candidate(
                    url=loc_abs,
                    source="response_location",
                    parent=seed,
                    score=1.5 + self._score_url_similarity(seed, loc_abs),
                    kind=self._classify_url_kind(loc_abs, ""),
                    status=status,
                    evidence=("header:location",),
                )

        for link_url in self._extract_header_links(headers, base_url=final_url or requested_url):
            await self._remember_candidate(
                url=link_url,
                source="response_link_header",
                parent=seed,
                score=1.4 + self._score_url_similarity(seed, link_url),
                kind=self._classify_url_kind(link_url, ""),
                status=status,
                evidence=("header:link",),
            )

        accept_kind = self._classify_url_kind(seed, ctype)
        if accept_kind != "unknown":
            self._host_accept_bias[self._host(seed)] = accept_kind
        if request_headers.get("Referer"):
            self._note_referer(seed, request_headers["Referer"], weight=1.0)

        if not body:
            return
        if not self._looks_textlike(ctype) and kind not in {"html", "json"}:
            return

        fingerprint = self._response_memo.make_fingerprint(
            final_url=seed,
            status=status,
            content_type=ctype,
            body=body,
        )
        memo = self._response_memo.get(fingerprint)
        if memo is not None:
            self._past_link_guard.note_parse(seed, mode="memo", extracted_urls=memo.extracted_urls)
            await self._remember_children_from_cache(seed, memo.extracted_urls)
            return

        mode = self._past_link_guard.select_parse_mode(
            seed,
            fingerprint=fingerprint,
            body_size=len(body),
            content_type=ctype,
        )
        if mode == "skip":
            self._response_memo.remember(
                fingerprint=fingerprint,
                final_url=seed,
                status=status,
                content_type=ctype,
                extracted_urls=(),
                mode=mode,
            )
            self._past_link_guard.note_parse(seed, mode="skip", extracted_urls=())
            return

        extracted_urls = self._mine_body_urls(
            body=body,
            content_type=ctype,
            base_url=final_url or requested_url,
            kind=kind,
            mode=mode,
        )
        self._response_memo.remember(
            fingerprint=fingerprint,
            final_url=seed,
            status=status,
            content_type=ctype,
            extracted_urls=extracted_urls,
            mode=mode,
        )
        self._past_link_guard.note_parse(seed, mode=mode, extracted_urls=extracted_urls)
        await self._remember_children_from_cache(seed, extracted_urls)

    async def _remember_children_from_cache(self, seed: str, urls: Iterable[str]) -> None:
        seed_c = self._canonicalize_url(seed)
        if not seed_c:
            return
        for child in list(urls)[:300]:
            c_child = self._canonicalize_url(child)
            if not c_child or c_child == seed_c:
                continue
            score = 0.75 + self._score_url_similarity(seed_c, c_child)
            child_kind = self._classify_url_kind(c_child, "")
            if child_kind in {"video", "audio", "image", "manifest", "json"}:
                score += 0.6
            await self._remember_candidate(
                url=c_child,
                source="body_extract",
                parent=seed_c,
                score=score,
                kind=child_kind,
                status=None,
                evidence=("cached/memo extract",),
            )

    def _mine_body_urls(
        self,
        *,
        body: bytes,
        content_type: str,
        base_url: str,
        kind: str,
        mode: str,
    ) -> List[str]:
        text = self._decode_body(body)
        if not text:
            return []

        text_cap = self.max_html_chars
        if mode == "light":
            text_cap = min(text_cap, 180_000)
        text = text[:text_cap]

        urls: Set[str] = set(self._extract_urls_from_text(text))
        lowered = (content_type or "").lower()
        htmlish = ("html" in lowered) or (text[:256].lower().count("<html") > 0) or (text[:2048].lower().count("href=") > 0)
        jsonish = (kind == "json") or self._looks_jsonish(text)

        if htmlish:
            if mode == "full":
                urls.update(self._extract_asset_urls_from_html(text, base_url, max_assets=300))
            else:
                for m in self._HTML_ATTR_RE.finditer(text):
                    raw = (m.group(1) or "").strip()
                    if raw and not raw.startswith(("#", "javascript:", "mailto:", "tel:")):
                        full = self._canonicalize_url(urljoin(base_url, raw))
                        if full:
                            urls.add(full)
                            if len(urls) >= 300:
                                break
        elif jsonish:
            urls.update(self._extract_urls_from_jsonish(text, base_url, limit=300))

        # Stable return order reduces churn in child-digest tracking.
        return list(sorted(urls))[:300]

    async def _build_guidance_bundle(self, seed_url: str, *, limit: int = 24) -> _GuidanceBundle:
        seed = self._canonicalize_url(seed_url)
        host = self._host(seed)
        referer = self._pick_best_referer(seed)
        accept_kind = self._host_accept_bias.get(host) or self._classify_url_kind(seed, "")
        accept = self._MEDIA_ACCEPTS.get(accept_kind, self._MEDIA_ACCEPTS["generic"])

        candidates: List[Tuple[float, Dict[str, Any]]] = []
        for cand_url in self._seed_to_candidates.get(seed, set()):
            intel = self._intel_by_url.get(cand_url)
            if not intel:
                continue
            sim = self._score_url_similarity(seed, cand_url)
            total = float(intel.score) + sim + min(1.5, 0.2 * intel.hits)
            if intel.kind in {"video", "audio", "manifest", "json", "image"}:
                total += 0.6
            candidates.append((
                total,
                {
                    "url": intel.canonical_url,
                    "score": round(total, 3),
                    "kind": intel.kind,
                    "source": intel.source,
                    "hits": intel.hits,
                    "content_type": intel.content_type or "",
                    "status": intel.status,
                    "parent": intel.parent,
                    "evidence": list(intel.evidence[:8]),
                },
            ))

        candidates.sort(key=lambda x: (x[0], x[1]["hits"]), reverse=True)
        return _GuidanceBundle(
            seed_url=seed_url,
            canonical_seed=seed,
            referer=referer,
            accept=accept,
            candidates=[row for _, row in candidates[: max(1, int(limit))]],
        )

    async def _remember_candidate(
        self,
        *,
        url: str,
        source: str,
        parent: str = "",
        score: float = 0.0,
        kind: str = "unknown",
        status: Optional[int] = None,
        content_type: str = "",
        evidence: Iterable[str] = (),
    ) -> None:
        cu = self._canonicalize_url(url)
        if not cu:
            return
        parent_c = self._canonicalize_url(parent) if parent else ""
        if parent_c and parent_c == cu:
            parent_c = ""

        async with self._intel_lock:
            now = time.time()
            host = self._host(cu)
            path = urlparse(cu).path or "/"
            tokens = tuple(self._url_tokens(cu))
            ev = tuple(str(x) for x in evidence if str(x).strip())[:12]
            existing = self._intel_by_url.get(cu)
            if existing is None:
                self._intel_by_url[cu] = _LinkIntel(
                    url=url,
                    canonical_url=cu,
                    host=host,
                    path=path,
                    source=source,
                    parent=parent_c,
                    score=float(score),
                    hits=1,
                    first_seen=now,
                    last_seen=now,
                    content_type=content_type,
                    status=status,
                    kind=kind,
                    tokens=tokens,
                    evidence=ev,
                )
            else:
                existing.last_seen = now
                existing.hits += 1
                existing.score = max(float(existing.score), float(score))
                if content_type and not existing.content_type:
                    existing.content_type = content_type
                if status is not None:
                    existing.status = status
                if kind and existing.kind == "unknown":
                    existing.kind = kind
                if parent_c and not existing.parent:
                    existing.parent = parent_c
                if ev:
                    merged = list(existing.evidence)
                    for one in ev:
                        if one not in merged:
                            merged.append(one)
                    existing.evidence = tuple(merged[:12])

            if parent_c:
                self._relation_budget.add_child(self._children_by_parent, parent_c, cu, intel=self._intel_by_url)
                self._relation_budget.add_child(self._seed_to_candidates, parent_c, cu, intel=self._intel_by_url)
                self._note_referer(cu, parent_c, weight=max(0.5, score))

            self._prune_intel_if_needed()

    def _prune_intel_if_needed(self) -> None:
        if len(self._intel_by_url) <= self._MAX_INTEL_URLS:
            return
        drop_n = max(64, len(self._intel_by_url) - self._MAX_INTEL_URLS)
        oldest = sorted(
            self._intel_by_url.items(),
            key=lambda kv: (kv[1].last_seen, kv[1].hits, kv[1].score),
        )[:drop_n]
        dead = {k for k, _ in oldest}
        for k in dead:
            self._intel_by_url.pop(k, None)
        for mapping in (self._children_by_parent, self._seed_to_candidates):
            for parent in list(mapping.keys()):
                mapping[parent].difference_update(dead)
                if not mapping[parent]:
                    mapping.pop(parent, None)

    def _note_referer(self, url: str, referer: str, *, weight: float) -> None:
        u = self._canonicalize_url(url)
        r = self._canonicalize_url(referer)
        if not u or not r or u == r:
            return
        host = self._host(u)
        self._relation_budget.add_referer(self._host_referers, host, r, max(0.1, weight))

    def _pick_best_referer(self, url: str) -> Optional[str]:
        cu = self._canonicalize_url(url)
        if not cu:
            return None
        intel = self._intel_by_url.get(cu)
        if intel and intel.parent:
            return intel.parent
        host = self._host(cu)
        bucket = self._host_referers.get(host) or {}
        if bucket:
            return max(bucket.items(), key=lambda kv: kv[1])[0]
        return self._host_last_ok_url.get(host)

    # ------------------------------------------------------------------
    # Private helpers
    # ------------------------------------------------------------------

    def _request_coalesce_key(
        self,
        *,
        method: str,
        url: str,
        want_body: bool,
        allow_redirects: bool,
        headers: Optional[Dict[str, str]],
        max_bytes: int,
    ) -> str:
        canon = self._canonicalize_url(url) or str(url or "")
        h = []
        for k, v in sorted((headers or {}).items(), key=lambda kv: str(kv[0]).lower()):
            kl = str(k).lower()
            if kl in {"range", "accept", "referer"}:
                h.append(f"{kl}={v}")
        return "|".join([
            method.upper().strip(),
            "1" if want_body else "0",
            "1" if allow_redirects else "0",
            str(int(max_bytes)),
            canon,
            "&".join(h),
        ])

    def _build_ssl_context(self) -> ssl.SSLContext:
        if self.verify:
            ctx = ssl.create_default_context(cafile=self.ca_bundle or None)
            ctx.check_hostname = True
            ctx.verify_mode = ssl.CERT_REQUIRED
            return ctx
        ctx = ssl.create_default_context()
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
        return ctx

    def _base_browser_headers(self) -> Dict[str, str]:
        return {
            "User-Agent": self.ua,
            "Accept": self._MEDIA_ACCEPTS["html"],
            "Accept-Language": "en-US,en;q=0.9",
            "Cache-Control": "no-cache",
            "Pragma": "no-cache",
        }

    def _per_request_headers(self, url: str) -> Dict[str, str]:
        out: Dict[str, str] = {"User-Agent": self.ua}
        kind = self._host_accept_bias.get(self._host(url)) or self._classify_url_kind(url, "")
        out["Accept"] = self._MEDIA_ACCEPTS.get(kind, self._MEDIA_ACCEPTS["generic"])
        referer = self._pick_best_referer(url)
        if referer and referer != self._canonicalize_url(url):
            out["Referer"] = referer
        return out

    def _host(self, url: str) -> str:
        try:
            return urlparse(str(url or "")).netloc.lower().split(":")[0]
        except Exception:
            return ""

    def _choose_proxy(self) -> Optional[str]:
        if self.proxy_pool:
            try:
                return random.choice(self.proxy_pool)
            except Exception:
                return self.proxy
        return self.proxy

    def _get_host_semaphore(self, host: str) -> asyncio.Semaphore:
        sem = self._host_sem.get(host)
        if sem is None:
            sem = asyncio.Semaphore(max(1, self.max_conn_per_host))
            self._host_sem[host] = sem
        return sem

    async def _respect_host_cooldown(self, host: str) -> None:
        while True:
            until = self._host_cooldown_until.get(host, 0.0)
            remaining = until - time.time()
            if remaining <= 0:
                return
            await asyncio.sleep(min(remaining, 0.5))

    async def _set_host_cooldown(self, host: str, seconds: float) -> None:
        async with self._cooldown_lock:
            self._host_cooldown_until[host] = max(self._host_cooldown_until.get(host, 0.0), time.time() + max(0.0, seconds))

    def _parse_retry_after(self, headers: Dict[str, str]) -> Optional[float]:
        raw = self._header_get(headers, "retry-after")
        if not raw:
            return None
        raw = raw.strip()
        if raw.isdigit():
            return float(int(raw))
        return None

    def _retry_delay(self, attempt: int, *, server_hint: Optional[float] = None) -> float:
        if server_hint is not None:
            return max(0.0, float(server_hint))
        base = min(self.backoff_cap, self.backoff_base * (2 ** max(0, attempt)))
        return base + random.random() * min(0.25, base / 3.0)

    def _is_retryable_status(self, status: Optional[int]) -> bool:
        return bool(status in self._RETRYABLE_STATUS)

    def _is_toxic_domain(self, host: str) -> bool:
        host = (host or "").lower()
        if not host:
            return False
        if any(d and (host == d.lower() or host.endswith("." + d.lower())) for d in self.domain_denylist):
            return True
        return any(h in host for h in self.parked_domain_hints)

    def _header_get(self, headers: Dict[str, str], key: str) -> str:
        key_l = key.lower()
        for k, v in (headers or {}).items():
            if str(k).lower() == key_l:
                return str(v)
        return ""

    def _looks_textlike(self, ctype: str) -> bool:
        ct = (ctype or "").lower()
        return any(ct.startswith(p) or p in ct for p in self._TEXTLIKE_MIME_HINTS)

    def _looks_jsonish(self, text: str) -> bool:
        s = (text or "").lstrip()
        return s.startswith("{") or s.startswith("[")

    def _decode_body(self, body: bytes) -> str:
        try:
            return body.decode("utf-8", errors="ignore")[: self.max_html_chars]
        except Exception:
            try:
                return body.decode("latin-1", errors="ignore")[: self.max_html_chars]
            except Exception:
                return ""

    def _magic_byte_violation(self, url: str, ctype: str, probe: bytes) -> bool:
        ct = (ctype or "").lower()
        path = (urlparse(url).path or "").lower()
        if probe.startswith(self._MAGIC_EXE):
            if any(ct.startswith(ok) for ok in self.magic_pe_kill_mime_allow):
                return False
            if any(path.endswith(ext) for ext in self.magic_pe_kill_ext_block):
                return True
        return False

    def _shannon_entropy(self, data: bytes) -> float:
        if not data:
            return 0.0
        counts = [0] * 256
        for b in data:
            counts[b] += 1
        total = float(len(data))
        ent = 0.0
        for c in counts:
            if c:
                p = c / total
                ent -= p * math.log2(p)
        return ent

    def _printable_ratio(self, data: bytes) -> float:
        if not data:
            return 1.0
        printable = sum(1 for b in data if b in (9, 10, 13) or 32 <= b <= 126)
        return printable / max(1, len(data))

    async def _read_bounded_secure(self, resp, *, url: str, max_bytes: int) -> Tuple[bytes, str]:
        headers = dict(resp.headers or {})
        ctype = self._header_get(headers, "content-type")
        encoding = self._header_get(headers, "content-encoding").lower().strip()

        content_length_raw = self._header_get(headers, "content-length")
        try:
            content_length = int(content_length_raw) if content_length_raw else 0
        except Exception:
            content_length = 0

        if any(h in (ctype or "").lower() for h in self.heavy_mime_hints) and max_bytes > self.heavy_snippet_cap:
            max_bytes = min(max_bytes, self.heavy_snippet_cap)

        if content_length > 0 and self.enable_decompression_bomb_guard:
            if content_length > max(self.decompress_hard_cap_bytes, max_bytes * 4):
                try:
                    resp.close()
                except Exception:
                    pass
                return b"", "content_length_hard_cap_blocked"

        decompressor = None
        if self.enable_decompression_bomb_guard:
            try:
                if encoding == "gzip":
                    decompressor = zlib.decompressobj(16 + zlib.MAX_WBITS)
                elif encoding == "deflate":
                    decompressor = zlib.decompressobj()
            except Exception:
                decompressor = None

        out = bytearray()
        entropy_probe = bytearray()
        first_probe_done = False
        compressed_read = 0

        while True:
            try:
                chunk = await asyncio.wait_for(resp.content.read(self.chunk_size), timeout=self.chunk_timeout_s)
            except asyncio.TimeoutError:
                try:
                    resp.close()
                except Exception:
                    pass
                return bytes(out), "chunk_timeout"
            except Exception as e:
                return bytes(out), f"read_error:{e}"

            if not chunk:
                break

            compressed_read += len(chunk)
            produced = chunk
            if decompressor is not None:
                try:
                    produced = decompressor.decompress(chunk)
                except Exception:
                    return bytes(out), "decompression_failed"

                if self.enable_decompression_bomb_guard and compressed_read > 0:
                    ratio = (len(out) + len(produced)) / max(1, compressed_read)
                    if ratio > self.decompress_ratio_limit:
                        return bytes(out), "decompression_ratio_blocked"
                    if (len(out) + len(produced)) > self.decompress_hard_cap_bytes:
                        return bytes(out), "decompression_hard_cap_blocked"

            if self.enable_magic_byte_verification and not first_probe_done:
                first_probe_done = True
                if self._magic_byte_violation(url, ctype, produced[:16]):
                    try:
                        resp.close()
                    except Exception:
                        pass
                    return b"", "magic_byte_blocked"

            out.extend(produced)

            if self.enable_entropy_filter and self._looks_textlike(ctype) and len(entropy_probe) < self.entropy_sample_bytes:
                entropy_probe.extend(produced[: max(0, self.entropy_sample_bytes - len(entropy_probe))])

            if len(out) >= max_bytes:
                try:
                    resp.close()
                except Exception:
                    pass
                del out[max_bytes:]
                break

        if decompressor is not None:
            try:
                tail = decompressor.flush()
                if tail:
                    if self.enable_decompression_bomb_guard and compressed_read > 0:
                        ratio = (len(out) + len(tail)) / max(1, compressed_read)
                        if ratio > self.decompress_ratio_limit:
                            return bytes(out), "decompression_ratio_blocked"
                        if (len(out) + len(tail)) > self.decompress_hard_cap_bytes:
                            return bytes(out), "decompression_hard_cap_blocked"
                    out.extend(tail)
                    if len(out) > max_bytes:
                        del out[max_bytes:]
            except Exception:
                pass

        if self.enable_entropy_filter and self._looks_textlike(ctype) and entropy_probe:
            ent = self._shannon_entropy(bytes(entropy_probe))
            pr = self._printable_ratio(bytes(entropy_probe))
            if ent >= self.entropy_threshold and pr < self.min_printable_ratio:
                return bytes(out), "entropy_blocked"

        return bytes(out), ""

    def _canonicalize_url(self, u: str) -> str:
        try:
            p = urlparse(str(u or "").strip())
            if p.scheme not in ("http", "https") or not p.netloc:
                return ""
            host = p.netloc.lower().split(":")[0]
            path = p.path or "/"
            if not path.startswith("/"):
                path = "/" + path
            qs = [
                (k, v)
                for (k, v) in parse_qsl(p.query, keep_blank_values=False)
                if k.lower() not in self._TRACKING_QS
            ]
            query = urlencode(qs, doseq=True)
            return urlunparse((p.scheme.lower(), host, path, p.params, query, ""))
        except Exception:
            return ""

    def _url_tokens(self, url: str) -> List[str]:
        parsed = urlparse(str(url or ""))
        base = f"{parsed.netloc} {parsed.path} {parsed.query}".lower().replace("-", " ").replace("_", " ")
        toks = [m.group(0).lower() for m in self._TOKEN_RE.finditer(base)]
        out: List[str] = []
        seen: Set[str] = set()
        for t in toks:
            if len(t) < 2:
                continue
            if t not in seen:
                seen.add(t)
                out.append(t)
        return out[:64]

    def _score_url_similarity(self, seed_url: str, cand_url: str) -> float:
        seed = self._canonicalize_url(seed_url)
        cand = self._canonicalize_url(cand_url)
        if not seed or not cand:
            return 0.0
        if seed == cand:
            return 4.0
        ps = urlparse(seed)
        pc = urlparse(cand)
        score = 0.0
        if ps.netloc == pc.netloc:
            score += 1.4
        else:
            hs = ps.netloc.split(".")
            hc = pc.netloc.split(".")
            if len(hs) >= 2 and len(hc) >= 2 and hs[-2:] == hc[-2:]:
                score += 0.7
        if ps.path and pc.path:
            if pc.path.startswith(ps.path.rsplit("/", 1)[0]):
                score += 0.8
            if ps.path.split("/")[-1] and ps.path.split("/")[-1] in pc.path:
                score += 0.35
        ts = set(self._url_tokens(seed))
        tc = set(self._url_tokens(cand))
        if ts and tc:
            inter = len(ts & tc)
            union = len(ts | tc)
            if union:
                score += 2.4 * (inter / union)
            if any(tok in tc for tok in ("manifest", "playlist", "segment", "stream", "cdn", "video", "audio", "download")):
                score += 0.4
        return round(score, 4)

    def _classify_url_kind(self, url: str, content_type: str) -> str:
        ul = (url or "").lower()
        ct = (content_type or "").lower()
        if "text/html" in ct:
            return "html"
        if "application/json" in ct:
            return "json"
        if any(x in ct for x in ("application/vnd.apple.mpegurl", "application/x-mpegurl", "application/dash+xml")):
            return "manifest"
        if any(x in ul for x in (".m3u8", ".mpd")):
            return "manifest"
        if ct.startswith("video/") or any(x in ul for x in (".mp4", ".webm", ".mkv", ".ts", ".m4s")):
            return "video"
        if ct.startswith("audio/") or any(x in ul for x in (".mp3", ".m4a", ".aac", ".ogg", ".opus", ".wav")):
            return "audio"
        if ct.startswith("image/") or any(x in ul for x in (".jpg", ".jpeg", ".png", ".gif", ".webp", ".avif", ".svg")):
            return "image"
        if "json" in ct or "/api/" in ul or "graphql" in ul:
            return "json"
        if any(x in ul for x in self._ASSETISH_HINTS):
            return "asset"
        return "unknown"

    def _extract_urls_from_text(self, text: str) -> List[str]:
        out: List[str] = []
        seen: Set[str] = set()
        for m in self._URL_RE.finditer(text or ""):
            raw = m.group(0).strip().rstrip(")],.;:'\"")
            u = self._canonicalize_url(unescape(raw))
            if u and u not in seen:
                seen.add(u)
                out.append(u)
        return out

    def _extract_urls_from_jsonish(self, text: str, base_url: str, *, limit: int) -> List[str]:
        out: List[str] = []
        seen: Set[str] = set()
        for u in self._extract_urls_from_text(text):
            if u not in seen:
                seen.add(u)
                out.append(u)
                if len(out) >= limit:
                    return out
        for m in re.finditer(r'"(?:url|src|href|manifest|playlist|download|file)"\s*:\s*"([^\"]+)"', text or "", re.I):
            raw = m.group(1)
            cand = self._canonicalize_url(urljoin(base_url, raw.replace("\\/", "/")))
            if cand and cand not in seen:
                seen.add(cand)
                out.append(cand)
                if len(out) >= limit:
                    break
        return out

    def _extract_asset_urls_from_html(self, html: str, base_url: str, *, max_assets: int) -> List[str]:
        out: List[str] = []
        seen: Set[str] = set()
        if not html:
            return out

        def _add(raw: str) -> None:
            if len(out) >= max_assets:
                return
            raw = (raw or "").strip()
            if not raw or raw.startswith(("#", "javascript:", "mailto:", "tel:")):
                return
            full = self._canonicalize_url(urljoin(base_url, raw))
            if full and full not in seen:
                seen.add(full)
                out.append(full)

        parse_cap = min(self.max_html_chars, 250_000)
        html_slice = html[:parse_cap]

        if BeautifulSoup is not None and len(html_slice) <= 250_000:
            try:
                soup = BeautifulSoup(html_slice, "html.parser")
                for tag in soup.find_all(["a", "img", "video", "audio", "source", "link", "meta", "iframe"]):
                    for attr in ("href", "src", "data-src", "data-href", "poster", "content"):
                        val = tag.get(attr)
                        if isinstance(val, str):
                            _add(val)
                        if len(out) >= max_assets:
                            return out
            except Exception:
                pass

        if len(out) < max_assets:
            for m in self._HTML_ATTR_RE.finditer(html_slice):
                _add(m.group(1))
                if len(out) >= max_assets:
                    return out

        if len(out) < max_assets:
            for u in self._extract_urls_from_text(html_slice):
                if u not in seen:
                    seen.add(u)
                    out.append(u)
                    if len(out) >= max_assets:
                        return out
        return out

    def _extract_header_links(self, headers: Dict[str, str], *, base_url: str) -> List[str]:
        raw = self._header_get(headers, "link")
        if not raw:
            return []
        out: List[str] = []
        seen: Set[str] = set()
        for part in raw.split(","):
            m = re.search(r"<([^>]+)>", part)
            if not m:
                continue
            u = self._canonicalize_url(urljoin(base_url, m.group(1).strip()))
            if u and u not in seen:
                seen.add(u)
                out.append(u)
        return out
