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
        deny_resource_types: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {"stylesheet", "font", "manifest", "other"})

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
            "application/json", "text/json", "application/problem+json"
        })
        json_body_max_kb: int = 256
        json_url_patterns: "NetworkSniffer.Set[str]" = field(default_factory=lambda: {
            "/api/player", "/player_api", "/player/",
            "/manifest", "/playlist", "/video/", "/audio/", "/graphql"
        })

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
        canonical_page_url = self._canonicalize_url(page_url)

        found_items: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        derived_items: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []
        json_hits: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []

        seen_network: "NetworkSniffer.Set[str]" = set()
        seen_derived: "NetworkSniffer.Set[str]" = set()
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

        # NEW: response timeline events for correlation
        resp_events: "NetworkSniffer.List[NetworkSniffer.Dict[str, Any]]" = []

        # NEW: script urls for bundle scanning
        script_urls: "NetworkSniffer.List[str]" = []
        seen_scripts: "NetworkSniffer.Set[str]" = set()

        # binary signature tasks
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

        self._log(f"[NetworkSniffer] Start sniff: {canonical_page_url} (timeout={tmo}s)", log)

        # Install init scripts BEFORE goto
        if self.cfg.enable_mse_sniff:
            await self._install_mse_bridge(page, mse_events, log=log)
        if self.cfg.enable_param_sniff:
            await self._install_param_bridge(page, param_events, log=log)

        # ---------------- request handler ---------------- #
        def handle_request(req):
            try:
                rurl = self._to_str(getattr(req, "url", None))
                req_types[rurl] = self._to_str(getattr(req, "resource_type", None))
            except Exception:
                pass

            # redirect chain
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

            # request evidence (forensics + salvage header subset)
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

            # collect script URLs (for optional bundle scan)
            try:
                rt = self._to_str(getattr(req, "resource_type", None))
                if rt == "script":
                    u = self._canonicalize_url(self._to_str(getattr(req, "url", None)))
                    if u and u not in seen_scripts and self._host_allowed(u):
                        seen_scripts.add(u)
                        script_urls.append(u)
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
        def mine_headers(url: str, headers_lc: "NetworkSniffer.Dict[str, str]"):
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

        # ---------------- binary sniff helpers ---------------- #
        def req_hdrs_for(u: str) -> "NetworkSniffer.Dict[str, str]":
            ev = request_evidence.get(u) or request_evidence.get(self._canonicalize_url(u)) or {}
            return ev.get("headers_subset") or {}

        async def binary_sniff_one(*, url: str, ctype: str, resource_type: str, content_length: "NetworkSniffer.Optional[int]"):
            async with binary_sem:
                cu = self._canonicalize_url(url)
                if not cu or cu in seen_binary_sig:
                    return
                if len(seen_binary_sig) >= int(self.cfg.binary_sniff_max_tasks):
                    return
                seen_binary_sig.add(cu)

                prefix = await self._get_prefix_bytes(
                    api_ctx,
                    cu,
                    req_hdrs_for(cu),
                    timeout_ms=int(self.cfg.binary_sniff_timeout_ms),
                    prefix_bytes=int(self.cfg.binary_sniff_prefix_bytes),
                )

                kind2, cth, detail = self._guess_kind_from_magic(prefix)
                if not kind2:
                    return

                if not self._is_allowed_by_extensions(cu, extensions, kind2):
                    return

                if len(found_items) < max_items:
                    found_items.append({
                        "url": cu,
                        "text": f"[BinarySig {kind2.capitalize()}] ({detail})",
                        "tag": "binary_sig_sniff",
                        "kind": kind2,
                        "content_type": cth or (ctype or "?"),
                        "size": str(content_length) if content_length is not None else "?",
                    })

                if len(json_hits) < max_json:
                    sha = self.hashlib.sha256(prefix).hexdigest() if prefix else None
                    json_hits.append({
                        "url": cu,
                        "json": {
                            "binary_signature": True,
                            "detected_kind": kind2,
                            "detail": detail,
                            "content_type_hint": cth,
                            "prefix_sha256": sha,
                            "prefix_len": len(prefix) if prefix else 0,
                        },
                        "source_page": canonical_page_url,
                    })

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
                    if self._looks_like_ad(netloc, path):
                        return

                seen_network.add(canonical_url)

                # timeline event for correlation
                try:
                    resp_events.append({
                        "ts": self._ms_now(),
                        "type": "resp",
                        "url": canonical_url,
                        "resource_type": resource_type,
                        "status": getattr(response, "status", None),
                    })
                except Exception:
                    pass

                try:
                    hdr_raw = getattr(response, "headers", None) or {}
                    headers = {self._to_str(k).lower(): self._to_str(v) for (k, v) in hdr_raw.items()}
                except Exception:
                    headers = {}

                ctype = (headers.get("content-type") or "").lower()
                url_lower = canonical_url.lower()

                mine_headers(canonical_url, headers)

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

                cl_header = self._to_str(headers.get("content-length") or "")
                content_length: "NetworkSniffer.Optional[int]" = None
                try:
                    if cl_header.isdigit():
                        content_length = int(cl_header)
                except Exception:
                    content_length = None

                p = self._safe_urlparse(canonical_url)
                path = self._to_str(p.path or "/").lower()
                is_junk_ext = self._is_junk_by_extension(path)

                if (not is_blob) and resource_type and self._deny_by_resource_type(resource_type):
                    return

                if (not is_blob) and self._should_sniff_json(url_lower, ctype, content_length):
                    self.asyncio.create_task(handle_json(response, canonical_url))
                    return

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

                kind = (
                    self._classify_by_extension(path)
                    or (self._classify_by_content_type(ctype) if ctype else None)
                    or self._classify_by_stream_hint(url_lower)
                )

                if not kind:
                    seg_kind = self._looks_like_segment(url_lower, ctype, content_length, headers)
                    if seg_kind:
                        kind = seg_kind

                # Binary signature sniff scheduling
                if self.cfg.enable_binary_signature_sniff:
                    should_probe = self._is_binary_suspect(
                        canonical_url,
                        ctype=ctype,
                        resource_type=resource_type,
                        content_length=content_length,
                    )
                    if should_probe:
                        if (not self.cfg.binary_sniff_only_if_unknown_kind) or (kind is None):
                            if len(binary_tasks) < int(self.cfg.binary_sniff_max_tasks):
                                binary_tasks.append(self.asyncio.create_task(
                                    binary_sniff_one(
                                        url=canonical_url,
                                        ctype=ctype,
                                        resource_type=resource_type,
                                        content_length=content_length,
                                    )
                                ))

                if not kind:
                    return

                if not self._is_allowed_by_extensions(canonical_url, extensions, kind):
                    return

                mkind = self._is_manifest(canonical_url, ctype)
                if mkind and kind == "video" and len(manifests_to_expand) < max_manifests:
                    manifests_to_expand.append((response, mkind, canonical_url))
                    if self.cfg.prefer_master_manifests:
                        manifests_to_expand.sort(key=lambda t: (0 if "master" in self._to_str(t[2]).lower() else 1))

                if len(found_items) < max_items:
                    cd = self._to_str(headers.get("content-disposition") or "")
                    filename = None
                    if cd:
                        m = self.re.search(r'filename\*?=(?:UTF-8\'\')?"?([^";]+)"?', cd, self.re.I)
                        if m:
                            filename = self._to_str(m.group(1))

                    item: "NetworkSniffer.Dict[str, Any]" = {
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

                if self.cfg.enable_url_salvage:
                    status = getattr(response, "status", None)
                    if self._salvage_should_target(canonical_url, status=status, kind=kind):
                        host = self._to_str(self._safe_urlparse(canonical_url).netloc).lower()
                        if host:
                            cnt = salvage_host_counts.get(host, 0)
                            if cnt >= int(self.cfg.salvage_max_targets_per_host):
                                return
                        score = self._salvage_score(canonical_url, status=status, kind=kind)
                        prev = salvage_info.get(canonical_url)
                        if (prev is None) or (float(prev.get("score", 0.0)) < score):
                            salvage_info[canonical_url] = {"url": canonical_url, "score": score, "status": status, "kind": kind}
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

            # allow param bridge to flush
            if self.cfg.enable_param_sniff:
                try:
                    await page.wait_for_timeout(max(80, int(self.cfg.param_flush_interval_ms)))
                except Exception:
                    pass

            # wait for pending binary-sniff tasks (bounded)
            if self.cfg.enable_binary_signature_sniff and binary_tasks:
                try:
                    await self.asyncio.wait_for(
                        self.asyncio.gather(*binary_tasks, return_exceptions=True),
                        timeout=max(0.25, min(2.5, tmo * 0.25)),
                    )
                except Exception:
                    pass

            if self.cfg.enable_redirect_tracking and redirect_events and len(json_hits) < max_json:
                json_hits.append({
                    "url": canonical_page_url,
                    "json": {"redirect_chain": redirect_events[: int(self.cfg.max_redirect_events)]},
                    "source_page": canonical_page_url,
                })

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

            if self.cfg.enable_forensics and self.cfg.forensics_hash_via_probe and api_ctx is not None and forensics:
                sem = self.asyncio.Semaphore(8)

                async def guard_hash(bundle: "NetworkSniffer.Dict[str, Any]"):
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

            if self.cfg.enable_url_salvage and api_ctx is not None and salvage_info:
                targets = list(salvage_info.values())
                targets.sort(key=lambda d: float(d.get("score", 0.0)), reverse=True)
                targets = targets[: int(self.cfg.salvage_max_targets_total)]

                sem = self.asyncio.Semaphore(int(self.cfg.salvage_probe_concurrency))

                def req_hdrs_for_salvage(u: str) -> "NetworkSniffer.Dict[str, str]":
                    ev = request_evidence.get(u) or request_evidence.get(self._canonicalize_url(u)) or {}
                    return ev.get("headers_subset") or {}

                async def salvage_guard(info: "NetworkSniffer.Dict[str, Any]"):
                    async with sem:
                        u = self._to_str(info.get("url"))
                        return await self._salvage_one(
                            api_ctx,
                            u,
                            req_hdrs_for_salvage(u),
                            log=log,
                            observed_status=info.get("status"),
                            observed_kind=info.get("kind"),
                        )

                salvage_bundles = await self.asyncio.gather(*[salvage_guard(i) for i in targets])

            # --- MSE post-processing (same spirit as your version) ---
            if self.cfg.enable_mse_sniff and mse_events:
                # Keep your existing MSE interpretation minimal here (you can expand further if you want)
                if len(json_hits) < max_json:
                    json_hits.append({
                        "url": canonical_page_url,
                        "json": {"mse_bundle": {
                            "source_page": canonical_page_url,
                            "count": len(mse_events),
                            "items": mse_events[: int(self.cfg.mse_max_events)],
                        }},
                        "source_page": canonical_page_url,
                    })

            # --- PARAM post-processing + correlation ---
            param_summary = self._postprocess_param_events(param_events)
            if self.cfg.enable_param_sniff and len(json_hits) < max_json:
                json_hits.append({
                    "url": canonical_page_url,
                    "json": {"param_bundle": {
                        "source_page": canonical_page_url,
                        "counts_top": param_summary.get("top_keys", [])[:80],
                        "nav_urls": param_summary.get("nav_urls", [])[:200],
                        "total_events": param_summary.get("total_events", 0),
                        "capture_values": bool(self.cfg.param_capture_values),
                    }},
                    "source_page": canonical_page_url,
                })

            # --- router boot snapshot (truncated) ---
            boot = None
            try:
                boot = await page.evaluate("""() => {
                  try {
                    return {
                      next: window.__NEXT_DATA__ || null,
                      nuxt: window.__NUXT__ || null,
                      apollo: window.__APOLLO_STATE__ || null
                    };
                  } catch(e) { return { next:null, nuxt:null, apollo:null }; }
                }""")
            except Exception:
                boot = None

            if boot and len(json_hits) < max_json:
                # truncate big objects safely
                def _truncate_obj(o, max_chars=120000):
                    try:
                        s = self.json.dumps(o)
                        if len(s) > max_chars:
                            return {"truncated": True, "preview": s[:max_chars]}
                        return o
                    except Exception:
                        return {"truncated": True, "preview": self._to_str(o)[:max_chars]}

                json_hits.append({
                    "url": canonical_page_url,
                    "json": {"boot_state": _truncate_obj(boot)},
                    "source_page": canonical_page_url,
                })

            # --- get HTML (needed for script src extraction + return) ---
            try:
                html = await page.content()
            except Exception as e:
                self._log(f"[NetworkSniffer] Failed to get page content: {e}", log)
                html = ""

            # --- Bundle scan (optional) ---
            if self.cfg.enable_bundle_param_scan and api_ctx is not None:
                # extend scripts with <script src> parsed from HTML
                for u in self._extract_script_srcs_from_html(html, canonical_page_url):
                    cu = self._canonicalize_url(u)
                    if cu and cu not in seen_scripts and self._host_allowed(cu):
                        seen_scripts.add(cu)
                        script_urls.append(cu)

                bundle_scan = await self._bundle_param_scan(api_ctx, script_urls, log=log)
                if len(json_hits) < max_json:
                    json_hits.append({
                        "url": canonical_page_url,
                        "json": {"bundle_param_scan": bundle_scan},
                        "source_page": canonical_page_url,
                    })

            # --- Param-to-endpoint correlation ---
            if self.cfg.enable_param_sniff:
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
                await self.asyncio.wait_for(page.close(), timeout=3.0)
            except Exception:
                pass

        merged_items_any = found_items + derived_items + blob_placeholders
        merged_items = [self._normalize_item(it) for it in merged_items_any if it.get("url")]

        summary = (
            f"[NetworkSniffer] Finished sniff for {canonical_page_url}: "
            f"media={len(found_items)} derived={len(derived_items)} "
            f"blob={len(blob_placeholders)} json_hits={len(json_hits)} "
            f"forensics={len(forensics)} salvage={len(salvage_bundles)} mse={len(mse_events)} "
            f"param_events={len(param_events)} scripts={len(script_urls)} "
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
        click_timeout_ms: int = 2500
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

        enable_meta_scan: bool = True  # meta content, canonical, og:, twitter:
        enable_link_rel_scan: bool = True  # preload/prefetch/modulepreload/alternate

        enable_srcset_scan: bool = True

        # NOTE: computedStyle can be EXPENSIVE on huge pages.
        enable_css_url_scan: bool = True   # style tags + inline style url(...)
        enable_computed_style_bg_scan: bool = False  # OFF by default for anti-stuck
        computed_style_bg_budget: int = 350          # max elements to computed-style scan
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

        # selectors for direct URL-bearing elements
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
            # if it's wedged, don't propagate—sniffer must return
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

                # no timeout kwarg; use asyncio.wait_for around evaluate
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

    # ------------------------- JS passes ------------------------- #

    _JS_COMMON = r"""
    (args) => {
      const {
        selectors, includeShadow, dataKeys,
        onclickRegexes, redirectHints, scriptJsonHints,
        baseUrl, maxItems, maxDomNodes, shadowHostLimit,
        enableMeta, enableRelLinks, enablePerf, maxPerf,
        enableCssUrls, enableComputedBg, computedBgBudget, maxStyleChars,
        enableSrcset,
        enableScriptScan, scriptLimit, maxScriptChars, enableJsonParse, maxJsonParseChars,
        enableStorage, maxStorageKeys, maxStorageChars,
        enableSpa, maxSpaChars, spaKeys,
        enableWebpack, webpackLimit, maxWebpackFnChars, webpackUrlRegex, webpackApiHints
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
                if (m[1]) { if (!push(el, m[1], (el.tagName||"").toLowerCase(), `inline-${k}`)) return false; }
              }
            } catch {}
          }
          if (!pushAny(el, v, (el.tagName||"").toLowerCase(), `inline-text-${k}`)) return false;
        }
        return true;
      }

      function sniffStyleUrls(el) {
        if (!enableCssUrls) return true;

        // inline style attribute is cheap
        try {
          const st = el.getAttribute?.("style") || "";
          if (st) { if (!pushAny(el, st, (el.tagName||"").toLowerCase(), "style-attr")) return false; }
        } catch {}

        // computed background-image can be expensive; do it only if enabled and budgeted
        if (!enableComputedBg) return true;
        return true;
      }

      function scanRoot(root) {
        let scanned = 0;
        try {
          const els = root.querySelectorAll?.(selectors) || [];
          for (const el of els) {
            scanned++;
            if (scanned > maxDomNodes) break;

            const tag = (el.tagName || "a").toLowerCase();

            const url = el.href || el.currentSrc || el.src ||
                        el.getAttribute?.("href") || el.getAttribute?.("src") || "";
            if (!push(el, url, tag, "dom")) return;

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

      function scanComputedBgBudgeted() {
        if (!enableCssUrls || !enableComputedBg) return;
        let cnt = 0;
        let els = [];
        try { els = Array.from(document.querySelectorAll("*")).slice(0, Math.max(1, computedBgBudget)); } catch {}
        for (const el of els) {
          if (out.length >= maxItems) return;
          cnt++;
          try {
            const cs = window.getComputedStyle?.(el);
            const bg = cs && cs.getPropertyValue && cs.getPropertyValue("background-image");
            if (bg && bg.includes("url(")) {
              if (!pushAny(el, bg, (el.tagName||"").toLowerCase(), "style-bg")) return;
            }
          } catch {}
        }
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

        if (enableRelLinks) {
          try {
            const rels = new Set(["preload","prefetch","modulepreload","dns-prefetch","preconnect","alternate","canonical"]);
            const links = Array.from(document.querySelectorAll("link[href]")).slice(0, 500);
            for (const l of links) {
              if (out.length >= maxItems) return;
              const rel = String(l.getAttribute("rel") || "").toLowerCase().trim();
              if (!rel) continue;
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
              if (name.includes("url") || name.startsWith("og:") || name.startsWith("twitter:") || name.includes("image")) {
                if (!pushAny(m, content, "meta", `meta-${name || "content"}`)) return;
              } else if (content.includes("http") || content.includes("://") || content.startsWith("/")) {
                if (!pushAny(m, content, "meta", "meta-content")) return;
              }
            }
          } catch {}
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
        pushAny(document, styleText, "style", "style-tag");
      }

      function scanScriptsBounded() {
        if (!enableScriptScan) return;
        let scripts = [];
        try { scripts = Array.from(document.querySelectorAll("script")).slice(0, scriptLimit); } catch {}
        for (const s of scripts) {
          if (out.length >= maxItems) return;

          const type = String(s.getAttribute("type") || "").toLowerCase();
          const isJsonType = type.includes("json") || type.includes("ld+json");

          let txt = "";
          try { txt = (s.textContent || "").trim(); } catch {}
          if (!txt) continue;
          if (txt.length > maxScriptChars) txt = txt.slice(0, maxScriptChars);

          pushAny(s, txt, "script", "script-text");

          if (!enableJsonParse) continue;

          // only attempt JSON parse when it looks like JSON and is within size cap
          if (!(isJsonType || txt.startsWith("{") || txt.startsWith("["))) continue;
          if (txt.length > maxJsonParseChars) continue;

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

        try {
          const nodes = [];
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

      // Execute in cheap→heavier order
      scanRoot(document);
      scanShadowRootsBounded();
      scanMetaAndRelLinks();
      scanPerfEntries();
      scanCssTextBounded();

      // computedStyle scan last (and optional)
      scanComputedBgBudgeted();

      scanStorage();
      scanSpaState();
      scanScriptsBounded();
      scanWebpackModulesBounded();

      return { items: out, capped: out.length >= maxItems };
    }
    """

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

        page = await context.new_page()

        # Whole-run watchdog hard cap
        hard_cap = max(3.0, tmo * float(self.cfg.watchdog_multiplier))

        async def _run() -> Tuple[str, List[Dict[str, str]]]:
            nonlocal html, links, seen_urls_in_js

            try:
                # these are safe in older PW
                try:
                    page.set_default_timeout(int(max(1.0, tmo) * 1000))
                    page.set_default_navigation_timeout(int(max(5.0, tmo) * 1000))
                except Exception:
                    pass

                # optional resource blocking
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

                js_timeout_ms = int(max(tmo, 6.0) * 1000)
                wait_after_ms = int(self.cfg.wait_after_goto_ms)
                wait_mode = getattr(self.cfg, "goto_wait_until", "domcontentloaded")

                selector_js = ", ".join(self.cfg.selectors)

                self._log(f"Start: {canonical_page_url} timeout={tmo}s", log)

                # navigation
                try:
                    await page.goto(canonical_page_url, wait_until=wait_mode, timeout=js_timeout_ms)
                except Exception as e:
                    self._log(f"goto timeout/fail on {canonical_page_url} (wait_until={wait_mode}): {e}", log)

                if wait_after_ms > 0:
                    await page.wait_for_timeout(wait_after_ms)

                # auto-scroll (budgeted)
                await self._auto_scroll(page, tmo, log)

                # extra settle
                await page.wait_for_timeout(max(200, int(tmo * 1000 * 0.08)))

                # html snapshot (never uses timeout kwarg)
                try:
                    html = await self._pw_content(page, log)
                except Exception as e:
                    self._log(f"page.content() skipped/timeout: {e}", log)
                    html = ""

                # evaluate once with all passes (single evaluate is safer than many)
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

                    "enableMeta": bool(self.cfg.enable_meta_scan),
                    "enableRelLinks": bool(self.cfg.enable_link_rel_scan),

                    "enablePerf": bool(self.cfg.enable_perf_entries),
                    "maxPerf": int(self.cfg.max_perf_entries),

                    "enableCssUrls": bool(self.cfg.enable_css_url_scan),
                    "enableComputedBg": bool(self.cfg.enable_computed_style_bg_scan),
                    "computedBgBudget": int(self.cfg.computed_style_bg_budget),
                    "maxStyleChars": int(self.cfg.max_style_chars),

                    "enableSrcset": bool(self.cfg.enable_srcset_scan),

                    "enableScriptScan": bool(self.cfg.enable_script_scan),
                    "scriptLimit": int(self.cfg.script_soft_limit),
                    "maxScriptChars": int(self.cfg.max_script_chars),
                    "enableJsonParse": bool(self.cfg.enable_json_parse_in_scripts),
                    "maxJsonParseChars": int(self.cfg.max_json_parse_chars),

                    "enableStorage": bool(self.cfg.enable_storage_scan),
                    "maxStorageKeys": int(self.cfg.max_storage_keys),
                    "maxStorageChars": int(self.cfg.max_storage_chars),

                    "enableSpa": bool(self.cfg.enable_spa_state_scan),
                    "maxSpaChars": int(self.cfg.max_spa_json_chars),
                    "spaKeys": list(self.cfg.spa_state_keys),

                    "enableWebpack": bool(self.cfg.enable_webpack_scan),
                    "webpackLimit": int(self.cfg.webpack_module_soft_limit),
                    "maxWebpackFnChars": int(self.cfg.max_webpack_fn_chars),
                    "webpackUrlRegex": self.cfg.webpack_url_regex,
                    "webpackApiHints": list(self.cfg.webpack_api_hints),
                }

                raw_payload = {}
                try:
                    raw_payload = await self._pw_eval(page, self._JS_COMMON, eval_args, log) or {}
                except Exception as e:
                    self._log(f"DOM/Meta/Perf/Style/Script/Storage/SPA pass failed/timeout: {e}", log)
                    raw_payload = {}

                raw_links = raw_payload.get("items") or []
                self._log(f"Raw items total (single-pass): {len(raw_links)}", log)

                # optional click simulation (bounded) — uses action timeouts, no kwarg timeouts
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

                                if not el_info.get("isVisible"):
                                    continue

                                await h.scroll_into_view_if_needed(timeout=1000)
                                await h.click(timeout=int(self.cfg.click_timeout_ms))
                                await page.wait_for_timeout(250)

                                # after click, re-run the single evaluate quickly
                                try:
                                    click_payload = await self._pw_eval(page, self._JS_COMMON, eval_args, log) or {}
                                    raw_links.extend(click_payload.get("items") or [])
                                except Exception as e:
                                    self._log(f"Click re-scan failed: {e}", log)

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

            return html, links

        try:
            return await asyncio.wait_for(_run(), timeout=hard_cap)
        except asyncio.TimeoutError:
            self._log(f"Watchdog: sniff exceeded hard cap {hard_cap:.2f}s; returning partials.", log)
            return html, links
        finally:
            try:
                await self._pw_close(page, log)
            except Exception:
                pass


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
        canonical_page_url = _canonicalize_url(page_url)
        runtime_hits: List[Dict[str, Any]] = []

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
                self._log(f"goto timeout on {canonical_page_url} (wait_until={wait_mode}): {e}", log)

            # Let page settle a bit
            await page.wait_for_timeout(int(tmo * 1000 * 0.2))

            # Best-effort "play" poke (kept from your code)
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

    Contract:

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
            "kind": "...",
            "meta": {...}
        }

    Advanced features added:
      - UI barrier scan (captcha / paywall / cookie / adblock / cloudflare hints)
      - Overlay detection (z-index + pointer-events + transparent blockers + scroll-lock)
      - Hit-test blocker grid (elementFromPoint) to catch invisible panes
      - CDP event listener extraction (Chromium only) + element confidence scoring
      - Optional AX tree scan (Chromium CDP if available, else Playwright accessibility snapshot)
      - Dynamic simulation loop:
          * short scroll(s)
          * click 1–2 likely CTAs
          * re-run overlay + hit-test + barrier scans after each action
      - Hard budgets: never bricks your pipeline; always returns partial data
    """

    # ------------------------------------------------------------------ #
    # Config
    # ------------------------------------------------------------------ #
    @dataclass
    class Config:
        # generic controls
        timeout: float = 8.0
        max_hits: int = 300
        wait_after_load_ms: int = 900

        # global hard budgets
        hard_total_budget_s: float = 12.0         # total sniff budget (guardrail)
        per_eval_timeout_s: float = 3.5           # JS evaluate timeout
        per_cdp_timeout_s: float = 2.5            # CDP send timeout
        per_action_settle_ms: int = 450

        # ---------------- Dynamic simulation ----------------
        enable_dynamic_simulation: bool = True
        sim_scroll_steps: int = 3
        sim_scroll_delay_ms: int = 350
        sim_click_targets: int = 2
        sim_click_timeout_ms: int = 2200

        # click target text cues (lowercased contains)
        cta_text_hints: List[str] = field(default_factory=lambda: [
            "accept", "agree", "continue", "close", "ok", "okay", "got it",
            "play", "watch", "enter", "allow", "next", "submit",
            "sign in", "log in", "login", "sign up", "register",
        ])

        # ---------------- CDP: Event Listener Extraction ----------------
        enable_cdp_listeners: bool = True
        listener_types: Set[str] = field(default_factory=lambda: {
            "click", "mousedown", "mouseup",
            "submit",
            "keydown", "keyup",
            "touchstart", "touchend",
            "pointerdown", "pointerup",
        })
        max_listener_hits: int = 140
        max_candidate_nodes: int = 520

        candidate_selector: str = (
            "button, a, input, select, textarea, summary, details, label, "
            "[role='button'], [role='link'], [tabindex], [contenteditable='true'], "
            "div, span, li, svg"
        )

        include_listener_flags: bool = True
        include_outer_html_snippet: bool = True
        outer_html_max_chars: int = 320

        # Listener scoring
        enable_listener_scoring: bool = True
        max_scoring_nodes: int = 120  # score only first N listener-passing nodes

        # ---------------- Overlays / Modals (JS) ----------------
        enable_overlay_detection: bool = True
        min_z_index: int = 900
        coverage_threshold_percent: float = 50.0
        max_overlay_hits: int = 60

        # overlay extras
        detect_scroll_lock: bool = True
        overlay_keywords: List[str] = field(default_factory=lambda: [
            "cookie", "consent", "subscribe", "sign in", "log in",
            "disable adblock", "adblock", "enable javascript", "paywall",
            "verify you are human", "captcha", "hcaptcha", "recaptcha",
        ])

        # ---------------- Hit-test blocker grid (JS) ----------------
        enable_hit_test_blockers: bool = True
        hit_test_grid: int = 3            # 3 => 3x3 + center (effectively 9 points)
        max_hit_test_hits: int = 30

        # ---------------- UI barrier scan (JS) ----------------
        enable_ui_barrier_scan: bool = True
        max_barrier_hits: int = 40

        # ---------------- Forms (JS) ----------------
        enable_form_extraction: bool = True
        max_form_hits: int = 90
        max_inputs_per_form: int = 90

        redact_input_types: Set[str] = field(default_factory=lambda: {"password"})
        redact_name_regex: str = r"(csrf|token|auth|bearer|secret|key|session|jwt)"
        emit_summary_hit: bool = True

        # form classification
        enable_form_classification: bool = True

        # honeypot detection
        enable_honeypot_detection: bool = True

        # ---------------- AX / Accessibility ----------------
        enable_ax_tree_scan: bool = True
        # roles to keep
        ax_roles: Set[str] = field(default_factory=lambda: {
            "button", "link", "checkbox", "textbox", "combobox", "menuitem"
        })
        max_ax_hits: int = 120

        # if using CDP AX tree, we try mapping backendDOMNodeId -> nodeId (best-effort)
        try_map_ax_to_dom: bool = True

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
        confidence: Optional[float] = None
        reasons: List[str] = field(default_factory=list)

    @dataclass
    class OverlayMem:
        tag_name: str
        id: str
        class_name: str
        z_index: int
        coverage: str
        text_preview: str
        meta: Dict[str, Any] = field(default_factory=dict)

    @dataclass
    class BarrierMem:
        barrier_type: str
        evidence: str
        selector_hint: str = ""
        meta: Dict[str, Any] = field(default_factory=dict)

    @dataclass
    class HitTestMem:
        point: Tuple[int, int]
        tag_name: str
        id: str
        class_name: str
        pointer_events: str
        opacity: float
        z_index: str
        position: str
        rect: Dict[str, Any]
        text_preview: str
        outer_html: str

    @dataclass
    class FormMem:
        action: str
        method: str
        id: str
        class_name: str
        input_count: int
        inputs: List[Dict[str, Any]]
        form_kind: str = "unknown"
        honeypot_suspected: bool = False
        honeypot_reasons: List[str] = field(default_factory=list)

    @dataclass
    class AXMem:
        role: str
        name: str
        value: str
        disabled: bool
        focused: bool
        backend_dom_node_id: Optional[int] = None
        node_id: Optional[int] = None
        selector_hint: str = ""
        meta: Dict[str, Any] = field(default_factory=dict)

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
        self._barriers: List[InteractionSniffer.BarrierMem] = []
        self._hit_tests: List[InteractionSniffer.HitTestMem] = []
        self._forms: List[InteractionSniffer.FormMem] = []
        self._ax: List[InteractionSniffer.AXMem] = []
        self._seen_fingerprints: Set[Tuple[Any, ...]] = set()

        # used during dynamic passes
        self._phase_tags: List[str] = []  # e.g. ["pre", "post1", "post2"]

    # ------------------------------------------------------------------ #
    # Logging helper
    # ------------------------------------------------------------------ #
    def _log(self, msg: str, log_list: Optional[List[str]]) -> None:
        full = f"[InteractionSniffer] {msg}"
        try:
            if log_list is not None:
                log_list.append(full)
            if self.logger is not None:
                # your logger likely has log_message()
                self.logger.log_message(full)  # type: ignore[attr-defined]
        except Exception:
            pass

    # ------------------------------------------------------------------ #
    # Helpers: timeouts
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
            self._log(f"CDP send {method} failed/timeout: {e}", log)
            return None

    def _canon_url(self, u: str) -> str:
        # Keep conservative; your suite likely has a canonicalizer already.
        return (u or "").strip()

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
        total_budget = max(tmo, self.cfg.hard_total_budget_s)
        html: str = ""
        hits: List[Dict[str, Any]] = []
        page = None

        self._log(f"Start interaction sniff: {page_url} timeout={tmo}s budget={total_budget}s", log)

        async def _run() -> Tuple[str, List[Dict[str, Any]]]:
            nonlocal html, hits, page
            page = await context.new_page()
            await page.goto(page_url, wait_until="domcontentloaded", timeout=int(tmo * 1000))
            await page.wait_for_timeout(int(self.cfg.wait_after_load_ms))

            # ---------------- PRE SCAN ----------------
            self._phase_tags.append("pre")
            await self._collect_phase(page, page_url, log, phase="pre", context=context)

            # CDP listeners early (helps pick click targets)
            if self.cfg.enable_cdp_listeners:
                await self._collect_cdp_listeners(context, page, page_url, log)

            # AX scan (optional; helps pick click targets too)
            if self.cfg.enable_ax_tree_scan:
                await self._collect_ax_tree(context, page, page_url, log)

            # Listener scoring (optional)
            if self.cfg.enable_listener_scoring and self._listeners:
                await self._score_listeners(page, log)

            # ---------------- DYNAMIC SIMULATION ----------------
            if self.cfg.enable_dynamic_simulation:
                await self._simulate_and_rescan(context, page, page_url, log)

            # HTML snapshot
            try:
                html = await page.content()
            except Exception as e:
                self._log(f"Error getting HTML for {page_url}: {e}", log)
                html = ""

            hits = self._materialize_hits(page_url)

            # global cap
            if len(hits) > self.cfg.max_hits:
                hits = hits[: self.cfg.max_hits]
            return html or "", hits

        try:
            # hard guardrail: never hang indefinitely
            html, hits = await asyncio.wait_for(_run(), timeout=total_budget)
        except asyncio.TimeoutError:
            self._log(f"Global sniff budget exceeded for {page_url}; returning partial hits.", log)
            hits = self._materialize_hits(page_url)
            if len(hits) > self.cfg.max_hits:
                hits = hits[: self.cfg.max_hits]
        except PWTimeoutError:
            self._log(f"Timeout while loading {page_url}", log)
            hits = self._materialize_hits(page_url)
        except Exception as e:
            self._log(f"Fatal error on {page_url}: {e}", log)
            hits = self._materialize_hits(page_url)
        finally:
            if page is not None:
                try:
                    await asyncio.wait_for(page.close(), timeout=3.0)
                except Exception as e:
                    self._log(f"Error closing page for {page_url}: {e}", log)

        self._log(f"Finished interaction sniff for {page_url}: hits={len(hits)}", log)
        return html or "", hits

    # ------------------------------------------------------------------ #
    # Phase collector (overlays/forms/barriers/hit-test) used pre/post
    # ------------------------------------------------------------------ #
    async def _collect_phase(self, page, page_url: str, log: Optional[List[str]], phase: str, context=None) -> None:
        # 1) Forms
        if self.cfg.enable_form_extraction:
            await self._collect_forms(page, page_url, log, phase=phase)

        # 2) Overlays (now includes pointer-events + transparent blockers + scroll-lock)
        if self.cfg.enable_overlay_detection:
            await self._collect_overlays(page, page_url, log, phase=phase)

        # 3) UI barrier scan
        if self.cfg.enable_ui_barrier_scan:
            await self._collect_ui_barriers(page, page_url, log, phase=phase)

        # 4) Hit-test blockers grid
        if self.cfg.enable_hit_test_blockers:
            await self._collect_hit_test_blockers(page, page_url, log, phase=phase)

    # ------------------------------------------------------------------ #
    # JS: Forms (now includes classification + honeypot detection)
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

    def _classify_form_kind(self, form_action: str, inputs: List[Dict[str, Any]]) -> str:
        if not self.cfg.enable_form_classification:
            return "unknown"
        a = (form_action or "").lower()
        if any(x in a for x in ("/login", "/signin", "/sign-in", "/session", "/auth")):
            return "login"
        if any(x in a for x in ("/signup", "/sign-up", "/register")):
            return "signup"
        # input-based heuristics
        types = {str(i.get("type") or "").lower() for i in inputs}
        names = " ".join([str(i.get("name") or "").lower() for i in inputs])
        if "password" in types:
            return "login"
        if any(k in names for k in ("search", "q", "query")):
            return "search"
        if any(k in names for k in ("card", "cc", "checkout", "shipping", "billing")):
            return "checkout"
        return "unknown"

    def _detect_honeypot(self, raw_inputs: List[Dict[str, Any]]) -> Tuple[bool, List[str]]:
        if not self.cfg.enable_honeypot_detection:
            return False, []
        reasons: List[str] = []
        for i in raw_inputs:
            try:
                name = (i.get("name") or "").lower()
                itype = (i.get("type") or "").lower()
                style = (i.get("style") or "").lower()
                aria_hidden = bool(i.get("ariaHidden", False))
                rect = i.get("rect") or {}
                w = float(rect.get("w") or 0)
                h = float(rect.get("h") or 0)

                # classic token hidden fields are not honeypots; they're normal
                if itype == "hidden" and re.search(self.cfg.redact_name_regex, name, re.IGNORECASE):
                    continue

                # suspicious: offscreen or zero-size but still present
                if "left:-9999" in style or "top:-9999" in style or "opacity:0" in style:
                    reasons.append(f"offscreen/hidden-style field: {name or itype}")
                if aria_hidden and itype not in ("hidden",):
                    reasons.append(f"aria-hidden input: {name or itype}")
                if (w <= 1 or h <= 1) and itype not in ("hidden",):
                    reasons.append(f"tiny/0-size input: {name or itype}")
            except Exception:
                continue
        return (len(reasons) > 0), reasons[:6]

    async def _collect_forms(self, page, page_url: str, log: Optional[List[str]], phase: str) -> None:
        try:
            payload = await self._safe_eval(
                page,
                """
                (cfg) => {
                    const maxForms = cfg.maxForms;
                    const maxInputs = cfg.maxInputs;
                    const out = [];
                    const forms = Array.from(document.querySelectorAll('form')).slice(0, maxForms);

                    function rectOf(el){
                        try {
                            const r = el.getBoundingClientRect();
                            return {x:r.x,y:r.y,w:r.width,h:r.height};
                        } catch { return {x:0,y:0,w:0,h:0}; }
                    }

                    for (const f of forms) {
                        const inputs = [];
                        const els = Array.from(f.querySelectorAll('input, textarea, select, button'))
                                         .slice(0, maxInputs);

                        for (const i of els) {
                            const st = (i.getAttribute("style") || "");
                            inputs.push({
                                name: i.name || i.id || "",
                                type: (i.type || i.tagName || "").toLowerCase(),
                                value: (typeof i.value === "string" ? i.value : ""),
                                required: !!i.required,
                                disabled: !!i.disabled,
                                autocomplete: (i.autocomplete || ""),
                                placeholder: (i.placeholder || ""),
                                label: (() => {
                                    try {
                                      const id = i.id;
                                      if (id) {
                                        const l = document.querySelector(`label[for="${CSS.escape(id)}"]`);
                                        if (l) return (l.innerText || "").trim().slice(0,80);
                                      }
                                    } catch {}
                                    return "";
                                })(),
                                style: st,
                                ariaHidden: (i.getAttribute("aria-hidden") === "true"),
                                rect: rectOf(i)
                            });
                        }

                        out.push({
                            action: f.action || "",
                            method: (f.method || "get").toLowerCase(),
                            id: f.id || "",
                            className: (typeof f.className === "string" ? f.className : ""),
                            input_count: inputs.length,
                            inputs: inputs
                        });
                    }
                    return out;
                }
                """,
                {"maxForms": int(self.cfg.max_form_hits), "maxInputs": int(self.cfg.max_inputs_per_form)},
                log,
            )

            forms = payload if isinstance(payload, list) else []
            for f in forms[: self.cfg.max_form_hits]:
                if not isinstance(f, dict):
                    continue
                raw_inputs = f.get("inputs") or []
                if not isinstance(raw_inputs, list):
                    raw_inputs = []

                # redact + bound value
                redacted_inputs: List[Dict[str, Any]] = []
                for inp in raw_inputs[: self.cfg.max_inputs_per_form]:
                    if not isinstance(inp, dict):
                        continue
                    name = str(inp.get("name") or "")
                    itype = str(inp.get("type") or "")
                    val = str(inp.get("value") or "")
                    if self._should_redact_field(name, itype):
                        val = "[REDACTED]"
                    else:
                        if len(val) > 200:
                            val = val[:200] + "…"
                    redacted_inputs.append({
                        "name": name,
                        "type": itype,
                        "value": val,
                        "required": bool(inp.get("required", False)),
                        "disabled": bool(inp.get("disabled", False)),
                        "autocomplete": str(inp.get("autocomplete") or ""),
                        "placeholder": str(inp.get("placeholder") or ""),
                        "label": str(inp.get("label") or ""),
                    })

                # classify + honeypot
                form_kind = self._classify_form_kind(str(f.get("action") or ""), redacted_inputs)
                honeypot, reasons = self._detect_honeypot(raw_inputs)

                self._forms.append(
                    InteractionSniffer.FormMem(
                        action=str(f.get("action") or ""),
                        method=str(f.get("method") or "get"),
                        id=str(f.get("id") or ""),
                        class_name=str(f.get("className") or ""),
                        input_count=int(f.get("input_count") or len(redacted_inputs)),
                        inputs=redacted_inputs,
                        form_kind=form_kind,
                        honeypot_suspected=honeypot,
                        honeypot_reasons=reasons,
                    )
                )

            if self._forms:
                self._log(f"[{phase}] Extracted {len(self._forms)} form definitions (cum)", log)
        except Exception as e:
            self._log(f"Form extraction error: {e}", log)

    # ------------------------------------------------------------------ #
    # JS: Overlays / Modals (enhanced)
    # ------------------------------------------------------------------ #
    async def _collect_overlays(self, page, page_url: str, log: Optional[List[str]], phase: str) -> None:
        try:
            payload = await self._safe_eval(
                page,
                """
                (config) => {
                    const { minZ, minCoverage, maxHits, detectScrollLock, keywords } = config;
                    const results = [];

                    const vw = Math.max(document.documentElement.clientWidth || 0, window.innerWidth || 0);
                    const vh = Math.max(document.documentElement.clientHeight || 0, window.innerHeight || 0);
                    const viewportArea = Math.max(1, vw * vh);

                    const bodyOv = (() => {
                      try { return (getComputedStyle(document.body).overflow || ""); } catch { return ""; }
                    })();
                    const htmlOv = (() => {
                      try { return (getComputedStyle(document.documentElement).overflow || ""); } catch { return ""; }
                    })();

                    const all = Array.from(document.querySelectorAll('div, section, aside, iframe, dialog, [role="dialog"], [aria-modal="true"]'));

                    function hasKeyword(txt){
                      const t = String(txt||"").toLowerCase();
                      for (const k of (keywords||[])) {
                        if (k && t.includes(String(k).toLowerCase())) return true;
                      }
                      return false;
                    }

                    for (const el of all) {
                        if (results.length >= maxHits) break;

                        const style = window.getComputedStyle(el);
                        const zRaw = style.zIndex;
                        const z = parseInt(zRaw, 10);
                        const pos = style.position;
                        const vis = style.visibility;
                        const disp = style.display;
                        const opac = parseFloat(style.opacity || "1");
                        const pe = style.pointerEvents || "";
                        const bg = style.backgroundColor || "";
                        const inset = style.inset || "";
                        const ta = style.touchAction || "";
                        const bf = style.backdropFilter || style.webkitBackdropFilter || "";

                        // allow "auto" z-index but still detect full-screen blockers later via hit-test
                        if (Number.isNaN(z)) continue;

                        const rect = el.getBoundingClientRect();
                        const area = Math.max(0, rect.width) * Math.max(0, rect.height);
                        if (area <= 0) continue;

                        const coveragePct = (area / viewportArea) * 100;

                        const txt = (el.innerText || "").trim();
                        const txtPrev = txt.slice(0, 120);

                        const isOverlayLike =
                            (z >= minZ) &&
                            vis !== 'hidden' && disp !== 'none' &&
                            (pos === 'fixed' || pos === 'absolute') &&
                            coveragePct >= minCoverage;

                        if (!isOverlayLike) continue;

                        // extra blockers: transparent but click-blocking
                        const transparentBlocker =
                            (pe !== 'none') &&
                            ((opac === 0) || bg === 'rgba(0, 0, 0, 0)' || bg === 'transparent');

                        const fullScreenLike =
                            (String(inset).includes("0")) &&
                            (rect.width >= vw * 0.9) && (rect.height >= vh * 0.9);

                        const keywordHit = hasKeyword(txtPrev);

                        results.push({
                            tagName: el.tagName.toLowerCase(),
                            id: el.id || "",
                            className: (typeof el.className === "string" ? el.className : ""),
                            zIndex: z,
                            zIndexRaw: zRaw,
                            coverage: coveragePct.toFixed(1) + '%',
                            textPreview: txtPrev.slice(0, 80),
                            pointerEvents: pe,
                            opacity: opac,
                            background: bg,
                            inset: inset,
                            touchAction: ta,
                            backdropFilter: bf,
                            fullScreenLike: !!fullScreenLike,
                            transparentBlocker: !!transparentBlocker,
                            keywordHit: !!keywordHit,
                            rect: {x: rect.x, y: rect.y, w: rect.width, h: rect.height},
                            scrollLock: detectScrollLock ? ((bodyOv === "hidden") || (htmlOv === "hidden")) : false,
                            bodyOverflow: bodyOv,
                            htmlOverflow: htmlOv
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

            overlays = []
            body_ov = ""
            html_ov = ""
            if isinstance(payload, dict):
                overlays = payload.get("overlays") or []
                body_ov = str(payload.get("bodyOverflow") or "")
                html_ov = str(payload.get("htmlOverflow") or "")

                # emit scroll_lock hit if relevant and overlay exists
                if self.cfg.detect_scroll_lock and overlays:
                    if body_ov == "hidden" or html_ov == "hidden":
                        self._barriers.append(
                            InteractionSniffer.BarrierMem(
                                barrier_type="scroll_lock",
                                evidence=f"bodyOverflow={body_ov} htmlOverflow={html_ov}",
                                selector_hint="document.body/documentElement",
                                meta={"phase": phase},
                            )
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
                        meta={
                            "phase": phase,
                            "pointerEvents": ov.get("pointerEvents"),
                            "opacity": ov.get("opacity"),
                            "background": ov.get("background"),
                            "inset": ov.get("inset"),
                            "touchAction": ov.get("touchAction"),
                            "backdropFilter": ov.get("backdropFilter"),
                            "fullScreenLike": bool(ov.get("fullScreenLike", False)),
                            "transparentBlocker": bool(ov.get("transparentBlocker", False)),
                            "keywordHit": bool(ov.get("keywordHit", False)),
                            "rect": ov.get("rect") or {},
                            "zIndexRaw": ov.get("zIndexRaw"),
                            "scrollLock": bool(ov.get("scrollLock", False)),
                        },
                    )
                )

            if overlays:
                self._log(f"[{phase}] Overlay detection: +{len(overlays)} hits (cum={len(self._overlays)})", log)

        except Exception as e:
            self._log(f"Overlay detection error: {e}", log)

    # ------------------------------------------------------------------ #
    # JS: UI barrier scan (captcha/paywall/adblock/cloudflare/etc)
    # ------------------------------------------------------------------ #
    async def _collect_ui_barriers(self, page, page_url: str, log: Optional[List[str]], phase: str) -> None:
        try:
            payload = await self._safe_eval(
                page,
                """
                (cfg) => {
                    const maxHits = cfg.maxHits;
                    const out = [];

                    function push(type, evidence, selector){
                      if (out.length >= maxHits) return;
                      out.push({type, evidence, selector: selector || ""});
                    }

                    // 1) Captcha iframes / scripts
                    const ifr = Array.from(document.querySelectorAll('iframe[src], script[src]')).slice(0, 250);
                    for (const el of ifr) {
                      if (out.length >= maxHits) break;
                      const src = String(el.getAttribute("src") || "");
                      const low = src.toLowerCase();
                      if (!src) continue;
                      if (low.includes("recaptcha") || low.includes("hcaptcha") || low.includes("captcha") || low.includes("turnstile")) {
                        push("captcha", src, el.tagName.toLowerCase());
                      }
                      if (low.includes("/cdn-cgi/") || low.includes("cloudflare") || low.includes("cf-")) {
                        push("cloudflare_challenge", src, el.tagName.toLowerCase());
                      }
                    }

                    // 2) Keyword walls in visible text (bounded)
                    const bodyText = (() => {
                      try { return (document.body && (document.body.innerText || "")) || ""; }
                      catch { return ""; }
                    })().toLowerCase();

                    const keywords = [
                      ["paywall", ["subscribe", "subscription", "continue reading", "to continue reading"]],
                      ["cookie_consent", ["cookie", "consent", "privacy choices", "gdpr"]],
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

                    // 3) Known challenge containers (selectors)
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

            barriers = payload if isinstance(payload, list) else []
            for b in barriers[: self.cfg.max_barrier_hits]:
                if not isinstance(b, dict):
                    continue
                self._barriers.append(
                    InteractionSniffer.BarrierMem(
                        barrier_type=str(b.get("type") or "unknown"),
                        evidence=str(b.get("evidence") or ""),
                        selector_hint=str(b.get("selector") or ""),
                        meta={"phase": phase},
                    )
                )

            if barriers:
                self._log(f"[{phase}] UI barriers: +{len(barriers)} (cum={len(self._barriers)})", log)

        except Exception as e:
            self._log(f"UI barrier scan error: {e}", log)

    # ------------------------------------------------------------------ #
    # JS: Hit-test blocker grid (elementFromPoint)
    # ------------------------------------------------------------------ #
    async def _collect_hit_test_blockers(self, page, page_url: str, log: Optional[List[str]], phase: str) -> None:
        try:
            payload = await self._safe_eval(
                page,
                """
                (cfg) => {
                    const grid = Math.max(2, cfg.grid|0);
                    const maxHits = cfg.maxHits|0;

                    const vw = Math.max(document.documentElement.clientWidth||0, window.innerWidth||0);
                    const vh = Math.max(document.documentElement.clientHeight||0, window.innerHeight||0);

                    const pts = [];
                    // grid points inside viewport (avoid edges)
                    for (let gy=0; gy<grid; gy++){
                      for (let gx=0; gx<grid; gx++){
                        const x = Math.floor((gx+1) * vw / (grid+1));
                        const y = Math.floor((gy+1) * vh / (grid+1));
                        pts.push([x,y]);
                      }
                    }
                    // ensure center
                    pts.push([Math.floor(vw/2), Math.floor(vh/2)]);

                    function safeOuter(el){
                      try { return (el && el.outerHTML ? String(el.outerHTML).slice(0, 420) : ""); } catch { return ""; }
                    }

                    function infoAt(x,y){
                      let el = null;
                      try { el = document.elementFromPoint(x,y); } catch { el = null; }
                      if (!el) return null;
                      let st = null;
                      try { st = window.getComputedStyle(el); } catch { st = null; }
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
                      const fp = `${it.tagName}#${it.id}.${it.className}|${it.pointerEvents}|${it.opacity}|${it.position}|${it.zIndex}`;
                      if (seen.has(fp)) continue;
                      seen.add(fp);

                      // blocker-ish heuristic: pointer-events active AND element covers large area OR is fixed
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

            items = payload if isinstance(payload, list) else []
            for it in items[: self.cfg.max_hit_test_hits]:
                if not isinstance(it, dict):
                    continue
                self._hit_tests.append(
                    InteractionSniffer.HitTestMem(
                        point=tuple(it.get("point") or (0, 0)),
                        tag_name=str(it.get("tagName") or ""),
                        id=str(it.get("id") or ""),
                        class_name=str(it.get("className") or ""),
                        pointer_events=str(it.get("pointerEvents") or ""),
                        opacity=float(it.get("opacity") or 1.0),
                        z_index=str(it.get("zIndex") or ""),
                        position=str(it.get("position") or ""),
                        rect=dict(it.get("rect") or {}),
                        text_preview=str(it.get("textPreview") or ""),
                        outer_html=str(it.get("outerHTML") or ""),
                    )
                )

            if items:
                self._log(f"[{phase}] Hit-test blockers: +{len(items)} (cum={len(self._hit_tests)})", log)

        except Exception as e:
            self._log(f"Hit-test scan error: {e}", log)

    # ------------------------------------------------------------------ #
    # CDP: Event listeners (Chromium only) + confidence scoring hooks
    # ------------------------------------------------------------------ #
    async def _collect_cdp_listeners(self, context, page, page_url: str, log: Optional[List[str]]) -> None:
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
            doc = await self._cdp_send(cdp, "DOM.getDocument", {"depth": 1, "pierce": True}, log)
            root_node_id = (doc or {}).get("root", {}).get("nodeId")
            if not root_node_id:
                self._log("CDP: no DOM root nodeId", log)
                return

            sel = str(self.cfg.candidate_selector or "div,span,button,a,input")
            qs = await self._cdp_send(cdp, "DOM.querySelectorAll", {"nodeId": root_node_id, "selector": sel}, log)
            node_ids = (qs or {}).get("nodeIds", []) or []
            if not node_ids:
                self._log("CDP: no candidates matched selector", log)
                return

            node_ids = node_ids[: int(self.cfg.max_candidate_nodes)]

            def _attr_list_to_dict(attr_list: List[str]) -> Dict[str, str]:
                try:
                    return dict(zip(attr_list[0::2], attr_list[1::2]))
                except Exception:
                    return {}

            for nid in node_ids:
                if found >= int(self.cfg.max_listener_hits):
                    break

                inspected += 1
                try:
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
                    attr_list = (attrs_resp or {}).get("attributes", []) or []
                    attr_dict = _attr_list_to_dict(attr_list)

                    desc = await self._cdp_send(cdp, "DOM.describeNode", {"nodeId": nid}, log)
                    node_name = str((desc or {}).get("node", {}).get("nodeName") or "")

                    flags: Dict[str, Any] = {}
                    if self.cfg.include_listener_flags:
                        flags = {
                            "count": len(relevant),
                            "capture": any(bool(r.get("useCapture")) for r in relevant),
                            "passive": any(bool(r.get("passive")) for r in relevant),
                            "once": any(bool(r.get("once")) for r in relevant),
                        }

                    outer_html = None
                    if self.cfg.include_outer_html_snippet:
                        oh = await self._cdp_send(cdp, "DOM.getOuterHTML", {"nodeId": nid}, log)
                        outer_html = str((oh or {}).get("outerHTML") or "")
                        if outer_html and len(outer_html) > int(self.cfg.outer_html_max_chars):
                            outer_html = outer_html[: int(self.cfg.outer_html_max_chars)] + "…"

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

            self._log(f"CDP listener scan: inspected={inspected} found={found}", log)
        except Exception as e:
            self._log(f"CDP listener scan failed: {e}", log)
        finally:
            try:
                await cdp.detach()
            except Exception:
                pass

    # ------------------------------------------------------------------ #
    # Listener scoring (computed style / rect / visibility / cues)
    # ------------------------------------------------------------------ #
    async def _score_listeners(self, page, log: Optional[List[str]]) -> None:
        try:
            # score only first N to keep it bounded
            todo = self._listeners[: int(self.cfg.max_scoring_nodes)]
            if not todo:
                return

            node_ids = [int(x.node_id) for x in todo]
            payload = await self._safe_eval(
                page,
                """
                (nodeIds) => {
                  // Given CDP nodeIds, we cannot directly access nodes by nodeId in JS.
                  // So we approximate: return a list of "best effort" candidates by querying for common id/class.
                  // We'll do scoring by fingerprints from attributes we already have in Python later.
                  return { ok: true };
                }
                """,
                node_ids,
                log,
            )

            # We can't map CDP nodeId -> DOM element in pure page.evaluate without CDP.
            # Instead: do a scoring heuristic purely from attributes + outerHTML when available.
            for l in todo:
                conf, reasons = self._score_from_attrs(l.attributes, l.outer_html or "", l.node_name, l.types)
                l.confidence = conf
                l.reasons = reasons

            self._log(f"Listener scoring: scored={len(todo)} (attr/outerHTML heuristic)", log)
        except Exception as e:
            self._log(f"Listener scoring error: {e}", log)

    def _score_from_attrs(self, attrs: Dict[str, str], outer_html: str, node_name: str, types: List[str]) -> Tuple[float, List[str]]:
        reasons: List[str] = []
        score = 0.0

        nn = (node_name or "").lower()
        if nn in ("button", "a", "input", "select", "textarea", "label"):
            score += 0.35
            reasons.append(f"native:{nn}")

        role = (attrs.get("role") or "").lower()
        if role in ("button", "link", "menuitem"):
            score += 0.25
            reasons.append(f"role:{role}")

        tabindex = attrs.get("tabindex")
        if tabindex is not None:
            score += 0.10
            reasons.append("tabindex")

        if "contenteditable" in (attrs.get("contenteditable") or "").lower():
            score += 0.08
            reasons.append("contenteditable")

        # aria signals
        for k in ("aria-label", "aria-controls", "aria-expanded"):
            if attrs.get(k):
                score += 0.08
                reasons.append(k)

        # dataset tracking signals
        for k in list(attrs.keys()):
            lk = k.lower()
            if lk.startswith("data-") and any(x in lk for x in ("testid", "action", "track", "analytics")):
                score += 0.07
                reasons.append(f"data:{lk}")
                break

        # class hints
        cls = (attrs.get("class") or "").lower()
        if any(s in cls for s in ("btn", "button", "cta", "primary", "submit")):
            score += 0.10
            reasons.append("class-hint")

        # outerHTML hints
        oh = (outer_html or "").lower()
        if any(s in oh for s in ("onclick", "data-action", "aria-label", "role=\"button\"")):
            score += 0.07
            reasons.append("outerHTML-hint")

        # types
        if "click" in types:
            score += 0.05
            reasons.append("has-click")

        score = max(0.0, min(1.0, score))
        return score, reasons[:8]

    # ------------------------------------------------------------------ #
    # AX / Accessibility scan (CDP first, fallback to Playwright snapshot)
    # ------------------------------------------------------------------ #
    async def _collect_ax_tree(self, context, page, page_url: str, log: Optional[List[str]]) -> None:
        # Try CDP AX tree on Chromium; fallback to page.accessibility.snapshot
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
                    if not nodes:
                        return

                    # helper: pull properties
                    def _prop(node: Dict[str, Any], key: str) -> str:
                        try:
                            v = node.get(key)
                            if isinstance(v, dict) and "value" in v:
                                return str(v.get("value") or "")
                            return str(v or "")
                        except Exception:
                            return ""

                    kept = 0
                    for n in nodes:
                        if kept >= int(self.cfg.max_ax_hits):
                            break
                        if not isinstance(n, dict):
                            continue

                        role = _prop(n, "role").lower()
                        if role and role not in self.cfg.ax_roles:
                            continue

                        name = _prop(n, "name")
                        value = _prop(n, "value")
                        disabled = False
                        focused = False
                        try:
                            props = n.get("properties") or []
                            for p in props:
                                pn = str(p.get("name") or "")
                                pv = p.get("value") or {}
                                if pn == "disabled":
                                    disabled = bool(pv.get("value", False))
                                if pn == "focused":
                                    focused = bool(pv.get("value", False))
                        except Exception:
                            pass

                        backend_id = None
                        try:
                            backend_id = int(n.get("backendDOMNodeId")) if n.get("backendDOMNodeId") else None
                        except Exception:
                            backend_id = None

                        self._ax.append(
                            InteractionSniffer.AXMem(
                                role=role or "unknown",
                                name=str(name or ""),
                                value=str(value or ""),
                                disabled=bool(disabled),
                                focused=bool(focused),
                                backend_dom_node_id=backend_id,
                                selector_hint="ax_tree",
                                meta={"source": "cdp", "page": page_url},
                            )
                        )
                        kept += 1

                    # Best-effort: map backendDOMNodeId -> nodeId (optional)
                    if self.cfg.try_map_ax_to_dom and self._ax:
                        await self._map_ax_backend_to_dom_nodeid(cdp, log)

                    self._log(f"AX tree (CDP): kept={len(self._ax)}", log)
                finally:
                    try:
                        await cdp.detach()
                    except Exception:
                        pass
                return
            except Exception as e:
                self._log(f"AX tree via CDP failed; will fallback: {e}", log)

        # Fallback: Playwright snapshot
        try:
            snap = await asyncio.wait_for(page.accessibility.snapshot(), timeout=self.cfg.per_eval_timeout_s)
            # snapshot is a tree; we BFS it and keep nodes with roles
            kept = 0
            q = [snap] if isinstance(snap, dict) else []
            while q and kept < int(self.cfg.max_ax_hits):
                cur = q.pop(0)
                if not isinstance(cur, dict):
                    continue
                role = str(cur.get("role") or "").lower()
                name = str(cur.get("name") or "")
                value = str(cur.get("value") or "")
                disabled = bool(cur.get("disabled", False))
                focused = bool(cur.get("focused", False))

                if role in self.cfg.ax_roles:
                    self._ax.append(
                        InteractionSniffer.AXMem(
                            role=role,
                            name=name,
                            value=value,
                            disabled=disabled,
                            focused=focused,
                            selector_hint="ax_snapshot",
                            meta={"source": "playwright", "page": page_url},
                        )
                    )
                    kept += 1

                ch = cur.get("children") or []
                if isinstance(ch, list):
                    q.extend(ch)

            if self._ax:
                self._log(f"AX snapshot (Playwright): kept={len(self._ax)}", log)
        except Exception as e:
            self._log(f"AX snapshot failed: {e}", log)

    async def _map_ax_backend_to_dom_nodeid(self, cdp, log: Optional[List[str]]) -> None:
        # In CDP, DOM.pushNodesByBackendIdsToFrontend can map backend ids -> nodeIds.
        backend_ids = []
        for a in self._ax:
            if a.backend_dom_node_id and a.node_id is None:
                backend_ids.append(int(a.backend_dom_node_id))
        backend_ids = backend_ids[: 200]
        if not backend_ids:
            return

        resp = await self._cdp_send(
            cdp,
            "DOM.pushNodesByBackendIdsToFrontend",
            {"backendNodeIds": backend_ids},
            log,
        )
        node_ids = (resp or {}).get("nodeIds") or []
        if not isinstance(node_ids, list) or len(node_ids) != len(backend_ids):
            return

        # assign back
        idx = 0
        for a in self._ax:
            if a.backend_dom_node_id and a.node_id is None:
                a.node_id = int(node_ids[idx]) if node_ids[idx] else None
                idx += 1

    # ------------------------------------------------------------------ #
    # Dynamic simulation: scroll + click likely CTAs + rescan per step
    # ------------------------------------------------------------------ #
    async def _simulate_and_rescan(self, context, page, page_url: str, log: Optional[List[str]]) -> None:
        try:
            # 1) short scroll(s)
            for i in range(max(0, int(self.cfg.sim_scroll_steps))):
                try:
                    await page.evaluate("() => window.scrollBy(0, Math.max(200, window.innerHeight * 0.7));")
                    await page.wait_for_timeout(int(self.cfg.sim_scroll_delay_ms))
                except Exception:
                    break

            # collect post-scroll phase (no click yet)
            self._phase_tags.append("post_scroll")
            await self._collect_phase(page, page_url, log, phase="post_scroll", context=context)

            # 2) choose click targets
            targets = await self._pick_click_targets(page, log)
            if not targets:
                self._log("Dynamic sim: no click targets selected.", log)
                return

            clicks_done = 0
            for t in targets[: int(self.cfg.sim_click_targets)]:
                if clicks_done >= int(self.cfg.sim_click_targets):
                    break
                try:
                    # click via selector
                    sel = t.get("selector") or ""
                    if not sel:
                        continue

                    # ensure visible
                    try:
                        h = await page.query_selector(sel)
                        if not h:
                            continue
                        await h.scroll_into_view_if_needed(timeout=1200)
                        await h.click(timeout=int(self.cfg.sim_click_timeout_ms))
                    except Exception:
                        # fallback: click by JS
                        try:
                            await page.evaluate(
                                """
                                (sel) => {
                                  const el = document.querySelector(sel);
                                  if (el) el.click();
                                }
                                """,
                                sel,
                            )
                        except Exception:
                            continue

                    clicks_done += 1
                    await page.wait_for_timeout(int(self.cfg.per_action_settle_ms))

                    phase = f"post_click_{clicks_done}"
                    self._phase_tags.append(phase)
                    await self._collect_phase(page, page_url, log, phase=phase, context=context)

                except Exception:
                    continue

            self._log(f"Dynamic sim: scroll_steps={self.cfg.sim_scroll_steps} clicks={clicks_done}", log)
        except Exception as e:
            self._log(f"Dynamic simulation error: {e}", log)

    async def _pick_click_targets(self, page, log: Optional[List[str]]) -> List[Dict[str, Any]]:
        """
        Choose likely CTAs:
          - visible buttons / role=button / a[role=button] with text hints
          - if we have listener hits with good confidence, prefer those by looking for IDs/classes in outerHTML
        Returns a list of {selector, text, reason}
        """
        # Primary: DOM-based selection (works everywhere)
        try:
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
                      if (r.bottom < 0 || r.right < 0) return false;
                      const vw = Math.max(document.documentElement.clientWidth||0, window.innerWidth||0);
                      const vh = Math.max(document.documentElement.clientHeight||0, window.innerHeight||0);
                      if (r.top > vh || r.left > vw) return false;
                      return true;
                    } catch { return false; }
                  }

                  function textOf(el){
                    try {
                      const t = (el.innerText || el.textContent || el.value || "").trim();
                      return t.slice(0, 90);
                    } catch { return ""; }
                  }

                  function makeSelector(el){
                    // best-effort stable selector
                    try {
                      if (el.id) return `#${CSS.escape(el.id)}`;
                      const cls = (typeof el.className === "string" ? el.className : "");
                      const c1 = cls.split(/\\s+/).filter(Boolean)[0];
                      if (c1) return `${el.tagName.toLowerCase()}.${CSS.escape(c1)}`;
                      const tn = el.tagName.toLowerCase();
                      if (tn === "button") return "button";
                      if (tn === "a") return "a";
                      return tn;
                    } catch {
                      return el.tagName ? el.tagName.toLowerCase() : "";
                    }
                  }

                  const candSel = "button, [role='button'], a[role='button'], input[type='button'], input[type='submit'], [onclick]";
                  const cands = Array.from(document.querySelectorAll(candSel)).slice(0, 260);

                  const scored = [];
                  for (const el of cands){
                    if (!isVisible(el)) continue;
                    const t = textOf(el);
                    const tl = t.toLowerCase();
                    let score = 0;
                    let why = [];
                    if (t) { score += 0.2; }
                    for (const h of hints){
                      if (h && tl.includes(h)) { score += 1.0; why.push(`text:${h}`); break; }
                    }
                    const st = getComputedStyle(el);
                    if ((st.cursor||"") === "pointer") { score += 0.15; why.push("cursor:pointer"); }
                    if (el.tagName.toLowerCase() === "button") { score += 0.2; why.push("button"); }
                    if (el.getAttribute("aria-label")) { score += 0.15; why.push("aria-label"); }

                    const sel = makeSelector(el);
                    if (!sel) continue;
                    scored.push({selector: sel, text: t, score, reason: why.join(",")});
                  }

                  scored.sort((a,b) => (b.score - a.score));
                  return scored.slice(0, max);
                }
                """,
                {"hints": self.cfg.cta_text_hints, "max": 6},
                log,
            )
            out = payload if isinstance(payload, list) else []
        except Exception:
            out = []

        # Secondary: blend in listener-confidence elements (if we can make stable selectors)
        # We only have id/class and outerHTML; so we can promote those by preferring #id and .class selectors.
        promoted: List[Dict[str, Any]] = []
        for l in self._listeners:
            conf = float(l.confidence or 0.0)
            if conf < 0.45:
                continue
            attrs = l.attributes or {}
            if attrs.get("id"):
                promoted.append({"selector": f"#{attrs['id']}", "text": "", "score": 0.9 + conf * 0.1, "reason": "listener:id"})
            else:
                cls = (attrs.get("class") or "").split()
                if cls:
                    promoted.append({"selector": f".{cls[0]}", "text": "", "score": 0.75 + conf * 0.1, "reason": "listener:class"})

        # combine, dedupe selectors
        combined = []
        seen = set()
        for it in (out or []) + promoted:
            try:
                sel = str(it.get("selector") or "")
                if not sel or sel in seen:
                    continue
                seen.add(sel)
                combined.append({"selector": sel, "text": it.get("text", ""), "reason": it.get("reason", "")})
            except Exception:
                continue

        return combined[: max(1, int(self.cfg.sim_click_targets) * 3)]

    # ------------------------------------------------------------------ #
    # Materialize final hits
    # ------------------------------------------------------------------ #
    def _materialize_hits(self, page_url: str) -> List[Dict[str, Any]]:
        hits: List[Dict[str, Any]] = []

        # 1) Event listener hits (now includes confidence/reasons)
        for l in self._listeners:
            meta = {
                "nodeId": l.node_id,
                "nodeName": l.node_name,
                "types": list(l.types),
                "attributes": dict(l.attributes or {}),
                "flags": dict(l.flags or {}),
                "is_pure_js": True,
            }
            if l.outer_html:
                meta["outerHTML"] = l.outer_html
            if l.confidence is not None:
                meta["confidence"] = float(l.confidence)
            if l.reasons:
                meta["reasons"] = list(l.reasons)

            hits.append({"page": page_url, "url": page_url, "tag": "interaction", "kind": "event_listener", "meta": meta})

        # 2) Overlays
        for ov in self._overlays:
            hits.append({
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
                    **(ov.meta or {}),
                },
            })

        # 3) UI barriers (captcha/paywall/consent/adblock/scroll_lock/etc)
        for b in self._barriers:
            hits.append({
                "page": page_url,
                "url": page_url,
                "tag": "interaction",
                "kind": "ui_barrier",
                "meta": {
                    "barrier_type": b.barrier_type,
                    "evidence": b.evidence,
                    "selector_hint": b.selector_hint,
                    **(b.meta or {}),
                },
            })

        # 4) Hit-test blockers
        for ht in self._hit_tests:
            hits.append({
                "page": page_url,
                "url": page_url,
                "tag": "interaction",
                "kind": "hit_test_blocker",
                "meta": {
                    "point": list(ht.point),
                    "tagName": ht.tag_name,
                    "id": ht.id,
                    "className": ht.class_name,
                    "pointerEvents": ht.pointer_events,
                    "opacity": ht.opacity,
                    "zIndex": ht.z_index,
                    "position": ht.position,
                    "rect": ht.rect,
                    "textPreview": ht.text_preview,
                    "outerHTML": ht.outer_html,
                },
            })

        # 5) Forms (now includes kind + honeypot)
        for f in self._forms:
            hits.append({
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
                    "form_kind": f.form_kind,
                    "honeypot_suspected": bool(f.honeypot_suspected),
                    "honeypot_reasons": list(f.honeypot_reasons or []),
                },
            })

        # 6) AX nodes
        for a in self._ax:
            hits.append({
                "page": page_url,
                "url": page_url,
                "tag": "interaction",
                "kind": "ax_node",
                "meta": {
                    "role": a.role,
                    "name": a.name,
                    "value": a.value,
                    "disabled": bool(a.disabled),
                    "focused": bool(a.focused),
                    "backendDOMNodeId": a.backend_dom_node_id,
                    "nodeId": a.node_id,
                    "selector_hint": a.selector_hint,
                    **(a.meta or {}),
                },
            })

        # 7) Summary
        if self.cfg.emit_summary_hit:
            s = self._build_summary_hit(page_url)
            if s is not None:
                hits.append(s)

        return hits

    def _build_summary_hit(self, page_url: str) -> Optional[Dict[str, Any]]:
        if not self._listeners and not self._overlays and not self._forms and not self._barriers and not self._hit_tests and not self._ax:
            return None

        # listener type counts
        top_listener_types: Dict[str, int] = {}
        for l in self._listeners:
            for t in l.types:
                top_listener_types[t] = top_listener_types.get(t, 0) + 1
        top_types = sorted(top_listener_types.items(), key=lambda kv: kv[1], reverse=True)[:10]

        # overlay severity
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

        # barrier histogram
        barrier_counts: Dict[str, int] = {}
        for b in self._barriers:
            barrier_counts[b.barrier_type] = barrier_counts.get(b.barrier_type, 0) + 1
        top_barriers = sorted(barrier_counts.items(), key=lambda kv: kv[1], reverse=True)[:10]

        meta: Dict[str, Any] = {
            "listener_count": len(self._listeners),
            "overlay_count": len(self._overlays),
            "form_count": len(self._forms),
            "barrier_count": len(self._barriers),
            "hit_test_blocker_count": len(self._hit_tests),
            "ax_node_count": len(self._ax),
            "top_listener_types": top_types,
            "top_barriers": top_barriers,
            "max_overlay_coverage_percent": max_coverage,
            "max_overlay_z_index": max_z,
            "phases_seen": list(dict.fromkeys(self._phase_tags)),
        }

        return {"page": page_url, "url": page_url, "tag": "interaction", "kind": "summary", "meta": meta}

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

    async def get_prefix(
            self,
            url: str,
            *,
            size: int = 8192,
            timeout_ms: Optional[int] = None,
            headers: Optional[Dict[str, str]] = None,
            allow_redirects: bool = True,
    ) -> bytes:
        """
        Fetches only the first `size` bytes of a resource (best-effort),
        using a Range request and the Secure Gateway protections.

        Returns: bytes (possibly shorter than requested).
        """
        url = str(url or "")
        size = max(0, int(size))
        if not url or size <= 0:
            return b""

        # Range header for prefix fetch
        h = dict(headers or {})
        if not any(k.lower() == "range" for k in h.keys()):
            h["Range"] = f"bytes=0-{max(0, size - 1)}"

        # NOTE: We don't plumb timeout_ms into aiohttp per-request here because your engine
        # already enforces strict total/connect/sock_read/chunk timeouts globally.
        # But we *can* guard the whole operation with asyncio.wait_for if you want.
        async def _do() -> bytes:
            r = await self._request(
                "GET",
                url,
                want_body=True,
                allow_redirects=allow_redirects,
                headers=h,
                max_bytes=size,
            )
            if not r.ok or not r.body:
                return b""
            # r.body is already bounded by max_bytes and passed through your secure reader.
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
        """
        Convenience probe for sniffers:
          - HEAD for status + headers
          - bounded GET prefix for hashing / verification

        Returns a dict shaped similarly to what NetworkSniffer._probe_url() builds.
        """
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
            # Your head() returns the response headers dict from _request
            ct = (hdrs.get("Content-Type") or hdrs.get("content-type") or None)
            cl = (hdrs.get("Content-Length") or hdrs.get("content-length") or None)
            out["content_type"] = ct
            out["content_length"] = cl
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
                if (hash_algo or "").lower() == "sha1":
                    out["hash_prefix"] = hashlib.sha1(prefix).hexdigest()
                elif (hash_algo or "").lower() == "md5":
                    out["hash_prefix"] = hashlib.md5(prefix).hexdigest()
                else:
                    out["hash_prefix"] = hashlib.sha256(prefix).hexdigest()
        except Exception as e:
            # don’t clobber prior error unless empty
            if not out["error"]:
                out["error"] = f"prefix_failed:{e}"

        try:
            if out["status"] is not None and 200 <= int(out["status"]) < 300:
                out["ok"] = True
        except Exception:
            pass

        return out
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