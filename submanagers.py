from __future__ import annotations

import asyncio
import collections  # For collections.Counter
import hashlib
import re
import sqlite3
import ssl
import threading
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Sequence, Iterable
from urllib.parse import urlparse, urljoin, parse_qsl, urlencode, urlunparse
import random  # For random delays
import json  # For JSON parsing in NetworkSniffer and JSSniffer
import xml.etree.ElementTree as ET

import aiohttp
from aiohttp import ClientTimeout

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
    Advanced Playwright network sniffer for VIDEO + AUDIO + IMAGES.

    Adds:
      - blob:/MediaSource recovery (records blob media placeholders)
      - HLS/DASH manifest expansion into derived segment links
      - Robust URL canonicalization for all captured URLs.
      - Granular logging for filtering decisions.
      - SAFE JSON sniffing (size + URL pattern gated).
      - Auto-scroll support to trigger lazy-loaded media/content.
      - Configurable goto_wait_until (e.g. 'commit' for Camoufox).
    """

    @dataclass
    class Config:
        timeout: float = 8.0
        max_items: int = 250
        max_json_hits: int = 100

        # how many derived items to add per manifest
        max_derived_per_manifest: int = 200
        # max manifests to expand per page
        max_manifests_to_expand: int = 10

        # If True, store sniff items even without size/ctype
        accept_unknown_streams: bool = True

        # ------------------ auto-scroll options ------------------ #
        enable_auto_scroll: bool = True
        max_scroll_steps: int = 20
        scroll_step_delay_ms: int = 400
        scroll_back_to_top: bool = False

        # How Playwright waits in page.goto; for Camoufox you can set "commit"
        goto_wait_until: str = "domcontentloaded"

        # ------------------ extension sets ------------------ #

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

        junk_extensions: Set[str] = field(default_factory=lambda: {
            ".js", ".css", ".json", ".html", ".woff", ".woff2",
            ".ttf", ".map", ".vtt", ".srt"
        })

        # ------------------ content-type sets ------------------ #

        video_prefixes: Set[str] = field(default_factory=lambda: {"video/"})
        audio_prefixes: Set[str] = field(default_factory=lambda: {"audio/"})
        image_prefixes: Set[str] = field(default_factory=lambda: {"image/"})

        hls_types: Set[str] = field(default_factory=lambda: {
            "application/x-mpegurl", "application/vnd.apple.mpegurl"
        })
        dash_types: Set[str] = field(default_factory=lambda: {
            "application/dash+xml", "application/vnd.mpeg.dash.mpd"
        })

        deny_content_substrings: Set[str] = field(default_factory=lambda: {
            "javascript", "css", "text/html", "font/"
        })
        deny_resource_types: Set[str] = field(default_factory=lambda: {
            "stylesheet", "font", "manifest", "other"
        })

        # ------------------ stream hint sets ------------------ #

        video_stream_hints: Set[str] = field(default_factory=lambda: {
            ".m3u8", "manifest.mpd", "master.m3u8", "chunklist.m3u8",
            "videoplayback", "dash", "hls", "stream", "cdn"
        })
        audio_stream_hints: Set[str] = field(default_factory=lambda: {
            "audio", "sound", "stream", ".mp3", ".m4a", ".aac",
            ".flac", ".ogg", ".opus"
        })

        # ------------------ ad/tracker sets ------------------ #

        ad_host_substrings: Set[str] = field(default_factory=lambda: {
            "doubleclick", "googlesyndication", "adservice", "adserver",
            "adsystem", "adnxs", "tracking", "analytics", "metrics",
            "scorecardresearch", "pixel.", "trk.", "stats.", "ad."
        })
        ad_path_keywords: Set[str] = field(default_factory=lambda: {
            "/ads/", "/adserver/", "/banner/", "/promo/", "/tracking/",
            "/click/", "/impression", "/pixel", "/sponsor/", "/advert/"
        })

        # ------------------ JSON sniff config ------------------ #

        enable_json_sniff: bool = True

        json_url_hints: Set[str] = field(default_factory=lambda: {
            "player", "manifest", "api", "metadata", "m3u8", "mpd",
            "playlist", "video", "audio"
        })
        json_content_types: Set[str] = field(default_factory=lambda: {
            "application/json", "text/json"
        })

        # HARD gate: only sniff JSON when BOTH:
        #  - Content-Length <= json_body_max_kb, AND
        #  - URL matches one of json_url_patterns.
        json_body_max_kb: int = 256
        json_url_patterns: Set[str] = field(default_factory=lambda: {
            "/api/player",
            "/player_api",
            "/player/",
            "/manifest",
            "/playlist",
            "/video/",
            "/audio/",
        })

    def __init__(self, config: Optional["NetworkSniffer.Config"] = None, logger=None):
        self.cfg = config or self.Config()
        self.logger = logger or DEBUG_LOGGER
        self._log("[NetworkSniffer] NetworkSniffer initialized", None)

    # ------------------------------ logging helper ------------------------------ #

    def _log(self, msg: str, log_list: Optional[List[str]]) -> None:
        try:
            if log_list is not None:
                log_list.append(msg)
            if self.logger is not None:
                self.logger.log_message(msg)
        except Exception:
            pass

    # ------------------------------ helpers ------------------------------ #

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

    def _should_sniff_json(
        self,
        url_lower: str,
        ctype: str,
        content_length: Optional[int],
    ) -> bool:
        if not self.cfg.enable_json_sniff:
            return False

        ct = (ctype or "").lower()
        if not (any(jt in ct for jt in self.cfg.json_content_types) or "/metadata/" in url_lower):
            return False

        if not any(h in url_lower for h in self.cfg.json_url_hints):
            return False

        if content_length is None:
            return False
        max_bytes = int(self.cfg.json_body_max_kb) * 1024
        if content_length > max_bytes:
            return False

        if not self._matches_json_pattern(url_lower):
            return False

        return True

    def _is_allowed_by_extensions(self, url: str, extensions: Optional[Set[str]], kind: Optional[str]) -> bool:
        if not extensions:
            return True

        parsed = urlparse(url)
        path = (parsed.path or "").lower()

        if any(path.endswith(ext.lower()) for ext in extensions):
            return True

        if self.cfg.accept_unknown_streams and kind in ("video", "audio"):
            return True

        return False

    def _is_manifest(self, url: str, ctype: str) -> Optional[str]:
        ul = url.lower()
        ct = (ctype or "").lower()
        if ul.endswith(".m3u8") or ct in self.cfg.hls_types:
            return "hls"
        if ul.endswith(".mpd") or ct in self.cfg.dash_types:
            return "dash"
        return None

    # ------------------ manifest parsing ------------------ #

    _HLS_URL_RE = re.compile(
        r'(?:\n|^)(?!#EXTINF|#EXT-X-)([^#\s]+\.(?:ts|mp4|m3u8)(?:\?[^#\s]*)?)$',
        re.MULTILINE | re.IGNORECASE
    )
    _HLS_GENERIC_URL_RE = re.compile(
        r'(?:\n|^)(?!#)(https?://[^#\s]+)$',
        re.MULTILINE | re.IGNORECASE
    )

    def _parse_hls_manifest(self, manifest_text: str, base_url: str) -> List[str]:
        out = []
        for m in self._HLS_URL_RE.finditer(manifest_text or ""):
            out.append(_canonicalize_url(urljoin(base_url, m.group(1).strip())))

        if not out:
            for m in self._HLS_GENERIC_URL_RE.finditer(manifest_text or ""):
                out.append(_canonicalize_url(urljoin(base_url, m.group(1).strip())))

        return out

    _MPD_URL_RE = re.compile(
        r'(?:media|initialization|sourceURL|href)\s*=\s*["\']([^"\']+)["\']',
        re.I
    )

    def _parse_mpd_manifest(self, manifest_text: str, base_url: str) -> List[str]:
        out = []
        try:
            root = ET.fromstring(manifest_text)
            for el in root.iter():
                for attr_name in ['media', 'initialization', 'sourceURL', 'href']:
                    if attr_name in el.attrib:
                        u = el.attrib[attr_name].strip()
                        if u:
                            out.append(_canonicalize_url(urljoin(base_url, u)))
            if out:
                return out
        except Exception:
            pass

        for m in self._MPD_URL_RE.finditer(manifest_text or ""):
            u = m.group(1).strip()
            if not u:
                continue
            out.append(_canonicalize_url(urljoin(base_url, u)))
        return out

    async def _expand_manifest(
        self,
        response: Response,
        manifest_kind: str,
        url: str,
        log: Optional[List[str]],
    ) -> List[str]:
        try:
            txt = await response.text()
        except Exception as e:
            self._log(f"[NetworkSniffer] Manifest read failed: {url} ({e})", log)
            return []

        if manifest_kind == "hls":
            derived = self._parse_hls_manifest(txt, url)
        else:
            derived = self._parse_mpd_manifest(txt, url)

        self._log(
            f"[NetworkSniffer] Expanded {manifest_kind} manifest: {url} -> {len(derived)} derived",
            log
        )
        return derived

    # ------------------ auto-scroll implementation ------------------ #

    async def _auto_scroll(self, page: "Page", tmo: float, log: Optional[List[str]]) -> None:
        if not self.cfg.enable_auto_scroll:
            return

        try:
            max_steps = max(1, int(self.cfg.max_scroll_steps))
            step_delay = max(50, int(self.cfg.scroll_step_delay_ms))

            max_total_ms = int(tmo * 1000 * 0.8)
            used_ms = 0

            self._log(
                f"[NetworkSniffer] Auto-scroll enabled: steps={max_steps}, step_delay={step_delay}ms",
                log,
            )

            last_height = await page.evaluate("() => document.body ? document.body.scrollHeight : 0")

            for i in range(max_steps):
                if used_ms >= max_total_ms:
                    self._log("[NetworkSniffer] Auto-scroll: reached time budget; stopping.", log)
                    break

                await page.evaluate("() => window.scrollBy(0, window.innerHeight);")
                await page.wait_for_timeout(step_delay)
                used_ms += step_delay

                new_height = await page.evaluate("() => document.body ? document.body.scrollHeight : 0")

                self._log(
                    f"[NetworkSniffer] Auto-scroll step {i + 1}/{max_steps}: "
                    f"height {last_height} -> {new_height}",
                    log,
                )

                if new_height <= last_height:
                    self._log("[NetworkSniffer] Auto-scroll: no further height growth; stopping.", log)
                    break

                last_height = new_height

            if self.cfg.scroll_back_to_top:
                try:
                    await page.evaluate("() => window.scrollTo(0, 0);")
                    self._log("[NetworkSniffer] Auto-scroll: scrolled back to top.", log)
                except Exception as e:
                    self._log(f"[NetworkSniffer] Auto-scroll: failed to scroll back to top: {e}", log)

        except Exception as e:
            self._log(f"[NetworkSniffer] Auto-scroll error: {e}", log)

    # ------------------ output normalization ------------------ #

    def _normalize_item(self, it: Dict[str, Any]) -> Dict[str, str]:
        return {
            "url": str(it.get("url") or ""),
            "text": str(it.get("text") or ""),
            "tag": str(it.get("tag") or "network_sniff"),
            "kind": str(it.get("kind") or "unknown"),
            "content_type": str(it.get("content_type") or "?"),
            "size": str(it.get("size") or "?"),
        }

    # ------------------------------ public ------------------------------ #

    async def sniff(
        self,
        context: BrowserContext,
        page_url: str,
        *,
        timeout: Optional[float] = None,
        log: Optional[List[str]] = None,
        extensions: Optional[Set[str]] = None,
    ) -> Tuple[str, List[Dict[str, str]], List[Dict[str, Any]]]:

        if context is None:
            self._log("[NetworkSniffer] No Playwright context; skipping sniff.", log)
            return "", [], []
        if Page is None:
            self._log("[NetworkSniffer] Playwright classes not found; skipping sniff.", log)
            return "", [], []

        tmo = float(timeout if timeout is not None else self.cfg.timeout)
        canonical_page_url = _canonicalize_url(page_url)

        found_items: List[Dict[str, Any]] = []
        json_hits: List[Dict[str, Any]] = []
        derived_items: List[Dict[str, Any]] = []

        seen_network: Set[str] = set()
        seen_derived: Set[str] = set()

        blob_placeholders: List[Dict[str, Any]] = []
        req_types: Dict[str, str] = {}

        html: str = ""

        page: Page = await context.new_page()
        wait_mode = getattr(self.cfg, "goto_wait_until", "domcontentloaded")

        try:
            max_items = int(self.cfg.max_items)
            max_json = int(self.cfg.max_json_hits)
            max_derived_per_manifest = int(self.cfg.max_derived_per_manifest)
            max_manifests = int(self.cfg.max_manifests_to_expand)

            manifests_to_expand: List[Tuple[Response, str, str]] = []

            self._log(
                f"[NetworkSniffer] Start sniff: {canonical_page_url} (timeout={tmo}s)",
                log
            )

            def handle_request(req: Request):
                try:
                    req_types[req.url] = req.resource_type
                except Exception:
                    pass

            page.on("request", handle_request)

            async def handle_json(resp: Response, url: str):
                if len(json_hits) >= max_json:
                    return
                try:
                    data = await resp.json()
                    json_hits.append({"url": url, "json": data, "source_page": canonical_page_url})
                except Exception as e:
                    self._log(f"[NetworkSniffer] Failed to parse JSON from {url}: {e}", log)

            def handle_response(response: Response):
                try:
                    url = response.url
                    canonical_url = _canonicalize_url(url)

                    if not canonical_url or canonical_url in seen_network:
                        return

                    is_blob = canonical_url.startswith("blob:")
                    resource_type = req_types.get(url, "")

                    if not is_blob:
                        parsed = urlparse(canonical_url)
                        path = (parsed.path or "/").lower()
                        netloc = parsed.netloc or ""
                        url_lower = canonical_url.lower()

                        if self._is_junk_by_extension(path):
                            self._log(f"[NetworkSniffer] Skipped junk ext: {canonical_url}", log)
                            return
                        if self._looks_like_ad(netloc, path):
                            self._log(f"[NetworkSniffer] Skipped ad: {canonical_url}", log)
                            return

                    seen_network.add(canonical_url)

                    ctype = (response.headers.get("content-type") or "").lower()
                    url_lower = canonical_url.lower()

                    cl_header = response.headers.get("content-length") or ""
                    content_length: Optional[int] = None
                    try:
                        if cl_header and cl_header.isdigit():
                            content_length = int(cl_header)
                    except Exception:
                        content_length = None

                    if (not is_blob) and ctype and self._deny_by_content_type(ctype):
                        self._log(
                            f"[NetworkSniffer] Skipped denied ctype: {canonical_url} ({ctype})",
                            log
                        )
                        return

                    if (not is_blob) and resource_type and self._deny_by_resource_type(resource_type):
                        self._log(
                            f"[NetworkSniffer] Skipped denied rtype: {canonical_url} ({resource_type})",
                            log
                        )
                        return

                    # ---- SAFE JSON sniff ----
                    if (not is_blob) and self._should_sniff_json(url_lower, ctype, content_length):
                        asyncio.create_task(handle_json(response, canonical_url))
                        return

                    # ---- Blob media handling ----
                    if is_blob:
                        if resource_type == "media":
                            blob_placeholders.append({
                                "url": canonical_url,
                                "text": "[Network Video Blob]",
                                "tag": "network_sniff",
                                "kind": "video",
                                "content_type": ctype or "?",
                                "size": response.headers.get("content-length", "?"),
                            })
                            if len(json_hits) < max_json:
                                json_hits.append({
                                    "url": canonical_url,
                                    "json": {"blob_media": canonical_url, "reason": "blob-media-detected"},
                                    "source_page": canonical_page_url
                                })
                            self._log(
                                f"[NetworkSniffer] Detected blob media: {canonical_url}",
                                log
                            )
                        return

                    parsed = urlparse(canonical_url)
                    path = (parsed.path or "/").lower()

                    kind = (
                        self._classify_by_extension(path)
                        or (self._classify_by_content_type(ctype) if ctype else None)
                        or self._classify_by_stream_hint(url_lower)
                    )
                    if not kind:
                        self._log(f"[NetworkSniffer] Skipped unknown kind: {canonical_url}", log)
                        return

                    if not self._is_allowed_by_extensions(canonical_url, extensions, kind):
                        self._log(
                            f"[NetworkSniffer] Skipped by extensions: {canonical_url} (kind={kind})",
                            log
                        )
                        return

                    mkind = self._is_manifest(canonical_url, ctype)
                    if mkind and kind == "video" and len(manifests_to_expand) < max_manifests:
                        manifests_to_expand.append((response, mkind, canonical_url))
                        self._log(
                            f"[NetworkSniffer] Identified manifest: {canonical_url} (kind={mkind})",
                            log
                        )

                    if len(found_items) >= max_items:
                        return

                    found_items.append({
                        "url": canonical_url,
                        "text": f"[Network {kind.capitalize()}]",
                        "tag": "network_sniff",
                        "kind": kind,
                        "content_type": ctype or "?",
                        "size": response.headers.get("content-length", "?"),
                    })
                    self._log(f"[NetworkSniffer] Added item: {canonical_url} (kind={kind})", log)

                except Exception as e:
                    self._log(
                        f"[NetworkSniffer][handle_response] Error processing {response.url}: {e}",
                        log
                    )
                    return

            page.on("response", handle_response)

            sniff_goto_timeout = max(15000, int(tmo * 1000))
            try:
                await page.goto(
                    canonical_page_url,
                    wait_until=wait_mode,
                    timeout=sniff_goto_timeout
                )
            except Exception as e:
                self._log(
                    f"[NetworkSniffer] goto timeout on {canonical_page_url} (wait_until={wait_mode}): {e}",
                    log
                )

            # ---- Auto-scroll to trigger more network activity ----
            await self._auto_scroll(page, tmo, log)

            # Final small wait (<= 20% of tmo)
            await page.wait_for_timeout(int(tmo * 1000 * 0.2))

            if manifests_to_expand:
                self._log(
                    f"[NetworkSniffer] Expanding {len(manifests_to_expand)} manifests...",
                    log
                )

                async def expand_one(resp: Response, mkind: str, murl: str):
                    derived_urls = await self._expand_manifest(resp, mkind, murl, log)
                    if not derived_urls:
                        return

                    for u in derived_urls[:max_derived_per_manifest]:
                        if u in seen_derived or u in seen_network:
                            continue
                        seen_derived.add(u)

                        dk = self._classify_by_extension(
                            urlparse(u).path or ""
                        ) or "video"
                        if not self._is_allowed_by_extensions(u, extensions, dk):
                            self._log(
                                f"[NetworkSniffer] Derived skipped by extensions: {u} (kind={dk})",
                                log
                            )
                            continue

                        derived_items.append({
                            "url": u,
                            "text": f"[Network {dk.capitalize()} Segment]",
                            "tag": "network_sniff",
                            "kind": dk,
                            "content_type": mkind,
                            "size": "?",
                        })
                        self._log(
                            f"[NetworkSniffer] Added derived item: {u} (kind={dk})",
                            log
                        )

                        if len(json_hits) < max_json:
                            json_hits.append({
                                "url": u,
                                "json": {"derived_from": murl, "manifest_type": mkind},
                                "source_page": canonical_page_url
                            })

                await asyncio.gather(*[
                    expand_one(resp, mkind, murl)
                    for (resp, mkind, murl) in manifests_to_expand
                ])

                self._log(
                    f"[NetworkSniffer] Finished manifest expansion. Total derived: {len(derived_items)}",
                    log
                )

            try:
                html = await page.content()
            except Exception as e:
                self._log(f"[NetworkSniffer] Failed to get page content: {e}", log)
                html = ""

        except Exception as e:
            self._log(f"[NetworkSniffer] Unexpected error during sniff for {canonical_page_url}: {e}", log)
        finally:
            try:
                try:
                    await asyncio.wait_for(page.close(), timeout=3.0)
                except asyncio.TimeoutError:
                    self._log("[NetworkSniffer] page.close() timed out; ignoring.", log)
            except Exception as e:
                self._log(f"[NetworkSniffer] Failed to close page: {e}", log)

            merged_items_any = found_items + derived_items + blob_placeholders
        merged_items = [self._normalize_item(it) for it in merged_items_any if it.get("url")]

        summary = (
            f"[NetworkSniffer] Finished sniff for {canonical_page_url}: "
            f"media={len(found_items)} derived={len(derived_items)} "
            f"blob={len(blob_placeholders)} json_hits={len(json_hits)} "
            f"(Total output: {len(merged_items)})"
        )
        self._log(summary, log)

        return html, merged_items, json_hits


# ======================================================================
# JSSniffer
# ======================================================================

class JSSniffer:
    """
    Shared-context Playwright JS DOM link sniffer.

    Output schema:
      link = {url, text, tag}

    Now:
      - Configurable goto_wait_until (e.g. 'commit' for Camoufox).
      - goto timeouts are non-fatal (log + continue).
      - Bounded auto-scroll relative to timeout.
    """

    @dataclass
    class Config:
        timeout: float = 8.0
        max_links: int = 500
        wait_after_goto_ms: int = 500
        include_shadow_dom: bool = True

        # ------------------ auto-scroll options ------------------ #
        enable_auto_scroll: bool = True
        max_scroll_steps: int = 20
        scroll_step_delay_ms: int = 400
        scroll_back_to_top: bool = False

        # How Playwright waits in page.goto; for Camoufox you can set "commit"
        goto_wait_until: str = "domcontentloaded"

        selectors: List[str] = field(default_factory=lambda: [
            "a[href]",
            "video[src]",
            "video source[src]",
            "source[src]",
            "audio[src]",
            "audio source[src]",
            "img[src]",
            "iframe[src]",
            "embed[src]",
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
            "data-href", "data-url", "data-src", "data-video", "data-video-url",
            "data-file", "data-stream", "data-mp4", "data-m3u8", "data-mpd",
            "data-audio", "data-audio-url", "data-image", "data-poster",
            "data-media-url"
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

        enable_click_simulation: bool = False
        max_click_targets: int = 6
        click_timeout_ms: int = 2500
        click_target_selectors: List[str] = field(default_factory=lambda: [
            "a[href]", "button", "[role=button]", "[onclick]",
            "div[role=link]", "span[role=link]"
        ])

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

    def _is_allowed_by_extensions(
        self,
        url: str,
        extensions: Optional[Set[str]],
        kind: Optional[str]
    ) -> bool:
        if not extensions:
            return True

        parsed = urlparse(url)
        p = (parsed.path or "").lower()

        if any(p.endswith(ext.lower()) for ext in extensions):
            return True

        if kind in ("video", "audio"):
            return True

        return False

    def _abs_url_js(self, base: str, u: str) -> str:
        try:
            return urljoin(base, u)
        except Exception:
            return u

    def _normalize_link(self, url: str, text: str, tag: str) -> Dict[str, str]:
        return {
            "url": url,
            "text": text or "",
            "tag": tag or "a",
        }

    # ------------------ auto-scroll implementation ------------------ #

    async def _auto_scroll(self, page: "Page", tmo: float, log: Optional[List[str]]) -> None:
        if not self.cfg.enable_auto_scroll:
            return

        try:
            max_steps = max(1, int(self.cfg.max_scroll_steps))
            step_delay = max(50, int(self.cfg.scroll_step_delay_ms))

            max_total_ms = int(tmo * 1000 * 0.7)
            used_ms = 0

            self._log(
                f"Auto-scroll enabled: steps={max_steps}, step_delay={step_delay}ms",
                log,
            )

            last_height = await page.evaluate(
                "() => document.body ? document.body.scrollHeight : 0"
            )

            for i in range(max_steps):
                if used_ms >= max_total_ms:
                    self._log("Auto-scroll: reached time budget; stopping.", log)
                    break

                await page.evaluate("() => window.scrollBy(0, window.innerHeight);")
                await page.wait_for_timeout(step_delay)
                used_ms += step_delay

                new_height = await page.evaluate(
                    "() => document.body ? document.body.scrollHeight : 0"
                )

                self._log(
                    f"Auto-scroll step {i + 1}/{max_steps}: "
                    f"height {last_height} -> {new_height}",
                    log,
                )

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
        context: BrowserContext,
        page_url: str,
        *,
        timeout: Optional[float] = None,
        log: Optional[List[str]] = None,
        extensions: Optional[Set[str]] = None,
    ) -> Tuple[str, List[Dict[str, str]]]:

        if context is None:
            self._log("No Playwright context; skipping JS sniff.", log)
            return "", []
        if Page is None:
            self._log("Playwright classes not found; skipping JS sniff.", log)
            return "", []

        tmo = float(timeout if timeout is not None else self.cfg.timeout)
        canonical_page_url = _canonicalize_url(page_url)

        html: str = ""
        links: List[Dict[str, str]] = []
        seen_urls_in_js: Set[str] = set()

        page: Page = await context.new_page()
        js_timeout_ms = int(max(tmo, 10.0) * 1000)
        wait_after_ms = int(self.cfg.wait_after_goto_ms)
        wait_mode = getattr(self.cfg, "goto_wait_until", "domcontentloaded")

        selector_js = ", ".join(self.cfg.selectors)
        data_keys_js = list(self.cfg.data_url_keys)
        onclick_regexes_js = [r.replace("\\", "\\\\") for r in self.cfg.onclick_url_regexes]
        redirect_hints_js = list(self.cfg.redirect_hints)
        script_json_hints_js = list(self.cfg.script_json_hints)

        self._log(f"Start: {canonical_page_url} timeout={tmo}s", log)

        try:
            # --- 1) Navigation: timeout is NON-FATAL --- #
            try:
                await page.goto(
                    canonical_page_url,
                    wait_until=wait_mode,
                    timeout=js_timeout_ms,
                )
            except Exception as e:
                self._log(
                    f"goto timeout on {canonical_page_url} (wait_until={wait_mode}): {e}",
                    log,
                )

            if wait_after_ms > 0:
                await page.wait_for_timeout(wait_after_ms)

            # ---- Auto-scroll to trigger lazy-loaded elements ----
            await self._auto_scroll(page, tmo, log)

            # Small extra delay after scroll (<= 10% of tmo, but at least 200ms)
            extra_wait = max(200, int(tmo * 1000 * 0.1))
            await page.wait_for_timeout(extra_wait)

            html = await page.content()

            raw_payload = await page.evaluate(
                """
                (args) => {
                  const {
                    selectors,
                    includeShadow,
                    dataKeys,
                    onclickRegexes,
                    redirectHints,
                    scriptJsonHints,
                    baseUrl
                  } = args;

                  const out = [];
                  const seen = new Set();

                  function absUrl(u) {
                    if (!u) return "";
                    try {
                      return new URL(u, baseUrl).href;
                    } catch {
                      return u;
                    }
                  }

                  function push(el, url, tag, reason=null) {
                    url = absUrl(String(url).trim());
                    if (!url || url.startsWith('blob:') || url.startsWith('javascript:') || url.startsWith('data:') || seen.has(url)) {
                      return;
                    }
                    seen.add(url);
                    const text = (el.innerText || el.textContent || el.title || "").trim();
                    const item = { url, text, tag };
                    if (reason) item.reason = reason;
                    out.push(item);
                  }

                  function sniffDataAttrs(el) {
                    for (const k of dataKeys) {
                      const v = el.getAttribute?.(k);
                      if (v) push(el, v, el.tagName.toLowerCase(), "data-attr");
                    }
                    for (const attr of (el.attributes || [])) {
                      const n = attr.name.toLowerCase();
                      const v = attr.value;
                      if (n.startsWith("data-") && v && (v.includes("http") || v.includes("://"))) {
                        push(el, v, el.tagName.toLowerCase(), "data-generic");
                      }
                    }
                  }

                  function sniffOnclick(el) {
                    const oc = el.getAttribute?.("onclick") || "";
                    if (!oc) return;
                    for (const rx of onclickRegexes) {
                      try {
                        const r = new RegExp(rx, "ig");
                        let m;
                        while ((m = r.exec(oc)) !== null) {
                          if (m[1]) push(el, m[1], el.tagName.toLowerCase(), "onclick");
                        }
                      } catch (e) {}
                    }
                    const ocl = oc.toLowerCase();
                    for (const h of redirectHints) {
                      if (ocl.includes(h)) {
                        const urlMatch = ocl.match(/(https?:)?\\/\\/[^\\s'"]+/);
                        if (urlMatch) {
                          push(el, urlMatch[0], el.tagName.toLowerCase(), "redirect-hint-url");
                        } else {
                          push(el, oc, el.tagName.toLowerCase(), "redirect-hint");
                        }
                        break;
                      }
                    }
                  }

                  function sniffInlineListeners(el) {
                    const inlineEvents = ["onclick","onmousedown","onmouseup","ontouchstart","ontouchend", "onplay", "oncanplay"];
                    for (const k of inlineEvents) {
                      const v = el.getAttribute?.(k);
                      if (v) {
                        for (const rx of onclickRegexes) {
                          try {
                            const r = new RegExp(rx, "ig");
                            let m;
                            while ((m = r.exec(v)) !== null) {
                              if (m[1]) push(el, m[1], el.tagName.toLowerCase(), `inline-listener-${k}`);
                            }
                          } catch {}
                        }
                      }
                    }
                  }

                  function walk(node) {
                    if (!node) return;

                    node.querySelectorAll?.(selectors).forEach(el => {
                      let url =
                        el.href ||
                        el.currentSrc ||
                        el.src ||
                        el.getAttribute("href") ||
                        el.getAttribute("src");
                      push(el, url, el.tagName.toLowerCase(), "dom");
                      sniffDataAttrs(el);
                      sniffOnclick(el);
                      sniffInlineListeners(el);
                    });

                    if (includeShadow) {
                      node.querySelectorAll?.("*").forEach(el => {
                        if (el.shadowRoot) walk(el.shadowRoot);
                      });
                    }
                  }

                  function scanScripts(doc) {
                    const scripts = Array.from(doc.querySelectorAll("script"));
                    for (const s of scripts) {
                      const txt = (s.textContent || "").trim();
                      if (!txt) continue;

                      const urls = txt.match(/(https?:)?\\/\\/[^\\s'"]{6,}/ig) || [];
                      for (const u of urls) push(s, u, "script", "script-raw-url");

                      if (txt.startsWith("{") || txt.startsWith("[")) {
                        try {
                          const data = JSON.parse(txt);
                          const stack = [data];
                          const visitedObjects = new WeakSet();
                          while (stack.length) {
                            const cur = stack.pop();
                            if (!cur || typeof cur !== "object" || visitedObjects.has(cur)) continue;
                            visitedObjects.add(cur);

                            if (typeof cur === "string") {
                              const low = cur.toLowerCase();
                              if (low.includes("http") || low.includes("m3u8") || low.includes("mpd")) {
                                push(s, cur, "script", "script-json-string");
                              }
                              continue;
                            }
                            if (Array.isArray(cur)) {
                              for (let i = cur.length - 1; i >= 0; i--) stack.push(cur[i]);
                              continue;
                            }
                            if (typeof cur === "object") {
                              for (const [k,v] of Object.entries(cur)) {
                                const kl = k.toLowerCase();
                                if (scriptJsonHints.some(h => kl.includes(h))) {
                                  if (typeof v === "string") push(s, v, "script", "script-json-key");
                                }
                                stack.push(v);
                              }
                            }
                          }
                        } catch (e) {}
                      }
                    }
                  }

                  walk(document);
                  scanScripts(document);

                  return { items: out };
                }
                """,
                {
                    "selectors": selector_js,
                    "includeShadow": self.cfg.include_shadow_dom,
                    "dataKeys": data_keys_js,
                    "onclickRegexes": onclick_regexes_js,
                    "redirectHints": redirect_hints_js,
                    "scriptJsonHints": script_json_hints_js,
                    "baseUrl": canonical_page_url,
                }
            ) or {}

            raw_links = raw_payload.get("items") or []
            self._log(f"Raw links from DOM/scripts: {len(raw_links)}", log)

            # Optional click simulation (unchanged)
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
                                tagName: el.tagName.toLowerCase(),
                                hasHref: !!el.href,
                                hasSrc: !!el.src,
                                innerText: el.innerText,
                                isVisible: el.offsetParent !== null
                            })""")

                            if (not el_info['isVisible'] or
                                (el_info['tagName'] == 'a' and el_info['hasHref'])):
                                self._log(
                                    f"Skipping click on {el_info['tagName']} "
                                    f"(visible={el_info['isVisible']}, hasHref={el_info['hasHref']}).",
                                    log
                                )
                                continue

                            self._log(
                                f"Clicking target {h_idx + 1}/{len(handles)}…",
                                log
                            )
                            await h.scroll_into_view_if_needed(timeout=1000)
                            await h.click(timeout=int(self.cfg.click_timeout_ms))
                            await page.wait_for_timeout(300)

                            click_raw = await page.evaluate(
                                """
                                (baseUrl) => {
                                  const out = [];
                                  const seen = new Set();
                                  function absUrl(u) {
                                    if (!u) return "";
                                    try { return new URL(u, baseUrl).href; } catch { return u; }
                                  }
                                  document.querySelectorAll("a[href], video[src], audio[src], img[src], source[src]")
                                    .forEach(el => {
                                      let url = el.href || el.currentSrc || el.src ||
                                                el.getAttribute("href") || el.getAttribute("src");
                                      url = absUrl(String(url).trim());
                                      if (!url || seen.has(url)) return;
                                      seen.add(url);
                                      out.push({url, tag: el.tagName.toLowerCase()});
                                    });
                                  return out;
                                }
                                """,
                                canonical_page_url
                            ) or []
                            for it in click_raw:
                                raw_links.append({
                                    "url": it.get("url"),
                                    "text": "",
                                    "tag": it.get("tag") or "a",
                                    "reason": "click-sim",
                                })
                            self._log(
                                f"Click {h_idx + 1} yielded {len(click_raw)} new links.",
                                log
                            )

                        except Exception as click_e:
                            self._log(
                                f"Error during click sim for target {h_idx + 1}: {click_e}",
                                log
                            )
                            continue
                except Exception as e:
                    self._log(f"Overall click-sim error: {e}", log)

            # Filter + normalize
            max_links = int(self.cfg.max_links)

            for item in raw_links:
                if len(links) >= max_links:
                    break

                url = (item.get("url") or "").strip()
                if not url:
                    continue

                canonical_url_py = _canonicalize_url(url)
                if canonical_url_py in seen_urls_in_js:
                    continue
                seen_urls_in_js.add(canonical_url_py)

                if self._is_junk_url(url):
                    self._log(f"Skipped junk URL: {url}", log)
                    continue

                kind = self._classify_kind(url)
                if not self._is_allowed_by_extensions(url, extensions, kind):
                    self._log(
                        f"Skipped by extensions: {url} (kind={kind})",
                        log
                    )
                    continue

                links.append(self._normalize_link(
                    url=canonical_url_py,
                    text=(item.get("text") or "").strip(),
                    tag=(item.get("tag") or "a"),
                ))
                self._log(f"Added JS item: {canonical_url_py}", log)

            self._log(f"Done: {len(links)} links for {canonical_page_url}", log)
        except Exception as e:
            self._log(f"Overall error on {canonical_page_url}: {e}", log)

        # --- Robust page close: NEVER let close() hang the whole sniffer --- #
        try:
            try:
                # Hard cap: if Camoufox / page is weird, give close() a small budget
                await asyncio.wait_for(page.close(), timeout=3.0)
            except asyncio.TimeoutError:
                self._log("page.close() timed out; ignoring and continuing.", log)
        except Exception as e:
            self._log(f"Failed to close page: {e}", log)
        return html, links

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

    async def _fetch_text(self, session: aiohttp.ClientSession, url: str,
                          timeout: float, log: list[str]) -> str:
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

    async def _download_binary(self, session: aiohttp.ClientSession, url: str,
                               path: Path, timeout: float,
                               log: list[str], budget: dict) -> bool:
        """
        Download binary URL into path, respecting global byte budget.
        Returns True if some bytes written.
        """
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

class HTTPSSubmanager:
    """
    Shared HTTPS engine for LinkTrackerBlock and other crawlers.

    Features:
    - One aiohttp session for the entire crawl (fast, low overhead).
    - Retries with exponential backoff.
    - Per-host concurrency limiting.
    - Unified GET/HEAD/text/bytes interfaces.
    - Optional automatic proxy rotation.
    - Explicit TLS control (verify, custom CA bundle).
    """

    def __init__(
        self,
        user_agent: str = "Mozilla/5.0 PromptChat/LinkTracker",
        timeout: float = 6.0,
        retries: int = 2,
        backoff_base: float = 0.35,
        max_conn_per_host: int = 8,
        proxy: Optional[str] = None,          # "http://127.0.0.1:8888"
        proxy_pool: Optional[list] = None,    # list of proxies to rotate
        verify: bool = True,
        ca_bundle: Optional[str] = None,      # e.g. path to certifi bundle in PyInstaller exe
    ):
        self.ua = user_agent
        self.timeout = timeout
        self.retries = retries
        self.backoff_base = backoff_base
        self.max_conn_per_host = max_conn_per_host

        self.proxy = proxy
        self.proxy_pool = proxy_pool or []

        self.verify = verify
        self.ca_bundle = ca_bundle

        self._session: Optional[aiohttp.ClientSession] = None
        self._connector: Optional[aiohttp.TCPConnector] = None

        # Fair per-host concurrency limit
        self._host_limiters: Dict[str, asyncio.Semaphore] = {}

        # SSL context initialized in __aenter__
        self._ssl_context: Optional[ssl.SSLContext] = None

    # ------------------------------------------------------------- #
    # Context manager
    # ------------------------------------------------------------- #
    async def __aenter__(self):
        # Build SSL context for HTTPS
        self._ssl_context = self._build_ssl_context()

        self._connector = aiohttp.TCPConnector(
            limit_per_host=self.max_conn_per_host,
            ssl=self._ssl_context,  # applies to HTTPS URLs
        )
        self._session = aiohttp.ClientSession(
            connector=self._connector,
            headers={"User-Agent": self.ua},
        )
        return self

    async def __aexit__(self, exc_type, exc, tb):
        if self._session:
            await self._session.close()
        self._session = None
        self._connector = None
        self._ssl_context = None

    # ------------------------------------------------------------- #
    # SSL / TLS helpers
    # ------------------------------------------------------------- #
    def _build_ssl_context(self) -> Optional[ssl.SSLContext]:
        """
        Build an SSLContext depending on verify + ca_bundle.
        aiohttp will use system defaults if we return None.
        """
        # If we don't want to customize anything, let aiohttp use defaults.
        if self.verify and not self.ca_bundle:
            return None

        # Explicit context
        if self.verify:
            # Verify ON with custom CA bundle (or default if path is None)
            ctx = ssl.create_default_context(
                cafile=self.ca_bundle if self.ca_bundle else None
            )
            # default: verify_mode = CERT_REQUIRED, check_hostname = True
            return ctx

        # verify = False: disable certificate verification (dangerous, but useful behind intercepting proxies)
        ctx = ssl.create_default_context()
        ctx.check_hostname = False
        ctx.verify_mode = ssl.CERT_NONE
        return ctx

    # ------------------------------------------------------------- #
    # Internal helpers
    # ------------------------------------------------------------- #
    def _get_host_semaphore(self, url: str) -> asyncio.Semaphore:
        from urllib.parse import urlparse
        host = urlparse(url).netloc.lower()
        if host not in self._host_limiters:
            self._host_limiters[host] = asyncio.Semaphore(self.max_conn_per_host)
        return self._host_limiters[host]

    def _choose_proxy(self) -> Optional[str]:
        if self.proxy:
            return self.proxy
        if self.proxy_pool:
            import random
            return random.choice(self.proxy_pool)
        return None

    # ------------------------------------------------------------- #
    # Core request with retries + host limit
    # ------------------------------------------------------------- #
    async def _request(self, method: str, url: str, **kwargs):
        if not self._session:
            raise RuntimeError("HTTPSSubmanager must be used in an async context.")

        sem = self._get_host_semaphore(url)
        proxy = self._choose_proxy()

        for attempt in range(self.retries + 1):
            try:
                async with sem:
                    async with self._session.request(
                        method,
                        url,
                        proxy=proxy,
                        timeout=ClientTimeout(total=self.timeout),
                        **kwargs,
                    ) as resp:
                        return resp

            except Exception:
                if attempt >= self.retries:
                    return None
                await asyncio.sleep(self.backoff_base * (1 + attempt))

        return None

    # ------------------------------------------------------------- #
    # Public GET/HEAD helpers
    # ------------------------------------------------------------- #
    async def get_text(self, url: str) -> str:
        """
        GET url and return decoded text ("" on non-200 or error).
        Works for both HTTPS and HTTP URLs; HTTPS uses the SSL context.
        """
        resp = await self._request("GET", url)
        if not resp or resp.status != 200:
            return ""
        try:
            return await resp.text()
        except Exception:
            return ""

    async def get_bytes(self, url: str) -> bytes:
        """
        GET url and return raw bytes (b"" on non-200 or error).
        """
        resp = await self._request("GET", url)
        if not resp or resp.status != 200:
            return b""
        try:
            return await resp.read()
        except Exception:
            return b""

    async def head(self, url: str) -> Tuple[Optional[int], Dict[str, str]]:
        """
        HEAD url and return (status, headers).
        If the server doesn't like HEAD, you'll just get (None, {}).
        """
        resp = await self._request("HEAD", url, allow_redirects=True)
        if not resp:
            return None, {}
        try:
            return resp.status, dict(resp.headers)
        except Exception:
            return resp.status, {}