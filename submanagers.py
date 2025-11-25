from __future__ import annotations

import asyncio
import collections  # For collections.Counter
import re
import sqlite3
import threading
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple, Sequence, Iterable
from urllib.parse import urlparse, urljoin, parse_qsl, urlencode, urlunparse
import random  # For random delays
import json  # For JSON parsing in NetworkSniffer and JSSniffer
import xml.etree.ElementTree as ET


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

    IMPORTANT: Output schema is normalized to legacy style:
      item = {url, text, tag, kind, content_type, size}
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
            "application/dash+xml", "application/vnd.mpeg.dash.mpd"  # Added common DASH type
        })

        deny_content_substrings: Set[str] = field(default_factory=lambda: {
            "javascript", "css", "text/html", "font/"
        })
        deny_resource_types: Set[str] = field(default_factory=lambda: {
            "stylesheet", "font", "manifest", "other"  # Manifest resource type can be too broad for direct asset
        })

        # ------------------ stream hint sets ------------------ #

        video_stream_hints: Set[str] = field(default_factory=lambda: {
            ".m3u8", "manifest.mpd", "master.m3u8", "chunklist.m3u8",
            "videoplayback", "dash", "hls", "stream", "cdn"  # Added generic stream/cdn hints
        })
        audio_stream_hints: Set[str] = field(default_factory=lambda: {
            "audio", "sound", "stream", ".mp3", ".m4a", ".aac", ".flac", ".ogg", ".opus"
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

        # ------------------ json sniff sets ------------------ #

        enable_json_sniff: bool = True
        json_url_hints: Set[str] = field(default_factory=lambda: {
            "player", "manifest", "api", "metadata", "m3u8", "mpd", "playlist", "video", "audio"
        })
        json_content_types: Set[str] = field(default_factory=lambda: {
            "application/json", "text/json"
        })

    def __init__(self, config: Optional["NetworkSniffer.Config"] = None, logger=None):
        self.cfg = config or self.Config()
        self.logger = logger

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

    def _should_sniff_json(self, url_lower: str, ctype: str) -> bool:
        if not self.cfg.enable_json_sniff:
            return False
        ct = (ctype or "").lower()
        if not any(jt in ct for jt in self.cfg.json_content_types) and "/metadata/" not in url_lower:
            return False
        return any(h in url_lower for h in self.cfg.json_url_hints)

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
        """Return 'hls' or 'dash' if this response is a manifest."""
        ul = url.lower()
        ct = (ctype or "").lower()
        if ul.endswith(".m3u8") or ct in self.cfg.hls_types:
            return "hls"
        if ul.endswith(".mpd") or ct in self.cfg.dash_types:
            return "dash"
        return None

    # ------------------ manifest parsing ------------------ #

    # HLS: Matches lines ending with .ts, .mp4, or .m3u8, or generic URLs without #.
    # More robust for actual media segments or sub-playlists.
    _HLS_URL_RE = re.compile(r'(?:\n|^)(?!#EXTINF|#EXT-X-)([^#\s]+\.(?:ts|mp4|m3u8)(?:\?[^#\s]*)?)$',
                             re.MULTILINE | re.IGNORECASE)
    _HLS_GENERIC_URL_RE = re.compile(r'(?:\n|^)(?!#)(https?://[^#\s]+)$',
                                     re.MULTILINE | re.IGNORECASE)  # Fallback for generic URLs

    def _parse_hls_manifest(self, manifest_text: str, base_url: str) -> List[str]:
        out = []
        for m in self._HLS_URL_RE.finditer(manifest_text or ""):
            out.append(_canonicalize_url(urljoin(base_url, m.group(1).strip())))

        # Fallback for more generic URLs if specific ones are not found
        if not out:
            for m in self._HLS_GENERIC_URL_RE.finditer(manifest_text or ""):
                out.append(_canonicalize_url(urljoin(base_url, m.group(1).strip())))

        return out

    # MPD: Looks for media, initialization, sourceURL, and href attributes in XML-like structures.
    _MPD_URL_RE = re.compile(r'(?:media|initialization|sourceURL|href)\s*=\s*["\']([^"\']+)["\']', re.I)

    def _parse_mpd_manifest(self, manifest_text: str, base_url: str) -> List[str]:
        out = []
        # Attempt XML parsing first for more robust extraction
        try:
            root = ET.fromstring(manifest_text)
            for el in root.iter():
                for attr_name in ['media', 'initialization', 'sourceURL', 'href']:
                    if attr_name in el.attrib:
                        u = el.attrib[attr_name].strip()
                        if u:
                            out.append(_canonicalize_url(urljoin(base_url, u)))
            if out:  # If XML parsing found something, use it
                return out
        except Exception:
            # Fallback to regex if XML parsing fails
            pass

        # Fallback regex parsing
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
            if log is not None:
                log.append(f"[Sniffer] Manifest read failed: {url} ({e})")
            return []

        if manifest_kind == "hls":
            derived = self._parse_hls_manifest(txt, url)
        else:  # manifest_kind == "dash"
            derived = self._parse_mpd_manifest(txt, url)

        if log is not None:
            log.append(f"[Sniffer] Expanded {manifest_kind} manifest: {url} -> {len(derived)} derived")

        return derived

    # ------------------ output normalization ------------------ #

    def _normalize_item(self, it: Dict[str, Any]) -> Dict[str, str]:
        """
        Legacy schema output only.
        """
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
            extensions: Optional[Set[str]] = None,  # Target extensions for filtering
    ) -> Tuple[str, List[Dict[str, str]], List[Dict[str, Any]]]:

        if context is None:
            if log is not None:
                log.append("[Sniffer] No Playwright context; skipping sniff.")
            return "", [], []
        if Page is None:  # Ensure Playwright classes are available
            if log is not None:
                log.append("[Sniffer] Playwright classes not found; skipping sniff.")
            return "", [], []

        tmo = float(timeout if timeout is not None else self.cfg.timeout)
        canonical_page_url = _canonicalize_url(page_url)  # Canonicalize page_url itself

        found_items: List[Dict[str, Any]] = []
        json_hits: List[Dict[str, Any]] = []
        derived_items: List[Dict[str, Any]] = []

        seen_network: Set[str] = set()  # Stores canonical URLs
        seen_derived: Set[str] = set()  # Stores canonical URLs

        # Track blob/media placeholders (internal shape, normalized later)
        blob_placeholders: List[Dict[str, Any]] = []

        # Track requests for resource_type to aid blob detection and filtering
        req_types: Dict[str, str] = {}

        page: Page = await context.new_page()

        max_items = int(self.cfg.max_items)
        max_json = int(self.cfg.max_json_hits)
        max_derived_per_manifest = int(self.cfg.max_derived_per_manifest)
        max_manifests = int(self.cfg.max_manifests_to_expand)

        manifests_to_expand: List[Tuple[Response, str, str]] = []  # (resp, kind, url)

        if log is not None:
            log.append(f"[Sniffer] Start sniff: {canonical_page_url} (timeout={tmo}s)")

        # -------- request tracking (helps blob recovery & resource type filtering) -------- #
        def handle_request(req: Request):
            try:
                # Store original URL (not canonicalized yet) -> resource_type
                # Canonicalization happens at response time for consistency
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
                if log is not None:
                    log.append(f"[Sniffer] Failed to parse JSON from {url}: {e}")

        def handle_response(response: Response):
            try:
                url = response.url
                canonical_url = _canonicalize_url(url)  # Canonicalize response URL early

                if not canonical_url or canonical_url in seen_network:
                    return

                # Check for blob URLs first as they don't have typical netloc/path
                is_blob = canonical_url.startswith("blob:")

                # Get resource type from request (using original URL)
                # This helps filter out unwanted types like stylesheets/fonts even if ctype is ambiguous
                resource_type = req_types.get(url, "")  # Use original URL for req_types lookup

                if not is_blob:
                    parsed = urlparse(canonical_url)
                    path = (parsed.path or "/").lower()
                    netloc = parsed.netloc or ""
                    url_lower = canonical_url.lower()

                    if self._is_junk_by_extension(path):
                        if log is not None: log.append(f"[Sniffer] Skipped junk ext: {canonical_url}")
                        return
                    if self._looks_like_ad(netloc, path):
                        if log is not None: log.append(f"[Sniffer] Skipped ad: {canonical_url}")
                        return

                seen_network.add(canonical_url)  # Mark canonical URL as seen

                ctype = (response.headers.get("content-type") or "").lower()
                url_lower = canonical_url.lower()

                if (not is_blob) and ctype and self._deny_by_content_type(ctype):
                    if log is not None: log.append(f"[Sniffer] Skipped denied ctype: {canonical_url} ({ctype})")
                    return

                if (not is_blob) and resource_type and self._deny_by_resource_type(resource_type):
                    if log is not None: log.append(f"[Sniffer] Skipped denied rtype: {canonical_url} ({resource_type})")
                    return

                if (not is_blob) and self._should_sniff_json(url_lower, ctype):
                    asyncio.create_task(handle_json(response, canonical_url))
                    return

                # --------- blob media placeholder detection --------- #
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
                        # Add a JSON hit for context
                        if len(json_hits) < max_json:
                            json_hits.append({
                                "url": canonical_url,
                                "json": {"blob_media": canonical_url, "reason": "blob-media-detected"},
                                "source_page": canonical_page_url
                            })
                    return  # Blobs are handled, no further classification

                parsed = urlparse(canonical_url)
                path = (parsed.path or "/").lower()

                kind = (
                        self._classify_by_extension(path)
                        or (self._classify_by_content_type(ctype) if ctype else None)
                        or self._classify_by_stream_hint(url_lower)
                )
                if not kind:
                    if log is not None: log.append(f"[Sniffer] Skipped unknown kind: {canonical_url}")
                    return

                if not self._is_allowed_by_extensions(canonical_url, extensions, kind):
                    if log is not None: log.append(f"[Sniffer] Skipped by extensions: {canonical_url} (kind={kind})")
                    return

                mkind = self._is_manifest(canonical_url, ctype)
                if mkind and kind == "video" and len(manifests_to_expand) < max_manifests:
                    manifests_to_expand.append((response, mkind, canonical_url))
                    if log is not None: log.append(f"[Sniffer] Identified manifest: {canonical_url} (kind={mkind})")

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
                if log is not None: log.append(f"[Sniffer] Added item: {canonical_url} (kind={kind})")

            except Exception as e:
                # Log specific errors within handle_response for debugging
                if log is not None:
                    log.append(f"[Sniffer][handle_response] Error processing {response.url}: {e}")
                if self.logger:
                    self.logger.log_message(f"[Sniffer][handle_response] Error processing {response.url}: {e}")
                return

        page.on("response", handle_response)

        sniff_goto_timeout = max(15000, int(tmo * 1000))
        try:
            await page.goto(canonical_page_url, wait_until="domcontentloaded", timeout=sniff_goto_timeout)
        except Exception as e:
            if log is not None:
                log.append(f"[Sniffer] goto timeout on {canonical_page_url}: {e}")
            if self.logger:
                self.logger.log_message(f"[Sniffer] goto timeout on {canonical_page_url}: {e}")

        await page.wait_for_timeout(int(tmo * 1000))

        # --------- expand manifests AFTER wait --------- #
        if manifests_to_expand:
            if log is not None: log.append(f"[Sniffer] Expanding {len(manifests_to_expand)} manifests...")

            async def expand_one(resp: Response, mkind: str, murl: str):
                derived_urls = await self._expand_manifest(resp, mkind, murl, log)
                if not derived_urls:
                    return

                for u in derived_urls[:max_derived_per_manifest]:
                    if u in seen_derived or u in seen_network:
                        continue
                    seen_derived.add(u)

                    dk = self._classify_by_extension(
                        urlparse(u).path or "") or "video"  # Assume video for manifest segments
                    if not self._is_allowed_by_extensions(u, extensions, dk):
                        if log is not None: log.append(f"[Sniffer] Derived skipped by extensions: {u} (kind={dk})")
                        continue

                    derived_items.append({
                        "url": u,
                        "text": f"[Network {dk.capitalize()} Segment]",  # More specific label
                        "tag": "network_sniff",
                        "kind": dk,
                        "content_type": mkind,
                        "size": "?",
                    })
                    if log is not None: log.append(f"[Sniffer] Added derived item: {u} (kind={dk})")

                    if len(json_hits) < max_json:
                        json_hits.append({
                            "url": u,
                            "json": {"derived_from": murl, "manifest_type": mkind},
                            "source_page": canonical_page_url
                        })

            await asyncio.gather(*[
                expand_one(resp, mkind, murl) for (resp, mkind, murl) in manifests_to_expand
            ])
            if log is not None: log.append(
                f"[Sniffer] Finished manifest expansion. Total derived: {len(derived_items)}")

        try:
            html = await page.content()
        except Exception as e:
            if log is not None: log.append(f"[Sniffer] Failed to get page content: {e}")
            html = ""

        try:
            await page.close()
        except Exception as e:
            if log is not None: log.append(f"[Sniffer] Failed to close page: {e}")

        merged_items_any = found_items + derived_items + blob_placeholders
        merged_items = [self._normalize_item(it) for it in merged_items_any if it.get("url")]

        if log is not None:
            log.append(
                f"[Sniffer] Finished sniff for {canonical_page_url}: "
                f"media={len(found_items)} derived={len(derived_items)} blob={len(blob_placeholders)} "
                f"json_hits={len(json_hits)} (Total output: {len(merged_items)})"
            )

        if self.logger:
            self.logger.log_message(
                f"[Sniffer] Finished {canonical_page_url}. "
                f"media={len(found_items)} derived={len(derived_items)} blob={len(blob_placeholders)} "
                f"json_hits={len(json_hits)} (Total output: {len(merged_items)})"
            )

        return html, merged_items, json_hits


# ======================================================================
# JSSniffer
# ======================================================================

class JSSniffer:
    """
    Shared-context Playwright JS DOM link sniffer.

    Keeps original behavior:
      - extension filtering
      - optional shadow DOM walking
      - logging
      - same sniff() signature you’re calling

    Adds hijack-detection upgrades:
      ✔ JS event listener detection (incl. shadow DOM) (inline only for now)
      ✔ data-* attribute extraction (specific + generic url-ish)
      ✔ script-tag JSON scanning for URLs/manifests
      ✔ onclick pattern extraction
      ✔ redirect detection
      ✔ shadow DOM listener scanning
      ✔ optional safe click simulation fallback
      ✔ In-browser URL resolution for robustness.

    IMPORTANT: Output schema is normalized to legacy JS-link style:
      link = {url, text, tag}
    """

    @dataclass
    class Config:
        timeout: float = 8.0
        max_links: int = 500
        wait_after_goto_ms: int = 500  # Added small default wait
        include_shadow_dom: bool = True

        selectors: List[str] = field(default_factory=lambda: [
            "a[href]",
            "video[src]",
            "video source[src]",
            "source[src]",
            "audio[src]",  # Added audio
            "audio source[src]",  # Added audio source
            "img[src]",  # Added images
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
            "data-audio", "data-audio-url", "data-image", "data-poster", "data-media-url"  # Added generic
        })

        onclick_url_regexes: List[str] = field(default_factory=lambda: [
            r"""['"]((?:https?:)?//[^'"]+)['"]""",  # Generic URL in quotes
            r"""location\.href\s*=\s*['"]([^'"]+)['"]""",
            r"""window\.open\(\s*['"]([^'"]+)['"]""",
            r"""window\.location\.assign\(\s*['"]([^'"]+)['"]\)""",
            r"""window\.location\.replace\(\s*['"]([^'"]+)['"]\)""",
            r"""decodeURIComponent\s*\(\s*['"]([^'"]+)['"]\)""",  # Handle encoded URLs
        ])

        redirect_hints: Set[str] = field(default_factory=lambda: {
            "location.href", "window.location", "window.open", "document.location",
            "location.replace", "location.assign", "navigate", "redirect"  # Added more keywords
        })

        script_json_hints: Set[str] = field(default_factory=lambda: {
            "url", "src", "file", "video", "audio", "stream", "manifest",
            "m3u8", "mpd", "playlist", "dash", "hls", "media"  # Added more keywords
        })

        enable_click_simulation: bool = False
        max_click_targets: int = 6
        click_timeout_ms: int = 2500
        click_target_selectors: List[str] = field(default_factory=lambda: [
            "a[href]", "button", "[role=button]", "[onclick]",
            "div[role=link]", "span[role=link]"  # Added more interactive elements
        ])

    def __init__(self, config: Optional["JSSniffer.Config"] = None, logger=None):
        self.cfg = config or self.Config()
        self.logger = logger

    # ------------------------- helpers ------------------------- #

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

        if kind in ("video", "audio"):  # Broadly accept video/audio if no specific extensions
            return True

        return False

    def _abs_url_js(self, base: str, u: str) -> str:
        # This function is now primarily for Python-side fallback,
        # as JS side will do the resolution.
        try:
            return urljoin(base, u)
        except Exception:
            return u

    def _normalize_link(self, url: str, text: str, tag: str) -> Dict[str, str]:
        return {
            "url": url,  # Canonicalized later in VideoLinkTrackerBlock
            "text": text or "",
            "tag": tag or "a",
        }

    # ------------------------- main sniff ------------------------- #

    async def sniff(
            self,
            context: BrowserContext,
            page_url: str,
            *,
            timeout: Optional[float] = None,
            log: Optional[List[str]] = None,
            extensions: Optional[Set[str]] = None,  # Target extensions for filtering
    ) -> Tuple[str, List[Dict[str, str]]]:

        if context is None:
            if log is not None:
                log.append("[JSSniffer] No Playwright context; skipping JS sniff.")
            return "", []
        if Page is None:  # Ensure Playwright classes are available
            if log is not None:
                log.append("[JSSniffer] Playwright classes not found; skipping JS sniff.")
            return "", []

        tmo = float(timeout if timeout is not None else self.cfg.timeout)
        canonical_page_url = _canonicalize_url(page_url)  # Canonicalize page_url itself

        html = ""
        links: List[Dict[str, str]] = []
        seen_urls_in_js: Set[str] = set()  # Tracks URLs resolved IN JAVASCRIPT

        page: Page = await context.new_page()
        js_timeout_ms = int(max(tmo, 10.0) * 1000)
        wait_after_ms = int(self.cfg.wait_after_goto_ms)

        selector_js = ", ".join(self.cfg.selectors)
        include_shadow = "true" if self.cfg.include_shadow_dom else "false"
        data_keys_js = list(self.cfg.data_url_keys)
        onclick_regexes_js = [r.replace("\\", "\\\\") for r in self.cfg.onclick_url_regexes]  # Escape for JS
        redirect_hints_js = list(self.cfg.redirect_hints)
        script_json_hints_js = list(self.cfg.script_json_hints)

        if log is not None:
            log.append(f"[JSSniffer] Start: {canonical_page_url} timeout={tmo}s")

        try:
            await page.goto(canonical_page_url, wait_until="domcontentloaded", timeout=js_timeout_ms)
            if wait_after_ms > 0:
                await page.wait_for_timeout(wait_after_ms)

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
                  const seen = new Set(); // Stores absolute, resolved URLs

                  function absUrl(u) {
                    if (!u) return "";
                    try {
                      return new URL(u, baseUrl).href;
                    } catch {
                      return u; // Return original if resolution fails
                    }
                  }

                  function push(el, url, tag, reason=null) {
                    url = absUrl(String(url).trim()); // Resolve absolute URL
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
                    for (const attr of el.attributes || []) {
                      const n = attr.name.toLowerCase();
                      const v = attr.value;
                      // Generic data- attribute with a URL-like value
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
                      } catch (e) {
                        // console.error("Regex error:", e);
                      }
                    }
                    const ocl = oc.toLowerCase();
                    for (const h of redirectHints) {
                      if (ocl.includes(h)) {
                        // For redirect hints, try to extract any URL from the onclick string itself
                        const urlMatch = ocl.match(/(https?:)?\\/\\/[^\\s'"]+/);
                        if (urlMatch) {
                            push(el, urlMatch[0], el.tagName.toLowerCase(), "redirect-hint-url");
                        } else {
                            // If no specific URL, record the onclick content as a hint
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
                        // Attempt to extract URLs from the inline script, similar to onclick
                        for (const rx of onclickRegexes) {
                            try {
                                const r = new RegExp(rx, "ig");
                                let m;
                                while ((m = r.exec(v)) !== null) {
                                    if (m[1]) push(el, m[1], el.tagName.toLowerCase(), `inline-listener-${k}`);
                                }
                            } catch {}
                        }
                        // push(el, v, el.tagName.toLowerCase(), `inline-listener-${k}`); // Option to record raw script
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
                      sniffInlineListeners(el); // Check for inline listeners
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

                      // Extract raw URLs from script text
                      const urls = txt.match(/(https?:)?\\/\\/[^\\s'"]{6,}/ig) || [];
                      for (const u of urls) push(s, u, "script", "script-raw-url");

                      // Attempt JSON parsing if text looks like JSON
                      if (txt.startsWith("{") || txt.startsWith("[")) {
                        try {
                          const data = JSON.parse(txt);
                          const stack = [data];
                          const visitedObjects = new WeakSet(); // Prevent circular references
                          while (stack.length) {
                            const cur = stack.pop();
                            if (!cur || typeof cur !== "object" || visitedObjects.has(cur)) continue;
                            visitedObjects.add(cur);

                            if (typeof cur === "string") { // Handle string values that might be URLs
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
                                // If key is a hint, and value is a string, push it
                                if (scriptJsonHints.some(h => kl.includes(h))) {
                                  if (typeof v === "string") push(s, v, "script", "script-json-key");
                                }
                                stack.push(v); // Push value for further recursive scanning
                              }
                            }
                          }
                        } catch (e) {
                          // console.error("JSON parse error in script:", e);
                        }
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
                    "baseUrl": canonical_page_url  # Pass base URL for in-JS resolution
                }
            ) or {}

            raw_links = raw_payload.get("items") or []
            if log is not None: log.append(f"[JSSniffer] Raw links from DOM/scripts: {len(raw_links)}")

            # ------------------------------------------------------------
            # Optional safe click simulation (limited)
            # ------------------------------------------------------------
            if self.cfg.enable_click_simulation:
                if log is not None: log.append(f"[JSSniffer] Starting click simulation...")
                try:
                    click_sel = ", ".join(self.cfg.click_target_selectors)
                    handles = await page.query_selector_all(click_sel)
                    handles = handles[: int(self.cfg.max_click_targets)]
                    if log is not None: log.append(f"[JSSniffer] Found {len(handles)} click targets.")

                    for h_idx, h in enumerate(handles):
                        try:
                            # Use evaluate to get element properties to filter before clicking
                            el_info = await h.evaluate("""el => ({
                                tagName: el.tagName.toLowerCase(),
                                hasHref: !!el.href,
                                hasSrc: !!el.src,
                                innerText: el.innerText,
                                isVisible: el.offsetParent !== null
                            })""")

                            # Skip invisible elements or those likely to just navigate away immediately
                            if not el_info['isVisible'] or el_info['tagName'] == 'a' and el_info['hasHref']:
                                if log is not None: log.append(
                                    f"[JSSniffer] Skipping click on {el_info['tagName']} (visible={el_info['isVisible']}, hasHref={el_info['hasHref']}).")
                                continue

                            if log is not None: log.append(f"[JSSniffer] Clicking target {h_idx + 1}/{len(handles)}...")
                            await h.scroll_into_view_if_needed(timeout=1000)
                            await h.click(timeout=int(self.cfg.click_timeout_ms))
                            await page.wait_for_timeout(300)  # Give some time for JS to react

                            # Re-scan for new links after click
                            click_raw = await page.evaluate(
                                """
                                (baseUrl) => {
                                  const out = [];
                                  const seen = new Set(); // Local seen for this click scan
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
                                canonical_page_url  # Pass base URL for in-JS resolution
                            ) or []
                            for it in click_raw:
                                raw_links.append({
                                    "url": it.get("url"),  # Already absolute and resolved in JS
                                    "text": "",
                                    "tag": it.get("tag") or "a",
                                    "reason": "click-sim"
                                })
                            if log is not None: log.append(
                                f"[JSSniffer] Click {h_idx + 1} yielded {len(click_raw)} new links.")

                        except Exception as click_e:
                            if log is not None:
                                log.append(f"[JSSniffer] Error during click sim for target {h_idx + 1}: {click_e}")
                            continue
                except Exception as e:
                    if log is not None:
                        log.append(f"[JSSniffer] Overall click-sim error: {e}")

            # ------------------------------------------------------------
            # Filter + enforce limits + normalize legacy output
            # ------------------------------------------------------------
            max_links = int(self.cfg.max_links)

            for item in raw_links:
                if len(links) >= max_links:
                    break

                url = (item.get("url") or "").strip()  # This URL is ALREADY absolute and resolved from JS
                if not url:
                    continue

                # The `seen_urls_in_js` set (from `page.evaluate`) helps with initial filtering
                # but we need a Python-side `seen` set for canonicalized URLs from different sources
                canonical_url_py = _canonicalize_url(url)
                if canonical_url_py in seen_urls_in_js:  # Re-use the JS-side seen for efficiency
                    continue
                seen_urls_in_js.add(canonical_url_py)  # Add canonical URL to the Python-side seen set

                if self._is_junk_url(url):  # Check against junk prefixes (e.g., blob:, javascript:)
                    if log is not None: log.append(f"[JSSniffer] Skipped junk URL: {url}")
                    continue

                kind = self._classify_kind(url)
                if not self._is_allowed_by_extensions(url, extensions, kind):
                    if log is not None: log.append(f"[JSSniffer] Skipped by extensions: {url} (kind={kind})")
                    continue

                # legacy JS-link shape ONLY (URL is already canonicalized by this point)
                links.append(self._normalize_link(
                    url=canonical_url_py,  # Use the canonicalized URL for output
                    text=(item.get("text") or "").strip(),
                    tag=(item.get("tag") or "a"),
                ))
                if log is not None: log.append(f"[JSSniffer] Added JS item: {canonical_url_py}")

            if log is not None:
                log.append(f"[JSSniffer] Done: {len(links)} links for {canonical_page_url}")

        except Exception as e:
            if log is not None:
                log.append(f"[JSSniffer] Overall error on {canonical_page_url}: {e}")
            if self.logger:
                self.logger.log_message(f"[JSSniffer] Overall error on {canonical_page_url}: {e}")

        try:
            await page.close()
        except Exception as e:
            if log is not None: log.append(f"[JSSniffer] Failed to close page: {e}")

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


