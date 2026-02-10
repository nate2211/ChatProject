# ========================================================
# ================  blocks.py  ===========================
# ========================================================
from __future__ import annotations

import ast
import asyncio
import collections
import fnmatch
import functools
import gzip
import hashlib
import html
import json
import os
import re
import sqlite3
import sys
import threading
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
import random
from typing import Any, Dict, Tuple, List, Optional, Set
import json as _json
import os as _os
import time
from urllib.parse import urlencode, urlparse, urljoin, unquote, quote_plus, parse_qsl, urlunparse, quote

import aiohttp
import feedparser
import numpy as np
import requests
from bs4 import BeautifulSoup
from camoufox import AsyncCamoufox
from playwright.async_api import async_playwright, Page, Response
from playwright.sync_api import BrowserContext
from registry import BLOCKS
from models import get_chat_model  # <-- models now live separately
import xml.etree.ElementTree as ET
import re as _re
from dotenv import load_dotenv
from PIL import Image
import submanagers
from stores import LinkTrackerStore, VideoTrackerStore, CorpusStore, WebCorpusStore, PlaywrightCorpusStore, \
    CodeCorpusStore, PageTrackerStore, LinkCrawlerStore, LinkContentCrawlerStore, CDNStore, DirectLinkTrackerStore
from loggers import DEBUG_LOGGER

load_dotenv()
# ---------------- Paths & helpers ----------------
APP_DIR = _os.path.join(_os.path.expanduser("~"), ".promptchat")
MEMORY_PATH = _os.path.join(APP_DIR, "memory.json")
HISTORY_PATH = _os.path.join(APP_DIR, "history.json")


def ensure_app_dirs() -> None:
    _os.makedirs(APP_DIR, exist_ok=True)
    for p in (MEMORY_PATH, HISTORY_PATH):
        if not _os.path.exists(p):
            with open(p, "w", encoding="utf-8") as f:
                f.write("{}")


def parse_extras(items: List[str]) -> Dict[str, Dict[str, Any]]:
    def _coerce(v: str) -> Any:
        s = v.strip()
        low = s.lower()
        if low in ("true", "false"):
            return low == "true"
        try:
            if s.isdigit():
                return int(s)
            return float(s)
        except Exception:
            pass
        if (s.startswith("'") and s.endswith("'")) or (s.startswith('"') and s.endswith('"')):
            return s[1:-1]
        if (s.startswith("{") and s.endswith("}")) or (s.startswith("[") and s.endswith("]")):
            try:
                return _json.loads(s)
            except Exception:
                return s
        return s

    out: Dict[str, Dict[str, Any]] = {}
    for item in items:
        if "=" not in item:
            continue
        k, v = item.split("=", 1)
        if "." in k:
            group, key = k.split(".", 1)
        else:
            group, key = "all", k
        group = group.strip().lower()
        key = key.strip()
        out.setdefault(group, {})[key] = _coerce(v)
    return out


# ======================= Utilities =========================================
_UA = (
    "Mozilla/5.0 (X11; Linux x86_64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/122.0 Safari/537.36"
)


def _http_get(url: str, *, timeout: float = 12.0, headers: Optional[Dict[str, str]] = None) -> requests.Response:
    h = {"User-Agent": _UA, "Accept": "*/*"}
    if headers:
        h.update(headers)
    resp = requests.get(url, timeout=timeout, headers=h)
    resp.raise_for_status()
    return resp


def _is_json_content(resp: requests.Response) -> bool:
    ctype = (resp.headers.get("Content-Type") or "").lower()
    return "application/json" in ctype or resp.text.strip().startswith("{") or resp.text.strip().startswith("[")


def _safe_json(resp: requests.Response) -> Any:
    try:
        return resp.json()
    except Exception:
        return json.loads(resp.text)


def _markdown_list(items: List[Dict[str, Any]], title_key="title", url_key="link",
                   extra_keys: Optional[List[str]] = None, limit: int = 10) -> str:
    out = []
    for row in items[:limit]:
        title = row.get(title_key) or row.get("name") or row.get("headline") or "(no title)"
        link = row.get(url_key) or row.get("url") or row.get("href") or ""
        extra = []
        if extra_keys:
            for k in extra_keys:
                v = row.get(k)
                if v:
                    if isinstance(v, (dict, list)):
                        v = json.dumps(v, ensure_ascii=False)[:240] + "…" if len(json.dumps(v)) > 240 else json.dumps(v,
                                                                                                                      ensure_ascii=False)
                    extra.append(f"_{k}:_ {v}")
        title = html.escape(str(title))
        if link:
            out.append(f"- [{title}]({link})" + (f" — {' • '.join(extra)}" if extra else ""))
        else:
            out.append(f"- {title}" + (f" — {' • '.join(extra)}" if extra else ""))
    return "\n".join(out) if out else "_(no items)_"


def _fallback_parse_rss(xml_text: str, *, limit: int = 10) -> List[Dict[str, Any]]:
    # Very small RSS/Atom fallback (title + link + published)
    items: List[Dict[str, Any]] = []
    try:
        root = ET.fromstring(xml_text)
    except Exception:
        return items
    ns = {"atom": "http://www.w3.org/2005/Atom"}
    # Atom entries
    for e in root.findall(".//atom:entry", ns):
        title = (e.findtext("atom:title", default="", namespaces=ns) or "").strip()
        link_el = e.find("atom:link", ns)
        href = link_el.get("href") if link_el is not None else ""
        pub = (e.findtext("atom:updated", default="", namespaces=ns) or "").strip()
        if title or href:
            items.append({"title": title, "link": href, "published": pub})
    # RSS items
    for i in root.findall(".//item"):
        title = (i.findtext("title") or "").strip()
        link = (i.findtext("link") or "").strip()
        pub = (i.findtext("pubDate") or "").strip()
        if title or link:
            items.append({"title": title, "link": link, "published": pub})
    return items[:limit]


def _parse_feed(url: str, *, limit: int = 10) -> List[Dict[str, Any]]:
    """Parse RSS/Atom using feedparser if available, else tiny fallback."""
    if feedparser is not None:
        d = feedparser.parse(url)
        out = []
        for e in d.entries[:limit]:
            out.append({
                "title": getattr(e, "title", ""),
                "link": getattr(e, "link", ""),
                "published": getattr(e, "published", getattr(e, "updated", "")),
                "summary": getattr(e, "summary", ""),
            })
        return out
    # Fallback: fetch and parse minimal
    resp = _http_get(url)
    return _fallback_parse_rss(resp.text, limit=limit)


def _extract_first_img_src(html_text: str) -> Optional[str]:
    # very light heuristic for <img src="..."> (used for APOD page)
    m = re.search(r'<img[^>]+src=["\']([^"\']+)["\']', html_text, flags=re.IGNORECASE)
    return m.group(1) if m else None


# ======================= Presets ===========================================
NEWS_PRESETS: Dict[str, str] = {
    # RSS/Atom
    "bbc_world": "http://feeds.bbci.co.uk/news/world/rss.xml",
    "npr_news": "https://feeds.npr.org/1001/rss.xml",
    "nyt_tech": "https://rss.nytimes.com/services/xml/rss/nyt/Technology.xml",
    "ars_index": "https://feeds.arstechnica.com/arstechnica/index",
    # JSON
    "spaceflight_news": "https://api.spaceflightnewsapi.net/v3/articles",
    "wikipedia_python": "https://en.wikipedia.org/api/rest_v1/page/summary/Python_(programming_language)",
    # Meteo (set your coords via params)
    # "open_meteo_custom": "https://api.open-meteo.com/v1/forecast?latitude=35&longitude=139&current_weather=true",
}

NASA_PRESETS: Dict[str, str] = {
    "nasa_breaking": "https://www.nasa.gov/rss/dyn/breaking_news.rss",
    "nasa_image_of_the_day": "https://www.nasa.gov/rss/dyn/lg_image_of_the_day.rss",
    # APOD HTML page (no key) — we’ll scrape a first image + caption
    "apod_html": "https://apod.nasa.gov/apod/astropix.html",
    # NASA Images API (JSON) — use with q param in execute
    "nasa_images_api": "https://images-api.nasa.gov/search",
}

_FENCE_RE = _re.compile(
    r"""
    ^```[ \t]*([A-Za-z0-9_\-\+\.]*)[ \t]*\n   # opening fence with optional lang
    (.*?)                                      # code body (non-greedy)
    \n```[ \t]*$                               # closing fence
    """,
    _re.MULTILINE | _re.DOTALL | _re.VERBOSE
)

_IDENT_RE = _re.compile(
    r"""
    (?:
      [A-Za-z_][A-Za-z0-9_]* # snake/UPPER/mixed
      (?:\.[A-Za-z_][A-Za-z0-9_]*)* # dotted api.name
    )
    |
    (?:
      [A-Za-z][a-z0-9]+(?:[A-Z][a-z0-9]+)+   # camelCase/PascalCase
    )
    |
    (?:
      [a-z0-9]+(?:-[a-z0-9]+)+               # kebab-case
    )
    """,
    _re.VERBOSE
)


def _extract_prose_terms(text: str, *, top_k: int = 50, min_len: int = 4) -> List[str]:
    """Extracts common terms from prose, ignoring stopwords."""
    counts: Dict[str, int] = {}
    for raw in text.split():
        w = "".join(ch.lower() for ch in raw if ch.isalnum() or ch in "-_")
        if not w or len(w) < min_len or w in _STOPWORDS:
            continue
        counts[w] = counts.get(w, 0) + 1
    terms = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
    return [t for t, _ in terms[:top_k]]


def _extract_code_identifiers(text: str, *, top_k: int = 100, min_len: int = 3) -> List[str]:
    """Extracts API names, function names, and identifiers from code."""
    ids = _IDENT_RE.findall(text or "")
    counts: Dict[str, int] = {}
    for s in ids:
        tok = s.strip().strip(".")
        if len(tok) < min_len:
            continue
        low = tok.lower()
        if low in _STOPWORDS:
            continue
        counts[tok] = counts.get(tok, 0) + 1
    # Rank by frequency
    ranked = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
    return [t for t, _ in ranked[:top_k]]


# ---------------- Caching for local ML models ----------------
@functools.lru_cache(maxsize=4)
def _get_hf_pipeline(task: str, model: str | None = None, *, device: str | int = "auto", verbose: bool = False):
    """
    Cached loader for Hugging Face pipelines.
    This is kept outside the block to ensure the cache is shared.
    Supports auto-selecting device (GPU/CPU).
    """
    try:
        import os
        os.environ.setdefault("TRANSFORMERS_NO_TF", "1")
        from transformers import pipeline
        import torch
    except ImportError:
        print(
            "[_get_hf_pipeline] ERROR: `transformers` or `torch` not installed. Please `pip install transformers torch`")
        return None

    resolved_device: int = -1  # Default to CPU
    if device == "auto":
        if torch.cuda.is_available():
            resolved_device = 0  # Use first GPU
    elif isinstance(device, int):
        resolved_device = device
    elif device == "cpu":
        resolved_device = -1

    if verbose:
        dev_str = f"cuda:{resolved_device}" if resolved_device >= 0 else "cpu"
        print(
            f"[_get_hf_pipeline] Loading pipeline: task={task}, model={model or 'default'}, device={dev_str}... (this may take a moment on first run)")

    try:
        from transformers import pipeline
        p = pipeline(task=task, model=model, device=resolved_device, framework="pt")
        if verbose:
            print(f"[_get_hf_pipeline] Pipeline loaded on device: {p.device}")
        return p
    except Exception as e:
        print(f"[_get_hf_pipeline] ERROR: Failed to load pipeline (task={task}, model={model}): {e}")
        return None


# ---------------- Base class ----------------
@dataclass
class BaseBlock:
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[Any, Dict[str, Any]]:
        raise NotImplementedError

    def get_params_info(self) -> Dict[str, Any]:
        """Returns a dictionary of default parameters for the GUI."""
        return {}

    # [NEW] Generic helper to run a sub-block pipeline on a value
    def run_sub_pipeline(
            self,
            initial_value: Any,
            pipeline_param_name: str,
            parent_params: Dict[str, Any],
            collect: bool = False,
    ) -> Any:
        """
        Runs a mini-pipeline of sub-blocks on a value.

        Args:
            initial_value: The starting value (e.g., a query string).
            pipeline_param_name: The key in 'parent_params' that holds the list/string of
                                 sub-blocks (e.g., "subpipeline").
            parent_params: The main block's 'params' dict.
            collect: If True, return a rich dict with per-block outputs and
                     classified queries/urls. If False, return only the final
                     value (backwards-compatible behavior).

        Returns:
            If collect is False (default):
                The final, processed value from the last sub-block.
            If collect is True:
                {
                  "__subpipeline__": True,
                  "final": <final_value>,
                  "by_block": { "<block_name>": <output>, ... },
                  "queries": [ ... ],  # deduped list of query-like strings
                  "urls":    [ ... ],  # deduped list of http(s) URLs
                }
        """
        from registry import SUB_BLOCKS
        import subblocks  # noqa: F401
        import sys

        pipeline_def = parent_params.get(pipeline_param_name, None)

        if pipeline_def is None:
            # Nothing configured, just return the input
            if not collect:
                return initial_value
            return {
                "__subpipeline__": True,
                "final": initial_value,
                "by_block": {},
                "queries": [],
                "urls": [],
            }

        if isinstance(pipeline_def, str):
            sub_block_names = [s.strip() for s in pipeline_def.split("|") if s.strip()]
        elif isinstance(pipeline_def, list):
            sub_block_names = [str(s) for s in pipeline_def]
        else:
            sub_block_names = []

        if not sub_block_names:
            if not collect:
                return initial_value
            return {
                "__subpipeline__": True,
                "final": initial_value,
                "by_block": {},
                "queries": [],
                "urls": [],
            }

        current_value = initial_value

        # --- helpers used only when collect=True -------------------------
        def _looks_like_url_list(values: list[Any]) -> bool:
            first_non_empty = None
            for v in values:
                s = str(v).strip()
                if s:
                    first_non_empty = s
                    break
            if not first_non_empty:
                return False
            return first_non_empty.startswith("http://") or first_non_empty.startswith("https://")

        def _dedupe(seq: list[str]) -> list[str]:
            out = []
            seen = set()
            for s in seq:
                if s not in seen:
                    seen.add(s)
                    out.append(s)
            return out

        by_block: Dict[str, Any] = {}
        all_queries: list[str] = []
        all_urls: list[str] = []

        # -----------------------------------------------------------------
        for sub_block_name in sub_block_names:
            try:
                # Collect params for this sub-block (prefix syntax: subblock.param=value)
                sub_params: Dict[str, Any] = {}
                prefix = f"{sub_block_name}."
                for k, v in parent_params.items():
                    if k.startswith(prefix):
                        sub_params[k[len(prefix):]] = v

                sub_block_inst = SUB_BLOCKS.create(sub_block_name)
                output = sub_block_inst.execute(current_value, params=sub_params)

                # Always update the streaming value
                current_value = output

                if collect:
                    # Record raw output
                    by_block[sub_block_name] = output

                    # Classify outputs into queries vs URLs
                    if isinstance(output, list):
                        # List of "something": queries or URL list
                        items = [str(x).strip() for x in output if str(x).strip()]
                        if not items:
                            continue

                        if _looks_like_url_list(items):
                            # Treat as URL list
                            for u in items:
                                if u.startswith("http://") or u.startswith("https://"):
                                    all_urls.append(u)
                        else:
                            # Treat as query-ish strings
                            all_queries.extend(items)

                    elif isinstance(output, str):
                        s = output.strip()
                        if not s:
                            pass
                        elif s.startswith("http://") or s.startswith("https://"):
                            all_urls.append(s)
                        else:
                            all_queries.append(s)

            except Exception as e:
                print(f"[BaseBlock] Sub-pipeline failed at '{sub_block_name}': {e}", file=sys.stderr)
                # Stop the sub-pipeline, but keep the last good value
                if not collect:
                    return current_value
                return {
                    "__subpipeline__": True,
                    "final": current_value,
                    "by_block": by_block,
                    "queries": _dedupe(all_queries),
                    "urls": _dedupe(all_urls),
                }

        if not collect:
            # Old behavior
            return current_value

        # Rich bundle for multi-block pipelines
        return {
            "__subpipeline__": True,
            "final": current_value,
            "by_block": by_block,
            "queries": _dedupe(all_queries),
            "urls": _dedupe(all_urls),
        }


# ---------------- Memory & History stores ----------------
class Memory:
    @staticmethod
    def load() -> Dict[str, Any]:
        try:
            with open(MEMORY_PATH, "r", encoding="utf-8") as f:
                return _json.load(f)
        except Exception:
            return {}

    @staticmethod
    def save(data: Dict[str, Any]) -> None:
        with open(MEMORY_PATH, "w", encoding="utf-8") as f:
            _json.dump(data, f, indent=2, ensure_ascii=False)


class HistoryStore:
    @staticmethod
    def load() -> List[Dict[str, str]]:
        try:
            with open(HISTORY_PATH, "r", encoding="utf-8") as f:
                obj = _json.load(f)
            msgs = obj.get("messages", [])
            return [m for m in msgs if isinstance(m, dict) and "role" in m and "content" in m]
        except Exception:
            return []

    @staticmethod
    def save(messages: List[Dict[str, str]]) -> None:
        with open(HISTORY_PATH, "w", encoding="utf-8") as f:
            _json.dump({"messages": messages[-200:]}, f, indent=2, ensure_ascii=False)

    @staticmethod
    def append(msg: Dict[str, str]) -> None:
        msgs = HistoryStore.load()
        msgs.append(msg)
        HistoryStore.save(msgs)


# ---------------- Guard ----------------
@dataclass
class GuardBlock(BaseBlock):
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        blocked = params.get("blocked", [])
        if isinstance(blocked, str):
            blocked = [blocked]
        repl = str(params.get("replacement", "[redacted]"))
        text = str(payload)
        for b in blocked or []:
            text = text.replace(b, repl)
        return text, {"blocked": len(blocked or [])}

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "blocked": "word1,word2",
            "replacement": "[redacted]"
        }


BLOCKS.register("guard", GuardBlock)


# ---------------- Tools (calc/time) ----------------
def _safe_eval_expr(expr: str) -> float:
    allowed = set("0123456789.+-*/() ")
    if not set(expr) <= allowed:
        raise ValueError("Unsupported characters in expression")
    try:
        return float(eval(expr, {"__builtins__": {}}, {}))  # noqa: S307
    except Exception as e:
        raise ValueError(f"Bad expression: {expr}") from e


@dataclass
class ToolRouterBlock(BaseBlock):
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        text = str(payload).strip()
        meta: Dict[str, Any] = {"routed": False}

        if text.lower().startswith("calc:"):
            expr = text.split(":", 1)[1].strip()
            val = _safe_eval_expr(expr)
            meta.update({"tool": "calc", "expr": expr})
            return str(val), meta

        if text.lower().startswith("time"):
            parts = text.split()
            now = time.time()
            if len(parts) > 1 and parts[1].startswith("+"):
                try:
                    now += float(parts[1][1:])
                except Exception:
                    pass
            meta.update({"tool": "time", "epoch": now})
            return str(int(now)), meta

        if any(op in text for op in ("+", "-", "*", "/")):
            try:
                val = _safe_eval_expr(text)
                meta.update({"tool": "calc-inline"})
                return str(val), meta
            except Exception:
                pass

        meta.update({"tool": None})
        return text, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "info": "Payload-driven. No parameters."
        }


BLOCKS.register("tools", ToolRouterBlock)


# ---------------- History ----------------
@dataclass
class HistoryBlock(BaseBlock):
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        op = str(params.get("op", "show"))
        if op == "clear":
            HistoryStore.save([])
            return "OK", {"op": op}
        if op == "drop":
            msgs = HistoryStore.load()
            if msgs:
                msgs.pop()
                HistoryStore.save(msgs)
            return "OK", {"op": op}
        n = int(params.get("n", 10))
        msgs = HistoryStore.load()[-n:]
        text = "\n".join(f"[{m['role']}] {m['content']}" for m in msgs)
        return text, {"op": "show", "n": n, "count": len(msgs)}

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "op": "show",
            "n": 10
        }


BLOCKS.register("history", HistoryBlock)


# ---------------- Memory ----------------
@dataclass
class MemoryBlock(BaseBlock):
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        op = str(params.get("op", "get")).lower()
        key = str(params.get("key", "default"))
        store = Memory.load()

        if op == "set":
            store[key] = payload if params.get("value") is None else params.get("value")
            Memory.save(store)
            return payload, {"op": op, "key": key}  # <-- FIX: Return payload
        if op == "clear":
            if key == "*":
                store.clear()
            else:
                store.pop(key, None)
            Memory.save(store)
            return payload, {"op": op, "key": key}  # <-- FIX: Return payload
        return _json.dumps(store.get(key)), {"op": op, "key": key}

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "op": "get",
            "key": "default",
            "value": None
        }


BLOCKS.register("memory", MemoryBlock)


# ---------------- Self-check ----------------
@dataclass
class SelfCheckBlock(BaseBlock):
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        text = str(payload).strip()
        if not text:
            return "(no output) — consider re-running with more context)", {"fixed": True}
        if len(text.split()) < 5:
            return text + "\n\n(That was a short answer — want me to expand?)", {"short": True}
        return text, {"short": False}

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "info": "No parameters."
        }


BLOCKS.register("self_check", SelfCheckBlock)

# --- term extraction for lexicon ---
_STOPWORDS = {
    "the", "a", "an", "and", "or", "but", "if", "on", "in", "to", "for", "from", "of", "at", "by", "with", "as", "is",
    "are",
    "was", "were", "be", "been", "being", "that", "this", "these", "those", "it", "its", "into", "about", "over",
    "under",
    "up", "down", "out", "so", "than", "then", "too", "very", "can", "cannot", "could", "should", "would", "will",
    "may",
    "might", "must", "do", "does", "did", "done", "doing", "have", "has", "had", "having", "not", "no", "yes", "you",
    "your",
    "yours", "we", "our", "ours", "they", "their", "theirs", "i", "me", "my", "mine", "he", "she", "him", "her", "his",
    "hers",
    "them", "there", "here", "also", "such", "via"
}


def _extract_terms(text: str, *, top_k: int = 50, min_len: int = 4) -> List[str]:
    counts: Dict[str, int] = {}
    for raw in text.split():
        w = "".join(ch.lower() for ch in raw if ch.isalnum() or ch in "-_")
        if not w or len(w) < min_len or w in _STOPWORDS:
            continue
        counts[w] = counts.get(w, 0) + 1
    terms = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
    return [t for t, _ in terms[:top_k]]


# ================- Prompt Builder (Smart & Dissecting) ================
@dataclass
class PromptBlock(BaseBlock):
    """
    Assembles a final prompt from a template and context/lexicon from Memory.

    Features
    --------
    • SMART: Auto-detects context/lexicon keys from Memory based on
      priority lists, with manual override.
    • DISSECTING: Optionally dissects the payload (prompt) into:
        {task}   – what the model should do (summarize, explain, compare…)
        {topics} – condensed topic terms extracted from the prompt
    """

    # --- Auto-detection config ---
    PREFERRED_CONTEXT_KEYS = ["web_context", "corpus_docs"]
    PREFERRED_LEXICON_KEYS = ["web_lexicon", "corpus_lexicon", "intel_prose"]

    # Canonical task verbs
    _TASK_WORDS = {
        "summarize", "explain", "compare", "contrast", "define", "describe",
        "analyze", "evaluate", "argue", "answer", "list", "provide",
        "generate", "create", "write", "detail", "outline", "discuss",
        "rewrite", "translate", "debug", "fix"
    }

    # Question words that imply "answer/explain"
    _QUESTION_LEADS = {"what", "why", "how", "when", "where", "which", "who"}

    # --- Helper Methods ---

    def _format_value(self, value: Any, fallback: str) -> str:
        """Helper to format memory values for injection."""
        if value is None:
            return fallback
        if isinstance(value, str):
            return value if value.strip() else fallback
        if isinstance(value, list):
            terms = [str(v) for v in value if str(v).strip()]
            return ", ".join(terms) if terms else fallback
        if isinstance(value, dict):
            try:
                return _json.dumps(value, indent=2)
            except Exception:
                return str(value)
        return str(value)

    def _find_key_in_store(self, store: Dict[str, Any], keys: List[str]) -> Optional[str]:
        """Find the first key in the list that exists and has content in the store."""
        for key in keys:
            if store.get(key):
                return key
        return None

    # --- Prompt Dissection ---

    def _tokenize_prompt(self, text: str) -> List[str]:
        """
        Light tokenization: lowercased, alnum + internal -/' preserved.
        """
        tokens: List[str] = []
        for raw in (text or "").split():
            w = "".join(ch.lower() for ch in raw if ch.isalnum() or ch in "'-")
            w = w.strip("'-")
            if w:
                tokens.append(w)
        return tokens

    def _dedupe_preserve_order(self, items: List[str]) -> List[str]:
        seen = set()
        out: List[str] = []
        for x in items:
            if x not in seen:
                seen.add(x)
                out.append(x)
        return out

    def _infer_task_from_tokens(self, tokens: List[str]) -> str:
        """
        Infer a task phrase from tokens.
        Priority:
          1) Explicit task word in prompt (summarize, explain, rewrite, …)
          2) Question-style prompt → 'answer' / 'explain'
          3) Fallback: 'address'
        """
        # 1) Direct task word
        for t in tokens:
            if t in self._TASK_WORDS:
                return t

        # 2) If prompt starts with a question lead, treat as "answer/explain"
        if tokens:
            first = tokens[0]
            if first in self._QUESTION_LEADS or first.endswith("?"):
                return "answer"

        # 3) Otherwise, default neutral task
        return "address"

    def _dissect_prompt(self, payload_str: str, max_topics: int = 16) -> Dict[str, Any]:
        """
        Dissects a prompt into 'task' and 'topics'.
        Also returns the raw topic token list for metadata.
        """
        tokens = self._tokenize_prompt(payload_str)

        if not tokens:
            return {"task": "address", "topics_str": "the following", "topics_list": []}

        task = self._infer_task_from_tokens(tokens)

        # Remove task tokens & stopwords to get topics
        topic_candidates = [
            t for t in tokens
            if t not in self._TASK_WORDS and t not in _STOPWORDS
        ]

        topics_list = self._dedupe_preserve_order(topic_candidates)[:max_topics]
        topics_str = " ".join(topics_list) if topics_list else "the following"

        return {
            "task": task,
            "topics_str": topics_str,
            "topics_list": topics_list,
        }

    # --- Main Execution ---

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        """
        Build the final prompt using:
          • {context} – from Memory (auto or explicit key)
          • {lexicon} – from Memory (auto or explicit key)
          • {payload} – original user request
          • {task}    – inferred/explicit task from the prompt
          • {topics}  – condensed topic summary from the prompt
        """
        # Default template uses dissected keys but is backward-compatible via format_map
        template = str(params.get(
            "template",
            "### Context\n{context}\n\n"
            "### Key Terms\n{lexicon}\n\n"
            "### Task\n"
            "Using the context and key terms provided, your goal is to **{task}** "
            "the following topics: **{topics}**.\n\n"
            "(Original Request: {payload})"
        ))

        fallback_text = str(params.get("fallback_text", "(none)"))
        # Allow per-run toggle of dissection
        dissect_enabled = bool(params.get("dissect", True))
        max_topics = int(params.get("max_topics", 16))

        store = Memory.load()
        payload_str = str(payload).strip()

        meta: Dict[str, Any] = {
            "template_keys_provided": ["payload", "context", "lexicon", "task", "topics"],
            "context_key_used": None,
            "lexicon_key_used": None,
            "context_chars": 0,
            "lexicon_terms": 0,
            "dissected_task": None,
            "dissected_topics": None,
            "dissected_topics_list": None,
            "error": None,
        }

        # --- Dissect payload -> task/topics (optional) ---
        if dissect_enabled:
            dissected = self._dissect_prompt(payload_str, max_topics=max_topics)
            task_str = dissected["task"]
            topics_str = dissected["topics_str"]
            meta["dissected_task"] = task_str
            meta["dissected_topics"] = topics_str
            meta["dissected_topics_list"] = dissected["topics_list"]
        else:
            task_str = "address"
            topics_str = "the following"
            meta["dissected_task"] = task_str
            meta["dissected_topics"] = topics_str
            meta["dissected_topics_list"] = []

        # --- Smart Context-Key-Finding ---
        context_str = fallback_text
        explicit_context_key = params.get("context_key")

        if explicit_context_key and explicit_context_key not in (
                "(Optional: auto-detected if blank)", "", None
        ):
            # If explicit key exists but is empty, fall back to auto
            if store.get(explicit_context_key):
                meta["context_key_used"] = explicit_context_key
            else:
                meta["context_key_used"] = self._find_key_in_store(
                    store, self.PREFERRED_CONTEXT_KEYS
                )
        else:
            meta["context_key_used"] = self._find_key_in_store(
                store, self.PREFERRED_CONTEXT_KEYS
            )

        if meta["context_key_used"]:
            context_str = self._format_value(store.get(meta["context_key_used"]), fallback_text)

        # --- Smart Lexicon-Key-Finding ---
        lexicon_str = fallback_text
        explicit_lexicon_key = params.get("lexicon_key")

        if explicit_lexicon_key and explicit_lexicon_key not in (
                "(Optional: auto-detected if blank)", "", None
        ):
            if store.get(explicit_lexicon_key):
                meta["lexicon_key_used"] = explicit_lexicon_key
            else:
                meta["lexicon_key_used"] = self._find_key_in_store(
                    store, self.PREFERRED_LEXICON_KEYS
                )
        else:
            meta["lexicon_key_used"] = self._find_key_in_store(
                store, self.PREFERRED_LEXICON_KEYS
            )

        if meta["lexicon_key_used"]:
            lexicon_str = self._format_value(store.get(meta["lexicon_key_used"]), fallback_text)

        # --- Final Prompt Assembly ---
        try:
            format_map = defaultdict(
                lambda: "",
                {
                    "payload": payload_str,
                    "context": context_str,
                    "lexicon": lexicon_str,
                    "task": task_str,
                    "topics": topics_str,
                },
            )

            final_prompt = template.format_map(format_map)

            meta["context_chars"] = len(context_str) if context_str != fallback_text else 0
            meta["lexicon_terms"] = (
                len([t for t in lexicon_str.split(",") if t.strip()])
                if lexicon_str != fallback_text
                else 0
            )

        except Exception as e:
            final_prompt = f"[TEMPLATE ERROR: {e}]\n\n{payload_str}"
            meta["error"] = str(e)

        return final_prompt, meta

    def get_params_info(self) -> Dict[str, Any]:
        """Returns default parameters for the GUI / CLI help."""
        return {
            "template": (
                "### Context\n{context}\n\n"
                "### Key Terms\n{lexicon}\n\n"
                "### Task\n"
                "Using the context, your goal is to **{task}** the following "
                "topics: **{topics}**.\n"
                "(Original Request: {payload})"
            ),
            "context_key": "(Optional: auto-detected if blank)",
            "lexicon_key": "(Optional: auto-detected if blank)",
            "fallback_text": "(none)",
            "dissect": True,  # Toggle smart prompt dissection on/off
            "max_topics": 16,  # Max topic terms extracted from the prompt
        }


# Register the new block
BLOCKS.register("prompt", PromptBlock)


# ================ Corpus (HF with timeout + wiki_api fallback) ================
@dataclass
class CorpusBlock(BaseBlock):
    """
    Resilient corpus puller:
      • provider = "wiki_api" (default) with short startup timeout
      • optional HF provider = "wikimedia/wikipedia" if explicitly requested
      • Caches results in a local SQLite FTS (Full-Text Search) database via CorpusStore.
      • Queries FTS database first, falling back to HF/API.
      • BM25-ish re-ranking, sentence extraction, auto-lexicon.
    """

    def __post_init__(self):
        # Per-instance DB objects (created lazily in execute)
        self.db: Optional[submanagers.DatabaseSubmanager] = None
        self.store: Optional[CorpusStore] = None

    # ---------------- DB init helper ---------------- #
    def _init_db(self, db_path: str, logger=None) -> None:
        """
        Initialize shared DatabaseSubmanager + CorpusStore.
        Idempotent.
        """
        if self.db and self.store:
            return

        cfg = submanagers.DatabaseConfig(path=str(db_path or "corpus_cache.db"))
        self.db = submanagers.DatabaseSubmanager(cfg, logger=logger)
        self.db.open()

        self.store = CorpusStore(db=self.db)
        self.store.ensure_schema()

    # ---------------- Main execute ---------------- #
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os, re, json, time, threading
        from math import log
        from typing import Dict, List
        from itertools import islice

        # ---- Params ----
        # NOTE: default provider is now "wiki_api" so we only hit Wikipedia unless you override.
        provider = str(params.get("provider", "wiki_api"))
        config = str(params.get("config", "20231101.en"))
        split = str(params.get("split", "train"))
        query = str(params.get("query", "")).strip()
        neg = [s.strip().lower() for s in str(params.get("neg", "")).split(",") if s.strip()]
        must_terms = [s.strip().lower() for s in str(params.get("must_terms", "")).split(",") if s.strip()]
        sample = int(params.get("sample", 50))
        columns = params.get("columns", ["title", "text"])
        sep = str(params.get("sep", "\n\n"))
        max_chars = int(params.get("max_chars", 2800))
        cache_dir = params.get("cache_dir")

        # DB Params
        db_path = str(params.get("db_path", os.path.join(APP_DIR, "corpus_cache.db")))
        use_db_cache = bool(params.get("use_db_cache", True))

        # ranking / extraction
        title_only = bool(params.get("title_only", False))
        whole_word = bool(params.get("whole_word", True))
        regex_query = params.get("regex")
        top_k_docs = int(params.get("top_k_docs", 5))
        top_k_sents = int(params.get("top_k_sents", 12))
        sent_window = int(params.get("sent_window", 1))
        min_doc_chars = int(params.get("min_doc_chars", 200))

        # streaming controls (HF only)
        streaming = bool(params.get("streaming", False))
        scan_limit = int(params.get("scan_limit", 200_000))
        hf_timeout = float(params.get("hf_timeout_sec", 10.0))  # startup timeout for HF path
        set_hf_env = bool(params.get("set_hf_env", True))

        # lexicon
        export_lexicon = bool(params.get("export_lexicon", True))
        lexicon_key = str(params.get("lexicon_key", "corpus_lexicon"))
        inject_lexicon = bool(params.get("inject_lexicon", True))
        inject_context = bool(params.get("inject_context", True))
        lexicon_top_k = int(params.get("lexicon_top_k", 40))
        lexicon_min_len = int(params.get("lexicon_min_len", 4))
        use_phrases = bool(params.get("lexicon_phrases", True))

        meta: Dict[str, Any] = {"db_source": "none"}

        # ---- DB: init if needed ----
        if use_db_cache:
            self._init_db(db_path, logger=getattr(self, "logger", None))

        # ---- DB wrapper helpers using CorpusStore ----
        def _save_many_to_db(docs: List[Dict[str, str]], config_key: str):
            if not (use_db_cache and self.store and docs):
                return
            try:
                self.store.save_many(docs, config_key)
            except Exception as e:
                print(f"[CorpusBlock] DB bulk save failed: {e}")

        def _load_from_db(q: str, config_key: str) -> List[Dict[str, str]]:
            if not (use_db_cache and self.store and q):
                return []
            # Fetch a larger candidate pool from DB to feed into BM25
            fetch_limit = max(sample * 5, 50)
            return self.store.search_fts(q, config_key, fetch_limit)

        # ---- Standard Helpers ----
        def _normalize(v) -> str:
            if v is None:
                return ""
            if isinstance(v, str):
                return v
            if isinstance(v, list):
                return " ".join(_normalize(x) for x in v)
            if isinstance(v, dict):
                return " ".join(_normalize(x) for x in v.values())
            return str(v)

        def _tokenize(t: str) -> List[str]:
            return re.findall(r"[A-Za-z0-9][A-Za-z0-9_\-]+", t.lower())

        def _contains_whole_word(t: str, q: str) -> bool:
            return re.search(rf"\b{re.escape(q)}\b", t, flags=re.IGNORECASE) is not None

        q_pattern = re.compile(regex_query, re.IGNORECASE) if isinstance(regex_query, str) and regex_query.strip() else None

        def _matches(title: str, text: str) -> bool:
            """
            Used by the HF provider only (NOT for wiki_api HTTP fetch).
            """
            hay = title if title_only else (title + "\n" + text)
            if len(hay) < min_doc_chars:
                return False
            # positive
            if q_pattern:
                if not q_pattern.search(hay):
                    return False
            elif query:
                if whole_word:
                    if not _contains_whole_word(hay, query):
                        return False
                else:
                    if query.lower() not in hay.lower():
                        return False
            # must terms
            for m in must_terms:
                if m and (m not in hay.lower()):
                    return False
            # negatives
            for n in neg:
                if re.search(rf"\b{re.escape(n)}\b", hay, flags=re.IGNORECASE):
                    return False
            return True

        def _split_sents(text: str) -> List[str]:
            bits = re.split(r"(?<=[.!?])\s+|\n+", text.strip())
            return [b.strip() for b in bits if b.strip()]

        # ---- wiki_api provider (simple: send query as-is, no special-casing) ----
        def _fetch_wiki_api_pages(topic: str) -> List[Dict[str, str]]:
            """
            Take the query string as-is, use it to search Wikipedia, and return pages.
            No special-case heuristics, no prompt-like logic.
            Uses the REST /page/summary/{title} endpoint (JSON) and pulls 'extract'.
            """
            import requests

            topic = (topic or "").strip()
            if not topic:
                return []

            session = requests.Session()
            session.headers.update({"User-Agent": "promptchat/mini-crawler"})

            titles: List[str] = []

            # 1) Use the raw topic as the search string (no modifications)
            try:
                r = session.get(
                    "https://en.wikipedia.org/w/api.php",
                    params={
                        "action": "opensearch",
                        "search": topic,      # <-- raw query
                        "limit": 5,
                        "namespace": 0,
                        "format": "json",
                    },
                    timeout=8,
                )
                r.raise_for_status()
                data = r.json()
                # data[3] is an array of full wiki URLs; strip /wiki/ prefix
                titles = [re.sub(r"^.*/wiki/", "", u) for u in data[3]]
            except Exception:
                titles = []

            # 2) Fallback: direct page guess from the topic
            if not titles:
                titles = [topic.replace(" ", "_")]

            docs: List[Dict[str, str]] = []
            for t in titles:
                try:
                    # Use REST summary endpoint (stable + documented)
                    url = f"https://en.wikipedia.org/api/rest_v1/page/summary/{t}"
                    r = session.get(url, timeout=8)
                    if r.status_code != 200:
                        continue

                    data = r.json()
                    title = data.get("title") or t.replace("_", " ")
                    text = data.get("extract") or ""

                    # Skip completely empty extracts
                    if not text.strip():
                        continue

                    docs.append({"title": title, "text": text})

                    if sample > 0 and len(docs) >= sample:
                        break
                except Exception:
                    continue

            return docs
        # ---- HF provider with startup timeout, then fallback to wiki_api ----
        def _load_hf_docs() -> List[Dict[str, str]]:
            from datasets import load_dataset
            docs: List[Dict[str, str]] = []

            if set_hf_env:
                os.environ.setdefault("HF_HUB_HTTP_TIMEOUT", "12")
                os.environ.setdefault("HF_HUB_ENABLE_HF_TRANSFER", "0")
                os.environ.setdefault("HF_HUB_DISABLE_TELEMETRY", "1")

            start_evt = threading.Event()
            err_box = {"exc": None}
            out_box = {"docs": None}

            def _worker():
                try:
                    if streaming:
                        ds = load_dataset(provider, config, split=split, cache_dir=cache_dir, streaming=True)
                        count = 0
                        for rec in islice(ds, 0, max(0, scan_limit)):
                            title = _normalize(rec.get("title"))
                            text = _normalize(rec.get("text") or rec.get("body"))
                            if _matches(title, text):
                                docs.append({"title": title, "text": text})
                            count += 1
                            if sample > 0 and len(docs) >= sample * 2:
                                break
                        if sample >= 0:
                            docs[:] = docs[:sample]
                    else:
                        ds = load_dataset(provider, config, split=split, cache_dir=cache_dir)
                        keep: List[Dict[str, str]] = []
                        stop = min(len(ds), scan_limit) if scan_limit > 0 else len(ds)
                        for i in range(stop):
                            rec = ds[i]
                            title = _normalize(rec.get("title"))
                            text = _normalize(rec.get("text") or rec.get("body"))
                            if _matches(title, text):
                                keep.append({"title": title, "text": text})
                            if sample > 0 and len(keep) >= sample:
                                break
                        docs[:] = keep[:sample] if sample >= 0 else keep
                    out_box["docs"] = docs
                except Exception as e:
                    err_box["exc"] = e
                finally:
                    start_evt.set()

            th = threading.Thread(target=_worker, daemon=True)
            th.start()
            # Wait for either first batch or error, up to hf_timeout seconds.
            start_evt.wait(timeout=hf_timeout)
            if out_box["docs"] is not None:
                return out_box["docs"]
            if err_box["exc"] is not None:
                raise err_box["exc"]
            # Timeout: give up on HF now
            return []

        # ---- acquire docs (provider or fallback) ----
        docs_raw: List[Dict[str, str]] = []
        used_provider = provider

        # Use a stable config key for DB
        if provider == "wiki_api":
            db_config_key = "wiki_api"
        else:
            db_config_key = config  # config key for DB

        # Try DB first
        if use_db_cache:
            docs_raw = _load_from_db(query, db_config_key)
            if docs_raw:
                meta["db_source"] = "fts_cache"

        # If DB cache is empty, go to upstream
        if not docs_raw:
            meta["db_source"] = "fetch"
            if provider == "wiki_api":
                docs_raw = _fetch_wiki_api_pages(query)
                # db_config_key is already "wiki_api" here
            else:
                try:
                    docs_raw = _load_hf_docs()
                    if not docs_raw:
                        used_provider = "wiki_api"
                        db_config_key = "wiki_api"
                        docs_raw = _fetch_wiki_api_pages(query)
                except Exception:
                    used_provider = "wiki_api"
                    db_config_key = "wiki_api"
                    docs_raw = _fetch_wiki_api_pages(query)

            _save_many_to_db(docs_raw, db_config_key)

        # ---- no docs? return early ----
        if not docs_raw:
            base = "" if payload is None else str(payload)
            meta.update({
                "rows": 0,
                "note": "no docs matched or provider unavailable",
                "provider": used_provider,
                "query": query,
                "regex": bool(q_pattern),
                "neg": neg,
                "must": must_terms,
                "streaming": streaming,
                "scan_limit": scan_limit,
                "db_path": db_path if use_db_cache else None,
            })
            return base, meta

        # ---- ranking (BM25-ish + regex boost) ----
        corpus_tokens = [set(_tokenize((d["title"] + " " + d["text"]).lower())) for d in docs_raw]
        N = len(corpus_tokens)
        q_terms = set(_tokenize(query)) if query else set()
        df: Dict[str, int] = {}
        for terms in corpus_tokens:
            for t in terms:
                df[t] = df.get(t, 0) + 1

        def _bm25ish_score(doc_text: str) -> float:
            words = _tokenize(doc_text)
            L = len(words) or 1
            score = 0.0
            if q_terms:
                for t in q_terms:
                    tf = words.count(t)
                    if tf == 0:
                        continue
                    idf = log((N - df.get(t, 0) + 0.5) / (df.get(t, 0) + 0.5) + 1.0)
                    k1, b, avgdl = 1.2, 0.75, 2000.0
                    score += idf * ((tf * (k1 + 1)) / (tf + k1 * (1 - b + b * (L / avgdl))))
            if q_pattern and q_pattern.search(doc_text):
                score += 2.0
            return score

        ranked = sorted(
            docs_raw,
            key=lambda d: _bm25ish_score(d["title"] + " " + d["text"]),
            reverse=True,
        )[: max(1, top_k_docs)]

        # ---- sentence extraction ----
        hit_sents: List[str] = []
        per_doc_quota = max(1, top_k_sents // max(1, len(ranked)))
        for d in ranked:
            title = (d["title"] or "").strip()
            sents = _split_sents(d["text"] or "")
            scored: List[tuple[float, int, str]] = []
            for idx, s in enumerate(sents):
                tok = set(_tokenize(s))
                overlap = len(tok & q_terms) if q_terms else 0
                if q_pattern and q_pattern.search(s):
                    overlap += 2
                if query and whole_word and _contains_whole_word(s, query):
                    overlap += 1
                if overlap > 0:
                    scored.append((float(overlap), idx, s))
            took = 0
            for _, idx, _ in sorted(scored, key=lambda x: (-x[0], x[1]))[:per_doc_quota]:
                lo = max(0, idx - sent_window)
                hi = min(len(sents), idx + sent_window + 1)
                chunk = " ".join(sents[lo:hi]).strip()
                if chunk and chunk not in hit_sents:
                    if title and (not hit_sents or not hit_sents[-1].startswith("# ")):
                        hit_sents.append(f"# {title}")
                    hit_sents.append(chunk)
                    took += 1
            if took == 0 and sents:
                chunk = " ".join(sents[: max(1, sent_window + 1)]).strip()
                if chunk and chunk not in hit_sents:
                    if title and (not hit_sents or not hit_sents[-1].startswith("# ")):
                        hit_sents.append(f"# {title}")
                    hit_sents.append(chunk)

        context = sep.join(hit_sents).strip()
        if max_chars > 0 and len(context) > max_chars:
            context = context[:max_chars] + "…"

        # ---- lexicon ----
        def _extract_terms_local(text: str, *, top_k: int = 50, min_len: int = 4) -> List[str]:
            counts: Dict[str, int] = {}
            for raw in text.split():
                w = "".join(ch.lower() for ch in raw if ch.isalnum() or ch in "-_")
                if len(w) < min_len or w in _STOPWORDS:
                    continue
                counts[w] = counts.get(w, 0) + 1
            return [t for t, _ in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:top_k]]

        lexicon: List[str] = _extract_terms_local(
            context, top_k=lexicon_top_k, min_len=lexicon_min_len
        ) if context else []

        if use_phrases and context:
            phrase_candidates = re.findall(
                r"\b([A-Za-z0-9][A-Za-z0-9_\-]+(?:\s+[A-Za-z0-9][A-Za-z0-9_\-]+){1,3})\b",
                context,
            )
            phrase_counts: Dict[str, int] = {}
            for ph in phrase_candidates:
                ph = ph.lower().strip()
                if any(tok in _STOPWORDS for tok in ph.split()):
                    continue
                phrase_counts[ph] = phrase_counts.get(ph, 0) + 1
            phrases = [p for p, _ in sorted(phrase_counts.items(), key=lambda kv: (-kv[1], kv[0]))[:10]]
            lexicon = list(dict.fromkeys(phrases + lexicon))[:lexicon_top_k]

        if export_lexicon and lexicon:
            store = Memory.load()
            store[lexicon_key] = lexicon
            Memory.save(store)

        base = "" if payload is None else str(payload)
        parts: List[str] = [base] if base else []
        if inject_lexicon and lexicon:
            parts.append("[lexicon]\n" + ", ".join(lexicon))
        if inject_context and context:
            parts.append("[context]\n" + context)
        out = sep.join(p for p in parts if p).strip()

        meta.update({
            "rows": len(docs_raw),
            "ranked_docs": len(ranked),
            "provider": used_provider,
            "streaming": streaming if used_provider != "wiki_api" else False,
            "scan_limit": scan_limit if used_provider != "wiki_api" else None,
            "truncated": len(context) >= max_chars if max_chars > 0 else False,
            "lexicon_key": lexicon_key if (export_lexicon and lexicon) else None,
            "lexicon_size": len(lexicon),
            "query": query,
            "neg": neg,
            "must": must_terms,
            "title_only": title_only,
            "whole_word": whole_word,
            "regex": bool(q_pattern),
            "context_len": len(context),
            "hit_sents": len(hit_sents),
            "db_path": db_path if use_db_cache else None,
            "db_source": meta.get("db_source", "none"),
        })
        return out, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "provider": "wiki_api",          # default: direct Wikipedia REST only
            "config": "20231101.en",
            "split": "train",
            "query": "",
            "neg": "",
            "must_terms": "",
            "sample": 50,
            "columns": ["title", "text"],
            "sep": "\n\n",
            "max_chars": 2800,
            "cache_dir": None,
            "title_only": False,
            "whole_word": True,
            "regex": None,
            "top_k_docs": 5,
            "top_k_sents": 12,
            "sent_window": 1,
            "min_doc_chars": 200,
            "streaming": False,
            "scan_limit": 200000,
            "hf_timeout_sec": 10.0,
            "set_hf_env": True,
            "export_lexicon": True,
            "lexicon_key": "corpus_lexicon",
            "inject_lexicon": True,
            "inject_context": True,
            "lexicon_top_k": 40,
            "lexicon_min_len": 4,
            "lexicon_phrases": True,
            "db_path": "corpus_cache.db",
            "use_db_cache": True,
        }


# keep registration
BLOCKS.register("corpus", CorpusBlock)


# ================ Chat (no personas/prompts; uses lexicon only) ================
@dataclass
class ChatBlock(BaseBlock):
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        model_name = str(params.get("model", "lexicon"))
        keep_history = bool(params.get("keep_history", True))
        lexicon_key = str(params.get("lexicon_key", "corpus_lexicon"))
        style = str(params.get("style", "plain"))  # "plain" | "bullets" | "outline"

        # --- NEW PARAMETERS ---
        # Read the parameters you are trying to pass
        include_context = bool(params.get("include_context", True))
        max_bullets = int(params.get("max_bullets", int(params.get("max_terms", 8))))  # Use max_terms as fallback
        max_chars = int(params.get("max_chars", 0))  # 0 = unlimited

        text = str(payload or "")

        # --- [NEW] Robust parser ---
        try:
            # Get the *last* context block
            inline_ctx = text.rsplit("[context]\n", 1)[1] if include_context else ""
        except Exception:
            inline_ctx = ""

        try:
            # Get the *last* lexicon block
            lex_part = text.rsplit("[lexicon]\n", 1)[1]
            # Ensure we don't grab context that might follow
            lex_part = lex_part.split("\n[", 1)[0]
            inline_lex = [w.strip() for w in lex_part.split(",") if w.strip()]
        except Exception:
            inline_lex = []
        # --- End new parser ---

        if not inline_lex:
            store = Memory.load()
            raw = store.get(lexicon_key)
            if isinstance(raw, list):
                inline_lex = [str(w) for w in raw]

        # remove blocks from user text
        core = text
        # Clean up the payload for the "core" text
        if inline_ctx:
            core = core.rsplit("[context]\n", 1)[0]
        if inline_lex:
            # This is tricky; we just rsplit on the tag
            core = core.rsplit("[lexicon]\n", 1)[0]
        core = core.strip()

        # --- Apply sub-pipeline to core text (grammar fix, etc.) ---
        if "subpipeline" in params and str(params["subpipeline"]).strip():
            core = self.run_sub_pipeline(
                initial_value=core,
                pipeline_param_name="subpipeline",
                parent_params=params
            )

        # --- [END NEW] ---

        # very small summarizer over the context:
        def summarize(ctx: str, k: int = 8) -> List[str]:  # k is max_bullets
            import re
            sents_raw = re.split(r"(?<=[.!?])\s+|\n+|(?=\s*#\s)", ctx)
            good_sents = []
            for s in sents_raw:
                s = s.strip()
                if not s: continue
                if s.startswith("# "):  # Skip titles
                    continue
                if len(s) > 600:  # Skip massive "sentences"
                    continue
                if s.count(' ') < 4:  # Skip things that aren't real sentences
                    continue
                good_sents.append(s)

            # prefer sentences with lexicon overlap
            def score(s: str) -> int:
                tok = set(s.lower().split())
                return sum(1 for t in inline_lex if t in tok)

            ranked = sorted(((score(s), idx, s) for idx, s in enumerate(good_sents)), key=lambda x: (-x[0], x[1]))

            final_bullets = []
            seen = set()
            for _, _, s in ranked:
                if s not in seen:
                    final_bullets.append(s)
                    seen.add(s)
                    # Stop once we have k unique sentences
                    if len(final_bullets) >= k:  # Use k (max_bullets)
                        break
            return final_bullets

        # --- Use new max_bullets param ---
        bullets = summarize(inline_ctx, k=max_bullets) if inline_ctx else []

        # Get model (and pass max_terms to it)
        model_kwargs = {}
        if "max_terms" in params:
            model_kwargs["max_terms"] = int(params["max_terms"])
        model = get_chat_model(model_name, **model_kwargs)

        if style == "bullets":
            if bullets:
                body = "- " + "\n- ".join(bullets)
            elif inline_lex:
                body = "- " + "\n- ".join(inline_lex[:max_bullets])
            else:
                body = core or "No context available."
        elif style == "outline" and bullets:
            body = "\n".join(f"{i + 1}. {s}" for i, s in enumerate(bullets))
        else:
            # Use core text as a fallback if no bullets and no context
            body = " ".join(bullets) if bullets else (inline_ctx or core)

        # --- Pass max_chars to model's generate method ---
        gen_kwargs = {"lexicon": inline_lex}
        if max_chars > 0:
            gen_kwargs["max_chars"] = max_chars

        # --- [NEW] Pass sub-block params to model's generate ---
        # This lets HF-LLM model see the style, etc.
        if "subpipeline" in params:
            gen_kwargs["subpipeline"] = params.get("subpipeline")
        if "english_chat.op" in params:
            gen_kwargs["style"] = params.get("english_chat.op")

        reply = model.generate(body, **gen_kwargs)

        if keep_history:
            HistoryStore.append({"role": "user", "content": text})
            HistoryStore.append({"role": "assistant", "content": reply})

        return reply, {"model": model_name, "lexicon_used": len(inline_lex), "ctx_sents": len(bullets)}

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "model": "lexicon",
            "keep_history": True,
            "lexicon_key": "corpus_lexicon",
            "style": "plain",
            "include_context": True,
            "max_bullets": 8,
            "max_terms": 8,
            "max_chars": 0,
            "subpipeline": "english_chat",  # <--- NEW PARAM
            "english_chat.op": "passthrough"  # <--- NEW PARAM
        }


BLOCKS.register("chat", ChatBlock)


# ================ WebCorpus (web search + fetch + summarize) ================

@dataclass
class WebCorpusBlock(BaseBlock):
    """
    Web corpus builder:
      • Search engines: duckduckgo (default), serpapi, google_cse
      • Fetch N pages (with timeout, cache), strip boilerplate, de-dup
      • Regex / must / negative filtering
      • BM25-ish re-ranking + sentence extraction
      • Exports lexicon into Memory and injects [lexicon]/[context] into pipeline
      • Pluggable query processing via `subpipeline` param.
      • Uses DatabaseSubmanager + WebCorpusStore for persistent caching.
      • Optional JSSniffer + NetworkSniffer enrichment for top URLs.
    """

    def __post_init__(self):
        # Per-instance DB objects (created lazily in execute)
        self.db: Optional[submanagers.DatabaseSubmanager] = None
        self.store: Optional[WebCorpusStore] = None

        # Lazy-init sniffers when needed
        self._js_sniffer: Optional[submanagers.JSSniffer] = None
        self._net_sniffer: Optional[submanagers.NetworkSniffer] = None

    # ---------------- DB init helper ---------------- #

    def _init_db(self, db_path: str, logger=None) -> None:
        """
        Initialize shared DatabaseSubmanager + WebCorpusStore.
        Idempotent.
        """
        if self.db and self.store:
            return

        cfg = submanagers.DatabaseConfig(path=str(db_path or "webcorpus.db"))
        self.db = submanagers.DatabaseSubmanager(cfg, logger=logger)
        self.db.open()

        self.store = WebCorpusStore(db=self.db)
        self.store.ensure_schema()

    # ---------------- Sniffer init helpers ---------------- #

    def _ensure_sniffers(self, logger=None) -> None:
        if self._js_sniffer is None:
            self._js_sniffer = submanagers.JSSniffer(logger=logger or getattr(self, "logger", None))
        if self._net_sniffer is None:
            self._net_sniffer = submanagers.NetworkSniffer(logger=logger or getattr(self, "logger", None))

    # ---------------- Main execute ---------------- #
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os, re, time, hashlib, json, sys, traceback
        from math import log
        from typing import List, Dict, Tuple
        from urllib.parse import urlparse
        from threading import Thread

        logger = getattr(self, "logger", None)

        # ---- Params ----
        query_raw = str(params.get("query", "") or str(payload or "")).strip()
        engine = str(params.get("engine", "duckduckgo")).lower()  # duckduckgo | serpapi | google_cse
        num_results = int(params.get("num_results", 10))
        max_fetch = int(params.get("max_fetch", 8))  # how many pages to actually fetch
        timeout_sec = float(params.get("timeout", 8.0))
        read_timeout = float(params.get("read_timeout", 12.0))
        user_agent = str(params.get("user_agent", "promptchat/webcorpus"))
        pause = float(params.get("pause", 0.7))  # polite delay between fetches
        max_concurrent_fetch = int(params.get("max_concurrent_fetch", 4))
        cache_dir = str(params.get("cache_dir", os.path.join(APP_DIR, "webcache")))
        os.makedirs(cache_dir, exist_ok=True)

        # DB Params
        db_path = str(params.get("db_path", os.path.join(APP_DIR, "webcorpus.db")))
        use_db_cache = bool(params.get("use_db_cache", True))

        # Sniffer params
        use_js_sniffer = bool(params.get("use_js_sniffer", False))
        use_network_sniffer = bool(params.get("use_network_sniffer", False))
        sniffer_timeout = float(params.get("sniffer_timeout", 8.0))
        max_sniffer_pages = int(params.get("max_sniffer_pages", 4))

        # text handling
        regex_query = params.get("regex")
        neg = [s.strip() for s in str(params.get("neg", "")).split(",") if s.strip()]
        must_terms = [s.strip().lower() for s in str(params.get("must_terms", "")).split(",") if s.strip()]
        top_k_docs = int(params.get("top_k_docs", 6))
        top_k_sents = int(params.get("top_k_sents", 18))
        sent_window = int(params.get("sent_window", 1))
        max_chars = int(params.get("max_chars", 2800))
        min_doc_chars = int(params.get("min_doc_chars", 400))
        site_include = [s.strip().lower() for s in str(params.get("site_include", "")).split(",") if s.strip()]
        site_exclude = [s.strip().lower() for s in str(params.get("site_exclude", "")).split(",") if s.strip()]

        min_term_overlap = int(params.get("min_term_overlap", 1))

        # lexicon export
        export_lexicon = bool(params.get("export_lexicon", True))
        lexicon_key = str(params.get("lexicon_key", "web_lexicon"))
        inject_lexicon = bool(params.get("inject_lexicon", True))
        inject_context = bool(params.get("inject_context", True))
        lexicon_top_k = int(params.get("lexicon_top_k", 40))
        lexicon_min_len = int(params.get("lexicon_min_len", 4))
        use_phrases = bool(params.get("lexicon_phrases", True))

        # context export
        export_context = bool(params.get("export_context", True))
        context_key = str(params.get("context_key", "web_context"))
        append_ctx = bool(params.get("append_context", False))

        # compile regex
        q_pattern = re.compile(regex_query, re.IGNORECASE) if isinstance(regex_query, str) and regex_query.strip() else None

        meta: Dict[str, Any] = {
            "engine": engine,
            "query": query_raw,
            "errors": [],
        }

        # ---- DB: init if needed ----
        if use_db_cache:
            self._init_db(db_path, logger=logger)

        # ---- Build list of queries to run (subpipeline OR raw) ----
        queries_to_run: Any

        if "subpipeline" in params and str(params["subpipeline"]).strip():
            queries_to_run = self.run_sub_pipeline(
                initial_value=query_raw,
                pipeline_param_name="subpipeline",
                parent_params=params,
            )
        else:
            queries_to_run = [query_raw] if query_raw else []

        if isinstance(queries_to_run, str):
            queries_to_run = [queries_to_run]
        elif not isinstance(queries_to_run, list):
            queries_to_run = [query_raw] if query_raw else []

        queries_to_run = [q.strip() for q in queries_to_run if isinstance(q, str) and q.strip()]

        if not queries_to_run:
            base = "" if payload is None else str(payload)
            return base, {
                "rows": 0,
                "note": "empty query",
                "engine": engine,
                "query": query_raw,
                "queries_run": [],
            }

        meta["queries_run"] = queries_to_run

        # ---- Helpers ----
        def _tokenize(t: str) -> List[str]:
            return re.findall(r"[A-Za-z0-9][A-Za-z0-9_\-]+", (t or "").lower())

        def _split_sents(text: str) -> List[str]:
            bits = re.split(r"(?<=[.!?])\s+|\n+", (text or "").strip())
            return [b.strip() for b in bits if b.strip()]

        def _clean_domain(u: str) -> str:
            try:
                netloc = urlparse(u).netloc.lower()
                return netloc.split(":")[0]
            except Exception:
                return ""

        def _allow_site(u: str) -> bool:
            d = _clean_domain(u)
            if site_include and not any(d.endswith(s) for s in site_include):
                return False
            if any(d.endswith(s) for s in site_exclude):
                return False
            return True

        # ---- DB helpers via WebCorpusStore ----

        def _load_from_db(url: str) -> Tuple[str, str] | None:
            if not (use_db_cache and self.store):
                return None
            try:
                rec = self.store.get_page(url)
                if rec:
                    return rec.title, rec.content
            except Exception as e:
                print(f"[WebCorpusBlock] DB load failed for {url}: {e}", file=sys.stderr)
            return None

        def _save_to_db(url: str, title: str, content: str):
            if not (use_db_cache and self.store):
                return
            try:
                self.store.save_page(
                    url=url,
                    title=title,
                    content=content,
                    engine=engine,
                    query=query_raw,
                )
            except Exception as e:
                print(f"[WebCorpusBlock] DB save failed for {url}: {e}", file=sys.stderr)

        # ---- File Cache (used by async fetch) ----
        def _cache_path(url: str) -> str:
            h = hashlib.sha1(url.encode("utf-8")).hexdigest()
            return os.path.join(cache_dir, f"{h}.json")

        def _save_cache(url: str, html: str) -> None:
            try:
                with open(_cache_path(url), "w", encoding="utf-8") as f:
                    json.dump({"url": url, "html": html}, f)
            except Exception:
                pass

        def _load_cache(url: str) -> str | None:
            try:
                with open(_cache_path(url), "r", encoding="utf-8") as f:
                    obj = json.load(f)
                return obj.get("html")
            except Exception:
                return None

        def _extract_text(html: str, url: str) -> str:
            try:
                import trafilatura
                clean_text = trafilatura.extract(
                    html,
                    include_comments=False,
                    include_tables=False,
                    deduplicate=True,
                )
                return clean_text or ""
            except ImportError:
                pass
            except Exception:
                pass

            try:
                from bs4 import BeautifulSoup
                soup = BeautifulSoup(html or "", "html.parser")
                for t in soup(["script", "style", "noscript"]):
                    t.extract()
                return soup.get_text(" ", strip=True)
            except Exception:
                return ""

        def _matches(text: str, query: str) -> bool:
            if not text or len(text) < min_doc_chars:
                return False
            low = text.lower()

            for m in must_terms:
                if m and m not in low:
                    return False

            for n in neg:
                if n and re.search(rf"\b{re.escape(n)}\b", text, flags=re.IGNORECASE):
                    return False

            if q_pattern and not q_pattern.search(text):
                return False

            if query and not q_pattern:
                qt = [t for t in _tokenize(query) if t not in _STOPWORDS]
                if qt:
                    overlap = sum(1 for t in qt if t in low)
                    if overlap < min_term_overlap:
                        return False

            return True

        def _matches_any(text: str) -> bool:
            if not queries_to_run:
                return _matches(text, query_raw)
            for q in queries_to_run:
                if q and _matches(text, q):
                    return True
            return False

        # ---- Search backends ----
        def search_duckduckgo(q: str, n: int) -> List[str]:
            errors = []
            # 1. Try DDGS library (curl_cffi based)
            try:
                from ddgs import DDGS  # pip install duckduckgo_search
                with DDGS() as ddgs:
                    out = []
                    for r in ddgs.text(q, max_results=n, safesearch="off"):
                        u = r.get("href") or r.get("url")
                        if u:
                            out.append(u)
                    if out:
                        return out
            except Exception as e:
                errors.append(f"DDGS lib failed: {e}")

            # 2. Fallback: HTML scraping via requests
            import requests
            urls = []
            try:
                ua_fallback = (
                    user_agent
                    if "Mozilla" in user_agent
                    else "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                         "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
                )

                r = requests.get(
                    "https://html.duckduckgo.com/html/",
                    params={"q": q},
                    headers={"User-Agent": ua_fallback},
                    timeout=(timeout_sec, read_timeout),
                )
                if r.status_code == 200:
                    from bs4 import BeautifulSoup
                    soup = BeautifulSoup(r.text, "html.parser")
                    for a in soup.select(
                        "a.result__a, a.result__url, a.result__a.js-result-title-link"
                    ):
                        href = a.get("href")
                        if href and href.startswith("http"):
                            urls.append(href)
                            if len(urls) >= n:
                                break
                else:
                    errors.append(f"DDG HTML fallback failed: status {r.status_code}")
            except Exception as e:
                errors.append(f"DDG HTML fallback exception: {e}")

            if errors:
                meta["errors"].extend(errors)
            return urls

        def search_serpapi(q: str, n: int) -> List[str]:
            key = os.environ.get("SERPAPI_KEY")
            if not key:
                meta["errors"].append("SERPAPI_KEY missing")
                return []
            import requests

            try:
                r = requests.get(
                    "https://serpapi.com/search",
                    params={"engine": "google", "q": q, "num": n, "api_key": key},
                    timeout=(timeout_sec, read_timeout),
                )
                r.raise_for_status()
                data = r.json()
                out = []
                for item in (data.get("organic_results") or []):
                    u = item.get("link")
                    if u:
                        out.append(u)
                return out[:n]
            except Exception as e:
                meta["errors"].append(f"SerpApi failed: {e}")
                return []

        def search_google_cse(q: str, n: int) -> List[str]:
            cx = os.environ.get("GOOGLE_CSE_ID")
            key = os.environ.get("GOOGLE_API_KEY")
            if not (cx and key):
                meta["errors"].append("GOOGLE_CSE_ID or GOOGLE_API_KEY missing")
                return []
            import requests

            out = []
            try:
                for start in range(1, min(n, 10) + 1, 10):
                    r = requests.get(
                        "https://www.googleapis.com/customsearch/v1",
                        params={"q": q, "cx": cx, "key": key, "num": min(10, n), "start": start},
                        timeout=(timeout_sec, read_timeout),
                    )
                    r.raise_for_status()
                    data = r.json()
                    for item in (data.get("items") or []):
                        u = item.get("link")
                        if u:
                            out.append(u)
                    if len(out) >= n:
                        break
            except Exception as e:
                meta["errors"].append(f"Google CSE failed: {e}")
                return out[:n]
            return out[:n]

        # ---- Run searches for each query ----
        all_urls: List[str] = []
        search_errors = []

        for q in queries_to_run:
            if not q:
                continue
            try:
                if engine == "serpapi":
                    urls = search_serpapi(q, num_results)
                elif engine == "google_cse":
                    urls = search_google_cse(q, num_results)
                else:
                    urls = search_duckduckgo(q, num_results)
                all_urls.extend(urls)
            except Exception as e:
                tb = traceback.format_exc()
                search_errors.append(f"Search error for '{q}': {e}\n{tb}")

        if search_errors:
            meta["errors"].extend(search_errors)

        # Filter by site allow/deny, dedupe domains
        seen = set()
        filtered = []
        for u in all_urls:
            if not _allow_site(u):
                continue
            d = _clean_domain(u)
            if d in seen:
                continue
            seen.add(d)
            filtered.append(u)
        urls = filtered[:max_fetch] if max_fetch > 0 else filtered

        # ---- Fetch pages (async) ----
        docs_raw: List[Dict[str, Any]] = []

        async def _fetch_all():
            nonlocal docs_raw
            if not urls:
                return
            try:
                import aiohttp
            except ImportError:
                # Fallback: sync fetch if aiohttp is not available
                meta["errors"].append("aiohttp not found, falling back to requests")
                import requests

                for u in urls:
                    # DB first
                    db_entry = _load_from_db(u)
                    if db_entry:
                        db_title, db_text = db_entry
                        if _matches_any(db_text):
                            docs_raw.append({"title": db_title, "text": db_text, "url": u})
                        continue

                    html = _load_cache(u)
                    if not html:
                        try:
                            r = requests.get(
                                u,
                                headers={"User-Agent": user_agent},
                                timeout=(timeout_sec, read_timeout),
                            )
                            if r.status_code == 200 and r.text:
                                html = r.text
                                _save_cache(u, html)
                        except Exception:
                            html = ""
                    if not html:
                        continue

                    text = _extract_text(html, u)
                    if not _matches_any(text):
                        continue

                    title_guess = _clean_domain(u)
                    try:
                        from bs4 import BeautifulSoup
                        soup = BeautifulSoup(html, "html.parser")
                        t = (soup.title.string or "").strip() if soup.title else ""
                        if t:
                            title_guess = t
                    except Exception:
                        pass

                    _save_to_db(u, title_guess, text)
                    docs_raw.append({"title": title_guess, "text": text, "url": u})
                    time.sleep(pause)
                return

            timeout = aiohttp.ClientTimeout(
                total=None,
                sock_connect=timeout_sec,
                sock_read=read_timeout,
            )
            sem = asyncio.Semaphore(max(1, max_concurrent_fetch))

            async def _fetch_one(u: str, session: "aiohttp.ClientSession"):
                nonlocal docs_raw

                # DB first
                db_entry = _load_from_db(u)
                if db_entry:
                    db_title, db_text = db_entry
                    if _matches_any(db_text):
                        docs_raw.append({"title": db_title, "text": db_text, "url": u})
                    return

                html = _load_cache(u)
                if not html:
                    try:
                        await asyncio.sleep(pause)
                        async with sem:
                            async with session.get(
                                u,
                                headers={"User-Agent": user_agent},
                                timeout=timeout,
                            ) as resp:
                                if resp.status == 200:
                                    html_text = await resp.text()
                                    _save_cache(u, html_text)
                                    html = html_text
                                else:
                                    html = ""
                    except Exception:
                        html = ""

                if not html:
                    return

                text = _extract_text(html, u)
                if not _matches_any(text):
                    return

                title_guess = _clean_domain(u)
                try:
                    from bs4 import BeautifulSoup
                    soup = BeautifulSoup(html, "html.parser")
                    t = (soup.title.string or "").strip() if soup.title else ""
                    if t:
                        title_guess = t
                except Exception:
                    pass

                _save_to_db(u, title_guess, text)
                docs_raw.append({"title": title_guess, "text": text, "url": u})

            async with aiohttp.ClientSession(timeout=timeout) as session:
                tasks = [_fetch_one(u, session) for u in urls]
                await asyncio.gather(*tasks, return_exceptions=True)

        # Run the async fetcher, handling "loop already running" case
        try:
            if urls:
                try:
                    loop = asyncio.get_event_loop()
                except RuntimeError:
                    loop = None

                if not loop or not loop.is_running():
                    asyncio.run(_fetch_all())
                else:
                    exc_holder: Dict[str, BaseException] = {}

                    def _runner():
                        try:
                            new_loop = asyncio.new_event_loop()
                            asyncio.set_event_loop(new_loop)
                            new_loop.run_until_complete(_fetch_all())
                        except BaseException as e:
                            exc_holder["exc"] = e
                        finally:
                            new_loop.close()

                    t = Thread(target=_runner, daemon=True)
                    t.start()
                    t.join()
                    if "exc" in exc_holder:
                        raise exc_holder["exc"]
        except Exception as e:
            tb = traceback.format_exc()
            base = "" if payload is None else str(payload)
            meta.update({
                "rows": 0,
                "note": f"fetch failed: {e}",
                "traceback": tb,
                "engine": engine,
                "query": query_raw,
            })
            meta.setdefault("errors", []).append(f"Fetch error: {e}")
            return base, meta

        if not docs_raw:
            base = "" if payload is None else str(payload)
            meta.update({
                "rows": 0,
                "note": "no pages matched",
                "engine": engine,
                "query": query_raw,
                "regex": bool(q_pattern),
                "neg": neg,
                "must_terms": must_terms,
                "sites": {"include": site_include, "exclude": site_exclude},
                "urls_found": len(all_urls),
                "urls_filtered": len(urls),
            })
            return base, meta

        # ---- ranking BM25-ish (+ regex boost) ----
        corpus_tokens = [set(_tokenize(d["title"] + " " + d["text"])) for d in docs_raw]
        N = len(corpus_tokens)

        q_terms = set(_tokenize(query_raw)) if query_raw else set()
        df: Dict[str, int] = {}
        for terms in corpus_tokens:
            for t in terms:
                df[t] = df.get(t, 0) + 1

        def _bm25ish_score(doc_text: str) -> float:
            words = _tokenize(doc_text)
            L = len(words) or 1
            score = 0.0
            if q_terms:
                for t in q_terms:
                    tf = words.count(t)
                    if tf == 0:
                        continue
                    idf = log((N - df.get(t, 0) + 0.5) / (df.get(t, 0) + 0.5) + 1.0)
                    k1, b, avgdl = 1.2, 0.75, 2000.0
                    score += idf * ((tf * (k1 + 1)) / (tf + k1 * (1 - b + b * (L / avgdl))))
            if q_pattern and q_pattern.search(doc_text):
                score += 2.0
            return score

        ranked = sorted(
            docs_raw,
            key=lambda d: _bm25ish_score(d["title"] + " " + d["text"]),
            reverse=True,
        )[: max(1, top_k_docs)]

        # ---- optional JS + Network sniff on top URLs ----
        sniff_links: List[Dict[str, str]] = []
        sniff_media: List[Dict[str, str]] = []

        async def _run_sniffers_on_top_urls(urls_to_sniff: List[str]):
            nonlocal sniff_links, sniff_media
            if not urls_to_sniff:
                return
            from playwright.async_api import async_playwright

            self._ensure_sniffers(logger=logger)

            async with async_playwright() as p:
                browser = await p.chromium.launch(headless=True)
                context = await browser.new_context()

                try:
                    for u in urls_to_sniff:
                        log_buf: List[str] = []

                        # JS sniff
                        if use_js_sniffer and self._js_sniffer is not None:
                            try:
                                _, links = await self._js_sniffer.sniff(
                                    context,
                                    u,
                                    timeout=sniffer_timeout,
                                    log=log_buf,
                                    extensions=None,
                                )
                                sniff_links.extend(links)
                            except Exception as e:
                                if logger:
                                    logger.log_message(f"[WebCorpusBlock] JSSniffer error for {u}: {e}")

                        # Network sniff
                        if use_network_sniffer and self._net_sniffer is not None:
                            try:
                                _, media_items, _json_hits = await self._net_sniffer.sniff(
                                    context,
                                    u,
                                    timeout=sniffer_timeout,
                                    log=log_buf,
                                    extensions=None,
                                )
                                sniff_media.extend(media_items)
                            except Exception as e:
                                if logger:
                                    logger.log_message(f"[WebCorpusBlock] NetworkSniffer error for {u}: {e}")
                finally:
                    await context.close()
                    await browser.close()

        if (use_js_sniffer or use_network_sniffer) and ranked:
            top_urls_for_sniff = [d.get("url") for d in ranked if d.get("url")][:max_sniffer_pages]

            try:
                loop = None
                try:
                    loop = asyncio.get_event_loop()
                except RuntimeError:
                    loop = None

                if not loop or not loop.is_running():
                    asyncio.run(_run_sniffers_on_top_urls(top_urls_for_sniff))
                else:
                    exc_holder: Dict[str, BaseException] = {}

                    def _sniff_runner():
                        try:
                            new_loop = asyncio.new_event_loop()
                            asyncio.set_event_loop(new_loop)
                            new_loop.run_until_complete(_run_sniffers_on_top_urls(top_urls_for_sniff))
                        except BaseException as e:
                            exc_holder["exc"] = e
                        finally:
                            new_loop.close()

                    t = Thread(target=_sniff_runner, daemon=True)
                    t.start()
                    t.join()
                    if "exc" in exc_holder:
                        raise exc_holder["exc"]
            except Exception as e:
                meta.setdefault("errors", []).append(f"Sniffer error: {e}")

        # ---- sentence extraction ----
        hit_sents: List[str] = []
        per_doc_quota = max(1, top_k_sents // max(1, len(ranked)))
        for d in ranked:
            title = (d["title"] or "").strip()
            sents = _split_sents(d["text"] or "")
            scored: List[Tuple[float, int, str]] = []
            for idx, s in enumerate(sents):
                tok = set(_tokenize(s))
                overlap = len(tok & q_terms) if q_terms else 0
                if q_pattern and q_pattern.search(s):
                    overlap += 2
                if overlap > 0:
                    scored.append((float(overlap), idx, s))

            took = 0
            for _, idx, _ in sorted(scored, key=lambda x: (-x[0], x[1]))[:per_doc_quota]:
                lo = max(0, idx - sent_window)
                hi = min(len(sents), idx + sent_window + 1)
                chunk = " ".join(sents[lo:hi]).strip()
                if chunk and chunk not in hit_sents:
                    if title and (not hit_sents or not hit_sents[-1].startswith("# ")):
                        src = f"# {title} — {d.get('url', '')}".strip()
                        hit_sents.append(src)
                    hit_sents.append(chunk)
                    took += 1

            if took == 0 and sents:
                chunk = " ".join(sents[: max(1, sent_window + 1)]).strip()
                if chunk and chunk not in hit_sents:
                    if title and (not hit_sents or not hit_sents[-1].startswith("# ")):
                        src = f"# {title} — {d.get('url', '')}".strip()
                        hit_sents.append(src)
                    hit_sents.append(chunk)

        context = "\n\n".join(hit_sents).strip()
        if max_chars > 0 and len(context) > max_chars:
            context = context[:max_chars] + "…"

        # ---- lexicon (from context) ----
        def _extract_terms_local(text: str, *, top_k: int = 50, min_len: int = 4) -> List[str]:
            counts: Dict[str, int] = {}
            for raw in text.split():
                w = "".join(ch.lower() for ch in raw if ch.isalnum() or ch in "-_")
                if len(w) < min_len or w in _STOPWORDS:
                    continue
                counts[w] = counts.get(w, 0) + 1
            return [t for t, _ in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:top_k]]

        lexicon = _extract_terms_local(context, top_k=lexicon_top_k, min_len=lexicon_min_len) if context else []
        if use_phrases and context:
            phrases = re.findall(
                r"\b([A-Za-z0-9][A-Za-z0-9_\-]+(?:\s+[A-Za-z0-9][A-Za-z0-9_\-]+){1,3})\b",
                context,
            )
            pc: Dict[str, int] = {}
            for ph in phrases:
                ph = ph.lower().strip()
                if any(tok in _STOPWORDS for tok in ph.split()):
                    continue
                pc[ph] = pc.get(ph, 0) + 1
            phrase_top = [p for p, _ in sorted(pc.items(), key=lambda kv: (-kv[1], kv[0]))[:10]]
            lexicon = list(dict.fromkeys(phrase_top + lexicon))[:lexicon_top_k]

        # ---- store lexicon + context in Memory ----
        if export_lexicon and lexicon:
            store_mem = Memory.load()
            store_mem[lexicon_key] = lexicon
            Memory.save(store_mem)

        if export_context and context:
            store_mem = Memory.load()
            if append_ctx and isinstance(store_mem.get(context_key), str) and store_mem[context_key]:
                store_mem[context_key] = store_mem[context_key].rstrip() + "\n\n" + context
            else:
                store_mem[context_key] = context
            Memory.save(store_mem)

        # ---- compose output ----
        base = "" if payload is None else str(payload)
        parts: List[str] = [base] if base else []
        if inject_lexicon and lexicon:
            parts.append("[lexicon]\n" + ", ".join(lexicon))
        if inject_context and context:
            parts.append("[context]\n" + context)
        out = "\n\n".join(parts).strip()

        meta.update({
            "engine": engine,
            "query": query_raw,
            "regex": bool(q_pattern),
            "neg": neg,
            "must_terms": must_terms,
            "rows": len(docs_raw),
            "ranked_docs": len(ranked),
            "lexicon_key": lexicon_key if (export_lexicon and lexicon) else None,
            "lexicon_size": len(lexicon),
            "context_key": context_key if (export_context and context) else None,
            "context_len": len(context),
            "top_urls": [d.get("url") for d in ranked],
            "site_include": site_include,
            "site_exclude": site_exclude,
            "min_term_overlap": min_term_overlap,
            "db_path": db_path if use_db_cache else None,
            "use_js_sniffer": use_js_sniffer,
            "use_network_sniffer": use_network_sniffer,
            "sniffer_timeout": sniffer_timeout,
            "sniff_links": sniff_links,      # normalized {url,text,tag}
            "sniff_media": sniff_media,      # normalized {url,text,tag,kind,content_type,size}
        })
        return out, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "",
            "subpipeline": "",
            "prompt_query.op": "clean_permutate",
            "engine": "duckduckgo, google_cse",
            "num_results": 10,
            "max_fetch": 8,
            "timeout": 8.0,
            "read_timeout": 12.0,
            "pause": 0.7,
            "max_concurrent_fetch": 4,
            "regex": None,
            "neg": "",
            "must_terms": "",
            "top_k_docs": 6,
            "top_k_sents": 18,
            "sent_window": 1,
            "max_chars": 2800,
            "min_doc_chars": 400,
            "site_include": "",
            "site_exclude": "",
            "lexicon_key": "web_lexicon",
            "context_key": "web_context",
            "append_context": False,
            "min_term_overlap": 1,
            "db_path": "webcorpus.db",
            "use_db_cache": True,
            "export_lexicon": True,
            "inject_lexicon": True,
            "inject_context": True,
            "lexicon_top_k": 40,
            "lexicon_min_len": 4,
            "lexicon_phrases": True,
            "export_context": True,
            # Sniffer options
            "use_js_sniffer": False,
            "use_network_sniffer": False,
            "sniffer_timeout": 8.0,
            "max_sniffer_pages": 4,
        }

BLOCKS.register("webcorpus", WebCorpusBlock)

# ================WebCorpus (Playwright Hybrid) ================
@dataclass
class PlaywrightBlock(BaseBlock):
    """
    Playwright-powered corpus builder (Hybrid v8.1):

      • Optional `subpipeline` to expand the raw query into multiple queries.
      • Hybrid search via DuckDuckGo (DDGS lib + HTML fallback).
      • Async Playwright scraping with optional:
           - NetworkSniffer (media detection + manifests + SAFE JSON sniff)
           - JSSniffer      (DOM/script link discovery)
      • Text extraction via trafilatura from final HTML.
      • Caches pages + sniff results in sqlite via DatabaseSubmanager + PlaywrightCorpusStore.
      • BM25-ish re-ranking + sentence extraction.
      • Lexicon/context export into Memory.
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os, re, json, time, sys, asyncio
        from math import log
        from typing import List, Dict, Tuple, Set
        from urllib.parse import urlparse
        from collections import defaultdict
        from threading import Thread

        try:
            import trafilatura
            from ddgs import DDGS
            from bs4 import BeautifulSoup
            import requests
            from playwright.async_api import async_playwright
        except ImportError:
            print("[PlaywrightBlock] ERROR: Missing dependencies. Please run:", file=sys.stderr)
            print("pip install playwright trafilatura duckduckgo_search beautifulsoup4 requests", file=sys.stderr)
            print("python -m playwright install --with-deps chromium", file=sys.stderr)
            return str(payload), {"error": "Missing dependencies. See console."}

        # ---- Base raw query ----
        query_raw = str(params.get("query", "") or str(payload or "")).strip()

        # ---- Optional subpipeline expansion ----
        subpipe_name = str(params.get("subpipeline", "")).strip()
        if subpipe_name:
            queries_to_run: Any = self.run_sub_pipeline(
                initial_value=query_raw,
                pipeline_param_name="subpipeline",
                parent_params=params,
            )
            if isinstance(queries_to_run, str):
                queries_to_run = [queries_to_run]
            elif not isinstance(queries_to_run, list):
                queries_to_run = [query_raw] if query_raw else []
        else:
            queries_to_run = [query_raw] if query_raw else []

        queries_to_run = [q.strip() for q in queries_to_run if str(q).strip()]

        if not queries_to_run:
            base = "" if payload is None else str(payload)
            return base, {
                "rows": 0,
                "note": "empty query",
                "engine": "hybrid_ddgs_playwright",
                "query": query_raw,
                "queries_run": [],
            }

        # Canonical query for BM25 / overlap
        query = query_raw or queries_to_run[0]

        # ---- Params ----
        num_results = int(params.get("num_results", 15))
        headless = bool(params.get("headless", True))
        timeout_sec = float(params.get("timeout", 15.0))
        read_timeout = float(params.get("read_timeout", 12.0))
        user_agent = str(params.get(
            "user_agent",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36"
        ))
        verbose = bool(params.get("verbose", False))

        # NEW: toggle sniffers
        use_network_sniff = bool(params.get("use_network_sniff", False))
        use_js_sniff = bool(params.get("use_js_sniff", False))

        # DB / store
        db_path = str(params.get("db_path", os.path.join(APP_DIR, "webcorpus.db")))
        use_db_cache = bool(params.get("use_db_cache", True))
        db_config = submanagers.DatabaseConfig(path=db_path)
        dbm = submanagers.DatabaseSubmanager(db_config)
        store = PlaywrightCorpusStore(dbm)
        store.ensure_schema()

        # Target & Learning
        default_targets = "grailed.com,hypebeast.com,vogue.com,depop.com,poshmark.com"
        target_sites = str(params.get("target_sites", default_targets))
        num_per_site = int(params.get("num_per_site", 2))
        num_general = int(params.get("num_general", 10))

        learn_new_sites = bool(params.get("learn_new_sites", True))
        learned_sites_key = str(params.get("learned_sites_key", "web_learned_sites"))
        learn_min_hits = int(params.get("learn_min_hits", 2))
        default_junk = (
            "pinterest.com,twitter.com,facebook.com,reddit.com,ebay.com,"
            "walmart.com,amazon.com,youtube.com,tiktok.com,instagram.com,linkedin.com"
        )
        junk_domains = str(params.get("junk_domains", default_junk))

        # text handling
        regex_query = params.get("regex")
        neg = [s.strip() for s in str(params.get("neg", "")).split(",") if s.strip()]
        must_terms = [s.strip().lower() for s in str(params.get("must_terms", "")).split(",") if s.strip()]
        top_k_docs = int(params.get("top_k_docs", 10))
        top_k_sents = int(params.get("top_k_sents", 25))
        sent_window = int(params.get("sent_window", 1))
        max_chars = int(params.get("max_chars", 4000))
        min_doc_chars = int(params.get("min_doc_chars", 250))
        site_exclude = [s.strip().lower() for s in str(params.get("site_exclude", "")).split(",") if s.strip()]
        min_term_overlap = int(params.get("min_term_overlap", 1))

        # lexicon export
        export_lexicon = bool(params.get("export_lexicon", True))
        lexicon_key = str(params.get("lexicon_key", "web_lexicon"))
        inject_lexicon = bool(params.get("inject_lexicon", True))
        inject_context = bool(params.get("inject_context", True))
        lexicon_top_k = int(params.get("lexicon_top_k", 40))
        lexicon_min_len = int(params.get("lexicon_min_len", 4))
        use_phrases = bool(params.get("lexicon_phrases", True))
        export_context = bool(params.get("export_context", True))
        context_key = str(params.get("context_key", "web_context"))
        append_ctx = bool(params.get("append_context", False))

        timeout_ms = int(timeout_sec * 1000)
        meta: Dict[str, Any] = {
            "engine": "hybrid_ddgs_playwright",
            "query": query_raw,
            "queries_run": queries_to_run,
            "headless": headless,
            "search_results": [],
            "scrape_errors": [],
            "scraped_urls": [],
            "search_method": "unknown",
            "learned_sites": [],
            "newly_learned": [],
            "db_path": db_path if use_db_cache else None,
            "sniffer_stats": {},
            "use_network_sniff": use_network_sniff,
            "use_js_sniff": use_js_sniff,
        }

        # compile regex
        q_pattern = re.compile(regex_query, re.IGNORECASE) if isinstance(regex_query, str) and regex_query.strip() else None

        # ---- Helpers ----
        def _tokenize(t: str) -> List[str]:
            return re.findall(r"[A-Za-z0-9][A-Za-z0-9_\-]+", (t or "").lower())

        def _split_sents(text: str) -> List[str]:
            bits = re.split(r"(?<=[.!?])\s+|\n+", (text or "").strip())
            return [b.strip() for b in bits if b.strip()]

        def _clean_domain(u: str) -> str:
            try:
                netloc = urlparse(u).netloc.lower()
                parts = netloc.split(".")
                if len(parts) > 2 and parts[0] in ("www", "m", "blog", "shop"):
                    return ".".join(parts[1:])
                return netloc.split(":")[0]
            except Exception:
                return ""

        def _term_overlap_ok(text: str) -> bool:
            if not query or min_term_overlap <= 0:
                return True
            qt = [t for t in _tokenize(query) if t not in _STOPWORDS]
            if not qt:
                return True
            low = text.lower()
            overlap = sum(1 for t in qt if t in low)
            return overlap >= min_term_overlap

        def _matches_filters(text: str) -> bool:
            if not text or len(text) < min_doc_chars:
                return False
            low = text.lower()

            for m in must_terms:
                if m and m not in low:
                    return False
            for n in neg:
                if n and re.search(rf"\b{re.escape(n)}\b", text, flags=re.IGNORECASE):
                    return False
            if q_pattern and not q_pattern.search(text):
                return False
            if not _term_overlap_ok(text):
                return False
            return True

        # ---- Hybrid search helper ----
        def _hybrid_search(q: str, n: int) -> List[Dict[str, str]]:
            try:
                if verbose:
                    print(f"[PlaywrightBlock] Searching (DDGS) for: {q}", file=sys.stderr)
                with DDGS() as ddgs:
                    out = []
                    for r in ddgs.text(q, max_results=n, safesearch="off"):
                        url = r.get("href") or r.get("url")
                        title = r.get("title") or _clean_domain(url)
                        if url:
                            out.append({"title": title, "url": url})
                if out:
                    meta["search_method"] = "ddgs_library"
                    return out
            except Exception as e:
                if verbose:
                    print(f"[PlaywrightBlock] DDGS failed: {e}", file=sys.stderr)

            if verbose:
                print(f"[PlaywrightBlock] Searching (HTML fallback) for: {q}", file=sys.stderr)
            urls = []
            try:
                r = requests.get(
                    "https://duckduckgo.com/html/",
                    params={"q": q},
                    headers={"User-Agent": user_agent},
                    timeout=(timeout_sec, read_timeout),
                )
                if r.status_code == 200:
                    soup = BeautifulSoup(r.text, "html.parser")
                    for a in soup.select("a.result__a, a.result__url, a.result__a.js-result-title-link"):
                        href = a.get("href")
                        title = a.get_text(strip=True) or _clean_domain(href)
                        if href and href.startswith("http"):
                            urls.append({"title": title, "url": href})
                            if len(urls) >= n:
                                break
                if urls:
                    meta["search_method"] = "requests_fallback"
                    return urls
            except Exception as e:
                if verbose:
                    print(f"[PlaywrightBlock] HTML fallback failed: {e}", file=sys.stderr)

            meta["search_method"] = "failed"
            return []

        # ---- 1. SEARCH (per query + targeted sites) ----
        docs_raw: List[Dict[str, str]] = []
        if not query:
            base = "" if payload is None else str(payload)
            return base, {"rows": 0, "note": "empty query", "engine": "playwright_hybrid"}

        search_links: List[Dict[str, str]] = []
        seen_urls: Set[str] = set()
        store_mem = Memory.load()

        sites_to_search: Set[str] = set()
        for s in target_sites.split(","):
            if s.strip():
                sites_to_search.add(s.strip())
        if learn_new_sites:
            learned_sites = store_mem.get(learned_sites_key, [])
            if isinstance(learned_sites, list):
                for s in learned_sites:
                    sites_to_search.add(str(s))
        meta["learned_sites"] = list(sites_to_search)

        junk_list: Set[str] = set()
        for s in junk_domains.split(","):
            if s.strip():
                junk_list.add(s.strip())
        for s in site_exclude:
            if s.strip():
                junk_list.add(s.strip())

        try:
            if verbose:
                print(f"[PlaywrightBlock] Running targeted search on {len(sites_to_search)} known sites...", file=sys.stderr)
            for site in sites_to_search:
                targeted_query = f"{query} site:{site}"
                links = _hybrid_search(targeted_query, n=num_per_site)
                for link in links:
                    url = link["url"]
                    if url not in seen_urls:
                        seen_urls.add(url)
                        search_links.append(link)

            if verbose:
                print(f"[PlaywrightBlock] Running general search for expanded queries...", file=sys.stderr)

            new_domain_counts: Dict[str, int] = defaultdict(int)
            discovered_links: List[Dict[str, str]] = []

            for q in queries_to_run:
                general_links = _hybrid_search(q, n=num_general)
                for link in general_links:
                    url = link["url"]
                    if url in seen_urls:
                        continue
                    domain = _clean_domain(url)
                    if not domain:
                        continue
                    if any(domain == s or domain.endswith("." + s) for s in junk_list):
                        continue
                    if any(domain == s or domain.endswith("." + s) for s in sites_to_search):
                        continue

                    search_text = (link.get("title", "") + " " + url)
                    if not _term_overlap_ok(search_text):
                        discovered_links.append(link)
                        seen_urls.add(url)
                        continue

                    new_domain_counts[domain] += 1
                    discovered_links.append(link)
                    seen_urls.add(url)

            newly_learned_sites: List[str] = []
            if learn_new_sites:
                for domain, count in new_domain_counts.items():
                    if count >= learn_min_hits:
                        newly_learned_sites.append(domain)
                if newly_learned_sites:
                    if verbose:
                        print(f"[PlaywrightBlock] Learning new domains: {newly_learned_sites}", file=sys.stderr)
                    current_learned = set(store_mem.get(learned_sites_key, []))
                    current_learned.update(newly_learned_sites)
                    store_mem[learned_sites_key] = list(current_learned)
                    Memory.save(store_mem)
                    meta["newly_learned"] = newly_learned_sites

            search_links.extend(discovered_links)
            search_links = search_links[:num_results]
            meta["search_results"] = search_links

            if verbose:
                print(f"[PlaywrightBlock] Total {len(search_links)} links to scrape.", file=sys.stderr)
            if not search_links:
                print(f"[PlaywrightBlock] ERROR: No search results for queries: {queries_to_run}", file=sys.stderr)

        except Exception as e:
            print(f"[PlaywrightBlock] FATAL ERROR during search step: {e}", file=sys.stderr)
            return str(payload), {"error": f"Search failed: {e}", **meta}

        # ---- 2. SCRAPE via async Playwright (+ optional sniffers) ----
        async def _run_playwright_scrape():
            nonlocal docs_raw, meta
            if not search_links:
                return

            if verbose:
                print(f"[PlaywrightBlock] Launching async browser (headless={headless})...", file=sys.stderr)

            async with async_playwright() as p:
                browser = await p.chromium.launch(
                    headless=headless,
                    args=["--disable-blink-features=AutomationControlled"],
                )
                context = await browser.new_context(
                    user_agent=user_agent,
                    java_script_enabled=True,
                )
                context.set_default_timeout(timeout_ms)

                net_sniffer = submanagers.NetworkSniffer() if use_network_sniff else None
                js_sniffer = submanagers.JSSniffer() if use_js_sniff else None

                sniffer_stats: Dict[str, Any] = {}

                for link in search_links:
                    url = link["url"]
                    title_guess = (link.get("title") or _clean_domain(url) or "").strip()

                    # ---- DB cache ----
                    cached = store.load_page(url) if use_db_cache else None
                    if cached:
                        text_cached = cached.get("content") or ""
                        if _matches_filters(text_cached):
                            if verbose:
                                print(f"[PlaywrightBlock] Using DB cache: {url}", file=sys.stderr)
                            docs_raw.append({
                                "title": cached.get("title") or title_guess,
                                "text": text_cached,
                                "url": url,
                            })
                            meta["scraped_urls"].append(url)
                            continue

                    try:
                        if verbose:
                            print(f"[PlaywrightBlock] Scraping: {url}", file=sys.stderr)

                        log_list: List[str] = []
                        html = ""
                        js_links: List[dict] = []
                        net_items: List[dict] = []
                        json_hits: List[dict] = []

                        # ---- Optional sniffers ----
                        if net_sniffer:
                            if verbose:
                                print(f"[PlaywrightBlock]  - NetworkSniffer enabled", file=sys.stderr)
                            html_net, net_items, json_hits = await net_sniffer.sniff(
                                context,
                                url,
                                timeout=timeout_sec,
                                log=log_list,
                                extensions=None,
                            )
                        else:
                            html_net = ""

                        if js_sniffer:
                            if verbose:
                                print(f"[PlaywrightBlock]  - JSSniffer enabled", file=sys.stderr)
                            html_js, js_links = await js_sniffer.sniff(
                                context,
                                url,
                                timeout=timeout_sec,
                                log=log_list,
                                extensions=None,
                            )
                        else:
                            html_js = ""

                        html = html_net or html_js or ""

                        # If sniffers are disabled OR did not produce HTML, do a direct Playwright fetch
                        if not html:
                            if verbose:
                                print(f"[PlaywrightBlock]  - Using direct Playwright fetch for {url}", file=sys.stderr)
                            page = await context.new_page()
                            try:
                                await page.goto(url, timeout=timeout_ms, wait_until="domcontentloaded")
                                await page.wait_for_timeout(1000)
                                html = await page.content()
                            finally:
                                try:
                                    await page.close()
                                except Exception:
                                    pass

                        if not html:
                            if verbose:
                                print(f"[PlaywrightBlock] No HTML captured for {url}", file=sys.stderr)
                            continue

                        text = trafilatura.extract(
                            html,
                            include_comments=False,
                            include_tables=False,
                            deduplicate=True,
                        ) or ""

                        if not _matches_filters(text):
                            if verbose:
                                print(f"[PlaywrightBlock] Filters rejected {url}", file=sys.stderr)
                            continue

                        # Save to store
                        store.save_page(
                            url=url,
                            title=title_guess,
                            content=text,
                            html=html,
                            js_links=js_links,
                            net_items=net_items,
                            json_hits=json_hits,
                        )

                        docs_raw.append({"title": title_guess, "text": text, "url": url})
                        meta["scraped_urls"].append(url)

                        if net_sniffer or js_sniffer:
                            sniffer_stats[url] = {
                                "media_items": len(net_items),
                                "json_hits": len(json_hits),
                                "js_links": len(js_links),
                                "log_lines": len(log_list),
                            }

                    except Exception as e:
                        err_msg = f"{url}: {str(e)[:140]}"
                        if verbose:
                            print(f"[PlaywrightBlock] SCRAPE_ERROR: {err_msg}", file=sys.stderr)
                        meta["scrape_errors"].append(err_msg)

                meta["sniffer_stats"] = sniffer_stats

                if verbose:
                    print(f"[PlaywrightBlock] Closing async browser.", file=sys.stderr)
                await browser.close()

        try:
            if search_links:
                try:
                    loop = asyncio.get_event_loop()
                except RuntimeError:
                    loop = None

                if not loop or not loop.is_running():
                    asyncio.run(_run_playwright_scrape())
                else:
                    exc_holder: Dict[str, BaseException] = {}

                    def _runner():
                        try:
                            new_loop = asyncio.new_event_loop()
                            asyncio.set_event_loop(new_loop)
                            new_loop.run_until_complete(_run_playwright_scrape())
                        except BaseException as e:
                            exc_holder["exc"] = e
                        finally:
                            new_loop.close()

                    t = Thread(target=_runner, daemon=True)
                    t.start()
                    t.join()
                    if "exc" in exc_holder:
                        raise exc_holder["exc"]

        except Exception as e:
            print(f"[PlaywrightBlock] FATAL ERROR during Playwright scrape: {e}", file=sys.stderr)
            return str(payload), {"error": f"Playwright execution failed: {e}", **meta}

        # ---- 3. Post-processing (BM25 + sentence extraction + lexicon) ----
        if verbose:
            print(f"[PlaywrightBlock] Post-processing {len(docs_raw)} documents...", file=sys.stderr)

        if not docs_raw:
            base = "" if payload is None else str(payload)
            print(f"[PlaywrightBlock] ERROR: No pages were successfully scraped.", file=sys.stderr)
            return base, {
                "rows": 0,
                "note": "no pages matched or scraped",
                "engine": "playwright_hybrid",
                "query": query,
                "regex": bool(q_pattern),
                "neg": neg,
                "must_terms": must_terms,
                **meta,
            }

        corpus_tokens = [set(_tokenize(d["title"] + " " + d["text"])) for d in docs_raw]
        N = len(corpus_tokens)
        q_terms = set(_tokenize(query))
        df: Dict[str, int] = {}
        for terms in corpus_tokens:
            for t in terms:
                df[t] = df.get(t, 0) + 1

        def _bm25ish_score(doc_text: str, doc_url: str) -> float:
            words = _tokenize(doc_text)
            L = len(words) or 1
            score = 0.0
            if q_terms:
                for t in q_terms:
                    tf = words.count(t)
                    if tf == 0:
                        continue
                    idf = log((N - df.get(t, 0) + 0.5) / (df.get(t, 0) + 0.5) + 1.0)
                    k1, b, avgdl = 1.2, 0.75, 2000.0
                    score += idf * ((tf * (k1 + 1)) / (tf + k1 * (1 - b + b * (L / avgdl))))
            if q_pattern and q_pattern.search(doc_text):
                score += 2.0

            doc_domain = _clean_domain(doc_url)
            if any(doc_domain == s or doc_domain.endswith("." + s) for s in sites_to_search):
                score += 1.0
            return score

        ranked = sorted(
            docs_raw,
            key=lambda d: _bm25ish_score(d["title"] + " " + d["text"], d["url"]),
            reverse=True,
        )[: max(1, top_k_docs)]

        hit_sents: List[str] = []
        per_doc_quota = max(1, top_k_sents // max(1, len(ranked)))
        for d in ranked:
            title = (d["title"] or "").strip()
            sents = _split_sents(d["text"] or "")
            scored: List[Tuple[float, int, str]] = []
            for idx, s in enumerate(sents):
                tok = set(_tokenize(s))
                overlap = len(tok & q_terms) if q_terms else 0
                if q_pattern and q_pattern.search(s):
                    overlap += 2
                if overlap > 0:
                    scored.append((float(overlap), idx, s))

            took = 0
            for _, idx, _ in sorted(scored, key=lambda x: (-x[0], x[1]))[:per_doc_quota]:
                lo = max(0, idx - sent_window)
                hi = min(len(sents), idx + sent_window + 1)
                chunk = " ".join(sents[lo:hi]).strip()
                if chunk and chunk not in hit_sents:
                    src = f"# {title} — {d.get('url', '')}".strip()
                    if src not in hit_sents:
                        hit_sents.append(src)
                    hit_sents.append(chunk)
                    took += 1

            if took == 0 and sents:
                chunk = " ".join(sents[: max(1, sent_window + 1)]).strip()
                if chunk and chunk not in hit_sents:
                    src = f"# {title} — {d.get('url', '')}".strip()
                    if src not in hit_sents:
                        hit_sents.append(src)
                    hit_sents.append(chunk)

        context = "\n\n".join(hit_sents).strip()
        if max_chars > 0 and len(context) > max_chars:
            context = context[:max_chars] + "…"

        def _extract_terms_local(text: str, *, top_k: int = 50, min_len: int = 4) -> List[str]:
            counts: Dict[str, int] = {}
            for raw in text.split():
                w = "".join(ch.lower() for ch in raw if ch.isalnum() or ch in "-_")
                if len(w) < min_len or w in _STOPWORDS:
                    continue
                counts[w] = counts.get(w, 0) + 1
            return [t for t, _ in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:top_k]]

        lexicon = _extract_terms_local(context, top_k=lexicon_top_k, min_len=lexicon_min_len) if context else []
        if use_phrases and context:
            phrases = re.findall(
                r"\b([A-Za-z0-9][A-Za-z0-9_\-]+(?:\s+[A-Za-z0-9][A-Za-z0-9_\-]+){1,3})\b",
                context,
            )
            pc: Dict[str, int] = {}
            for ph in phrases:
                ph = ph.lower().strip()
                if any(tok in _STOPWORDS for tok in ph.split()):
                    continue
                pc[ph] = pc.get(ph, 0) + 1
            phrase_top = [p for p, _ in sorted(pc.items(), key=lambda kv: (-kv[1], kv[0]))[:10]]
            lexicon = list(dict.fromkeys(phrase_top + lexicon))[:lexicon_top_k]

        if export_lexicon and lexicon:
            store_mem = Memory.load()
            store_mem[lexicon_key] = lexicon
            Memory.save(store_mem)
            if verbose:
                print(f"[PlaywrightBlock] Exported {len(lexicon)} terms to memory[{lexicon_key}]", file=sys.stderr)

        if export_context and context:
            store_mem = Memory.load()
            if append_ctx and isinstance(store_mem.get(context_key), str) and store_mem[context_key]:
                store_mem[context_key] = store_mem[context_key].rstrip() + "\n\n" + context
            else:
                store_mem[context_key] = context
            Memory.save(store_mem)
            if verbose:
                print(f"[PlaywrightBlock] Exported {len(context)} chars to memory[{context_key}]", file=sys.stderr)

        base = "" if payload is None else str(payload)
        parts: List[str] = [base] if base else []
        if inject_lexicon and lexicon:
            parts.append("[lexicon]\n" + ", ".join(lexicon))
        if inject_context and context:
            parts.append("[context]\n" + context)
        out = "\n\n".join(parts).strip()

        if verbose:
            print(f"[PlaywrightBlock] Execution complete. Outputting {len(out)} chars.", file=sys.stderr)

        meta.update({
            "rows": len(docs_raw),
            "ranked_docs": len(ranked),
            "lexicon_key": lexicon_key if (export_lexicon and lexicon) else None,
            "lexicon_size": len(lexicon),
            "context_key": context_key if (export_context and context) else None,
            "context_len": len(context),
            "top_urls": [d.get("url") for d in ranked],
            "site_exclude": site_exclude,
            "junk_domains": list(junk_list),
            "neg": neg,
            "must_terms": must_terms,
            "min_term_overlap": min_term_overlap,
        })
        return out, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "",
            "subpipeline": "",
            "num_results": 15,
            "headless": True,
            "timeout": 15.0,
            "read_timeout": 12.0,
            "verbose": False,
            "target_sites": "grailed.com,hypebeast.com,vogue.com,depop.com,poshmark.com",
            "num_per_site": 2,
            "num_general": 10,
            "learn_new_sites": True,
            "learned_sites_key": "web_learned_sites",
            "junk_domains": "pinterest.com,twitter.com,facebook.com",
            "top_k_docs": 10,
            "top_k_sents": 25,
            "max_chars": 4000,
            "min_doc_chars": 250,
            "lexicon_key": "web_lexicon",
            "context_key": "web_context",
            "append_context": False,
            "min_term_overlap": 1,
            "db_path": "webcorpus.db",
            "use_db_cache": True,
            # NEW:
            "use_network_sniff": False,
            "use_js_sniff": False,
        }


BLOCKS.register("playwright", PlaywrightBlock)


@dataclass
class TensorBlock(BaseBlock):
    """
    Runs a local Hugging Face transformers model for tasks like
    classification, NER, text-generation, etc. to add "intelligence"
    to the payload and pipeline.

    Features:
    - Tasks: zero-shot-classification, ner, sentiment-analysis,
             text2text-generation, summarization.
    - `device="auto"` for GPU support.
    - `auto_keywords_key="mem_key"`: Automatically extracts keywords/entities
      from NER or generation and saves them to a memory key for other
      blocks (like WebCorpus) to use.
    - `generation_prompt="task: {payload}"`: Template for generation tasks.
      For summarization, this acts as an *instruction line*.
    - `context_key="topic_context"`: For summarization, read context from Memory.
    - `max_input_chars=4000`: Clamp long contexts before sending to the model.
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        text = str(payload or "")
        if not text:
            return "", {"error": "TensorBlock received empty payload."}

        # --- Core params ---
        raw_task = str(params.get("task", "zero-shot-classification"))
        task = raw_task
        hf_task = raw_task  # what we actually pass to _get_hf_pipeline

        # Alias code-generation -> text2text-generation HF pipeline
        if raw_task == "code-generation":
            hf_task = "text2text-generation"
            task = "code-generation"

        model = params.get("model")  # None lets HF pipeline pick default
        model_name = str(model) if model else f"default_for_{hf_task}"
        device = params.get("device", "auto")
        verbose = bool(params.get("verbose", False))
        auto_keywords_key = params.get("auto_keywords_key")

        # Prompt template for generation-like tasks
        generation_prompt = str(params.get("generation_prompt", "{payload}"))

        output_key = params.get("output_key")
        inject_format = str(params.get("inject_format", "simple")).lower()
        inject_tag = str(params.get("inject_tag", task))
        sep = str(params.get("sep", "\n\n"))

        # New: context support for summarization
        context_key = str(params.get("context_key", "topic_context"))
        max_input_chars = int(params.get("max_input_chars", 4000))

        meta: Dict[str, Any] = {
            "task": task,
            "hf_task": hf_task,
            "model": model_name,
        }

        pipe = _get_hf_pipeline(
            hf_task,  # <--- use hf_task here
            model_name if model else None,
            device=device,
            verbose=verbose,
        )
        if pipe is None:
            return text, {"error": "Failed to load HF pipeline. See console logs.", "meta": meta}
        meta["device"] = str(pipe.device)

        # --- Task-specific arguments ---
        kwargs: Dict[str, Any] = {}
        run_text = text  # default input to pipeline

        if task == "zero-shot-classification":
            labels = str(params.get("labels", "general,technical,creative")).split(",")
            labels = [l.strip() for l in labels if l.strip()]
            if not labels:
                return text, {"error": "zero-shot-classification requires 'labels' param."}
            kwargs["candidate_labels"] = labels
            meta["labels"] = labels

        elif task == "ner":
            kwargs["grouped_entities"] = bool(params.get("grouped_entities", True))

        elif task in ("text2text-generation", "code-generation"):
            # Use the payload inside a template, e.g. "Rewrite this: {payload}"
            run_text = generation_prompt.format(payload=text)
            kwargs["max_new_tokens"] = int(params.get("max_new_tokens", 50))
            kwargs["do_sample"] = bool(params.get("do_sample", False))

        elif task == "summarization":
            # --- Context-aware summarization ---
            # 1) Load context from Memory (e.g. topic_context)
            context_text = ""
            try:
                store = Memory.load()
                raw_ctx = store.get(context_key, "")
                if isinstance(raw_ctx, str):
                    context_text = raw_ctx
                elif isinstance(raw_ctx, list):
                    # allow list-of-lines style storage
                    context_text = "\n".join(map(str, raw_ctx))
            except Exception as e:
                meta["context_error"] = f"Failed to load context from Memory: {e}"

            # Fallback to payload if we somehow have no context
            if not context_text.strip():
                context_text = text

            # 2) Clamp the context length
            if max_input_chars > 0 and len(context_text) > max_input_chars:
                context_text = context_text[:max_input_chars]
            meta["context_chars"] = len(context_text)
            meta["context_key_used"] = context_key

            # 3) Build an instruction line from generation_prompt
            #    e.g., "Summarize the following context about {payload}: {payload}"
            try:
                instruction = generation_prompt.format(payload=text, context=context_text)
            except Exception:
                instruction = generation_prompt.replace("{payload}", text)

            instruction = instruction.strip()
            if instruction:
                run_text = instruction + "\n\n" + context_text
            else:
                run_text = context_text

            # 4) Standard summarization kwargs
            kwargs["min_length"] = int(params.get("min_length", 10))
            # Support either max_length or max_new_tokens param names
            max_len = params.get("max_length", params.get("max_new_tokens", 100))
            kwargs["max_length"] = int(max_len)

        # --- Run Prediction ---
        try:
            prediction = pipe(run_text, **kwargs)
            meta["prediction_raw"] = prediction
        except Exception as e:
            return text, {"error": f"Prediction failed: {e}", "meta": meta}

        # --- Optional: persist raw prediction to Memory ---
        if output_key:
            try:
                store = Memory.load()
                store[output_key] = prediction
                Memory.save(store)
                meta["output_key"] = output_key
            except Exception as e:
                meta["memory_error"] = str(e)

        # --- Auto keyword extraction ---
        keywords_to_save: List[str] = []
        if auto_keywords_key:
            try:
                if task == "ner" and prediction:
                    # HF NER returns list[dict]
                    keywords_to_save = [e.get("word", "").strip()
                                        for e in prediction if e.get("word")]
                elif task == "text2text-generation" and prediction:
                    gen_text = prediction[0].get("generated_text", "")
                    keywords_to_save = [k.strip() for k in gen_text.split(",") if k.strip()]

                if keywords_to_save:
                    store = Memory.load()
                    existing = store.get(auto_keywords_key, [])
                    if isinstance(existing, list):
                        keywords_to_save = list(dict.fromkeys(existing + keywords_to_save))
                    store[auto_keywords_key] = keywords_to_save
                    Memory.save(store)
                    meta["auto_keywords_key"] = auto_keywords_key
                    meta["auto_keywords_saved"] = len(keywords_to_save)
            except Exception as e:
                meta["auto_keywords_error"] = str(e)

        # --- Injection into the original text ---
        injection = ""
        if inject_format == "simple":
            try:
                if task == "zero-shot-classification" and prediction:
                    # HF zero-shot: dict with 'labels' and 'scores'
                    top_label = prediction["labels"][0]
                    top_score = prediction["scores"][0]
                    injection = f"[{inject_tag}]\nlabel: {top_label}, score: {top_score:.4f}"

                elif task == "ner" and prediction:
                    entities = [f"{e['word']} ({e.get('entity_group', e.get('entity'))})"
                                for e in prediction if e.get("word")]
                    if entities:
                        injection = f"[{inject_tag}]\n" + ", ".join(entities)

                elif task == "sentiment-analysis" and prediction:
                    p = prediction[0]
                    injection = f"[{inject_tag}]\nlabel: {p['label']}, score: {p['score']:.4f}"

                elif task == "text2text-generation" and prediction:
                    gen_text = prediction[0].get("generated_text", "")
                    injection = f"[{inject_tag}]\n{gen_text}"

                elif task == "summarization" and prediction:
                    # HF summarization: list[dict] with 'summary_text'
                    summary_text = prediction[0].get("summary_text", "")
                    injection = f"[{inject_tag}]\n{summary_text}"
                    meta["summary_text"] = summary_text

            except Exception as e:
                meta["inject_error"] = f"Failed to create simple injection: {e}"

        elif inject_format == "json" and prediction:
            try:
                injection = f"[{inject_tag}]\n{_json.dumps(prediction)}"
            except Exception as e:
                meta["inject_error"] = f"Failed to create JSON injection: {e}"

        parts = [text]
        if injection:
            parts.append(injection)

        out = sep.join(parts)
        return out, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "task": "zero-shot-classification",
            "model": None,
            "device": "auto",
            "verbose": False,
            "auto_keywords_key": None,
            "generation_prompt": "{payload}",
            "context_key": "topic_context",
            "max_input_chars": 4000,
            "output_key": None,
            "inject_format": "simple",
            "inject_tag": "tensor",
            "sep": "\n\n",
            "labels": "general,technical,creative",
            "max_new_tokens": 50,
            "min_length": 10,
            "max_length": 100
        }


BLOCKS.register("tensor", TensorBlock)


# ================ Code Generation (Specialized, no-guides/no-fallbacks) ================

@dataclass
class CodeBlock(BaseBlock):

    # ---- helpers -------------------------------------------------
    def _trim_to_chars(self, text: str, max_chars: int) -> str:
        # 0 = no trim
        if max_chars and len(text) > max_chars:
            return text[:max_chars]
        return text

    def _guess_lang_from_prompt(self, prompt: str, explicit_lang: str) -> str:
        # ... unchanged ...
        lang = (explicit_lang or "").strip().lower() or "python"
        p = prompt.lower()
        if "javascript" in p and "typescript" not in p:
            return "javascript"
        if " typescript" in p or " ts " in p or " ts\n" in p:
            return "typescript"
        if "c++" in p or " cpp" in p:
            return "cpp"
        if "c#" in p or "csharp" in p:
            return "csharp"
        if "rust" in p:
            return "rust"
        if "java" in p and "javascript" not in p:
            return "java"
        if "go code" in p or "golang" in p:
            return "go"
        fence_lang_re = re.compile(r"```(\w+)")
        m = fence_lang_re.search(p)
        if m:
            return m.group(1).lower()
        ext_map = {
            ".py": "python", ".js": "javascript", ".ts": "typescript",
            ".rs": "rust", ".cs": "csharp", ".cpp": "cpp", ".cc": "cpp",
            ".java": "java", ".go": "go",
        }
        for ext, l in ext_map.items():
            if ext in p:
                return l
        return lang or "python"

    def _extract_code_block(self, s: str, lang: str = "python") -> str:
        # ... unchanged ...
        s = s.strip()
        if "```" not in s:
            return s
        parts = s.split("```")
        candidates = []
        LANG_TAGS = {
            "python", "py", "javascript", "js", "ts", "typescript",
            "cpp", "c++", "csharp", "c#", "rust", "java", "go", "php", "swift", "kotlin",
        }
        lang = (lang or "python").lower()
        for i in range(1, len(parts), 2):
            block = parts[i]
            lines = block.splitlines()
            if not lines:
                continue
            first = lines[0].strip().lower()
            stripped = False
            if first in LANG_TAGS:
                lines = lines[1:]
                stripped = True
            elif first.startswith(lang):
                lines = lines[1:]
                stripped = True
            body = "\n".join(lines).strip()
            if not body:
                continue
            score = self._score_code_like(body, lang=lang, lang_stripped=stripped)
            candidates.append((score, body))
        if not candidates:
            return s
        candidates.sort(key=lambda x: x[0], reverse=True)
        best = candidates[0][1].strip()
        return best or s

    def _score_code_like(self, block: str, lang: str, lang_stripped: bool) -> float:
        # ... unchanged ...
        lines = block.splitlines()
        if not lines:
            return 0.0
        text = block
        punct = sum(c in "{}[]();:.,+-=*/<>|&^%#" for c in text)
        letters = sum(c.isalpha() for c in text)
        digits = sum(c.isdigit() for c in text)
        indented = sum(1 for ln in lines if ln.startswith((" ", "\t")))
        keywords = 0
        lang = lang or "python"
        if lang == "python":
            KW = ("def ", "class ", "import ", "from ", "async ", "await ", "return ",
                  "with ", "for ", "while ", "if ", "elif ", "else:", "try:", "except", "finally:")
        elif lang in ("javascript", "typescript", "js", "ts"):
            KW = ("function ", "=>", "const ", "let ", "var ", "return ", "if (",
                  "for (", "while (", "class ", "async ", "await ")
        elif lang in ("cpp", "c++"):
            KW = ("#include", "std::", "int main", "template<", "namespace ", "class ")
        elif lang in ("csharp", "c#"):
            KW = ("using System", "namespace ", "class ", "public ", "static void Main")
        elif lang == "rust":
            KW = ("fn ", "let ", "mut ", "pub ", "impl ", "use ")
        elif lang == "java":
            KW = ("class ", "public static void main", "import ", "package ")
        elif lang == "go":
            KW = ("package ", "func main", "import ", "go func")
        else:
            KW = ("class ", "def ", "function ", "return ")
        for ln in lines:
            for kw in KW:
                if kw in ln:
                    keywords += 1
        score = (punct * 1.0 + digits * 0.3 + keywords * 6.0 + indented * 0.5)
        if lang_stripped:
            score *= 1.2
        lower = text.lower()
        if "traceback (most recent call last)" in lower:
            score -= 40.0
        if "error:" in lower or "exception:" in lower:
            score -= 15.0
        if "warning:" in lower:
            score -= 5.0
        if letters > 0:
            ratio = punct / max(letters, 1)
            score *= (1.0 + ratio)
        if len(lines) < 3:
            score *= 0.7
        elif len(lines) > 200:
            score *= 0.8
        return score

    def _strip_banner_comments(self, code: str) -> str:
        # ... unchanged ...
        lines = code.splitlines()
        if not lines:
            return code
        i = 0
        banner_lines = 0
        for ln in lines:
            t = ln.strip()
            if t.startswith("#") or t.startswith("//") or t.startswith("/*") or t.startswith("*"):
                banner_lines += 1
                i += 1
                if banner_lines >= 12:
                    break
                continue
            break
        if banner_lines >= 10:
            return "\n".join(lines[i:]).lstrip()
        head = "\n".join(lines[:10]).lower()
        if any(k in head for k in ("copyright", "licensed", "apache", "all rights reserved")):
            return "\n".join(lines[i:]).lstrip()
        return code

    def _strip_explanatory_lines(self, code: str) -> str:
        # ... unchanged ...
        lines = code.splitlines()
        out: List[str] = []
        skipping = True
        EXPL_PATTERNS = (
            "here is the", "here's the", "here is an example",
            "you can use the following", "the following code",
            "sample code", "for example:",
        )
        for ln in lines:
            ln_stripped = ln.strip().lower()
            if skipping:
                if not ln.strip():
                    continue
                if any(p in ln_stripped for p in EXPL_PATTERNS):
                    continue
                if any(sym in ln for sym in ("def ", "class ", "function ", "=>", "{", "}", "(", ")", "=")):
                    skipping = False
                    out.append(ln)
                else:
                    continue
            else:
                out.append(ln)
        if not out:
            return code
        return "\n".join(out)

    def _post_sanitize_code(self, code: str) -> str:
        # ... unchanged ...
        c = code.strip()
        if c.startswith("```") and c.endswith("```"):
            c = c.strip("`").strip()
        if "```" in c:
            c = c.split("```", 1)[0].rstrip()
        c = self._strip_explanatory_lines(c)
        c = c.replace("\r\n", "\n").replace("\r", "\n").rstrip()
        if not c.endswith("\n"):
            c += "\n"
        return c

    # ---- main ----------------------------------------------------
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        # Inputs
        user_prompt = str(params.get("prompt", "")).strip()
        if not user_prompt:
            return str(payload), {
                "error": "CodeBlock requires 'prompt' param (e.g., --extra code.prompt=...)"
            }

        # -------- FULL CONTEXT SUPPORT (multi-key + direct context) --------
        store = Memory.load()

        # DEFAULT to "code_context" now (CodeCorpus)
        ctx_key = str(params.get("context_key", "code_context"))

        # Optional direct context override / supplement
        direct_ctx = str(params.get("context", "")).strip()

        # NEW: allow merging multiple context keys, e.g.
        #   --extra code.extra_context_keys="code_search_context,other_context"
        extra_keys_raw = str(params.get("extra_context_keys", "")).strip()
        context_keys: List[str] = [ctx_key]
        if extra_keys_raw:
            context_keys.extend(
                k.strip() for k in extra_keys_raw.split(",") if k.strip()
            )

        ctx_pieces: List[str] = []

        # 1) Direct context (if provided) goes first
        if direct_ctx:
            ctx_pieces.append(direct_ctx)

        # 2) Memory-based contexts
        for k in context_keys:
            v = store.get(k, "")
            if isinstance(v, str):
                v = v.strip()
                if v:
                    ctx_pieces.append(v)

        ctx = "\n\n".join(ctx_pieces)

        # context_chars: 0 = full combined context
        context_chars = int(params.get("context_chars", params.get("code.context_chars", 0)))
        if ctx and context_chars > 0:
            ctx = ctx[:context_chars]

        if ctx:
            final_prompt = f"""### Context
            The following code snippets are provided for reference. Do not copy them blindly.

            {ctx}

            ### Instruction
            You are an expert developer. {user_prompt}

            ### Response
            ```python
            """
        else:
            final_prompt = user_prompt

        max_input_chars = int(params.get("max_input_chars", 8000))
        final_prompt = self._trim_to_chars(final_prompt, max_input_chars)

        explicit_lang = str(params.get("lang", "python"))
        lang = self._guess_lang_from_prompt(user_prompt, explicit_lang)

        model_name = str(params.get("model", "lexicon-adv")).strip().lower()

        # --- Safe model init kwargs ---
        init_kwargs: Dict[str, Any] = {}
        model_init_keys = [
            "model_name",
            "max_terms",
            "max_new_tokens",
            "temperature",
            "top_p",
            "top_k",
            "device",
            "mode",
        ]
        for key in model_init_keys:
            if key in params:
                init_kwargs[key] = params[key]
        try:
            model = get_chat_model(model_name, **init_kwargs)
        except Exception as e:
            return f"{payload}\n\n[code_solution] (Model error: {e})", {
                "error": "model_init_failed",
                "exception": str(e),
                "model": model_name,
            }

        # Runtime kwargs for .generate()
        style = str(params.get("style", "plain"))
        try:
            max_chars = int(params.get("max_chars", 0))
        except Exception:
            max_chars = 0

        # --- Lexicon: default from Memory["code_lexicon"] unless explicitly given ---
        lexicon = params.get("lexicon", None)
        lexicon_key = str(params.get("lexicon_key", "code_lexicon"))
        if lexicon is None:
            mem_lex = store.get(lexicon_key)
            if isinstance(mem_lex, list):
                lexicon = mem_lex

        try:
            gen_kwargs = params.copy()
            gen_kwargs.update({
                "lexicon": lexicon,
                "style": style,
                "max_chars": max_chars,
            })
            gen_text = model.generate(final_prompt, **gen_kwargs)

        except Exception as e:
            return f"{payload}\n\n[code_solution] (Error: {e})", {
                "error": "generation_failed",
                "exception": str(e),
                "model": model_name,
            }

        gen_text = (gen_text or "").strip()

        code_raw = self._extract_code_block(gen_text, lang=lang)
        code_raw = self._strip_banner_comments(code_raw)
        code_raw = self._post_sanitize_code(code_raw)

        if not code_raw.strip():
            code_raw = gen_text

        # --- subpipeline: ONLY if explicitly set & non-empty ---
        subpipeline_name = str(params.get("subpipeline", "")).strip()
        if subpipeline_name:
            code_raw = self.run_sub_pipeline(
                initial_value=code_raw,
                pipeline_param_name="subpipeline",
                parent_params=params,
            )

        wrap = bool(params.get("wrap", True))
        inject_tag = str(params.get("inject_tag", "code_solution"))

        if wrap:
            code_out = f"```{lang}\n{code_raw}\n```"
        else:
            code_out = code_raw

        result = f"{payload}\n\n[{inject_tag}]\n{code_out}"

        meta = {
            "model": model_name,
            "lang": lang,
            "context_key": ctx_key,
            "extra_context_keys": extra_keys_raw,
            "context_chars": len(ctx),
            "prompt_len": len(final_prompt),
            "tokens_generated": len(code_raw),
            "style": style,
            "max_chars": max_chars,
            "max_input_chars": max_input_chars,
            "used_context": bool(ctx),
            "subpipeline": subpipeline_name,
            "lexicon_key": lexicon_key,
            "lexicon_size": len(lexicon) if isinstance(lexicon, list) else 0,
            "used_direct_context": bool(direct_ctx),
        }
        return result, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "prompt": "REQUIRED: Write a python function...",

            # Context handling
            "context": "",                  # NEW: direct context blob
            "context_key": "code_context",  # DEFAULT: code context from CodeCorpus
            "extra_context_keys": "",       # e.g. "code_search_context,other_key"
            "context_chars": 0,             # 0 = full combined context

            # Lexicon handling
            "lexicon": None,                # optional explicit lexicon override
            "lexicon_key": "code_lexicon",  # DEFAULT: Memory["code_lexicon"]

            "model": "lexicon-adv",
            "max_input_chars": 8000,
            "wrap": True,
            "inject_tag": "code_solution",
            "lang": "python",

            "subpipeline": "",  # e.g. "code_chat"
            "code_chat.op": "passthrough",

            "style": "plain",
            "max_chars": 0,
            "max_terms": 12,

            "max_new_tokens": 128,
            "temperature": 0.7,
            "top_p": 0.9,
            "top_k": 50,
        }


BLOCKS.register("code", CodeBlock)

# ================ CodeCorpus (code docs & API learner) ================

@dataclass
class CodeCorpusBlock(BaseBlock):
    """
    Code-focused corpus builder (DBSubmanager + Sniffers + Lexicon edition).

      • Inputs: list of urls, sitemap(s), or (query + site_include) search.
      • Extracts: fenced / <pre>/<code> blocks from Markdown/HTML.
      • Saves ONLY code snippets to SQLite via DatabaseSubmanager + CodeCorpusStore.
      • Remembers scraped URLs (code_indexed_urls) and skips unless force_refresh=true.
      • Optional Playwright fallback for JS-heavy sites:
          - Optionally uses NetworkSniffer / JSSniffer (async) to get better HTML.
      • NEW: Builds a code lexicon + context (like WebCorpus) and exports them to Memory.
    """

    # --- Identifier & text processing ---

    _STOP = set([
        "the", "a", "an", "and", "or", "if", "on", "in", "to", "for", "from", "of", "at", "by",
        "with", "as", "is", "are", "was", "were", "be", "been", "being", "that", "this", "these",
        "those", "it", "its", "into", "about", "over", "under", "can", "should", "would", "will",
        "may", "might", "must", "do", "does", "did", "done", "have", "has", "had", "having", "not",
        "no", "yes", "you", "your", "we", "our", "they", "their", "there", "here", "also", "such",
        "via", "etc", "see",
        "code", "example", "examples", "note", "notes", "true", "false", "none", "null",
        "class", "function", "method", "module", "package", "return", "returns", "type", "types",
        "param", "parameter", "parameters",
    ])

    _IDENT_RE = re.compile(
        r"""
        (?:
          [A-Za-z_][A-Za-z0-9_]*           # snake/UPPER/mixed
          (?:\.[A-Za-z_][A-Za-z0-9_]*)*    # dotted api.name
        )
        |
        (?:
          [A-Za-z][a-z0-9]+(?:[A-Z][a-z0-9]+)+  # camelCase/PascalCase
        )
        |
        (?:
          [a-z0-9]+(?:-[a-z0-9]+)+              # kebab-case
        )
        """,
        re.VERBOSE,
    )

    _FENCE_RE = re.compile(
        r"""
        ^```[ \t]*([A-Za-z0-9_\-\+\.]*)[ \t]*\n   # opening fence with optional lang
        (.*?)                                     # code body (non-greedy)
        \n```[ \t]*$                              # closing fence
        """,
        re.MULTILINE | re.DOTALL | re.VERBOSE,
    )

    # ---- Heuristics ----

    def _looks_like_traceback(self, code: str) -> bool:
        c = code.lower()
        if "traceback (most recent call last)" in c:
            return True
        if "error:" in c or "exception" in c:
            lines = [ln.strip() for ln in code.splitlines() if ln.strip()]
            file_like = sum(
                ln.lower().startswith("file \"") or ln.lower().startswith("file '")
                for ln in lines
            )
            has_def = any("def " in ln or "class " in ln for ln in lines)
            if file_like >= 2 and not has_def:
                return True
        return False

    def _clean_domain(self, u: str) -> str:
        try:
            netloc = urlparse(u).netloc.lower()
            return netloc.split(":")[0]
        except Exception:
            return ""

    def _extract_identifiers(self, text: str, min_len: int) -> List[str]:
        ids = self._IDENT_RE.findall(text or "")
        out: List[str] = []
        for s in ids:
            tok = s.strip().strip(".")
            if len(tok) < min_len:
                continue
            low = tok.lower()
            if low in self._STOP:
                continue
            out.append(tok)
        return out

    # --- HTML / Markdown processing ---

    def _extract_text_html(self, html_text: str, has_trafilatura: bool) -> Tuple[str, List[str]]:
        """
        Return (clean_text, code_blocks) from HTML.
        """
        from bs4 import BeautifulSoup

        code_blocks: List[str] = []
        clean_text = ""

        if has_trafilatura:
            try:
                import trafilatura
                clean_text = trafilatura.extract(
                    html_text,
                    include_comments=False,
                    include_tables=False,
                    deduplicate=True,
                ) or ""
            except Exception:
                clean_text = ""

        try:
            soup = BeautifulSoup(html_text or "", "html.parser")
            # collect <pre>/<code> blocks as code
            for pre in soup.select("pre, code"):
                try:
                    code = pre.get_text("\n", strip=True)
                except Exception:
                    code = ""
                if code and len(code) >= 8:
                    code_blocks.append(code)

            if not clean_text:
                for t in soup(["script", "style", "noscript", "pre", "code"]):
                    t.extract()
                clean_text = soup.get_text(" ", strip=True)
        except Exception:
            pass

        return clean_text or "", code_blocks

    def _extract_text_md(self, md_text: str) -> Tuple[str, List[str]]:
        """Return (clean_text, code_blocks) from Markdown using regex fences only."""
        code_blocks: List[str] = []
        text = md_text or ""
        for m in self._FENCE_RE.finditer(text):
            code = m.group(2).strip()
            if len(code) >= 8:
                code_blocks.append(code)
        text_wo_fences = self._FENCE_RE.sub(" ", text)
        text_wo_inline = re.sub(r"`([^`]+)`", r"\1", text_wo_fences)
        clean = re.sub(r"[ \t]+", " ", text_wo_inline)
        clean = re.sub(r"\n{2,}", "\n", clean).strip()
        return clean, code_blocks

    # --- main execution ---

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import html
        import time
        import asyncio
        from collections import defaultdict

        # ---------- Params ----------
        query = str(params.get("query", "")).strip()
        urls_raw = str(params.get("urls", "")).strip()
        sitemaps_raw = str(params.get("sitemaps", "")).strip()

        site_include_raw = str(params.get("site_include", "")).strip()
        if not site_include_raw or site_include_raw.lower() in {"none", "any", "*"}:
            site_include: List[str] = []
        else:
            site_include = [
                s.strip().lower()
                for s in site_include_raw.split(",")
                if s.strip() and s.strip().lower() not in {"none", "any", "*"}
            ]

        site_exclude_raw = str(params.get("site_exclude", "")).strip()
        if not site_exclude_raw or site_exclude_raw.lower() in {"none", "any"}:
            site_exclude: List[str] = []
        else:
            site_exclude = [
                s.strip().lower()
                for s in site_exclude_raw.split(",")
                if s.strip() and s.strip().lower() not in {"none", "any"}
            ]

        max_pages = int(params.get("max_pages", 12))
        min_doc_chars = int(params.get("min_doc_chars", 200))

        learn_new_sites = bool(params.get("learn_new_sites", True))
        learned_sites_key = str(params.get("learned_sites_key", "learned_code_sites"))
        learn_min_hits = int(params.get("learn_min_hits", 2))

        db_path = str(params.get("db_path", "code_corpus.db"))

        timeout = float(params.get("timeout", 10.0))
        read_timeout = float(params.get("read_timeout", 12.0))
        user_agent = str(params.get("user_agent", "promptchat/codecorpus"))
        verbose = bool(params.get("verbose", False))

        use_playwright_fallback = bool(params.get("use_playwright_fallback", True))
        force_refresh = bool(params.get("force_refresh", False))

        # NEW: sniffers toggles (default False)
        use_network_sniff = bool(params.get("use_network_sniff", False))
        use_js_sniff = bool(params.get("use_js_sniff", False))

        # NEW: lexicon/context options (like WebCorpus)
        export_lexicon = bool(params.get("export_lexicon", True))
        lexicon_key = str(params.get("lexicon_key", "code_lexicon"))
        inject_lexicon = bool(params.get("inject_lexicon", True))
        inject_context = bool(params.get("inject_context", True))
        lexicon_top_k = int(params.get("lexicon_top_k", 60))
        lexicon_min_len = int(params.get("lexicon_min_len", 3))

        export_context = bool(params.get("export_context", True))
        context_key = str(params.get("context_key", "code_context"))
        append_ctx = bool(params.get("append_context", False))
        max_context_chars = int(params.get("max_context_chars", 8000))

        # Save onto self for helper usage
        self.timeout = timeout
        self.read_timeout = read_timeout
        self.user_agent = user_agent

        # --- Check dependencies ---
        try:
            import requests
        except Exception:
            return str(payload), {"error": "Install `requests` to use CodeCorpusBlock."}

        try:
            from bs4 import BeautifulSoup  # noqa: F401
        except Exception:
            return str(payload), {"error": "Install `beautifulsoup4` to use CodeCorpusBlock."}

        try:
            import trafilatura  # noqa: F401
            has_traf = True
        except Exception:
            has_traf = False

        try:
            from ddgs import DDGS  # noqa: F401
            has_ddgs = True
        except Exception:
            has_ddgs = False

        # Playwright imports (async)
        has_async_playwright = True
        try:
            from playwright.async_api import async_playwright  # noqa: F401
        except Exception:
            has_async_playwright = False
            if use_playwright_fallback or use_network_sniff or use_js_sniff:
                print(
                    "[CodeCorpusBlock] Warning: Playwright not installed; "
                    "disabling dynamic fallback & sniffers."
                )
                use_playwright_fallback = False
                use_network_sniff = False
                use_js_sniff = False

        # Sniffers
        if use_network_sniff:
            try:
                _ = submanagers.NetworkSniffer
            except AttributeError:
                print("[CodeCorpusBlock] NetworkSniffer not available; disabling.", flush=True)
                use_network_sniff = False
        if use_js_sniff:
            try:
                _ = submanagers.JSSniffer
            except AttributeError:
                print("[CodeCorpusBlock] JSSniffer not available; disabling.", flush=True)
                use_js_sniff = False

        def _allowed(url: str) -> bool:
            d = self._clean_domain(url)
            if not d:
                return False
            if site_include and not any(d.endswith(s) for s in site_include):
                return False
            if any(d.endswith(s) for s in site_exclude):
                return False
            return True

        def _get_page_static(url: str) -> str:
            """Fast static HTML fetch using requests."""
            try:
                r = requests.get(
                    url,
                    headers={"User-Agent": user_agent},
                    timeout=(timeout, read_timeout),
                )
                if r.status_code == 200:
                    return r.text
            except Exception as e:
                if verbose:
                    print(f"[CodeCorpusBlock] Static fetch failed for {url}: {e}")
            return ""

        # --- Initialize DB via DatabaseSubmanager + CodeCorpusStore ---
        db_config = submanagers.DatabaseConfig(path=db_path)
        dbm = submanagers.DatabaseSubmanager(db_config)
        store = CodeCorpusStore(dbm)
        try:
            store.ensure_schema()
        except Exception as e:
            return str(payload), {"error": f"Failed to initialize database at {db_path}: {e}"}

        # --- collect URLs ---
        candidates: List[str] = []
        if urls_raw:
            candidates.extend([u.strip() for u in urls_raw.split(",") if u.strip()])

        if sitemaps_raw:
            for sm in [s.strip() for s in sitemaps_raw.split(",") if s.strip()]:
                try:
                    xml = _get_page_static(sm)
                    if not xml:
                        continue
                    locs = re.findall(r"<loc>(.*?)</loc>", xml, re.IGNORECASE | re.DOTALL)
                    for loc in locs:
                        u = html.unescape(loc).strip()
                        if _allowed(u):
                            candidates.append(u)
                except Exception:
                    continue

        if query and not (urls_raw or sitemaps_raw) and has_ddgs:
            from ddgs import DDGS
            with DDGS() as ddgs:
                try:
                    for r in ddgs.text(query, max_results=max_pages * 2, safesearch="off"):
                        u = r.get("href") or r.get("url")
                        if u and _allowed(u):
                            candidates.append(u)
                except Exception as e:
                    if verbose:
                        print(f"[CodeCorpusBlock] DDGS search failed: {e}")

        seen = set()
        final_urls: List[str] = []
        for u in candidates:
            if u in seen:
                continue
            seen.add(u)
            if _allowed(u):
                final_urls.append(u)
            if len(final_urls) >= max_pages:
                break

        if not final_urls:
            return str(payload), {"rows": 0, "note": "no matching URLs found to scrape"}

        # --- If force_refresh: clear DB for these domains ---
        if force_refresh:
            domains = [self._clean_domain(u) for u in final_urls]
            store.clear_for_domains(domains)

        # --- Stats ---
        domain_hits: Dict[str, int] = defaultdict(int)
        total_code = 0
        total_indexed = 0
        total_updated = 0
        total_skipped = 0
        total_errors = 0

        # URLs that need dynamic fallback (JS-heavy)
        need_dynamic: List[str] = []

        # Snippets collected for context/lexicon
        snippets_for_context: List[Dict[str, str]] = []

        # --- 1) STATIC PASS ---
        for u in final_urls:
            try:
                current_time = time.time()
                last_scraped_time = store.get_last_scraped_time(u)

                if last_scraped_time > 0.0 and not force_refresh:
                    if verbose:
                        print(f"[CodeCorpusBlock] Skipping (already indexed): {u}")
                    total_skipped += 1
                    continue

                html_text = _get_page_static(u)
                if not html_text:
                    # If we have dynamic tools, we can retry later
                    if use_playwright_fallback or use_network_sniff or use_js_sniff:
                        need_dynamic.append(u)
                    else:
                        total_errors += 1
                    continue

                if u.lower().endswith(".md") or "/raw/" in u or "raw.githubusercontent.com" in u:
                    prose_body, code_blocks = self._extract_text_md(html_text)
                else:
                    prose_body, code_blocks = self._extract_text_html(html_text, has_traf)

                code_text = "\n\n".join(code_blocks).strip()

                # If static fetch got too little code and we have dynamic fallback, defer
                if len(code_text) < min_doc_chars and (
                    use_playwright_fallback or use_network_sniff or use_js_sniff
                ) and not u.lower().endswith(".md"):
                    if verbose:
                        print(
                            f"[CodeCorpusBlock] Static scrape for {u} "
                            f"got only {len(code_text)} code chars; deferring to dynamic."
                        )
                    need_dynamic.append(u)
                    continue

                if len(code_text) < min_doc_chars:
                    total_skipped += 1
                    continue

                # Extract title
                title = self._clean_domain(u)
                try:
                    if "<title" in html_text.lower():
                        from bs4 import BeautifulSoup
                        soup = BeautifulSoup(html_text, "html.parser")
                        if soup.title and soup.title.string:
                            title = " ".join(soup.title.string.strip().split())
                except Exception:
                    pass

                url_had_code = False
                for code in code_blocks:
                    code = (code or "").strip()
                    if len(code) < 20:
                        continue
                    if self._looks_like_traceback(code):
                        continue

                    store.upsert_snippet(u, title, code, kind="code")
                    total_code += 1
                    url_had_code = True
                    snippets_for_context.append({"url": u, "title": title, "code": code})

                if url_had_code:
                    store.mark_scraped(u, current_time)
                    domain_hits[self._clean_domain(u)] += 1
                    if last_scraped_time == 0.0:
                        total_indexed += 1
                    else:
                        total_updated += 1
                else:
                    total_skipped += 1

            except Exception as e:
                total_errors += 1
                if verbose:
                    print(f"[CodeCorpusBlock] Error processing (static) {u}: {e}")

        # --- 2) DYNAMIC PASS (Playwright + optional sniffers) ---
        async def _run_dynamic():
            if not need_dynamic:
                return

            from playwright.async_api import async_playwright

            # Lazy sniffers
            net_sniffer = None
            js_sniffer = None

            async with async_playwright() as p:
                browser = await p.chromium.launch(
                    headless=True,
                    args=["--disable-blink-features=AutomationControlled"],
                )
                context = await browser.new_context(
                    user_agent=user_agent,
                    java_script_enabled=True,
                )

                if use_network_sniff:
                    try:
                        net_sniffer = submanagers.NetworkSniffer()
                    except Exception:
                        net_sniffer = None
                if use_js_sniff:
                    try:
                        js_sniffer = submanagers.JSSniffer()
                    except Exception:
                        js_sniffer = None

                for u in need_dynamic:
                    nonlocal total_code, total_indexed, total_updated, total_skipped, total_errors

                    try:
                        current_time = time.time()
                        last_scraped_time = store.get_last_scraped_time(u)
                        if last_scraped_time > 0.0 and not force_refresh:
                            if verbose:
                                print(f"[CodeCorpusBlock] (dynamic) skipping already indexed: {u}")
                            total_skipped += 1
                            continue

                        html_text = ""
                        log_list: List[str] = []
                        js_links: List[dict] = []
                        net_items: List[dict] = []
                        json_hits: List[dict] = []

                        # Prefer sniffers if enabled
                        if net_sniffer:
                            if verbose:
                                print(f"[CodeCorpusBlock] NetworkSniffer for {u}", flush=True)
                            html_net, net_items, json_hits = await net_sniffer.sniff(
                                context,
                                u,
                                timeout=timeout,
                                log=log_list,
                                extensions=None,
                            )
                        else:
                            html_net = ""

                        if js_sniffer:
                            if verbose:
                                print(f"[CodeCorpusBlock] JSSniffer for {u}", flush=True)
                            html_js, js_links = await js_sniffer.sniff(
                                context,
                                u,
                                timeout=timeout,
                                log=log_list,
                                extensions=None,
                            )
                        else:
                            html_js = ""

                        html_text = html_net or html_js or ""

                        # Fallback: direct Playwright page content.
                        if not html_text and (use_playwright_fallback or not (net_sniffer or js_sniffer)):
                            page = await context.new_page()
                            try:
                                await page.goto(u, timeout=int(timeout * 1000), wait_until="domcontentloaded")
                                await page.wait_for_timeout(500)
                                html_text = await page.content()
                            finally:
                                try:
                                    await page.close()
                                except Exception:
                                    pass

                        if not html_text:
                            total_skipped += 1
                            continue

                        if u.lower().endswith(".md") or "/raw/" in u or "raw.githubusercontent.com" in u:
                            prose_body, code_blocks = self._extract_text_md(html_text)
                        else:
                            prose_body, code_blocks = self._extract_text_html(html_text, has_traf)

                        code_text = "\n\n".join(code_blocks).strip()
                        if len(code_text) < min_doc_chars:
                            total_skipped += 1
                            continue

                        title = self._clean_domain(u)
                        try:
                            if "<title" in html_text.lower():
                                from bs4 import BeautifulSoup
                                soup = BeautifulSoup(html_text, "html.parser")
                                if soup.title and soup.title.string:
                                    title = " ".join(soup.title.string.strip().split())
                        except Exception:
                            pass

                        url_had_code = False
                        for code in code_blocks:
                            code = (code or "").strip()
                            if len(code) < 20:
                                continue
                            if self._looks_like_traceback(code):
                                continue
                            store.upsert_snippet(u, title, code, kind="code")
                            total_code += 1
                            url_had_code = True
                            snippets_for_context.append({"url": u, "title": title, "code": code})

                        if url_had_code:
                            store.mark_scraped(u, current_time)
                            domain_hits[self._clean_domain(u)] += 1
                            if last_scraped_time == 0.0:
                                total_indexed += 1
                            else:
                                total_updated += 1
                        else:
                            total_skipped += 1

                    except Exception as e:
                        total_errors += 1
                        if verbose:
                            print(f"[CodeCorpusBlock] Error processing (dynamic) {u}: {e}", flush=True)

                await browser.close()

        # Run dynamic phase if needed
        if need_dynamic and (use_playwright_fallback or use_network_sniff or use_js_sniff) and has_async_playwright:
            try:
                loop = asyncio.get_event_loop()
            except RuntimeError:
                loop = None

            if not loop or not loop.is_running():
                asyncio.run(_run_dynamic())
            else:
                exc_holder: Dict[str, BaseException] = {}

                def _runner():
                    try:
                        new_loop = asyncio.new_event_loop()
                        asyncio.set_event_loop(new_loop)
                        new_loop.run_until_complete(_run_dynamic())
                    except BaseException as e:
                        exc_holder["exc"] = e
                    finally:
                        new_loop.close()

                t = threading.Thread(target=_runner, daemon=True)
                t.start()
                t.join()
                if "exc" in exc_holder:
                    if verbose:
                        print(f"[CodeCorpusBlock] Dynamic phase error: {exc_holder['exc']}")
                    total_errors += 1

        # --- Learn new domains ---
        newly_learned: List[str] = []
        if learn_new_sites:
            store_mem = Memory.load()
            learned = set(store_mem.get(learned_sites_key, []))
            for dom, c in domain_hits.items():
                if not dom:
                    continue
                if c >= learn_min_hits and dom not in learned and _allowed(f"https://{dom}/"):
                    learned.add(dom)
                    newly_learned.append(dom)
            if newly_learned:
                store_mem[learned_sites_key] = sorted(list(learned))
                Memory.save(store_mem)

        # --- Build code context & lexicon (like WebCorpus) ---
        # Context: concatenate snippets with headers
        context_chunks: List[str] = []
        total_ctx_chars = 0
        for sn in snippets_for_context:
            title = sn.get("title") or self._clean_domain(sn.get("url", ""))
            url = sn.get("url", "")
            code = sn.get("code", "").strip()
            if not code:
                continue
            header = f"# {title} — {url}".strip()
            block = f"{header}\n{code}"
            block_len = len(block)
            if max_context_chars > 0 and total_ctx_chars + block_len > max_context_chars:
                break
            context_chunks.append(block)
            total_ctx_chars += block_len + 2

        context = "\n\n".join(context_chunks).strip()

        # Lexicon: from identifiers in all snippets
        all_code_concat = "\n\n".join(sn["code"] for sn in snippets_for_context if sn.get("code"))
        lexicon: List[str] = []
        if all_code_concat:
            ids = self._extract_identifiers(all_code_concat, min_len=lexicon_min_len)
            counts: Dict[str, int] = {}
            for tok in ids:
                key = tok.strip()
                if not key:
                    continue
                counts[key] = counts.get(key, 0) + 1
            # sort by freq desc, then name
            lexicon = [
                t for t, _ in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
            ][:lexicon_top_k]

        # --- store lexicon + context in Memory ---
        if export_lexicon and lexicon:
            store_mem = Memory.load()
            store_mem[lexicon_key] = lexicon
            Memory.save(store_mem)

        if export_context and context:
            store_mem = Memory.load()
            if append_ctx and isinstance(store_mem.get(context_key), str) and store_mem[context_key]:
                store_mem[context_key] = store_mem[context_key].rstrip() + "\n\n" + context
            else:
                store_mem[context_key] = context
            Memory.save(store_mem)

        # --- Compose output ---
        base = "" if payload is None else str(payload)
        parts: List[str] = [base] if base else []

        if inject_lexicon and lexicon:
            parts.append("[lexicon]\n" + ", ".join(lexicon))
        if inject_context and context:
            parts.append("[context]\n" + context)

        out_msg = (
            f"Web corpus scan complete. Processed {len(final_urls)} URLs.\n"
            f"  - New Snippets Indexed: {total_indexed}\n"
            f"  - Snippets Updated:     {total_updated}\n"
            f"  - URLs Skipped:         {total_skipped}\n"
            f"  - Total Snippets Added: {total_code}\n"
            f"  - Errors:               {total_errors}"
        )
        parts.append("[corpus_update]\n" + out_msg)

        out = "\n\n".join(parts).strip()

        meta = {
            "db_path": db_path,
            "urls_scraped": len(final_urls),
            "total_code_snippets": total_code,
            "files_indexed": total_indexed,
            "files_updated": total_updated,
            "files_skipped": total_skipped,
            "errors": total_errors,
            "site_include": site_include,
            "site_exclude": site_exclude,
            "learned_sites_key": learned_sites_key if learn_new_sites else None,
            "newly_learned": newly_learned,
            "need_dynamic": need_dynamic,
            "use_network_sniff": use_network_sniff,
            "use_js_sniff": use_js_sniff,
            "lexicon_key": lexicon_key if (export_lexicon and lexicon) else None,
            "lexicon_size": len(lexicon),
            "context_key": context_key if (export_context and context) else None,
            "context_len": len(context),
        }
        return out, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "",
            "urls": "",
            "sitemaps": "",
            "site_include": "",
            "site_exclude": "github.com,stackoverflow.com",
            "max_pages": 12,
            "min_doc_chars": 200,
            "learn_new_sites": True,
            "learned_sites_key": "learned_code_sites",
            "db_path": "code_corpus.db",
            "timeout": 10.0,
            "read_timeout": 12.0,
            "use_playwright_fallback": True,
            "force_refresh": False,
            # sniffers:
            "use_network_sniff": False,
            "use_js_sniff": False,
            # lexicon/context (like WebCorpus, but code-specific):
            "export_lexicon": True,
            "inject_lexicon": True,
            "inject_context": True,
            "lexicon_key": "code_lexicon",
            "context_key": "code_context",
            "append_context": False,
            "lexicon_top_k": 60,
            "lexicon_min_len": 3,
            "export_context": True,
            "max_context_chars": 8000,
        }


# Register the block
BLOCKS.register("codecorpus", CodeCorpusBlock)

# ================ CodeSearch ================
@dataclass
class CodeSearchBlock(BaseBlock):
    """
    Code Retrieval + Lexicon Builder for CodeBlock.

    Exports:
      - Memory[export_context_key] -> formatted context blocks (fenced when code-like)
      - Memory[export_lexicon_key] -> list[str] lexicon tokens (API names etc.)

    Context packing is designed to feed CodeBlock:
      - prioritizes code-kind docs and code-like prose
      - adds minimal headers and stable fences
      - clamps snippet sizes to avoid blowing input window

    Lexicon is designed to help generation:
      - identifiers (snake/camel/dotted), imports/using/includes, class/function names
      - bigrams (e.g., "tf.keras", "async_playwright", "sqlite3.connect")
      - weighted by where they came from (title > code > prose), plus frequency across docs
    """

    # ----------------- config -----------------

    _SEARCH_STOP_WORDS = {
        "a", "an", "and", "are", "as", "at", "be", "by", "for", "from",
        "how", "in", "is", "it", "of", "on", "or", "show", "tell", "that",
        "the", "this", "to", "what", "when", "where", "which", "with",
        "me", "give", "using", "write", "basic", "script", "code", "function",
        "block", "class", "method", "model", "example", "examples", "guide",
    }

    _WS_RE = re.compile(r"\s+")
    _WORD_RE = re.compile(r"\w+")
    _IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
    _DOTTED_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+")
    _CAMEL_RE = re.compile(r"[A-Za-z][a-z0-9]+(?:[A-Z][a-z0-9]+)+")

    # Keep lexicon sane
    _LEX_STOP = {
        # general + code boilerplate
        "true", "false", "none", "null", "self", "this", "that", "these", "those",
        "return", "returns", "value", "values", "param", "params", "parameter", "parameters",
        "args", "kwargs", "var", "let", "const", "function", "class", "public", "private",
        "static", "void", "int", "float", "string", "bool", "dict", "list", "set", "tuple",
        "import", "from", "using", "namespace", "include", "define",
    }

    # ----------------- tokenize / extract -----------------

    def _tokenize_words(self, text: str) -> List[str]:
        return [t.lower() for t in self._WORD_RE.findall(text or "")]

    def _extract_identifiers(self, text: str) -> List[str]:
        """
        Return identifiers including dotted APIs and camelCase/PascalCase.
        We keep them as original case where possible (better for APIs),
        but we also dedupe case-insensitively later.
        """
        t = text or ""
        out: List[str] = []

        for m in self._DOTTED_RE.finditer(t):
            out.append(m.group(0))

        # raw identifiers
        for m in self._IDENT_RE.finditer(t):
            s = m.group(0)
            if len(s) >= 3:
                out.append(s)

        # camelCase / PascalCase (often API types)
        for m in self._CAMEL_RE.finditer(t):
            s = m.group(0)
            if len(s) >= 4:
                out.append(s)

        return out

    def _extract_import_hints(self, text: str) -> List[str]:
        """
        Pull common "import-ish" hints:
          - python: import x / from x import y
          - js/ts: from 'x'
          - c#: using X.Y;
          - cpp: #include <x>
        """
        t = text or ""
        out: List[str] = []

        # python
        for m in re.finditer(r"^\s*import\s+([A-Za-z0-9_\.]+)", t, re.MULTILINE):
            out.append(m.group(1))
        for m in re.finditer(r"^\s*from\s+([A-Za-z0-9_\.]+)\s+import\s+([A-Za-z0-9_\,\s]+)", t, re.MULTILINE):
            mod = m.group(1)
            out.append(mod)
            items = [x.strip() for x in m.group(2).split(",") if x.strip()]
            for it in items[:8]:
                out.append(f"{mod}.{it}")

        # js/ts
        for m in re.finditer(r"\bfrom\s+['\"]([^'\"]+)['\"]", t):
            pkg = m.group(1).strip()
            if pkg:
                out.append(pkg)

        # c#
        for m in re.finditer(r"^\s*using\s+([A-Za-z0-9_\.]+)\s*;", t, re.MULTILINE):
            out.append(m.group(1))

        # c/cpp
        for m in re.finditer(r"^\s*#include\s+[<\"]([^>\"]+)[>\"]", t, re.MULTILINE):
            out.append(m.group(1))

        return out

    def _extract_def_names(self, text: str) -> List[str]:
        """
        Grab function/class names across common languages.
        """
        t = text or ""
        out: List[str] = []

        # python
        out += [m.group(1) for m in re.finditer(r"^\s*def\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", t, re.MULTILINE)]
        out += [m.group(1) for m in re.finditer(r"^\s*class\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(|:)", t, re.MULTILINE)]

        # js/ts
        out += [m.group(1) for m in re.finditer(r"\bfunction\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", t)]
        out += [m.group(1) for m in re.finditer(r"\bclass\s+([A-Za-z_][A-Za-z0-9_]*)\b", t)]

        # c#/java
        out += [m.group(1) for m in re.finditer(r"\bclass\s+([A-Za-z_][A-Za-z0-9_]*)\b", t)]
        out += [m.group(1) for m in re.finditer(r"\binterface\s+([A-Za-z_][A-Za-z0-9_]*)\b", t)]

        # go
        out += [m.group(1) for m in re.finditer(r"^\s*func\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", t, re.MULTILINE)]

        # rust
        out += [m.group(1) for m in re.finditer(r"^\s*fn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", t, re.MULTILINE)]
        out += [m.group(1) for m in re.finditer(r"^\s*struct\s+([A-Za-z_][A-Za-z0-9_]*)\b", t, re.MULTILINE)]
        out += [m.group(1) for m in re.finditer(r"^\s*enum\s+([A-Za-z_][A-Za-z0-9_]*)\b", t, re.MULTILINE)]

        return out

    # ----------------- scoring -----------------

    def _code_likeness(self, text: str) -> float:
        if not text:
            return 0.0
        lines = (text or "").splitlines()
        punct = sum(c in "{}[]();:.,+-=*/<>|&^%#@" for c in text)
        letters = sum(c.isalpha() for c in text)
        indented = sum(1 for ln in lines if ln.startswith((" ", "\t")))
        lower = text.lower()
        kw = 0
        for k in ("def ", "class ", "import ", "return ", "if ", "for ", "while ",
                  "function ", "const ", "let ", "#include", "std::", "namespace ",
                  "public ", "fn ", "impl ", "await ", "async "):
            if k in lower:
                kw += 1
        ratio = punct / max(letters, 1)
        return float((ratio * 3.0) + (indented * 0.05) + (kw * 0.8))

    def _normalize_query(self, query: str) -> Dict[str, Any]:
        raw = (query or "").strip()
        toks = [t for t in self._tokenize_words(raw) if t not in self._SEARCH_STOP_WORDS]
        idents = {t for t in self._extract_identifiers(raw) if len(t) >= 3}
        return {"raw": raw, "tokens": toks, "idents": idents}

    def _format_fts_query(self, query: str, tokens: List[str]) -> str:
        q = (query or "").strip().replace('"', '""')
        phrase = f"\"{q}\"" if q else ""
        if not tokens:
            return phrase or q or ""
        toks = tokens[:12]
        and_part = " AND ".join(f"\"{t}\"*" for t in toks)
        or_part = " OR ".join(f"\"{t}\"*" for t in toks)
        if phrase:
            return f"({phrase}) OR ({and_part}) OR ({or_part})"
        return f"({and_part}) OR ({or_part})"

    def _origin_key(self, url: str) -> str:
        u = (url or "")
        return u.split("::", 1)[0].strip()

    def _score_doc(self, q_tokens: Set[str], q_idents: Set[str], doc: Dict[str, Any]) -> float:
        content = doc.get("content") or ""
        title = doc.get("title") or ""
        kind = (doc.get("kind") or "prose").lower()

        ctoks = set(self._tokenize_words(content))
        ttoks = set(self._tokenize_words(title))

        token_hits = (len(ctoks & q_tokens) * 1.0) + (len(ttoks & q_tokens) * 2.0)

        doc_idents = set(self._extract_identifiers(content)) | set(self._extract_identifiers(title))
        # normalize to lower for overlap
        doc_idents_l = {x.lower() for x in doc_idents}
        q_idents_l = {x.lower() for x in q_idents}
        ident_hits = len(doc_idents_l & q_idents_l) * 2.8

        # kind bias
        kind_boost = 1.35 if "code" in kind else 0.90

        # code-likeness
        cl = 1.0 + min(0.8, self._code_likeness(content) * 0.18)

        # size bell curve (prefer medium snippets)
        ln = len(content)
        if ln < 80:
            size = 0.45
        elif ln > 9000:
            size = 0.65
        else:
            size = 1.0

        return float((token_hits + ident_hits) * kind_boost * cl * size)

    # ----------------- context packing -----------------

    def _guess_code_lang(self, kind: str, snippet: str) -> str:
        k = (kind or "").lower()
        if "code:" in k:
            return k.split("code:", 1)[1].strip()
        s = (snippet or "").lower()
        if "def " in s and ("import " in s or "async " in s): return "python"
        if "function" in s and "{" in s: return "javascript"
        if "public class" in s or "system.out" in s: return "java"
        if "#include" in s or "std::" in s: return "cpp"
        if "using system" in s or "namespace" in s: return "csharp"
        if "fn " in s and "let " in s: return "rust"
        if "package " in s and "func " in s: return "go"
        return ""

    def _clamp_snippet(self, s: str, max_chars: int) -> str:
        if max_chars > 0 and len(s) > max_chars:
            return s[:max_chars].rstrip() + "\n# ...clamped...\n"
        return s

    def _render_context(self, selected: List[Tuple[float, Dict[str, Any]]], *, per_snippet_chars: int) -> str:
        blocks: List[str] = []
        for score, doc in selected:
            title = (doc.get("title") or "").strip()
            kind = (doc.get("kind") or "prose").strip()
            url = (doc.get("url") or "").strip()
            content = (doc.get("content") or "").rstrip()
            if not content:
                continue

            content = self._clamp_snippet(content, per_snippet_chars)

            lang = self._guess_code_lang(kind, content)
            is_codeish = ("code" in (kind or "").lower()) or (self._code_likeness(content) >= 1.2) or bool(lang)

            header = f"### {kind.upper()} | {title}".strip()
            if url:
                header += f"\n# source: {url}"

            if is_codeish:
                fence = lang or ""
                block = f"{header}\n```{fence}\n{content}\n```"
            else:
                block = f"{header}\n{content}"

            blocks.append(block)

        return "\n\n".join(blocks).strip()

    def _pack_diverse(
        self,
        ranked: List[Tuple[float, Dict[str, Any]]],
        *,
        top_k: int,
        max_chars: int,
        per_origin_cap: int,
        per_snippet_chars: int,
    ) -> Tuple[List[Tuple[float, Dict[str, Any]]], Dict[str, Any]]:
        chosen: List[Tuple[float, Dict[str, Any]]] = []
        per_origin: Dict[str, int] = {}
        total = 0

        for score, doc in ranked:
            if len(chosen) >= top_k:
                break

            origin = self._origin_key(doc.get("url", ""))
            if per_origin.get(origin, 0) >= per_origin_cap:
                continue

            content = doc.get("content") or ""
            if not content:
                continue

            # pre-clamp for packing estimate
            content_est = content if per_snippet_chars <= 0 else content[:per_snippet_chars]
            add_len = len(content_est) + 128  # header/fence overhead

            if max_chars > 0 and (total + add_len) > max_chars:
                continue

            chosen.append((score, doc))
            per_origin[origin] = per_origin.get(origin, 0) + 1
            total += add_len

        return chosen, {"diversity_groups": len(per_origin), "packed_chars": total}

    # ----------------- lexicon build -----------------

    def _add_lex_counts(self, counts: Dict[str, float], items: List[str], weight: float) -> None:
        for it in items:
            tok = (it or "").strip()
            if not tok:
                continue

            low = tok.lower()
            if low in self._LEX_STOP:
                continue
            if len(low) < 3:
                continue
            if low.isdigit():
                continue

            # Keep case for API aesthetics, but dedupe by lowercase
            counts[low] = counts.get(low, 0.0) + float(weight)

    def _bigrams(self, toks: List[str]) -> List[str]:
        out = []
        for i in range(len(toks) - 1):
            a, b = toks[i], toks[i + 1]
            if not a or not b:
                continue
            if a in self._SEARCH_STOP_WORDS or b in self._SEARCH_STOP_WORDS:
                continue
            if len(a) < 3 or len(b) < 3:
                continue
            out.append(f"{a}_{b}")
        return out

    def _build_lexicon(
        self,
        query: str,
        q_tokens: List[str],
        selected: List[Tuple[float, Dict[str, Any]]],
        *,
        top_k: int,
    ) -> List[str]:
        """
        Weighted lexicon from:
          - query tokens (seed)
          - titles (strong)
          - identifiers/imports/defnames from content (strong)
          - frequent words (weak)
          - bigrams from titles/query (medium)
        """
        counts: Dict[str, float] = {}

        # seed query tokens
        self._add_lex_counts(counts, q_tokens, weight=3.0)

        # seed from raw query identifiers too
        self._add_lex_counts(counts, self._extract_identifiers(query), weight=4.0)

        for score, doc in selected:
            title = (doc.get("title") or "")
            content = (doc.get("content") or "")
            kind = (doc.get("kind") or "prose").lower()

            # weights by kind
            w_kind = 1.25 if "code" in kind else 1.0
            w_score = 1.0 + min(1.5, score / 6.0)  # mild boost for top-ranked

            # title words + bigrams
            title_words = [t for t in self._tokenize_words(title) if t not in self._SEARCH_STOP_WORDS]
            self._add_lex_counts(counts, title_words, weight=2.6 * w_kind * w_score)
            self._add_lex_counts(counts, self._bigrams(title_words), weight=1.8 * w_kind * w_score)

            # identifiers + import hints + def/class names
            idents = self._extract_identifiers(content)
            imps = self._extract_import_hints(content)
            defs = self._extract_def_names(content)

            self._add_lex_counts(counts, idents, weight=2.2 * w_kind * w_score)
            self._add_lex_counts(counts, imps, weight=3.0 * w_kind * w_score)
            self._add_lex_counts(counts, defs, weight=3.2 * w_kind * w_score)

            # dotted APIs deserve a little extra
            dotted = [x for x in idents if "." in x]
            self._add_lex_counts(counts, dotted, weight=2.6 * w_kind * w_score)

        # rank: weight desc, then token
        ranked = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))

        # post-filter: avoid super-generic tokens
        out: List[str] = []
        for tok, w in ranked:
            if tok in self._LEX_STOP:
                continue
            # avoid "one-letter-ish" and noisy underscore bigrams that are too long
            if len(tok) > 64:
                continue
            out.append(tok)
            if len(out) >= top_k:
                break

        # Keep original casing? We stored lowercase keys.
        # For now, return lowercase (stable + matches your Memory usage).
        return out

    # ----------------- main -----------------

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        query = str(params.get("query", "")).strip()
        if not query:
            return str(payload), {"error": "CodeSearchBlock: 'query' parameter is required."}

        db_path = str(params.get("db_path", "code_corpus.db"))

        # retrieval
        top_k = int(params.get("top_k", 6))
        fetch_mult = int(params.get("fetch_mult", 10))
        fetch_limit = max(20, top_k * fetch_mult)

        # context packing
        max_chars = int(params.get("max_chars", 6500))
        per_origin_cap = int(params.get("per_origin_cap", 2))
        per_snippet_chars = int(params.get("per_snippet_chars", 1800))

        # exports
        export_context_key = str(params.get("export_context_key", "code_search_context"))
        export_lexicon_key = str(params.get("export_lexicon_key", "code_search_lexicon"))
        lexicon_top_k = int(params.get("lexicon_top_k", 80))

        inject = bool(params.get("inject", True))
        inject_lexicon = bool(params.get("inject_lexicon", True))

        qn = self._normalize_query(query)
        fts_query = self._format_fts_query(qn["raw"], qn["tokens"])

        # 1) fetch
        try:
            with sqlite3.connect(db_path) as conn:
                conn.row_factory = sqlite3.Row
                sql = """
                    SELECT url, title, content, kind
                    FROM docs
                    WHERE docs MATCH ?
                    LIMIT ?
                """
                cur = conn.execute(sql, (fts_query, fetch_limit))
                rows = [dict(r) for r in cur.fetchall()]
        except sqlite3.Error as e:
            return str(payload), {"error": f"DB Error: {e}", "query": query, "fts_query": fts_query}

        if not rows:
            return str(payload), {"note": "No results found in SQLite.", "hits": 0, "fts_query": fts_query}

        # 2) score + rank (pure python, deterministic)
        qtok_set = set(qn["tokens"])
        ranked: List[Tuple[float, Dict[str, Any]]] = []
        for doc in rows:
            ranked.append((self._score_doc(qtok_set, qn["idents"], doc), doc))
        ranked.sort(key=lambda x: x[0], reverse=True)

        # 3) pack context with diversity
        selected, pack_meta = self._pack_diverse(
            ranked,
            top_k=top_k,
            max_chars=max_chars,
            per_origin_cap=per_origin_cap,
            per_snippet_chars=per_snippet_chars,
        )

        # 4) render context
        full_context = self._render_context(selected, per_snippet_chars=per_snippet_chars)

        # 5) build lexicon from selected docs
        lexicon = self._build_lexicon(
            query=query,
            q_tokens=qn["tokens"],
            selected=selected,
            top_k=lexicon_top_k,
        )

        # 6) export
        store = Memory.load()
        store[export_context_key] = full_context
        store[export_lexicon_key] = lexicon
        Memory.save(store)

        out_text = "" if payload is None else str(payload)

        if inject and full_context:
            out_text += f"\n\n[{export_context_key}]\n{full_context}"
        if inject and inject_lexicon and lexicon:
            out_text += f"\n\n[{export_lexicon_key}]\n" + ", ".join(lexicon)

        meta = {
            "query": query,
            "fts_query": fts_query,
            "hits_found": len(rows),
            "hits_returned": len(selected),
            "ranker": "py_weighted_code_rank",
            "export_context_key": export_context_key,
            "export_lexicon_key": export_lexicon_key,
            "lexicon_size": len(lexicon),
            "top_k": top_k,
            "fetch_limit": fetch_limit,
            "max_chars": max_chars,
            "per_snippet_chars": per_snippet_chars,
            "per_origin_cap": per_origin_cap,
            **pack_meta,
        }
        return out_text, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "REQUIRED. The search string.",
            "db_path": "code_corpus.db",

            # retrieval
            "top_k": 6,
            "fetch_mult": 10,

            # context packing
            "max_chars": 6500,
            "per_origin_cap": 2,
            "per_snippet_chars": 1800,

            # exports
            "export_context_key": "code_search_context",
            "export_lexicon_key": "code_search_lexicon",
            "lexicon_top_k": 80,

            # output
            "inject": True,
            "inject_lexicon": True,
        }


BLOCKS.register("codesearch", CodeSearchBlock)


# ================ LocalCodeCorpus (scans local files) ================
@dataclass
class LocalCodeCorpusBlock(BaseBlock):
    """
    Scans a local directory for code files (.py, .js, etc.) and adds them
    to the same SQLite FTS5 database used by CodeCorpusBlock and CodeSearchBlock.

    This allows your RAG pipeline to have context on your local projects.
    It tracks modification times and only updates new or changed files.

    For .py files, it uses AST to index functions and classes individually
    for much more accurate search results.

    Enhanced:
      • Language-aware 'kind' field (code:py, code:js, prose:md, ...)
      • Markdown fences keep their language (```python vs ```js)
      • Python chunks get more descriptive titles and lightweight headers
      • max_class_lines param to avoid indexing giant classes as single blobs
    """

    # Map extensions to languages (for kind tagging)
    LANG_BY_EXT = {
        ".py": "python",
        ".js": "javascript",
        ".ts": "typescript",
        ".md": "markdown",
        ".txt": "text",
        ".java": "java",
        ".cpp": "cpp",
        ".c": "c",
        ".h": "c-header",
        ".rs": "rust",
        ".go": "go",
    }

    # Default maximum number of lines for a class before it's considered
    # "too big" to index as a single chunk. Overridable via param.
    MAX_CLASS_LINES = 140

    _MD_FENCE_RE = re.compile(
        r"""
        ```[ \t]*([A-Za-z0-9_\-\+\.]*)[ \t]*\n   # opening fence + optional lang
        (.*?)                                    # body
        \n```                                    # closing fence
        """,
        re.MULTILINE | re.DOTALL | re.VERBOSE
    )

    def _extract_md_fences(self, text: str) -> Tuple[str, List[Tuple[str, str]]]:
        """
        Extract fenced code blocks from Markdown text.

        Returns:
          (prose_without_fences,
           [(lang, code_block_1), (lang, code_block_2), ...])

        'lang' is the raw fence language (e.g. 'python', 'js', 'sh').
        """
        if not text:
            return "", []

        code_blocks: List[Tuple[str, str]] = []

        def _repl(match: re.Match) -> str:
            lang = (match.group(1) or "").strip().lower()
            body = (match.group(2) or "").strip()
            if len(body) >= 8:
                code_blocks.append((lang, body))
            # Replace with a single blank line to keep some structure
            return "\n"

        without_fences = self._MD_FENCE_RE.sub(_repl, text)
        # Normalize whitespace a bit
        without_fences = re.sub(r"[ \t]+", " ", without_fences)
        without_fences = re.sub(r"\n{3,}", "\n\n", without_fences)
        return without_fences.strip(), code_blocks

    def _init_fts_db(self, db_path: str):
        """
        Initializes the FTS5 table (same as CodeCorpusBlock).
        """
        with sqlite3.connect(db_path) as conn:
            conn.execute("""
            CREATE VIRTUAL TABLE IF NOT EXISTS docs USING fts5(
                url UNINDEXED,    -- File path or file_path::chunk_name
                title,            -- File name or file :: chunk
                content,          -- File content or chunk content
                kind,             -- 'code', 'prose', or language-tagged variants
                tokenize = 'porter unicode61'
            );
            """)

    def _init_tracking_db(self, db_path: str):
        """
        Initializes a separate table to track file modification times.
        """
        with sqlite3.connect(db_path) as conn:
            conn.execute("""
                         CREATE TABLE IF NOT EXISTS indexed_files
                         (
                             path
                             TEXT
                             PRIMARY
                             KEY,
                             last_indexed_mtime
                             REAL
                             NOT
                             NULL
                         );
                         """)

    def _get_last_mtime(self, conn: sqlite3.Connection, file_path: str) -> float:
        """Check the DB for the last indexed modification time of a file or chunk."""
        try:
            cur = conn.execute(
                "SELECT last_indexed_mtime FROM indexed_files WHERE path = ?", (file_path,)
            )
            row = cur.fetchone()
            return float(row[0]) if row else 0.0
        except sqlite3.Error as e:
            print(f"Error checking mtime for {file_path}: {e}")
            return 0.0

    # ---- helpers -------------------------------------------------
    def _kind_for_file(self, file_name: str, is_prose: bool) -> str:
        """
        Build a language-aware kind string like 'code:py' or 'prose:md'.
        """
        ext = os.path.splitext(file_name)[1].lower()
        lang = self.LANG_BY_EXT.get(ext, "")
        base = "prose" if is_prose else "code"
        if lang:
            return f"{base}:{lang}"
        return base

    def _kind_for_lang(self, lang: str, base: str = "code") -> str:
        """
        Build a kind from an explicit language (e.g. from Markdown fences).
        """
        lang = (lang or "").strip().lower()
        if not lang:
            return base
        return f"{base}:{lang}"

    # --- AST-based Python file processor ---
    def _process_python_file(
            self,
            conn: sqlite3.Connection,
            file_path: str,
            file_name: str,
            current_mtime: float,
            min_chars: int,
            max_class_lines: int,
    ) -> Tuple[int, int]:
        """
        Parse a .py file into functions/classes using AST and index them individually.
        Returns (new_chunks_indexed, chunks_updated).

        max_class_lines controls when we skip indexing a class as a single giant
        chunk and instead rely on its methods (FunctionDef/AsyncFunctionDef) as
        the primary units.
        """
        indexed = 0
        updated = 0
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()

            if len(content) < min_chars:
                return 0, 0  # Skip small files

            tree = ast.parse(content, filename=file_path)

            # 1. Index the top-level file docstring as "prose:py" (narrative context)
            file_docstring = ast.get_docstring(tree) or ""
            if file_docstring and len(file_docstring) > min_chars:
                last_mtime = self._get_last_mtime(conn, file_path)  # Use file_path as URL
                if current_mtime > last_mtime:
                    conn.execute(
                        "INSERT OR REPLACE INTO docs (url, title, content, kind) "
                        "VALUES (?, ?, ?, ?)",
                        (file_path, file_name, file_docstring, "prose:python")
                    )
                    conn.execute(
                        "INSERT OR REPLACE INTO indexed_files (path, last_indexed_mtime) "
                        "VALUES (?, ?)",
                        (file_path, current_mtime)
                    )
                    if last_mtime == 0.0:
                        indexed += 1
                    else:
                        updated += 1

            # 2. Index functions and classes as "code:python"
            #
            # Strategy:
            #   • Always index functions / async functions as before.
            #   • For classes:
            #       - If the class is small, index the whole class as one chunk.
            #       - If the class is huge (more than max_class_lines), SKIP the class chunk
            #         and let its methods (FunctionDef nodes inside) be the primary snippets.
            for node in ast.walk(tree):
                # ----- Classes (maybe giant) -----
                if isinstance(node, ast.ClassDef):
                    # Try to get full class source
                    try:
                        class_src = ast.get_source_segment(content, node) or ""
                    except Exception:
                        class_src = ""

                    if not class_src:
                        continue

                    class_lines = [ln for ln in class_src.splitlines() if ln.strip()]
                    # If class is huge, don't index it as one giant blob.
                    if len(class_lines) > max_class_lines:
                        # Methods inside this class will still be indexed separately
                        # as FunctionDef/AsyncFunctionDef nodes below.
                        continue

                    chunk_name = node.name
                    chunk_content = class_src
                    node_kind = "class"

                # ----- Functions / async functions (including methods) -----
                elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    chunk_name = node.name
                    try:
                        chunk_content = ast.get_source_segment(content, node)
                    except Exception:
                        continue

                    if not chunk_content or len(chunk_content) < min_chars:
                        continue

                    node_kind = "async_function" if isinstance(node, ast.AsyncFunctionDef) else "function"

                else:
                    continue  # other node types not indexed

                if len(chunk_content) < min_chars:
                    continue

                # Add a small header to help search ("where did this come from?")
                header_lines = [
                    f"# file: {file_path}",
                    f"# symbol: {chunk_name}",
                    ""
                ]
                combined_content = "\n".join(header_lines) + chunk_content

                # Use a unique URL/path for this chunk
                chunk_url = f"{file_path}::{chunk_name}"
                # Better titles for codesearch UI
                chunk_title = f"{file_name} :: {node_kind} {chunk_name}"

                # Check mtime for this *chunk*
                last_mtime = self._get_last_mtime(conn, chunk_url)

                if current_mtime > last_mtime:
                    conn.execute(
                        "INSERT OR REPLACE INTO docs (url, title, content, kind) "
                        "VALUES (?, ?, ?, ?)",
                        (chunk_url, chunk_title, combined_content, "code:python")
                    )
                    conn.execute(
                        "INSERT OR REPLACE INTO indexed_files (path, last_indexed_mtime) "
                        "VALUES (?, ?)",
                        (chunk_url, current_mtime)
                    )
                    if last_mtime == 0.0:
                        indexed += 1
                    else:
                        updated += 1

            # If we didn't index any chunks, at least update the main file's mtime
            # to prevent re-parsing it every time if it hasn't changed.
            if indexed == 0 and updated == 0:
                last_mtime = self._get_last_mtime(conn, file_path)
                if current_mtime > last_mtime:
                    conn.execute(
                        "INSERT OR REPLACE INTO indexed_files (path, last_indexed_mtime) "
                        "VALUES (?, ?)",
                        (file_path, current_mtime)
                    )

            return indexed, updated

        except (SyntaxError, ValueError) as e:
            print(f"Skipping {file_path} (AST parsing failed): {e}")
            return 0, 0
        except Exception as e:
            print(f"Error processing {file_path}: {e}")
            return 0, 0

    # --- Generic file processor ---
    def _process_generic_file(
            self,
            conn: sqlite3.Connection,
            file_path: str,
            file_name: str,
            current_mtime: float,
            last_mtime: float,
            min_chars: int
    ) -> Tuple[int, int]:
        """
        Indexes a non-Python file.

        Smarter behavior for Markdown:
          - Extract fenced code blocks → 'code:lang' kind with path::codeN URL.
          - Store remaining prose (if sufficiently long) as 'prose:md'.
        For other extensions:
          - Store whole file as 'code:lang' or 'prose:lang' based on extension.
        """
        indexed, updated = 0, 0
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()

            if len(content) < min_chars:
                return 0, 0

            # Markdown special handling
            if file_name.endswith(".md"):
                prose, code_blocks = self._extract_md_fences(content)

                # 1) Index code blocks individually as 'code:<lang>'
                chunk_idx = 0
                for lang, block in code_blocks:
                    block = (block or "").strip()
                    if len(block) < min_chars:
                        continue

                    chunk_idx += 1
                    chunk_url = f"{file_path}::code{chunk_idx}"
                    chunk_title = f"{file_name} :: code{chunk_idx}"

                    # Use fence language if present, else fall back to 'code'
                    kind = self._kind_for_lang(lang, base="code")

                    # Optional header so codesearch text queries can see origin/lang
                    header = []
                    header.append(f"# from_markdown_file: {file_name}")
                    if lang:
                        header.append(f"# fenced_lang: {lang}")
                    header.append("")
                    block_with_header = "\n".join(header) + block

                    conn.execute(
                        "INSERT OR REPLACE INTO docs (url, title, content, kind) "
                        "VALUES (?, ?, ?, ?)",
                        (chunk_url, chunk_title, block_with_header, kind)
                    )

                # 2) Index remaining prose as 'prose:markdown'
                if prose and len(prose) >= min_chars:
                    prose_kind = "prose:markdown"
                    conn.execute(
                        "INSERT OR REPLACE INTO docs (url, title, content, kind) "
                        "VALUES (?, ?, ?, ?)",
                        (file_path, file_name, prose, prose_kind)
                    )

                # 3) Update tracking table for the *file*
                if chunk_idx > 0 or (prose and len(prose) >= min_chars):
                    conn.execute(
                        "INSERT OR REPLACE INTO indexed_files (path, last_indexed_mtime) "
                        "VALUES (?, ?)",
                        (file_path, current_mtime)
                    )
                    if last_mtime == 0.0:
                        indexed = 1
                    else:
                        updated = 1

                return indexed, updated

            # Non-Markdown: single document as before, but with language-aware kind
            ext = os.path.splitext(file_name)[1].lower()
            is_prose = ext in (".md", ".txt")
            kind = self._kind_for_file(file_name, is_prose=is_prose)

            conn.execute(
                "INSERT OR REPLACE INTO docs (url, title, content, kind) "
                "VALUES (?, ?, ?, ?)",
                (file_path, file_name, content, kind)
            )

            conn.execute(
                "INSERT OR REPLACE INTO indexed_files (path, last_indexed_mtime) "
                "VALUES (?, ?)",
                (file_path, current_mtime)
            )

            if last_mtime == 0.0:
                indexed = 1
            else:
                updated = 1

        except Exception as e:
            print(f"Error processing generic file {file_path}: {e}")

        return indexed, updated

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        # ---------- Params ----------
        db_path = str(params.get("db_path", "code_corpus.db"))

        scan_path_raw = str(params.get("scan_path", "")).strip()
        if not scan_path_raw:
            return str(payload), {"error": "LocalCodeCorpusBlock requires 'scan_path' param."}

        scan_path = os.path.abspath(os.path.expanduser(scan_path_raw))

        extensions_raw = str(params.get("extensions", ".py,.js,.ts,.md,.txt,.java,.cpp,.c,.h,.rs,.go"))
        extensions = tuple([e.strip() for e in extensions_raw.split(',') if e.strip()])
        py_extensions = tuple([e for e in extensions if e == '.py'])  # Separate .py
        other_extensions = tuple([e for e in extensions if e != '.py'])  # All others

        min_chars = int(params.get("min_chars", 50))
        verbose = bool(params.get("verbose", False))

        check_for_updates = bool(params.get("check_for_updates", False))

        skip_default_dirs = bool(params.get("skip_default_dirs", True))
        skip_venv_dirs = bool(params.get("skip_venv_dirs", True))
        extra_skip_dirs_raw = str(params.get("extra_skip_dirs", ""))

        # NEW: configurable max_class_lines (overrides class default)
        max_class_lines = int(params.get("max_class_lines", self.MAX_CLASS_LINES))

        skip_set = set()
        if skip_default_dirs:
            skip_set.update(('.git', 'node_modules', '__pycache__'))
        if skip_venv_dirs:
            skip_set.update(('venv', '.venv'))
        if extra_skip_dirs_raw:
            skip_set.update([d.strip() for d in extra_skip_dirs_raw.split(',') if d.strip()])

        if not os.path.isdir(scan_path):
            return str(payload), {"error": f"Path not found or is not a directory: {scan_path}"}

        # --- Initialize DBs ---
        try:
            self._init_fts_db(db_path)
            self._init_tracking_db(db_path)
        except Exception as e:
            return str(payload), {"error": f"Failed to initialize database: {e}"}

        # --- Scan Files ---
        total_indexed = 0
        total_updated = 0
        total_skipped = 0
        total_errors = 0

        try:
            conn = sqlite3.connect(db_path)
        except Exception as e:
            return str(payload), {"error": f"Failed to open DB {db_path}: {e}"}

        try:
            for root, dirs, files in os.walk(scan_path, topdown=True):
                if skip_set:
                    dirs[:] = [d for d in dirs if d not in skip_set]

                for file in files:
                    # Decide which extensions list to check
                    is_py = file.endswith(py_extensions)
                    is_other = file.endswith(other_extensions)

                    if not (is_py or is_other):
                        continue

                    file_path = os.path.join(root, file)

                    try:
                        current_mtime = os.path.getmtime(file_path)
                        # For AST-parsed files, we check mtime per chunk inside _process_python_file
                        # For generic files, we check here.
                        last_mtime = self._get_last_mtime(conn, file_path)

                        if not check_for_updates and last_mtime > 0.0 and not is_py:
                            if verbose: print(f"Skipping (already indexed): {file_path}")
                            total_skipped += 1
                            continue

                        if check_for_updates and current_mtime <= last_mtime and not is_py:
                            if verbose: print(f"Skipping (up-to-date): {file_path}")
                            total_skipped += 1
                            continue

                        # Route to specific processor
                        if is_py:
                            indexed, updated = self._process_python_file(
                                conn, file_path, file, current_mtime, min_chars, max_class_lines
                            )
                        else:
                            indexed, updated = self._process_generic_file(
                                conn, file_path, file, current_mtime, last_mtime, min_chars
                            )

                        total_indexed += indexed
                        total_updated += updated
                        if indexed == 0 and updated == 0:
                            total_skipped += 1  # Skipped due to min_chars or other

                    except (IOError, OSError) as e:
                        if verbose: print(f"Error reading {file_path}: {e}")
                        total_errors += 1
                    except Exception as e:
                        if verbose: print(f"Error processing {file_path}: {e}")
                        total_errors += 1

            conn.commit()

        except Exception as e:
            total_errors += 1
            print(f"A critical error occurred: {e}")
        finally:
            conn.close()

        # --- Compose output ---
        base = "" if payload is None else str(payload)
        out_msg = (
            f"Local code scan complete for: {scan_path}\n"
            f"  - New Chunks Indexed: {total_indexed}\n"
            f"  - Chunks Updated:     {total_updated}\n"
            f"  - Files/Chunks Skipped: {total_skipped}\n"
            f"  - Errors:            {total_errors}"
        )

        meta = {
            "db_path": db_path,
            "scan_path": scan_path,
            "files_indexed": total_indexed,  # actually chunks
            "files_updated": total_updated,
            "files_skipped": total_skipped,
            "errors": total_errors,
            "max_class_lines": max_class_lines,
        }
        return f"{base}\n\n[local_corpus_update]\n{out_msg}", meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "scan_path": "REQUIRED: The local directory to scan (e.g., ~/PycharmProjects)",
            "db_path": "code_corpus.db",
            "extensions": ".py,.js,.ts,.md,.txt,.java,.cpp,.c,.h,.rs,.go",
            "min_chars": 50,
            "verbose": False,
            "check_for_updates": False,
            "skip_default_dirs": True,
            "skip_venv_dirs": True,
            "extra_skip_dirs": "",
            # NEW:
            "max_class_lines": self.MAX_CLASS_LINES,
        }


BLOCKS.register("localcodecorpus", LocalCodeCorpusBlock)


# ======================= NewsBlock =========================================
@dataclass
class NewsBlock(BaseBlock):
    """
    Fetches public news/info sources without keys.
    Params:
        url: (optional) direct URL to JSON/RSS/Atom/HTML feed
        preset: one of NEWS_PRESETS keys (e.g., 'reuters_top', 'spaceflight_news')
        limit: int (default 10) number of items to summarize
        open_meteo: dict with latitude/longitude if you want a dynamic Open-Meteo call,
                    e.g. {"latitude": 32.30, "longitude": -90.10, "current_weather": True}
    Output: Markdown list + meta with count & source,
            and a [context] block suitable for ChatBlock.
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        limit = int(params.get("limit", 10))
        preset = params.get("preset")
        url = params.get("url")
        items: List[Dict[str, Any]] = []
        meta: Dict[str, Any] = {"source": None, "count": 0, "kind": "news"}

        # Dynamic Open-Meteo builder
        if not url and "open_meteo" in params:
            q = dict(params.get("open_meteo") or {})
            if "latitude" not in q or "longitude" not in q:
                return ("Open-Meteo requires latitude and longitude", {"error": "missing_coords"})
            q.setdefault("current_weather", True)
            url = "https://api.open-meteo.com/v1/forecast?" + urlencode(q)

        if not url and preset:
            url = NEWS_PRESETS.get(str(preset), None)

        if not url:
            return ("No URL or known preset provided to NewsBlock.", {"error": "missing_url_or_preset"})

        meta["source"] = url

        # Fetch and branch by content type
        resp = _http_get(url)
        if _is_json_content(resp):
            data = _safe_json(resp)
            # Spaceflight News JSON shape: list of articles with 'title','url','summary'
            if isinstance(data, list):
                for row in data[:limit]:
                    items.append({
                        "title": row.get("title") or row.get("name") or "(no title)",
                        "link": row.get("url") or row.get("link") or "",
                        "summary": row.get("summary") or row.get("description") or "",
                        "published": row.get("publishedAt") or row.get("published") or "",
                    })
            elif isinstance(data, dict):
                # Wikipedia summary example
                title = data.get("title") or data.get("displaytitle") or "(no title)"
                link = data.get("content_urls", {}).get("desktop", {}).get("page") or data.get("extract_url") or ""
                items.append({
                    "title": title,
                    "link": link,
                    "summary": data.get("extract") or data.get("description") or "",
                    "published": data.get("timestamp") or "",
                })
            else:
                items.append({"title": "(unrecognized JSON)", "link": "", "summary": str(type(data))})
        else:
            ctype = (resp.headers.get("Content-Type") or "").lower()
            text = resp.text
            if "xml" in ctype or text.strip().startswith("<"):
                # RSS/Atom
                items = _parse_feed(url, limit=limit)
            else:
                # Plain HTML: try to find <title> and main links as a fallback
                tmatch = re.search(r"<title>(.*?)</title>", text, re.IGNORECASE | re.DOTALL)
                title = html.escape(tmatch.group(1).strip()) if tmatch else url
                # Grab some prominent <a> links as items
                links = re.findall(r'<a[^>]+href=["\']([^"\']+)["\'][^>]*>(.*?)</a>',
                                   text,
                                   flags=re.IGNORECASE | re.DOTALL)
                seen = set()
                for href, anchor in links:
                    if href.startswith("#") or href.startswith("javascript:"):
                        continue
                    key = (href, anchor.strip())
                    if key in seen:
                        continue
                    seen.add(key)
                    if len(items) >= limit:
                        break
                    clean_text = re.sub(r"\s+", " ", html.unescape(re.sub("<.*?>", "", anchor))).strip()
                    items.append({
                        "title": clean_text or "(link)",
                        "link": href,
                        "summary": "",
                        "published": "",
                    })
                if not items:
                    items.append({"title": title, "link": url, "summary": "", "published": ""})

        meta["count"] = len(items)

        # Original markdown list for human reading
        body_markdown = _markdown_list(items, extra_keys=["published", "summary"], limit=limit)

        # Build [context] block for ChatBlock: titles + summaries + published
        context_lines: List[str] = []
        for it in items[:limit]:
            t = str(it.get("title") or "(no title)")
            s = str(it.get("summary") or "")
            p = str(it.get("published") or "")
            line = t
            if s:
                line += f" — {s}"
            if p:
                line += f" (Published: {p})"
            context_lines.append(line)

        context_text = "\n".join(context_lines).strip()

        body = f"### NewsBlock · {meta['source']}\n{body_markdown}"
        if context_text:
            body += "\n\n[context]\n" + context_text

        # Expose context in meta as well (optional, might be handy elsewhere)
        meta["context_chars"] = len(context_text)

        return body, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "limit": 10,
            "preset": "e.g., bbc_world, npr_news, nyt_tech",
            "url": None,
            "open_meteo": "{'latitude': 32.3, 'longitude': -90.1}"
        }


BLOCKS.register("news", NewsBlock)


# ======================= NasaBlock =========================================
@dataclass
class NasaBlock(BaseBlock):
    """
    NASA feeds without keys.
    Params:
        preset: one of NASA_PRESETS ('nasa_breaking','nasa_image_of_the_day','apod_html','nasa_images_api')
        url: override to any NASA RSS/JSON/HTML endpoint
        q: for nasa_images_api (e.g., 'earth' or 'jupiter aurora')
        limit: max items (default 8)
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        limit = int(params.get("limit", 8))
        preset = params.get("preset")
        url = params.get("url")
        q = params.get("q")

        if not url and preset:
            url = NASA_PRESETS.get(str(preset), None)
        if not url:
            return ("No URL or preset provided to NasaBlock.", {"error": "missing_url_or_preset"})

        # Build NASA Images API query
        if preset == "nasa_images_api":
            query = {"q": q or "earth", "media_type": "image"}
            url = NASA_PRESETS["nasa_images_api"] + "?" + urlencode(query)

        meta: Dict[str, Any] = {"source": url, "count": 0, "kind": "nasa"}
        resp = _http_get(url)

        # ---------- JSON branch (NASA Images API) ----------
        if _is_json_content(resp):
            data = _safe_json(resp)
            items: List[Dict[str, Any]] = []
            # NASA Images API JSON shape:
            # { "collection": { "items": [ { "links":[{"href":...}], "data":[{"title":...,"description":...}] } ] } }
            coll = (data or {}).get("collection", {})
            for it in coll.get("items", [])[:limit]:
                title = ""
                desc = ""
                link = ""
                if isinstance(it.get("data"), list) and it["data"]:
                    title = it["data"][0].get("title", "")
                    desc = it["data"][0].get("description", "")
                if isinstance(it.get("links"), list) and it["links"]:
                    link = it["links"][0].get("href", "")
                items.append({"title": title or "(image)", "link": link, "summary": desc})
            meta["count"] = len(items)

            body_markdown = _markdown_list(items, extra_keys=["summary"], limit=limit)

            # Build [context] for ChatBlock
            context_lines: List[str] = []
            for it in items[:limit]:
                t = str(it.get("title") or "(image)")
                s = str(it.get("summary") or "")
                line = t
                if s:
                    line += f" — {s}"
                context_lines.append(line)
            context_text = "\n".join(context_lines).strip()

            body = f"### NasaBlock · {meta['source']}\n{body_markdown}"
            if context_text:
                body += "\n\n[context]\n" + context_text
            meta["context_chars"] = len(context_text)
            return (body, meta)

        # ---------- Non-JSON content ----------
        text = resp.text
        ctype = (resp.headers.get("Content-Type") or "").lower()

        # RSS/Atom
        if "xml" in ctype or text.strip().startswith("<"):
            items = _parse_feed(url, limit=limit)
            meta["count"] = len(items)

            body_markdown = _markdown_list(items, extra_keys=["published", "summary"], limit=limit)

            # Build [context] block
            context_lines: List[str] = []
            for it in items[:limit]:
                t = str(it.get("title") or "(no title)")
                s = str(it.get("summary") or "")
                p = str(it.get("published") or "")
                line = t
                if s:
                    line += f" — {s}"
                if p:
                    line += f" (Published: {p})"
                context_lines.append(line)
            context_text = "\n".join(context_lines).strip()

            body = f"### NasaBlock · {meta['source']}\n{body_markdown}"
            if context_text:
                body += "\n\n[context]\n" + context_text
            meta["context_chars"] = len(context_text)
            return (body, meta)

        # APOD HTML fallback (no key)
        if preset == "apod_html":
            img_src = _extract_first_img_src(text)  # often relative like "image/YY/foobar.jpg"
            if img_src and img_src.startswith("image/"):
                base = "https://apod.nasa.gov/apod/"
                img_src = base + img_src
            # Try to pull a caption
            caption_match = re.search(r"<b>(.*?)</b>", text, flags=re.IGNORECASE | re.DOTALL)
            caption = html.unescape(caption_match.group(1)).strip() if caption_match else "Astronomy Picture of the Day"
            items = [{"title": caption, "link": img_src or url, "summary": "APOD (no key)"}]
            meta["count"] = len(items)

            body_markdown = _markdown_list(items, extra_keys=["summary"], limit=limit)

            # Build [context]
            context_lines = [f"{caption} — APOD (no key)"]
            context_text = "\n".join(context_lines).strip()

            body = f"### NasaBlock · {meta['source']}\n{body_markdown}"
            if context_text:
                body += "\n\n[context]\n" + context_text
            meta["context_chars"] = len(context_text)
            return (body, meta)

        # Unknown HTML; provide a single item back (no real context to summarize)
        body = f"### NasaBlock · {meta['source']}\n- (unrecognized content) {url}"
        meta["context_chars"] = 0
        return (body, meta)

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "limit": 8,
            "preset": "e.g., nasa_breaking, apod_html",
            "url": None,
            "q": "e.g., earth, jupiter aurora"
        }


BLOCKS.register("nasa", NasaBlock)


# ================ Intelligence (Code vs. Prose) =====================================
@dataclass
class IntelligenceBlock(BaseBlock):
    """
    Passively learns from the pipeline by analyzing the structure of the payload.
    It differentiates between fenced code blocks and general prose.

    - "Code" Concepts: Extracts identifiers, API names, functions, and classes
      from ` ``` ` blocks.
    - "Prose" Concepts: Extracts keywords and terms from the text *outside*
      of code blocks.

    It tracks "similarities and differences" by noting which discovered
    concepts are *new* vs. *already known* in memory.

    This block populates memory keys that can be used by `ChatBlock` (via
    `lexicon_key`) or other blocks to build smarter, domain-aware responses.
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        text = str(payload or "")
        if not text:
            return "", {"error": "IntelligenceBlock received empty payload."}

        # --- Get parameters ---
        code_concepts_key = str(params.get("code_concepts_key", "intel_code_concepts"))
        prose_concepts_key = str(params.get("prose_concepts_key", "intel_prose_concepts"))
        min_len_code = int(params.get("min_len_code", 3))
        min_len_prose = int(params.get("min_len_prose", 4))
        top_k = int(params.get("top_k", 50))
        inject_analysis = bool(params.get("inject_analysis", False))
        inject_tag = str(params.get("inject_tag", "intel_analysis"))

        meta = {
            "prose_new": 0, "prose_seen": 0, "prose_total": 0,
            "code_new": 0, "code_seen": 0, "code_total": 0
        }

        # --- 1. Analyze Prose (Text outside code blocks) ---
        prose_text = _FENCE_RE.sub(" ", text)  # Remove fenced code
        found_prose = _extract_prose_terms(
            prose_text, top_k=top_k, min_len=min_len_prose
        )

        # --- 2. Analyze Code (Text inside code blocks) ---
        found_code = []
        for match in _FENCE_RE.finditer(text):
            code_block = match.group(2)
            found_code.extend(
                _extract_code_identifiers(
                    code_block, top_k=top_k, min_len=min_len_code
                )
            )
        # Dedup code terms
        found_code = list(dict.fromkeys(found_code))

        # --- 3. Update Memory (Track similarities/differences) ---
        store = Memory.load()

        # Update Prose Concepts
        existing_prose = set(store.get(prose_concepts_key, []))
        new_prose_count = 0
        seen_prose_count = 0
        for term in found_prose:
            if term not in existing_prose:
                new_prose_count += 1
                existing_prose.add(term)
            else:
                seen_prose_count += 1

        store[prose_concepts_key] = sorted(list(existing_prose))
        meta["prose_new"] = new_prose_count
        meta["prose_seen"] = seen_prose_count
        meta["prose_total"] = len(existing_prose)
        meta["prose_key"] = prose_concepts_key

        # Update Code Concepts
        existing_code = set(store.get(code_concepts_key, []))
        new_code_count = 0
        seen_code_count = 0
        for ident in found_code:
            if ident not in existing_code:
                new_code_count += 1
                existing_code.add(ident)
            else:
                seen_code_count += 1

        store[code_concepts_key] = sorted(list(existing_code))
        meta["code_new"] = new_code_count
        meta["code_seen"] = seen_code_count
        meta["code_total"] = len(existing_code)
        meta["code_key"] = code_concepts_key

        Memory.save(store)

        # --- 4. (Optional) Inject analysis into payload ---
        if inject_analysis:
            analysis = (
                f"[{inject_tag}]\n"
                f"Prose: {new_prose_count} new, {seen_prose_count} seen (Total: {meta['prose_total']})\n"
                f"Code: {new_code_count} new, {seen_code_count} seen (Total: {meta['code_total']})"
            )
            return f"{text}\n\n{analysis}", meta

        # By default, this block is silent and just passes the payload through
        return text, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "code_concepts_key": "intel_code_concepts",
            "prose_concepts_key": "intel_prose_concepts",
            "min_len_code": 3,
            "min_len_prose": 4,
            "top_k": 50,
            "inject_analysis": False,
            "inject_tag": "intel_analysis"
        }


BLOCKS.register("intelligence", IntelligenceBlock)


# ======================= ShoppingBlock =====================================
@dataclass
class ShoppingBlock(BaseBlock):
    """
    Shopping/Resale finder using targeted search engine operators.
    Instead of scraping sites directly (which block bots), this queries
    indexed listings via DuckDuckGo using `site:domain`.

    FEATURES:
    - Multi-site search (Grailed, Depop, Mercari, eBay, JP Markets).
    - Smart Currency Filtering: Can hide results in the wrong currency.
    - Debug Visibility: Shows headers for all requested sites even if empty.
    - JP Markets: Automatically translates query to Japanese (via googletrans)
      and searches JP sites with BOTH English and Japanese queries.
    - Pluggable Search Backend:
        * backend="ddg"        -> ddgs + requests+BeautifulSoup (default)
        * backend="playwright" -> Playwright-controlled DuckDuckGo search
    - Price normalization: best-effort extraction of amount + currency,
      plus USD/JPY normalized values (price_usd, price_jpy) per listing.
    """

    # Domain mapping
    SITES = {
        "grailed": "grailed.com",
        "depop": "depop.com",
        "poshmark": "poshmark.com",
        "ebay": "ebay.com",
        "mercari": "mercari.com",  # US/Global Mercari
        "mercari_jp": "jp.mercari.com",  # Japanese Mercari
        "rakuma": "fril.jp",  # Rakuma uses fril.jp domain
        "rakuten": "rakuten.co.jp",
        "yahoo_jp": "page.auctions.yahoo.co.jp",
        "therealreal": "therealreal.com",
        "vestiaire": "vestiairecollective.com",
        "jawnflip": "jawnflip.com",
    }

    # Domains considered "Japanese marketplaces"
    JP_DOMAINS = {
        "fril.jp",
        "rakuten.co.jp",
        "page.auctions.yahoo.co.jp",
        "jp.mercari.com",
    }

    # --------------- translation helpers -----------------

    def _translate_to_japanese(self, text: str) -> str:
        """
        Translate arbitrary query text to Japanese using googletrans.
        On failure, returns "" and JP sites fall back to English-only.
        """
        text = (text or "").strip()
        if not text:
            return ""

        try:
            from googletrans import Translator  # type: ignore
            translator = Translator()
            res = translator.translate(text, dest="ja")
            return (res.text or "").strip()
        except Exception:
            return ""

    # --------------- core execution -----------------

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import re
        import time

        # --- Params ---
        query = str(params.get("query", "") or str(payload or "")).strip()
        if not query:
            return "", {"error": "ShoppingBlock requires a query (e.g., 'Raf Simons riot bomber')"}

        # Parse requested sites
        default_sites = "grailed,depop,rakuma,mercari,mercari_jp"
        requested_sites = [s.strip().lower() for s in str(params.get("sites", default_sites)).split(",")]

        num_per_site = int(params.get("num_per_site", 6))
        timeout = float(params.get("timeout", 10.0))
        currency_filter = str(params.get("currency", "")).upper()  # e.g. USD, JPY
        backend = str(params.get("backend", "ddg")).lower()  # "ddg" or "playwright"

        # Memory export
        export_key = str(params.get("export_key", "shopping_results"))

        # Japanese version of the query (for JP domains)
        jp_query = self._translate_to_japanese(query)

        # --- FX setup (USD <-> JPY) ---
        fx_usd_to_jpy = 150.0  # fallback
        fx_jpy_to_usd = 1.0 / fx_usd_to_jpy
        try:
            import requests
            r = requests.get("https://open.er-api.com/v6/latest/USD", timeout=3)
            data = r.json()
            rate = data.get("rates", {}).get("JPY")
            if isinstance(rate, (int, float)) and rate > 0:
                fx_usd_to_jpy = float(rate)
                fx_jpy_to_usd = 1.0 / fx_usd_to_jpy
        except Exception:
            pass

        # --- Helpers ---
        def _extract_price(text: str) -> str:
            # "sold for"/"winning bid" patterns
            m_sold = re.search(
                r"(?:sold for|winning bid)[:\s]+([$€£¥]\s?\d+(?:[,\.]\d+)?)",
                text,
                re.IGNORECASE,
            )
            if m_sold:
                return m_sold.group(1)

            # Generic currency+number
            m = re.search(r"([$€£¥]\s?\d+(?:[,\.]\d{3})*(?:\.\d{2})?)", text)
            if m:
                return m.group(1)

            # "Price: 500 USD"
            m2 = re.search(
                r"(?:price|val)[:\s]+(\d+(?:[,\.]\d+)*\s?(?:USD|JPY|EUR|GBP))",
                text,
                re.IGNORECASE,
            )
            return m2.group(1) if m2 else ""

        def _normalize_price(price_str: str) -> Dict[str, Any]:
            """
            Best-effort parse of price string to extract:
              - raw: original string
              - currency: 'USD', 'JPY', 'EUR', 'GBP' or None
              - amount: float or None
              - usd: float or None
              - jpy: float or None
            """
            price_str = (price_str or "").strip()
            if not price_str:
                return {"raw": "", "currency": None, "amount": None, "usd": None, "jpy": None}

            upper = price_str.upper()
            currency = None
            if "JPY" in upper or "¥" in price_str:
                currency = "JPY"
            elif "USD" in upper or "$" in price_str:
                currency = "USD"
            elif "EUR" in upper or "€" in price_str:
                currency = "EUR"
            elif "GBP" in upper or "£" in price_str:
                currency = "GBP"

            # Strip non-numeric-ish chars except . and ,
            numeric_part = re.sub(r"[^\d.,]", "", price_str)
            if not numeric_part:
                return {"raw": price_str, "currency": currency, "amount": None, "usd": None, "jpy": None}

            # Convert "12,345.67" / "12.345,67" into a float-ish
            # Simple approach: remove commas, then float
            amount = None
            try:
                amount = float(numeric_part.replace(",", ""))
            except Exception:
                pass

            usd = None
            jpy = None
            if amount is not None:
                if currency == "USD":
                    usd = amount
                    jpy = amount * fx_usd_to_jpy
                elif currency == "JPY":
                    jpy = amount
                    usd = amount * fx_jpy_to_usd
                else:
                    # For EUR/GBP/unknown we don't guess; keep raw only
                    pass

            return {"raw": price_str, "currency": currency, "amount": amount, "usd": usd, "jpy": jpy}

        def _search_ddg_backend(q: str, site_domain: str, limit: int) -> List[Dict[str, str]]:
            """
            Backend 1: ddgs + HTML DuckDuckGo via requests.
            """
            full_query = f"site:{site_domain} {q}"
            results: List[Dict[str, str]] = []

            # Try DDGS library first
            try:
                from ddgs import DDGS

                with DDGS() as ddgs:
                    for r in ddgs.text(full_query, max_results=limit, safesearch='off'):
                        results.append(
                            {
                                "title": r.get("title", ""),
                                "link": r.get("href", ""),
                                "snippet": r.get("body", ""),
                            }
                        )
                    return results
            except Exception:
                pass

            # Fallback: HTML scraping
            import requests
            from bs4 import BeautifulSoup
            from urllib.parse import unquote

            try:
                headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"}
                resp = requests.get(
                    "https://html.duckduckgo.com/html/",
                    params={"q": full_query},
                    headers=headers,
                    timeout=timeout,
                )
                soup = BeautifulSoup(resp.text, "html.parser")
                for a in soup.select(".result__a")[:limit]:
                    href = a.get("href")
                    if href and "uddg=" in href:
                        href = unquote(href.split("uddg=")[1].split("&")[0])

                    snip = ""
                    parent = a.find_parent(".result__body")
                    if parent:
                        snip_el = parent.select_one(".result__snippet")
                        snip = snip_el.get_text(strip=True) if snip_el else ""

                    results.append(
                        {
                            "title": a.get_text(strip=True),
                            "link": href,
                            "snippet": snip,
                        }
                    )
            except Exception:
                pass

            return results

        def _search_playwright_backend(q: str, site_domain: str, limit: int) -> List[Dict[str, str]]:
            """
            Backend 2: Use Playwright to drive DuckDuckGo search.
            """
            results: List[Dict[str, str]] = []
            try:
                from playwright.sync_api import sync_playwright
                from urllib.parse import quote_plus

                full_query = f"site:{site_domain} {q}"
                url = f"https://duckduckgo.com/?q={quote_plus(full_query)}"

                with sync_playwright() as p:
                    browser = p.firefox.launch(headless=True)
                    page = browser.new_page()
                    page.goto(url, timeout=int(timeout * 1000))

                    try:
                        page.wait_for_selector("a.result__a", timeout=int(timeout * 1000))
                    except Exception:
                        pass

                    anchors = page.query_selector_all("a.result__a")
                    for a in anchors[:limit]:
                        try:
                            title = (a.inner_text() or "").strip()
                            href = a.get_attribute("href") or ""
                            snippet = ""
                            parent = a.closest("div.result")
                            if parent:
                                snip_el = parent.query_selector(".result__snippet")
                                if snip_el:
                                    snippet = (snip_el.inner_text() or "").strip()
                            results.append(
                                {
                                    "title": title,
                                    "link": href,
                                    "snippet": snippet,
                                }
                            )
                        except Exception:
                            continue

                    browser.close()
            except Exception:
                # If Playwright isn't available, fall back to ddg backend
                return _search_ddg_backend(q, site_domain, limit)

            return results

        def _search_site(q: str, site_domain: str, limit: int) -> List[Dict[str, str]]:
            """Dispatch to the appropriate backend."""
            if backend == "playwright":
                return _search_playwright_backend(q, site_domain, limit)
            return _search_ddg_backend(q, site_domain, limit)

        # --- Execution ---
        valid_domains: List[Tuple[str, str]] = []
        for s in requested_sites:
            if s in self.SITES:
                valid_domains.append((s, self.SITES[s]))
            elif "." in s:
                valid_domains.append((s.split(".")[0], s))

        all_hits: List[Dict[str, Any]] = []
        output_lines = [f"### 🛍️ Shopping Results: {query}"]

        any_filtered_by_currency = False

        for site_name, domain in valid_domains:
            # Base: English query
            hits = _search_site(query, domain, num_per_site)

            # For JP domains, also search with Japanese query (if available)
            if domain in self.JP_DOMAINS and jp_query:
                jp_hits = _search_site(jp_query, domain, num_per_site)
                seen_links = {h.get("link") for h in hits}
                for jh in jp_hits:
                    if jh.get("link") not in seen_links:
                        hits.append(jh)
                        seen_links.add(jh.get("link"))

            output_lines.append(f"\n**{site_name.title()}**")

            if not hits:
                output_lines.append("_(No results found via search engine)_")
                time.sleep(0.5)
                continue

            filtered_by_currency = 0
            displayed_any = False

            for h in hits:
                raw_title = h.get("title", "") or ""
                title = (
                    raw_title.replace(f" | {site_name.title()}", "")
                    .replace(" | eBay", "")
                    .strip()
                )
                link = h.get("link", "")
                snippet = h.get("snippet", "")
                price = _extract_price(title + " " + snippet)
                norm = _normalize_price(price)

                # --- Currency Logic (for filtering only) ---
                if currency_filter and norm["currency"]:
                    cur = norm["currency"]
                    if currency_filter in ["USD", "DOLLAR"] and cur == "JPY":
                        filtered_by_currency += 1
                        any_filtered_by_currency = True
                        continue
                    if currency_filter in ["JPY", "YEN"] and cur == "USD":
                        filtered_by_currency += 1
                        any_filtered_by_currency = True
                        continue

                item_data = {
                    "site": site_name,
                    "title": title,
                    "price": price,
                    "price_usd": norm["usd"],
                    "price_jpy": norm["jpy"],
                    "currency": norm["currency"],
                    "amount": norm["amount"],
                    "link": link,
                    "snippet": snippet,
                }
                all_hits.append(item_data)

                display_str = f"- [{title}]({link})"
                if price:
                    # Show raw price; you could append normalized if you want
                    display_str += f" — **{price}**"
                    if norm["usd"] is not None and norm["currency"] == "JPY":
                        display_str += f" (~${norm['usd']:.0f} USD)"
                    elif norm["jpy"] is not None and norm["currency"] == "USD":
                        display_str += f" (~¥{int(norm['jpy']):,} JPY)"

                output_lines.append(display_str)
                displayed_any = True

            if not displayed_any and filtered_by_currency > 0:
                output_lines.append(
                    f"_(Found {filtered_by_currency} results, "
                    f"but they were hidden by your currency filter '{currency_filter}')_"
                )
            elif not displayed_any:
                output_lines.append("_(No results matched criteria)_")

            if filtered_by_currency > 0 and displayed_any:
                output_lines.append(
                    f"_({filtered_by_currency} other items hidden by currency filter)_"
                )

            time.sleep(0.5)

        # --- Final meta / memory ---
        if export_key:
            store = Memory.load()
            store[export_key] = all_hits
            Memory.save(store)

        meta = {
            "query": query,
            "query_jp": jp_query,
            "sites_searched": [d[0] for d in valid_domains],
            "total_results": len(all_hits),
            "results": all_hits,
            "filtered_by_currency": any_filtered_by_currency,
            "backend": backend,
            "fx_usd_to_jpy": fx_usd_to_jpy,
        }

        return "\n".join(output_lines), meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "Raf Simons Riot Bomber",
            "sites": "grailed,depop,rakuma,mercari,mercari_jp",
            "num_per_site": 6,
            "timeout": 10.0,
            "currency": "USD",
            "backend": "ddg",  # or "playwright"
            "export_key": "shopping_results",
        }


BLOCKS.register("shopping", ShoppingBlock)


# ======================= LinkTrackerBlock ==================================

@dataclass
class LinkTrackerBlock(BaseBlock):
    """
    Async, search + crawl + media/doc/archives finder.

    Same features as your original, but now:
      • All sqlite access goes through DatabaseSubmanager + LinkTrackerStore.
      • No direct sqlite3 usage in this block.
      • Schema + queries are store-owned.
    """

    JUNK_FILENAME_KEYWORDS = {
        "sprite", "icon", "favicon", "logo", "tracking", "pixel", "blank", "placeholder",
    }

    IGNORED_EXTENSIONS = {
        ".css", ".js", ".json", ".xml", ".svg", ".png", ".jpg", ".jpeg",
        ".gif", ".ico", ".woff", ".woff2", ".ttf", ".eot", ".map"
    }

    _URL_RE = re.compile(r"https?://[^\s\"'<>\\)]+", re.IGNORECASE)

    MEGA_HOSTS = {"mega.nz", "www.mega.nz", "mega.co.nz", "www.mega.co.nz"}
    MEGA_PATH_MARKERS = ("/file/", "/folder/", "/embed/", "/#F!", "/#!")
    MEGA_QUERY_MARKERS = ("mega.nz",)  # fallback


    def __post_init__(self):
        # Store/submanager are initialized per-run when use_database=True
        self.db: Optional[submanagers.DatabaseSubmanager] = None
        self.store: Optional[LinkTrackerStore] = None
        self.js_sniffer = submanagers.JSSniffer(submanagers.JSSniffer.Config(enable_auto_scroll=True,max_scroll_steps=40,scroll_step_delay_ms=500))
        self.network_sniffer = submanagers.NetworkSniffer(submanagers.NetworkSniffer.Config(enable_auto_scroll=True,max_scroll_steps=40,scroll_step_delay_ms=500))
        self.runtime_sniffer = submanagers.RuntimeSniffer(submanagers.RuntimeSniffer.Config())

        self.react_sniffer = submanagers.ReactSniffer(
            submanagers.ReactSniffer.Config(
                hook_history_api=True,
                hook_link_clicks=True,
                inspect_react_devtools_hook=True,
            )
        )
        self.database_sniffer = submanagers.DatabaseSniffer(
            submanagers.DatabaseSniffer.Config(
                enable_indexeddb_dump=True,  # Get Metadata
                enable_backend_fingerprint=True,  # Get Tech Stack
                enable_html_link_scan=True,  # Scan HTML for raw links
                enable_backend_link_scan=True  # Scan JS Globals for links
            )
        )
        self.interaction_sniffer = submanagers.InteractionSniffer(
            submanagers.InteractionSniffer.Config(
                enable_cdp_listeners=True,
                enable_overlay_detection=True,
                enable_form_extraction=True
            )
        )
    # ------------------------------------------------------------------ #
    # Database lifecycle (Submanager + Store)
    # ------------------------------------------------------------------ #
    def _initialize_database(self, db_path: str, logger=None) -> None:
        """
        Create and open DBSubmanager + LinkTrackerStore, install schema.
        Idempotent.
        """
        if self.db and self.store:
            return

        cfg = submanagers.DatabaseConfig(path=str(db_path or "link_corpus.db"))
        self.db = submanagers.DatabaseSubmanager(cfg, logger=logger)
        self.db.open()

        self.store = LinkTrackerStore(db=self.db)
        self.store.ensure_schema()

    # ------------------------------------------------------------------ #
    # URL helpers
    # ------------------------------------------------------------------ #
    def _is_mega_link(self, u: str) -> bool:
        try:
            pu = urlparse(u)
            host = (pu.netloc or "").lower().split(":")[0]
            path = (pu.path or "").lower()
            frag = (pu.fragment or "").lower()
            full_low = u.lower()

            if host in self.MEGA_HOSTS:
                if any(m in path for m in self.MEGA_PATH_MARKERS):
                    return True
                if frag.startswith("f!") or frag.startswith("!") or "file/" in frag or "folder/" in frag:
                    return True
                return True
            if "mega.nz/#" in full_low or "mega.co.nz/#" in full_low:
                return True

            return False
        except Exception:
            return False

    # ------------------------------------------------------------------ #
    # Search engines (unchanged)
    # ------------------------------------------------------------------ #

    async def _search_searxng(
            self,
            q: str,
            max_results: int,
            timeout: float,
            base_url: Optional[str] = None,
            page_limit: int = 1,
    ) -> List[str]:
        """
        Query a SearXNG instance and return a list of result URLs.

        - Uses ?format=json
        - Respects max_results and page_limit
        - base_url can be passed via params['searxng_url'] or SEARXNG_URL env var.
        """
        import os, json

        # Where is SearXNG?
        base_url = (
                base_url
                or os.environ.get("SEARXNG_URL")
                or "http://127.0.0.1:8080"
        ).rstrip("/")

        search_url = base_url + "/search"

        max_results = max(1, min(int(max_results), 256))
        page_limit = max(1, min(int(page_limit), 5))

        out: List[str] = []
        did_dump_debug = False

        try:
            async with aiohttp.ClientSession() as session:
                for page_idx in range(page_limit):
                    if len(out) >= max_results:
                        break

                    # SearXNG pagination: 'pageno' is 1-based
                    params = {
                        "q": q,
                        "format": "json",
                        "pageno": str(page_idx + 1),
                    }

                    text = ""
                    status = None

                    try:
                        async with session.get(
                                search_url,
                                params=params,
                                timeout=aiohttp.ClientTimeout(total=timeout),
                        ) as resp:
                            status = resp.status
                            text = await resp.text()

                            # Classic misconfig case: JSON disabled -> 403 HTML
                            if status == 403:
                                if not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    print(
                                        f"[LinkTracker][SearXNG][debug] HTTP 403 "
                                        f"query={q!r} pageno={page_idx + 1}. Body preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            if status != 200:
                                if not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    print(
                                        f"[LinkTracker][SearXNG][debug] HTTP {status} "
                                        f"query={q!r} pageno={page_idx + 1}. Body preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            try:
                                data = json.loads(text)
                            except json.JSONDecodeError as e:
                                print(f"[LinkTracker][SearXNG] JSON decode error: {e}")
                                if not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    print(
                                        f"[LinkTracker][SearXNG][debug] Bad JSON preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            results = data.get("results") or []
                            if not results:
                                # No more pages.
                                break

                            for item in results:
                                u = item.get("url")
                                if u:
                                    out.append(u)
                                    if len(out) >= max_results:
                                        break

                    except aiohttp.ClientError as e:
                        print(f"[LinkTracker][SearXNG] AIOHTTP error: {e}")
                        if not did_dump_debug and text:
                            preview = text[:1500].replace("\n", " ")
                            print(
                                f"[LinkTracker][SearXNG][debug] ClientError body preview: {preview}"
                            )
                            did_dump_debug = True
                        break

        except Exception as e:
            print(f"[LinkTracker][SearXNG] General error: {e}")

        return out[:max_results]
    async def _search_duckduckgo(
        self,
        q: str,
        max_results: int,
        ua: str,
        timeout: float,
        page_limit: int = 1,
        per_page: int = 50,
    ) -> List[str]:
        import random

        pages: List[str] = []
        seen_urls: set[str] = set()
        did_dump_debug = False

        real_ua = (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/115.0.0.0 Safari/537.36"
        )

        headers = {
            "User-Agent": real_ua,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
            "Accept-Encoding": "gzip, deflate, br",
            "Referer": "https://duckduckgo.com/",
            "Origin": "https://duckduckgo.com",
            "DNT": "1",
            "Upgrade-Insecure-Requests": "1",
            "Sec-Fetch-Site": "same-origin",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Dest": "document",
        }

        max_results = max(1, min(int(max_results), 256))
        page_limit = max(1, min(int(page_limit), 5))
        base_url = "https://html.duckduckgo.com/html/"

        try:
            async with aiohttp.ClientSession(headers=headers) as session:
                for page_idx in range(page_limit):
                    if len(pages) >= max_results:
                        break

                    if page_idx > 0:
                        st = random.uniform(2.0, 5.0)
                        print(f"[LinkTracker] Sleeping {st:.2f}s between search pages...")
                        await asyncio.sleep(st)

                    offset = page_idx * 30
                    text = ""
                    status = None
                    final_url = base_url

                    try:
                        data = {'q': q, 's': str(offset), 'dc': str(offset)}
                        async with session.post(
                            base_url,
                            data=data,
                            timeout=aiohttp.ClientTimeout(total=timeout),
                        ) as resp:
                            status = resp.status
                            final_url = str(resp.url)

                            if status == 403:
                                print(f"[LinkTracker] 403 Forbidden on page {page_idx}.")
                                if not pages and not did_dump_debug:
                                    text = await resp.text()
                                    preview = text[:2000].replace("\n", " ")
                                    print(f"[LinkTracker][DDG][debug] 403 body preview: {preview}")
                                    did_dump_debug = True
                                return pages

                            resp.raise_for_status()
                            text = await resp.text()

                    except Exception as e:
                        print(f"[LinkTracker] DuckDuckGo request failed (page {page_idx}): {e}")
                        if not pages and text and not did_dump_debug:
                            preview = text[:2000].replace("\n", " ")
                            print(f"[LinkTracker][DDG][debug] Failed page HTML preview: {preview}")
                            did_dump_debug = True
                        break

                    if "Unfortunately, bots use DuckDuckGo too." in text:
                        print("[LinkTracker] Bot detected by DDG.")
                        if not pages and not did_dump_debug:
                            preview = text[:2000].replace("\n", " ")
                            print(f"[LinkTracker][DDG][debug] Bot wall preview: {preview}")
                            did_dump_debug = True
                        break

                    soup = BeautifulSoup(text, "html.parser")
                    found_new = False

                    for a in soup.select("a.result__a"):
                        if len(pages) >= max_results:
                            break
                        href = a.get("href")
                        if not href:
                            continue
                        if "uddg=" in href:
                            try:
                                href = unquote(href.split("uddg=", 1)[1].split("&", 1)[0])
                            except Exception:
                                pass

                        if href.startswith("http") and href not in seen_urls:
                            seen_urls.add(href)
                            pages.append(href)
                            found_new = True

                    if not found_new and not pages and not did_dump_debug:
                        preview = text[:2000].replace("\n", " ")
                        print(
                            f"[LinkTracker][DDG][debug] No results on page {page_idx} for query={q!r} "
                            f"(status={status}, url={final_url}). HTML preview: {preview}"
                        )
                        did_dump_debug = True

                    if not found_new:
                        break

        except Exception as e:
            print(f"[LinkTracker] DDG outer error: {e}")

        return pages[:max_results]

    async def _search_google_cse(
        self,
        q: str,
        n: int,
        timeout: float,
        page_limit: int = 1,
    ) -> List[str]:
        import os, json

        cx = os.environ.get("GOOGLE_CSE_ID")
        key = os.environ.get("GOOGLE_API_KEY")
        if not (cx and key):
            print("[LinkTracker][GoogleCSE] Missing GOOGLE_CSE_ID or GOOGLE_API_KEY env vars.")
            return []

        max_total = max(1, min(int(n), 100))
        per_page = min(10, max_total)
        max_pages_by_n = (max_total + per_page - 1) // per_page
        pages_to_fetch = max(1, min(int(page_limit) or 1, max_pages_by_n))

        out: List[str] = []
        did_dump_debug = False

        try:
            async with aiohttp.ClientSession() as session:
                for page_idx in range(pages_to_fetch):
                    if len(out) >= max_total:
                        break

                    start = 1 + page_idx * per_page
                    if start > 100:
                        break

                    text = ""
                    status = None

                    try:
                        async with session.get(
                            "https://www.googleapis.com/customsearch/v1",
                            params={
                                "q": q,
                                "cx": cx,
                                "key": key,
                                "num": per_page,
                                "start": start,
                            },
                            timeout=aiohttp.ClientTimeout(total=timeout),
                        ) as resp:
                            status = resp.status
                            text = await resp.text()

                            if status != 200:
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    print(
                                        f"[LinkTracker][GoogleCSE][debug] HTTP {status} "
                                        f"query={q!r} start={start}. Body preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            try:
                                data = json.loads(text)
                            except json.JSONDecodeError as e:
                                print(f"[LinkTracker][GoogleCSE] JSON decode error: {e}")
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    print(f"[LinkTracker][GoogleCSE][debug] Bad JSON preview: {preview}")
                                    did_dump_debug = True
                                break

                            err_obj = data.get("error")
                            if err_obj:
                                msg = err_obj.get("message") or "Unknown CSE error"
                                reason = ""
                                errors = err_obj.get("errors") or []
                                if errors and isinstance(errors, list):
                                    reason = errors[0].get("reason") or ""
                                print(
                                    f"[LinkTracker][GoogleCSE] API error for query={q!r}, "
                                    f"start={start}: {msg} ({reason})"
                                )
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    print(f"[LinkTracker][GoogleCSE][debug] Error JSON preview: {preview}")
                                    did_dump_debug = True
                                break

                            items = data.get("items") or []
                            if not items:
                                print(
                                    f"[LinkTracker][GoogleCSE] No items for query={q!r}, "
                                    f"start={start}. Stopping pagination."
                                )
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    print(f"[LinkTracker][GoogleCSE][debug] Empty items JSON preview: {preview}")
                                    did_dump_debug = True
                                break

                            for item in items:
                                u = item.get("link")
                                if u:
                                    out.append(u)
                                    if len(out) >= max_total:
                                        break

                    except aiohttp.ClientError as e:
                        print(f"[LinkTracker][GoogleCSE] AIOHTTP error: {e}")
                        if not out and text and not did_dump_debug:
                            preview = text[:1500].replace("\n", " ")
                            print(f"[LinkTracker][GoogleCSE][debug] ClientError body preview: {preview}")
                            did_dump_debug = True
                        break

        except Exception as e:
            print(f"[LinkTracker][GoogleCSE] General error: {e}")

        return out

    # ------------------------------------------------------------------ #
    # Sitemap helpers
    # ------------------------------------------------------------------ #
    def _looks_like_sitemap(self, url: str) -> bool:
        u = url.lower()
        return any(u.endswith(x) for x in [".xml", ".xml.gz", "sitemap", "sitemap.xml", "sitemap_index.xml"])

    def _decompress_if_needed(self, url: str, raw: bytes) -> str:
        if not raw:
            return ""
        if url.lower().endswith(".gz"):
            try:
                raw = gzip.decompress(raw)
            except Exception:
                return ""
        try:
            return raw.decode("utf-8", errors="ignore")
        except Exception:
            return ""

    def _parse_sitemap_any(self, xml_text: str) -> tuple[list[str], list[str]]:
        if not xml_text.strip():
            return [], []
        try:
            root = ET.fromstring(xml_text)
        except Exception:
            return [], []

        ns = ""
        if root.tag.startswith("{"):
            ns = root.tag.split("}", 1)[0] + "}"

        sitemap_urls = []
        page_urls = []

        if root.tag.endswith("sitemapindex"):
            for sm in root.findall(f".//{ns}sitemap/{ns}loc"):
                if sm.text and sm.text.strip().startswith("http"):
                    sitemap_urls.append(sm.text.strip())

        if root.tag.endswith("urlset"):
            for loc in root.findall(f".//{ns}url/{ns}loc"):
                if loc.text and loc.text.strip().startswith("http"):
                    page_urls.append(loc.text.strip())

        return sitemap_urls, page_urls

    # ------------------------------------------------------------------ #
    # Scoring / pagination helpers
    # ------------------------------------------------------------------ #
    def _score_site_url(self, u: str, keywords: list[str], targets: set[str]) -> int:
        path = urlparse(u).path.lower()
        score = 0

        for tok, w in [
            ("/details/", 8),
            ("/item/", 6),
            ("/watch/", 4),
            ("/download/", 9),
            ("/track/", 4),
            ("/file/", 4),
            ("/audio/", 3),
            ("/video/", 3),
            ("/docs/", 2),
        ]:
            if tok in path:
                score += w

        for tok, w in [
            ("/search", -6),
            ("/tag/", -3),
            ("/category/", -3),
            ("/browse", -3),
            ("/archives", -2),
        ]:
            if tok in path:
                score += w

        if any(path.endswith(ext) for ext in targets):
            score += 10

        low = u.lower().replace("%20", " ")
        score += sum(2 for k in keywords if k and k in low)

        return score

    def _extract_next_page_links(self, soup, base_url: str) -> list[str]:
        out = []
        for a in soup.select("a[rel=next], a.next, a:-soup-contains('Next'), a:-soup-contains('Older')"):
            href = a.get("href")
            if href:
                out.append(urljoin(base_url, href))
        return out[:3]

    def _extract_internal_result_links(self, soup, base_url: str, site_host: str) -> list[str]:
        out = []
        containers = soup.select(
            "article a[href], .result a[href], .search-result a[href], .item a[href], li a[href]"
        )
        for a in containers:
            href = a.get("href")
            if not href:
                continue
            full = urljoin(base_url, href)
            host = urlparse(full).netloc.lower()
            if site_host in host:
                out.append(full)
            if len(out) >= 200:
                break
        return list(dict.fromkeys(out))

    def _archive_ident_to_downloads(self, ident: str) -> list[str]:
        return [
            f"https://archive.org/metadata/{ident}",
            f"https://archive.org/download/{ident}/",
            f"https://archive.org/details/{ident}",
        ]

    async def _crawl_sitemaps_for_site(
        self,
        http: submanagers.HTTPSSubmanager,
        root: str,
        sm_urls: list[str],
        keywords: list[str],
        targets: set[str],
        per_site_cap: int,
        global_seen: set[str],
    ) -> list[str]:
        to_visit = list(dict.fromkeys(sm_urls))
        visited_sm = set()
        collected = []

        while to_visit and len(collected) < per_site_cap * 5:
            sm = to_visit.pop(0)
            if sm in visited_sm:
                continue
            visited_sm.add(sm)

            raw = await http.get_bytes(sm)
            xml = self._decompress_if_needed(sm, raw)
            child_sms, pages = self._parse_sitemap_any(xml)

            for c in child_sms:
                if c not in visited_sm and self._looks_like_sitemap(c):
                    to_visit.append(c)

            for p in pages:
                if p in global_seen:
                    continue
                global_seen.add(p)
                collected.append(p)

        collected.sort(key=lambda u: self._score_site_url(u, keywords, targets), reverse=True)
        return collected[:per_site_cap]

    # ------------------------------------------------------------------ #
    # Playwright shared context manager (unchanged)
    # ------------------------------------------------------------------ #
    async def _open_playwright_context(
            self,
            ua: str,
            block_resources: bool,
            blocked_resource_types: set[str],
            block_domains: bool,
            blocked_domains: set[str],
            log: List[str],
            *,
            use_camoufox: bool = False,
            camoufox_options: Optional[Dict[str, Any]] = None,

            # NEW:
            pw_launch_args: Optional[List[str]] = None,
            pw_headless: bool = True,
            pw_channel: Optional[str] = None,
            pw_proxy: Optional[Dict[str, Any]] = None,
    ):
        """
        Open a shared Playwright/Camoufox browser context.

        Returns (p_handle, browser, context) where:
          - For plain Playwright:
              p_handle = async_playwright() instance
          - For Camoufox:
              p_handle = AsyncCamoufox instance (so we can __aexit__ it later)
        """
        # ---- small helper for blocked domains ----
        def _host_matches_blocked(host: str) -> bool:
            host = host.split(":", 1)[0].lower()
            for bd in blocked_domains:
                bd = bd.lower()
                if not bd:
                    continue
                if host == bd or host.endswith("." + bd):
                    return True
            return False

        # ---- Camoufox path ----
        if use_camoufox:
            if AsyncCamoufox is None:
                log.append("[PlaywrightCtx] Camoufox requested but not installed; falling back to Chromium.")
            else:
                try:
                    # Default Camoufox launch opts; you can tweak these
                    options = {
                        "headless": True,
                        "block_images": block_resources,
                        "block_webrtc": True,
                        "geoip": False,
                        "humanize": False,
                    }
                    if camoufox_options:
                        options.update(camoufox_options)

                    # Async context manager: we keep the CM instance as p_handle
                    cf_cm = AsyncCamoufox(**options)
                    browser = await cf_cm.__aenter__()  # returns a Playwright-like Browser
                    context = await browser.new_context(user_agent=ua)

                    # Route blocking is exactly like Playwright Firefox
                    if block_resources or block_domains:
                        async def route_blocker(route, request):
                            rtype = (request.resource_type or "").lower()
                            try:
                                host = urlparse(request.url).netloc.lower()
                            except Exception:
                                host = ""

                            if block_domains and _host_matches_blocked(host):
                                await route.abort()
                                return

                            if block_resources and rtype in blocked_resource_types:
                                await route.abort()
                                return

                            await route.continue_()

                        await context.route("**/*", route_blocker)

                    log.append("[PlaywrightCtx] Camoufox context ready.")
                    return cf_cm, browser, context

                except Exception as e:
                    log.append(f"[PlaywrightCtx] Camoufox init failed ({e}); falling back to Chromium.")

        # ---- Standard Playwright (Chromium) path ----
        try:
            from playwright.async_api import async_playwright
        except ImportError:
            log.append("Playwright not installed.")
            return None, None, None

        p = await async_playwright().start()

        launch_opts = {
            "headless": pw_headless,
            "args": list(pw_launch_args or []),
        }
        if pw_channel:
            launch_opts["channel"] = pw_channel
        if pw_proxy:
            launch_opts["proxy"] = pw_proxy

        browser = await p.chromium.launch(**launch_opts)
        context = await browser.new_context(user_agent=ua)

        if block_resources or block_domains:
            async def route_blocker(route, request):
                rtype = (request.resource_type or "").lower()
                try:
                    host = urlparse(request.url).netloc.lower()
                except Exception:
                    host = ""

                if block_domains and _host_matches_blocked(host):
                    await route.abort()
                    return

                if block_resources and rtype in blocked_resource_types:
                    await route.abort()
                    return

                await route.continue_()

            await context.route("**/*", route_blocker)

        log.append("Playwright shared context ready.")
        return p, browser, context

    async def _close_playwright_context(self, p, browser, context, log: List[str]):
        # Close page context
        try:
            if context:
                close_ctx = getattr(context, "close", None)
                if callable(close_ctx):
                    if asyncio.iscoroutinefunction(close_ctx):
                        await close_ctx()
                    else:
                        close_ctx()
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox context: {e}")

        # Close browser
        try:
            if browser:
                close_browser = getattr(browser, "close", None)
                if callable(close_browser):
                    if asyncio.iscoroutinefunction(close_browser):
                        await close_browser()
                    else:
                        close_browser()
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox browser: {e}")

        # Close handle:
        #   - Playwright: p.stop()
        #   - Camoufox: await p.__aexit__(...)
        try:
            if p:
                stop = getattr(p, "stop", None)

                # async_playwright handle
                if stop:
                    if asyncio.iscoroutinefunction(stop):
                        await stop()
                    else:
                        stop()

                else:
                    # AsyncCamoufox (or any other async CM)
                    aexit = getattr(p, "__aexit__", None)
                    if aexit:
                        if asyncio.iscoroutinefunction(aexit):
                            await aexit(None, None, None)
                        else:
                            aexit(None, None, None)

            log.append("Playwright/Camoufox shared context closed.")
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox handle: {e}")
    async def _pw_fetch_with_sniff(self, context, page_url, timeout, log, extensions=None):
        return await asyncio.wait_for(self.network_sniffer.sniff(
            context, page_url,
            timeout=timeout,
            log=log,
            extensions=extensions,
        ),timeout=25)

    async def _pw_fetch_js_links(self, context, page_url, timeout, log, extensions=None):
        return await asyncio.wait_for(self.js_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
            extensions=extensions,
        ),timeout=25)
    async def _pw_fetch_runtime_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.runtime_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
        ),timeout=25)

    async def _pw_fetch_react_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.react_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
        ),timeout=25)

    async def _pw_fetch_database_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.database_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
        ),timeout=25)

    async def _pw_fetch_interaction_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.interaction_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log
        ),timeout=25)
    # ------------------------------------------------------------------ #
    # Main execution (Async)
    # ------------------------------------------------------------------ #
    async def _execute_async(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        # --------- Natural ChatBlock-style parsing of context / lexicon ---------
        text = str(payload or "")

        inline_ctx: str = ""
        inline_lex: List[str] = []

        # Last [context] block
        try:
            inline_ctx = text.rsplit("[context]\n", 1)[1]
        except Exception:
            inline_ctx = ""

        # Last [lexicon] block (up to the next [tag)
        try:
            lex_part = text.rsplit("[lexicon]\n", 1)[1]
            lex_part = lex_part.split("\n[", 1)[0]
            inline_lex = [w.strip() for w in lex_part.split(",") if w.strip()]
        except Exception:
            inline_lex = []

        # Core text = everything before the blocks
        core = text
        if inline_ctx:
            core = core.rsplit("[context]\n", 1)[0]
        if inline_lex:
            core = core.rsplit("[lexicon]\n", 1)[0]
        core = core.strip()

        query_raw = str(params.get("query", "") or str(payload or "")).strip()
        subpipeline = params.get("subpipeline", None)

        # --------- Extract URL seeds from context + lexicon (if present) ---------
        context_urls: List[str] = []
        if inline_ctx:
            ctx_slice = inline_ctx[:20000]   # sanity cap
            for m in self._URL_RE.finditer(ctx_slice):
                context_urls.append(m.group(0))

        lexicon_url_seeds: List[str] = []
        non_url_lex_terms: List[str] = []
        for term in inline_lex:
            t = term.strip()
            if not t:
                continue
            # If it looks like a URL, treat it as URL seed; otherwise as a keyword term
            if self._URL_RE.match(t):
                lexicon_url_seeds.append(t)
            else:
                non_url_lex_terms.append(t)

        use_camoufox = bool(params.get("use_camoufox", False))
        camoufox_options = params.get("camoufox_options") or {}
        if not isinstance(camoufox_options, dict):
            camoufox_options = {}
        camoufox_options.update({"i_know_what_im_doing": True})
        # ------------------- DB setup ------------------- #
        use_database = bool(params.get("use_database", False))
        db_path = params.get("db_path", "link_corpus.db")
        if use_database:
            self._initialize_database(db_path, logger=getattr(self, "logger", None))

        store = self.store  # local alias (may be None)

        # ----------------- Subpipeline ------------------ #
        pipeline_result: Any = query_raw
        pipeline_queries: List[str] = []
        pipeline_urls: List[str] = []

        if subpipeline:
            subpipe_out: Any = self.run_sub_pipeline(
                initial_value=query_raw,
                pipeline_param_name="subpipeline",
                parent_params=params,
                collect=True,
            )

            if isinstance(subpipe_out, dict) and subpipe_out.get("__subpipeline__"):
                pipeline_result = subpipe_out.get("final")
                pipeline_queries = list(subpipe_out.get("queries") or [])
                pipeline_urls = list(subpipe_out.get("urls") or [])
            else:
                pipeline_result = subpipe_out
        # Naturally merge URL seeds from [context] and [lexicon] into pipeline URLs
        extra_seed_urls: List[str] = []
        if context_urls:
            extra_seed_urls.extend(context_urls)
        if lexicon_url_seeds:
            extra_seed_urls.extend(lexicon_url_seeds)

        if extra_seed_urls:
            if not pipeline_urls:
                pipeline_urls = []
            pipeline_urls.extend(extra_seed_urls)

        # =========================================================================
        # <--- NEW: Memory Sources Ingestion (SocketPipe Bridge)
        # =========================================================================
        memory_sources_raw = str(params.get("memory_sources", "")).strip()

        if memory_sources_raw:
            try:
                mem_data = Memory.load()
                # Split "socketpipe_links, socketpipe_domains" into keys
                keys_to_read = [k.strip() for k in memory_sources_raw.split(",") if k.strip()]

                for key in keys_to_read:
                    data = mem_data.get(key)
                    if not data:
                        continue

                    # Handle lists (standard SocketPipe output) or single items
                    items = data if isinstance(data, list) else [data]

                    for item in items:
                        candidate = None

                        # 1. Extract string from Dict or raw String
                        if isinstance(item, dict):
                            # Try standard SocketPipe keys
                            candidate = item.get("url") or item.get("domain") or item.get("text")
                        elif isinstance(item, (str, int, float)):
                            candidate = str(item)

                        if not candidate:
                            continue

                        cand_str = str(candidate).strip()
                        if not cand_str:
                            continue

                        # 2. CLASSIFY: URL vs Keyword

                        # A) It's definitely a URL (http/https)
                        if "://" in cand_str or cand_str.startswith(("http:", "https:")):
                            pipeline_urls.append(cand_str)

                        # B) It looks like a domain (has dot, no spaces) -> Treat as Seed URL
                        elif "." in cand_str and " " not in cand_str and not cand_str.startswith("."):
                            # Prepend protocol to make it actionable
                            pipeline_urls.append(f"https://{cand_str}")

                        # C) It's just text -> Treat as Lexicon Keyword
                        else:
                            # Adds to list used for relevancy scoring
                            non_url_lex_terms.append(cand_str)

            except Exception as e:
                # Log but don't crash
                msg = f"[LinkTracker] Error reading memory sources '{memory_sources_raw}': {e}"
                print(msg)
        # ------------------- Config --------------------- #
        mode = str(params.get("mode", "docs")).lower()
        scan_limit = int(params.get("scan_limit", 5))
        max_pages_total = max(1, int(params.get("max_pages_total", scan_limit)))

        timeout = float(params.get("timeout", 5.0))
        verify_links = bool(params.get("verify", True))
        engine = str(params.get("engine", "duckduckgo")).lower()

        use_js = bool(params.get("use_js", False))
        return_all_js_links = bool(params.get("return_all_js_links", False))
        max_links_per_page = int(params.get("max_links_per_page", 500))
        search_results_cap = int(params.get("search_results_cap", 256))

        search_page_limit = int(params.get("search_page_limit", 1))
        search_per_page = int(params.get("search_per_page", 50))

        use_network_sniff = bool(params.get("use_network_sniff", False))
        return_network_sniff_links = bool(params.get("return_network_sniff_links", False))

        # NEW: runtime sniffer toggles
        use_runtime_sniff = bool(params.get("use_runtime_sniff", False))
        return_runtime_sniff_hits = bool(params.get("return_runtime_sniff_hits", False))
        use_react_sniff = bool(params.get("use_react_sniff", False))
        return_react_sniff_hits = bool(params.get("return_react_sniff_hits", False))

        use_interaction_sniff = bool(params.get("use_interaction_sniff", False))
        return_interaction_sniff_hits = bool(params.get("return_interaction_sniff_hits", False))

        use_database_sniff = bool(params.get("use_database_sniff", False))
        return_database_sniff_hits = bool(
            params.get("return_database_sniff_hits", False)
        )

        min_term_overlap_raw = int(params.get("min_term_overlap", 1))
        min_term_overlap = max(1, min_term_overlap_raw)

        custom_ext = str(params.get("extensions", "")).split(",")
        keywords_in_url = str(params.get("url_keywords", "")).split(",")
        site_require_raw = str(params.get("site_require", "")).split(",")
        required_sites = [s.strip().lower() for s in site_require_raw if s.strip()]
        max_depth = max(0, int(params.get("max_depth", 0)))

        # HTTP/TLS config for HTTPSSubmanager
        http_retries = int(params.get("http_retries", 2))
        http_max_conn_per_host = int(params.get("http_max_conn_per_host", 8))
        http_verify_tls = bool(params.get("http_verify_tls", True))
        http_ca_bundle = params.get("http_ca_bundle", None)

        db_allow_rescan = bool(params.get("db_allow_rescan", False))

        # PW blocking params
        block_resources = bool(params.get("block_resources", False))
        blocked_resource_types = {
            t.strip().lower()
            for t in str(params.get("blocked_resource_types", "")).split(",")
            if t.strip()
        } or {"image", "stylesheet", "font"}

        block_domains = bool(params.get("block_domains", True))
        user_blocked_domains = {
            d.strip().lower()
            for d in str(params.get("blocked_domains", "")).split(",")
            if d.strip()
        }

        default_blocked_domains = {
            "google-analytics.com", "googletagmanager.com", "doubleclick.net",
            "facebook.com", "facebook.net", "twitter.com", "scorecardresearch.com",
            "quantserve.com", "hotjar.com", "segment.io", "mixpanel.com",
            "cloudflareinsights.com", "stats.g.doubleclick.net",
            "adservice.google.com", "ads.yahoo.com", "adsafeprotected.com",
        }

        blocked_domains: set[str] = set()
        if block_domains:
            blocked_domains = default_blocked_domains.union(user_blocked_domains)

        pw_launch_args = params.get("pw_launch_args") or []
        if isinstance(pw_launch_args, str):
            # allow comma-separated string
            pw_launch_args = [a.strip() for a in pw_launch_args.split(",") if a.strip()]
        if not isinstance(pw_launch_args, list):
            pw_launch_args = []

        pw_headless = bool(params.get("pw_headless", True))
        pw_channel = params.get("pw_channel", None)  # e.g. "chrome"
        pw_proxy = params.get("pw_proxy", None)  # e.g. {"server":"http://127.0.0.1:8080"}

        # ------------------- Targets -------------------- #
        targets: set[str] = set()
        if mode == "media":
            targets.update([".mp3", ".wav", ".flac", ".m4a", ".ogg"])
        elif mode == "pictures":
            targets.update([
                ".jpg", ".jpeg", ".png", ".gif", ".webp",
                ".bmp", ".tiff", ".tif",
                ".heic", ".heif",
                ".avif", ".svg"
            ])
        elif mode == "docs":
            targets.update([".pdf", ".epub", ".mobi", ".doc", ".docx"])
        elif mode == "archives":
            targets.update([".zip", ".rar", ".7z", ".tar", ".gz"])

        for e in custom_ext:
            e = e.strip()
            if not e:
                continue
            if not e.startswith("."):
                e = "." + e
            targets.add(e.lower())

        if not targets:
            targets.update([".pdf", ".epub", ".mobi", ".doc", ".docx"])

        # ------------------- Keywords ------------------- #
        keywords: List[str] = [k.strip().lower() for k in keywords_in_url if k.strip()]
        strict_keywords = bool(params.get("strict_keywords", False))

        if query_raw:
            if strict_keywords:
                whole = query_raw.lower().strip()
                if whole and whole not in keywords:
                    keywords.append(whole)
            else:
                for qt in [w.strip().lower() for w in query_raw.split() if w.strip()]:
                    if qt not in keywords:
                        keywords.append(qt)
        # Add non-URL lexicon terms as natural keyword seasoning
        for term in non_url_lex_terms:
            lt = term.lower()
            if lt and lt not in keywords:
                keywords.append(lt)
        # -------------------- Helpers ------------------- #
        def _clean_domain(u: str) -> str:
            try:
                return urlparse(u).netloc.lower().split(":")[0]
            except Exception:
                return ""

        def _allowed_by_required_sites(u: str) -> bool:
            if not required_sites:
                return True
            d = _clean_domain(u)
            return any(req in d for req in required_sites)

        def _term_overlap_ok(haystack: str) -> bool:
            if not keywords:
                return True
            h = haystack.lower()
            hits = 0
            for k in keywords:
                if k and k in h:
                    hits += 1
                    if hits >= min_term_overlap:
                        return True
            return False

        def _clean_path(u: str) -> str:
            try:
                return urlparse(u).path.lower()
            except Exception:
                return ""

        def _augment_search_query(q: str, mode: str, required_sites: List[str]) -> str:
            sq = q.strip()
            site_clauses = []
            for raw in required_sites or []:
                s = (raw or "").strip().lower()
                if not s:
                    continue
                if "://" in s:
                    s = s.split("://", 1)[1]
                s = s.split("/", 1)[0].lstrip(".")
                if s:
                    site_clauses.append(f"site:{s}")

            if site_clauses:
                sites_expr = " OR ".join(site_clauses)
                sq = f"({sites_expr}) {sq}" if sq else f"({sites_expr})"

            q_lower = sq.lower()
            if mode == "media":
                if not any(x in q_lower for x in ["mp3", "flac", "m4a", "ogg"]):
                    sq = f"{sq} (mp3 OR flac OR m4a OR ogg)".strip()
            elif mode == "docs":
                if "filetype:pdf" not in q_lower:
                    sq = f"{sq} filetype:pdf".strip()
            return sq

        def _is_search_url(u: str) -> bool:
            try:
                pu = urlparse(u)
                path = (pu.path or "").lower()
                q = (pu.query or "").lower()
                if any(tok in path for tok in ["/search", "/results", "/query", "search.php"]):
                    return True
                if any(k + "=" in q for k in ["q", "query", "s", "search", "keyword"]):
                    return True
                return False
            except Exception:
                return False

        def _dedupe(seq: List[str]) -> List[str]:
            seen = set()
            out = []
            for s in seq:
                if s not in seen:
                    seen.add(s)
                    out.append(s)
            return out

        # -------------------- Triage -------------------- #
        candidate_pages: List[str] = []
        direct_asset_urls: List[str] = []
        queries_to_run: List[str] = []
        skip_search_engine = False

        if pipeline_urls:
            skip_search_engine = False
            unique_urls = _dedupe([str(u).strip() for u in pipeline_urls if str(u).strip()])

            for u in unique_urls:
                if not _allowed_by_required_sites(u):
                    continue
                path = _clean_path(u)

                if self._is_mega_link(u):
                    direct_asset_urls.append(u)
                    continue

                if any(path.endswith(ext) for ext in targets):
                    if _term_overlap_ok(u):
                        direct_asset_urls.append(u)
                    continue

                if any(path.endswith(ext) for ext in self.IGNORED_EXTENSIONS):
                    continue

                candidate_pages.append(u)

            candidate_pages = candidate_pages[:max_pages_total]

        if (not skip_search_engine) and pipeline_queries:
            for qv in pipeline_queries:
                qv_s = str(qv).strip()
                if qv_s:
                    queries_to_run.append(qv_s)

        if not pipeline_urls and not pipeline_queries:
            if isinstance(pipeline_result, list) and pipeline_result:
                for qv in pipeline_result:
                    qv_s = str(qv).strip()
                    if qv_s:
                        queries_to_run.append(qv_s)
            else:
                base_q: Optional[str] = None
                if isinstance(pipeline_result, str) and pipeline_result.strip():
                    base_q = pipeline_result.strip()
                elif query_raw:
                    base_q = query_raw
                if base_q:
                    queries_to_run.append(base_q)

        if not queries_to_run and query_raw and not skip_search_engine:
            queries_to_run = [query_raw]

        queries_to_run = _dedupe(queries_to_run)
        query = queries_to_run[0] if queries_to_run else query_raw

        # ---------------- Search discovery --------------- #
        explicit_site_seeds: set[str] = set()
        synthetic_search_seeds: set[str] = set()

        if not skip_search_engine and queries_to_run:
            ua_search = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/LinkTracker"
            seen_search_urls: set[str] = set()

            # -------- Engine: database (Store-backed) -------- #
            if engine == "database":
                if not use_database or not store:
                    print("[LinkTracker][db] engine=database requires use_database=True.")
                else:
                    print("[LinkTracker] Running Advanced Database Intelligence...")

                    db_seed_limit = int(params.get("db_seed_limit", 250))
                    db_seed_max_age_days = params.get("db_seed_max_age_days", None)

                    db_assets = store.fetch_db_seed_assets(
                        limit=db_seed_limit * 2,
                        require_keywords=keywords,
                        required_sites=required_sites,
                        max_age_days=db_seed_max_age_days,
                    )

                    proven_urls = [row["url"] for row in db_assets if row.get("url")]
                    predicted_urls = self._predict_next_in_sequence(proven_urls)
                    if predicted_urls:
                        print(f"[db] Generated {len(predicted_urls)} predictive sequence URLs (fuzzing).")
                        direct_asset_urls.extend(predicted_urls)

                    proven_hubs = store.fetch_proven_hubs(required_sites, min_hits=1)
                    if proven_hubs:
                        print(f"[db] identified {len(proven_hubs)} high-yield hubs for re-crawling.")
                        candidate_pages.extend(proven_hubs)

                    cand_from_db, direct_from_db = store.seed_pages_from_database(
                        db_assets=db_assets,
                        targets=targets,
                        max_pages_total=max_pages_total,
                        required_sites=required_sites,
                        keywords=keywords,
                        min_term_overlap=min_term_overlap,
                    )

                    candidate_pages.extend(cand_from_db)
                    direct_asset_urls.extend(direct_from_db)

                    candidate_pages = list(dict.fromkeys(candidate_pages))[:max_pages_total]
                    direct_asset_urls = list(dict.fromkeys(direct_asset_urls))

                    print(f"[db] Execution Plan: Checking {len(direct_asset_urls)} assets "
                          f"({len(predicted_urls)} predicted) & Crawling {len(candidate_pages)} hubs.")

            # -------- Engine: sites -------- #
            if engine == "sites" and required_sites:
                seed_pages, syn_seeds, exp_seeds = self._seed_pages_from_required_sites(
                    required_sites=required_sites,
                    queries=queries_to_run,
                    probe_cap_per_site=max(8, len(queries_to_run) * 3),
                    sitemap_cap_per_site=12,
                    hub_cap_per_site=10,
                )
                synthetic_search_seeds = syn_seeds
                explicit_site_seeds = exp_seeds

                per_site_cap = max(5, max_pages_total // max(1, len(required_sites)))
                global_seen = set()

                # Use a dedicated HTTPSSubmanager just for the “sites” engine
                ua_http_sites = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/LinkTracker"
                async with submanagers.HTTPSSubmanager(
                    user_agent=ua_http_sites,
                    timeout=timeout,
                    retries=http_retries,
                    max_conn_per_host=http_max_conn_per_host,
                    verify=http_verify_tls,
                    ca_bundle=http_ca_bundle,
                ) as http_sites:

                    for site in required_sites:
                        root = f"https://{site.strip().lstrip('.')}".rstrip("/") + "/"
                        host = urlparse(root).netloc.lower()

                        # --- robots.txt -> sitemap URLs ---
                        robots_url = root + "robots.txt"
                        try:
                            robots_txt = await http_sites.get_text(robots_url)
                        except Exception:
                            robots_txt = ""
                        sm_urls = self._extract_sitemap_urls_from_robots(robots_txt)

                        if not sm_urls:
                            sm_urls = [u for u in seed_pages if "sitemap" in u and site in u][:8]

                        # --- Crawl sitemaps for good candidate pages ---
                        best_from_sitemaps = await self._crawl_sitemaps_for_site(
                            http=http_sites,
                            root=root,
                            sm_urls=sm_urls,
                            keywords=keywords,
                            targets=targets,
                            per_site_cap=per_site_cap,
                            global_seen=global_seen,
                        )

                        # --- Expand from internal “search/hub” pages ---
                        hub_like = [u for u in seed_pages if site in u and _is_search_url(u)]
                        expanded_from_hubs: list[str] = []

                        for hub in hub_like[:3]:
                            try:
                                html_hub = await http_sites.get_text(hub)
                                soup = BeautifulSoup(html_hub or "", "html.parser")

                                expanded_from_hubs.extend(
                                    self._extract_internal_result_links(soup, hub, host)
                                )

                                for nxt in self._extract_next_page_links(soup, hub):
                                    html_nxt = await http_sites.get_text(nxt)
                                    soup_nxt = BeautifulSoup(html_nxt or "", "html.parser")
                                    expanded_from_hubs.extend(
                                        self._extract_internal_result_links(soup_nxt, nxt, host)
                                    )
                            except Exception:
                                # ignore hub failures; they’re just bonuses
                                pass

                        expanded_from_hubs = list(dict.fromkeys(expanded_from_hubs))
                        expanded_from_hubs.sort(
                            key=lambda u: self._score_site_url(u, keywords, targets), reverse=True
                        )
                        expanded_from_hubs = expanded_from_hubs[:per_site_cap]

                        merged = list(
                            dict.fromkeys(
                                [root]
                                + best_from_sitemaps
                                + expanded_from_hubs
                                + [u for u in seed_pages if site in u]
                            )
                        )
                        merged.sort(
                            key=lambda u: self._score_site_url(u, keywords, targets), reverse=True
                        )

                        for u in merged:
                            if len(candidate_pages) >= max_pages_total:
                                break
                            if _allowed_by_required_sites(u) and (not keywords or _term_overlap_ok(u)):
                                candidate_pages.append(u)

                candidate_pages = list(dict.fromkeys(candidate_pages))[:max_pages_total]

            # -------- Engine: duckduckgo -------- #
            elif engine == "duckduckgo":
                for qv in queries_to_run:
                    sq = _augment_search_query(qv, mode, required_sites)
                    try:
                        urls = await self._search_duckduckgo(
                            sq,
                            max_results=search_results_cap,
                            ua=ua_search,
                            timeout=timeout,
                            page_limit=search_page_limit,
                            per_page=search_per_page,
                        )
                    except Exception as e:
                        print(f"[search][ddg] error for {sq!r}: {e}")
                        urls = []

                    for u in urls:
                        if len(candidate_pages) >= max_pages_total:
                            break
                        if not u or u in seen_search_urls:
                            continue
                        if not _allowed_by_required_sites(u):
                            continue
                        candidate_pages.append(u)
                        seen_search_urls.add(u)

            # -------- Engine: google_cse -------- #
            elif engine == "google_cse":
                for qv in queries_to_run:
                    sq = _augment_search_query(qv, mode, required_sites)
                    try:
                        urls = await self._search_google_cse(
                            sq,
                            n=search_results_cap,
                            timeout=timeout,
                            page_limit=search_page_limit,
                        )
                    except Exception as e:
                        print(f"[search][cse] error for {sq!r}: {e}")
                        urls = []

                    for u in urls:
                        if len(candidate_pages) >= max_pages_total:
                            break
                        if not u or u in seen_search_urls:
                            continue
                        if not _allowed_by_required_sites(u):
                            continue
                        candidate_pages.append(u)
                        seen_search_urls.add(u)
            # -------- Engine: searxng -------- #
            elif engine == "searxng":
                searxng_url = params.get("searxng_url") or None
                for qv in queries_to_run:
                    sq = _augment_search_query(qv, mode, required_sites)
                    try:
                        urls = await self._search_searxng(
                            sq,
                            max_results=search_results_cap,
                            timeout=timeout,
                            base_url=searxng_url,
                            page_limit=search_page_limit,
                        )
                    except Exception as e:
                        print(f"[search][searxng] error for {sq!r}: {e}")
                        urls = []

                    for u in urls:
                        if len(candidate_pages) >= max_pages_total:
                            break
                        if not u or u in seen_search_urls:
                            continue
                        if not _allowed_by_required_sites(u):
                            continue
                        candidate_pages.append(u)
                        seen_search_urls.add(u)
        # ---------------- Crawl state ------------------ #
        found_assets: List[Dict[str, Any]] = []
        seen_asset_urls: set[str] = set()
        visited_pages: set[str] = set()

        log: List[str] = []
        all_js_links: List[Dict[str, str]] = []
        all_network_links: List[Dict[str, str]] = []
        all_runtime_hits: List[Dict[str, Any]] = []
        all_react_hits: List[Dict[str, Any]] = []  # [PATCH] New list
        all_database_hits: List[Dict[str, Any]] = []
        all_interaction_hits: List[Dict[str, Any]] = []
        # choose UA for HTTP engine
        ua_http = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/LinkTracker"

        # HTTPSSubmanager handles all HTTP(S) GET/HEAD for this run
        async with submanagers.HTTPSSubmanager(
            user_agent=ua_http,
            timeout=timeout,
            retries=http_retries,
            max_conn_per_host=http_max_conn_per_host,
            verify=http_verify_tls,
            ca_bundle=http_ca_bundle,
        ) as http:

            # ---------------- Direct assets ---------------- #
            if direct_asset_urls:
                for u in direct_asset_urls:
                    if use_database and store and store.asset_exists(u):
                        log.append(f"Skipping {u} (already in database)")
                        continue
                    if u in seen_asset_urls:
                        continue
                    seen_asset_urls.add(u)

                    status = "unverified"
                    size = "?"
                    if verify_links:
                        try:
                            h_status, headers = await http.head(u)
                            if h_status == 200:
                                status = "200 OK"
                                cl = headers.get("Content-Length")
                                if cl:
                                    try:
                                        size = f"{int(cl) // 1024} KB"
                                    except ValueError:
                                        size = "?"
                            else:
                                status = f"Dead ({h_status})"
                        except Exception:
                            status = "Timeout/Error"

                    if not verify_links or status == "200 OK":
                        filename = _clean_path(u).rsplit("/", 1)[-1] or "[asset]"
                        asset = {
                            "text": filename[:100],
                            "url": u,
                            "source": "<urls>",
                            "size": size,
                            "status": status,
                        }
                        found_assets.append(asset)
                        if use_database and store:
                            store.upsert_asset(asset)

            def _should_persist_page(u: str) -> bool:
                if engine != "sites":
                    return True
                if u in explicit_site_seeds or u in synthetic_search_seeds:
                    return False
                if _is_search_url(u):
                    return False
                return True

            # --- Shared Playwright context, if needed --- #
            pw_needed = (
                    use_js or
                    use_network_sniff or
                    use_runtime_sniff or
                    use_react_sniff or
                    use_database_sniff or
                    use_interaction_sniff
            )
            pw_p = pw_browser = pw_context = None
            try:
                if pw_needed:
                    ua_pw = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/LinkTracker"
                    pw_p, pw_browser, pw_context = await self._open_playwright_context(
                        ua=ua_pw,
                        block_resources=block_resources,
                        blocked_resource_types=blocked_resource_types,
                        block_domains=block_domains,
                        blocked_domains=blocked_domains,
                        log=log,
                        use_camoufox=use_camoufox,
                        camoufox_options=camoufox_options,
                        pw_launch_args=pw_launch_args,  # NEW
                        pw_headless=pw_headless,  # NEW
                        pw_channel=pw_channel,  # NEW
                        pw_proxy=pw_proxy,  # NEW
                    )
            except:
                # ALWAYS close Camoufox/Playwright if we opened it
                if pw_needed and (pw_p or pw_browser or pw_context):
                    await self._close_playwright_context(pw_p, pw_browser, pw_context, log)
            async def _process_page(
                page_url: str,
                depth: int,
                http: submanagers.HTTPSSubmanager,
            ) -> Dict[str, Any]:
                local_log: List[str] = []
                local_js_links: List[Dict[str, str]] = []
                local_network_links: List[Dict[str, str]] = []
                local_runtime_hits: List[Dict[str, Any]] = []  # NEW
                local_assets: List[Dict[str, Any]] = []
                local_react_hits: List[Dict[str, Any]] = []
                local_database_hits: List[Dict[str, Any]] = []
                local_interaction_hits: List[Dict[str, Any]] = []
                next_pages: List[str] = []
                self.network_sniffer.http = http
                try:
                    links_on_page: List[Dict[str, str]] = []
                    html = ""

                    sniff_items: List[Dict[str, str]] = []
                    sniff_parent_pages: List[str] = []

                    # 1) Network sniff (shared PW)
                    if use_network_sniff and pw_context:
                        sniff_html = ""
                        sniff_items = []
                        sniff_json = None

                        sniff_result = await self._pw_fetch_with_sniff(
                            pw_context, page_url, timeout, local_log, targets
                        )

                        # Backwards-compatible: accept (html, items) or (html, items, json_hits)
                        if isinstance(sniff_result, tuple):
                            if len(sniff_result) == 3:
                                sniff_html, sniff_items, sniff_json = sniff_result
                            elif len(sniff_result) == 2:
                                sniff_html, sniff_items = sniff_result
                            elif len(sniff_result) == 1:
                                sniff_html = sniff_result[0]
                        else:
                            # e.g. if you ever change sniff() to return a dict
                            sniff_html = sniff_result

                        html = sniff_html or html

                        # Archive metadata special-casing
                        if "archive.org/metadata/" in page_url:
                            try:
                                meta = json.loads(html) if html.strip().startswith("{") else {}
                                files = meta.get("files") or []
                                identifier = (meta.get("metadata") or {}).get("identifier", "")
                                for f in files:
                                    name = f.get("name", "")
                                    if not name:
                                        continue
                                    low = name.lower()
                                    if any(low.endswith(ext) for ext in targets):
                                        dl = f"https://archive.org/download/{identifier}/{name}"
                                        links_on_page.append({
                                            "url": dl,
                                            "text": name,
                                            "tag": "archive_file",
                                        })
                            except Exception:
                                # best-effort only
                                pass

                        # Pull identifiers from sniffed JSON
                        try:
                            if sniff_json:
                                for hit in sniff_json:
                                    data = hit.get("json") or {}
                                    docs = (((data.get("response") or {}).get("docs")) or [])
                                    for d in docs:
                                        ident = d.get("identifier")
                                        if ident:
                                            for u2 in self._archive_ident_to_downloads(ident):
                                                if _allowed_by_required_sites(u2):
                                                    links_on_page.append({
                                                        "url": u2,
                                                        "text": "[Archive identifier]",
                                                        "tag": "archive_ident",
                                                    })
                        except Exception as e:
                            local_log.append(f"JSON sniff parse error on {page_url}: {e}")

                        for si in sniff_items:
                            url_hit = si.get("url", "")
                            if not url_hit:
                                continue
                            local_network_links.append({
                                "page": page_url,
                                "url": url_hit,
                                "text": si.get("text", ""),
                                "tag": si.get("tag", "network_sniff"),
                                "size": si.get("size", "?"),
                            })
                            local_js_links.append({
                                "page": page_url,
                                "url": url_hit,
                                "text": si.get("text", ""),
                                "tag": si.get("tag", "network_sniff"),
                            })

                            try:
                                parsed = urlparse(url_hit)
                                path = parsed.path or ""
                                if "/" in path:
                                    parent_path = path.rsplit("/", 1)[0] + "/"
                                    parent_url = f"{parsed.scheme}://{parsed.netloc}{parent_path}"
                                    if _allowed_by_required_sites(parent_url):
                                        sniff_parent_pages.append(parent_url)
                            except Exception:
                                pass
                    if use_database_sniff and pw_context:
                        try:
                            db_html, db_hits = await self._pw_fetch_database_hits(
                                pw_context,
                                page_url,
                                timeout,
                                local_log,
                            )
                            # Use this HTML if previous sniffers failed to get it
                            if db_html and not html:
                                html = db_html

                            if db_hits:
                                local_database_hits.extend(db_hits)

                                # Feed content links back into the processing loop
                                for hit in db_hits:
                                    if hit.get("kind") == "content_link":
                                        u = hit.get("url")
                                        if u:
                                            # Add to links_on_page.
                                            # The subsequent loop will check if 'u' ends with a target extension (.pdf, .zip).
                                            links_on_page.append({
                                                "url": u,
                                                "text": "[DB Content]",
                                                "tag": "db_link"
                                            })

                                            # Also add to debug links list for visibility
                                            local_js_links.append({
                                                "page": page_url,
                                                "url": u,
                                                "text": "[DB Content]",
                                                "tag": "db_link"
                                            })
                        except Exception as e:
                            local_log.append(f"[LinkTracker][DB] Error on {page_url}: {e}")
                    # 1b) Runtime sniff (WebSockets, perf, storage, media events, etc.)
                    if use_runtime_sniff and pw_context:
                        rt_html = ""
                        rt_hits: list[dict[str, Any]] = []

                        rt_result = await self._pw_fetch_runtime_hits(
                            pw_context, page_url, timeout, local_log
                        )

                        # Accept (html, items, hits) or (html, hits)
                        if isinstance(rt_result, tuple):
                            if len(rt_result) == 3:
                                rt_html, _rt_items, rt_hits = rt_result
                            elif len(rt_result) == 2:
                                rt_html, rt_hits = rt_result
                            elif len(rt_result) == 1:
                                rt_html = rt_result[0]
                        else:
                            rt_html = rt_result

                        if rt_html and not html:
                            html = rt_html
                        if rt_hits:
                            local_runtime_hits.extend(rt_hits)

                    # 2) JS render/gather (shared PW)
                    if use_js and pw_context:
                        js_html, js_links = await self._pw_fetch_js_links(
                            pw_context, page_url, timeout, local_log
                        )
                        if js_html:
                            html = js_html
                        links_on_page.extend(js_links)

                        if not js_links:
                            preview = (html or "")[:2000].replace("\n", " ")
                            local_log.append(f"[debug] JS DOM preview (first 2000 chars): {preview}")

                        for jl in js_links:
                            local_js_links.append({
                                "page": page_url,
                                "url": jl.get("url", ""),
                                "text": jl.get("text", ""),
                                "tag": jl.get("tag", ""),
                            })
                    if use_react_sniff and pw_context:
                        try:
                            r_html, r_hits = await self._pw_fetch_react_hits(
                                pw_context, page_url, timeout, local_log
                            )
                            # Use React-rendered HTML if we don't have one yet
                            if r_html and not html:
                                html = r_html

                            if r_hits:
                                local_react_hits.extend(r_hits)

                                # Treat found React routes as potential next pages for BFS
                                for rh in r_hits:
                                    r_url = rh.get("url")
                                    if not r_url:
                                        continue

                                    # Verify site scope before adding to frontier
                                    if _allowed_by_required_sites(r_url):
                                        if depth < max_depth:
                                            next_pages.append(r_url)
                        except Exception as e:
                            local_log.append(f"[LinkTracker][React] Error on {page_url}: {e}")

                    if use_interaction_sniff and pw_context:
                        try:
                            i_html, i_hits = await self._pw_fetch_interaction_hits(
                                pw_context, page_url, timeout, local_log
                            )
                            # Use interaction HTML if we don't have a snapshot yet
                            if i_html and not html:
                                html = i_html

                            if i_hits:
                                local_interaction_hits.extend(i_hits)
                        except Exception as e:
                            local_log.append(f"[LinkTracker][Interaction] Error on {page_url}: {e}")
                    # 3) Plain HTML if PW didn't fill html
                    if not html:
                        try:
                            html = await http.get_text(page_url)
                            if not html:
                                raise RuntimeError("Empty HTML")
                        except Exception as e:
                            local_log.append(f"Error fetching {page_url}: {e}")
                            if use_database and self.store and _should_persist_page(page_url):
                                self.store.mark_scan_complete(page_url)
                            return {
                                "page": page_url,
                                "assets": local_assets,
                                "next_pages": next_pages,
                                "js_links": local_js_links,
                                "network_links": local_network_links,
                                "runtime_hits": local_runtime_hits,
                                "react_hits": local_react_hits,
                                "database_hits": local_database_hits,  # [PATCH] Return hits
                                "interaction_hits": local_interaction_hits,
                                "log": local_log,
                            }

                    soup = BeautifulSoup(html or "", "html.parser")

                    page_title = ""
                    try:
                        if soup.title and soup.title.string:
                            page_title = soup.title.string
                    except Exception:
                        page_title = ""

                    page_haystack = (page_title or "") + " " + page_url
                    page_has_keywords = _term_overlap_ok(page_haystack)

                    # Plain <a> links
                    link_count = 0
                    for a in soup.find_all("a", href=True):
                        links_on_page.append({
                            "url": a["href"],
                            "text": a.get_text(strip=True),
                            "tag": "a",
                        })
                        link_count += 1
                        if link_count >= max_links_per_page:
                            break

                    # Scan links for assets
                    for link in links_on_page:
                        raw_link = link["url"]
                        full_url = urljoin(page_url, raw_link)
                        path = urlparse(full_url).path.lower()

                        is_mega = self._is_mega_link(full_url)

                        if not is_mega and not any(path.endswith(ext) for ext in targets):
                            continue
                        if use_database and store and store.asset_exists(full_url):
                            local_log.append(f"Skipping asset {full_url} (already in database)")
                            continue

                        clean_url_for_matching = unquote(full_url).lower()
                        if keywords and not page_has_keywords:
                            haystack = f"{page_title} {link.get('text', '')} {clean_url_for_matching}".lower()
                            if not _term_overlap_ok(haystack):
                                continue

                        if not _allowed_by_required_sites(full_url):
                            continue

                        status = "unverified"
                        size = "?"
                        if verify_links and not is_mega:
                            try:
                                h_status, headers = await http.head(full_url)
                                if h_status == 200:
                                    status = "200 OK"
                                    cl = headers.get("Content-Length")
                                    if cl:
                                        try:
                                            size = f"{int(cl) // 1024} KB"
                                        except ValueError:
                                            size = "?"
                                elif h_status is None:
                                    status = "Timeout/Error"
                                else:
                                    status = f"Dead ({h_status})"
                            except Exception:
                                status = "Timeout/Error"
                        elif is_mega:
                            status = "MEGA link"

                        if not verify_links or status == "200 OK":
                            display_text = (link.get("text", "") or path.split("/")[-1])[:100]
                            tag = "mega" if is_mega else "a"
                            asset = {
                                "text": display_text or ("[mega link]" if is_mega else "[asset]"),
                                "url": full_url,
                                "source": page_url,
                                "size": size,
                                "status": status,
                                "tag": tag,
                            }
                            local_assets.append(asset)
                            if use_database and store:
                                store.upsert_asset(asset)

                    # Network-sniffed assets (already in sniff_items)
                    if sniff_items:
                        for item in sniff_items:
                            full_url = item.get("url")
                            if not full_url:
                                continue
                            if not _allowed_by_required_sites(full_url):
                                continue
                            if use_database and store and store.asset_exists(full_url):
                                local_log.append(f"Skipping sniffed asset {full_url} (already in database)")
                                continue

                            status = "sniffed"
                            size = item.get("size") or "?"
                            if verify_links:
                                try:
                                    h_status, headers = await http.head(full_url)
                                    if h_status == 200:
                                        status = "200 OK"
                                        cl = headers.get("Content-Length")
                                        if cl:
                                            try:
                                                size = f"{int(cl) // 1024} KB"
                                            except ValueError:
                                                size = "?"
                                    elif h_status is None:
                                        status = "Timeout/Error"
                                    else:
                                        status = f"Dead ({h_status})"
                                except Exception:
                                    status = "Timeout/Error"

                            if not verify_links or status == "200 OK":
                                display_text = (item.get("text") or full_url.rsplit("/", 1)[-1] or "[network asset]")[:100]
                                asset = {
                                    "text": display_text,
                                    "url": full_url,
                                    "source": page_url,
                                    "size": size,
                                    "status": status,
                                }
                                local_assets.append(asset)
                                if use_database and store:
                                    store.upsert_asset(asset)

                    # Next-level pages
                    if depth < max_depth:
                        for link in links_on_page:
                            raw_link = link.get("url") or ""
                            if not raw_link:
                                continue
                            full_url = urljoin(page_url, raw_link)
                            if not _allowed_by_required_sites(full_url):
                                continue

                            lpath = urlparse(full_url).path.lower()
                            if any(lpath.endswith(ext) for ext in targets):
                                continue

                            if keywords and not page_has_keywords:
                                haystack = (link.get("text") or "") + " " + full_url
                                if not _term_overlap_ok(haystack):
                                    continue

                            if engine == "sites":
                                if _is_search_url(full_url) and full_url not in explicit_site_seeds:
                                    continue

                            next_pages.append(full_url)

                    if depth < max_depth and sniff_parent_pages:
                        for parent_url in sniff_parent_pages:
                            if _allowed_by_required_sites(parent_url):
                                next_pages.append(parent_url)

                    if use_database and store and _should_persist_page(page_url):
                        store.mark_page_scanned(page_url)

                except Exception as e:
                    local_log.append(f"Error scanning {page_url}: {e}")
                    if use_database and store and _should_persist_page(page_url):
                        try:
                            store.mark_page_scanned(page_url)
                        except Exception as ee:
                            local_log.append(f"Error marking page scanned {page_url}: {ee}")

                return {
                    "page": page_url,
                    "assets": local_assets,
                    "next_pages": next_pages,
                    "js_links": local_js_links,
                    "network_links": local_network_links,
                    "runtime_hits": local_runtime_hits,  # NEW
                    "react_hits": local_react_hits,
                    "database_hits": local_database_hits,
                    "interaction_hits": local_interaction_hits,
                    "log": local_log,
                }

            # ---------------- BFS frontier ----------------- #
            frontier: List[str] = []
            site_buckets = {s: [] for s in required_sites} if required_sites else {}

            for u in candidate_pages:
                if not _allowed_by_required_sites(u):
                    continue
                if required_sites:
                    d = _clean_domain(u)
                    for s in required_sites:
                        if s in d:
                            site_buckets[s].append(u)
                            break
                else:
                    frontier.append(u)

            if required_sites:
                per_site_cap = max(3, max_pages_total // max(1, len(required_sites)))
                for s, bucket in site_buckets.items():
                    frontier.extend(bucket[:per_site_cap])

            # Initial frontier: only unique URLs
            frontier = list(dict.fromkeys(frontier))

            current_depth = 0
            pages_scanned = 0  # metric only

            DEBUG_LOGGER.log_message(
                f"[LinkTracker][BFS] Starting BFS with max_depth={max_depth}, "
                f"max_pages_total={max_pages_total}, initial_frontier={len(frontier)}"
            )

            # New: only log the rescan notice once (for information only)
            logged_rescan_notice = False

            # BFS over depths
            # NOTE: we no longer gate on pages_scanned < max_pages_total,
            # and we no longer **skip** pages based on page_scanned().
            # Ensure frontier is unique and respects the limit initially
            frontier = list(dict.fromkeys(frontier))[:max_pages_total]
            current_depth = 0
            logged_rescan_notice = False

            # --- BFS LOOP START ---
            # We check pages_scanned against max_pages_total to ensure global termination
            while frontier and current_depth <= max_depth:

                DEBUG_LOGGER.log_message(
                    f"[BFS] --- Starting Depth {current_depth} | "
                    f"Frontier Size: {len(frontier)} | Visited: {len(visited_pages)} | "
                    f"Scanned: {pages_scanned}/{max_pages_total} ---"
                )

                batch: List[str] = []

                # Calculate how many slots are left before hitting the global cap


                for u in frontier:
                    if u in visited_pages:
                        continue

                    # DB Page Scanned Check (Logic preserved from your snippet)
                    if use_database and self.store and self.store.page_scanned(u):
                        if not logged_rescan_notice:
                            DEBUG_LOGGER.log_message(
                                "[LinkTracker][db] page_scanned() is True, but processing anyway (DB skip disabled)."
                            )
                            logged_rescan_notice = True
                        # We still fall through and add 'u' to batch, as requested

                    batch.append(u)

                    # CRITICAL: Mark as visited immediately to prevent re-queueing in next_frontier
                    visited_pages.add(u)

                if not batch:
                    DEBUG_LOGGER.log_message(
                        f"[BFS] Depth {current_depth} – no valid pages to process in this batch. Stopping."
                    )
                    break

                DEBUG_LOGGER.log_message(f"[BFS] Processing batch of {len(batch)} URLs...")

                # Process this depth's batch
                if use_camoufox:
                    results: List[Dict[str, Any]] = []
                    for url in batch:
                        try:
                            res = await _process_page(url, current_depth, http)
                            results.append(res)
                        except Exception as e:
                            DEBUG_LOGGER.log_message(f"[LinkTracker][Camoufox] Fatal error on {url}: {e}")
                            continue
                else:
                    # Original concurrent behaviour
                    results = await asyncio.gather(
                        *[_process_page(url, current_depth, http) for url in batch]
                    )

                next_frontier_candidates: List[str] = []

                for res in results:
                    pages_scanned += 1

                    # Aggregate Logs & Links
                    all_js_links.extend(res.get("js_links", []))
                    all_network_links.extend(res.get("network_links", []))
                    all_runtime_hits.extend(res.get("runtime_hits", []))
                    all_react_hits.extend(res.get("react_hits", []))  # [PATCH]
                    all_database_hits.extend(res.get("database_hits", []))
                    all_interaction_hits.extend(res.get("interaction_hits", []))
                    # Collect Assets
                    for asset in res.get("assets", []):
                        a_url = asset.get("url")
                        if a_url and a_url not in seen_asset_urls:
                            seen_asset_urls.add(a_url)
                            found_assets.append(asset)

                    # Collect Next Pages (only if we haven't hit max depth)
                    if current_depth < max_depth:
                        next_pages = res.get("next_pages", [])
                        if next_pages:
                            next_frontier_candidates.extend(next_pages)

                # Filter next frontier against visited pages and current batch
                next_frontier = []
                seen_in_next = set()

                for url in next_frontier_candidates:
                    # Ensure we don't circle back to pages we just visited or are about to visit
                    if url not in visited_pages and url not in seen_in_next:
                        next_frontier.append(url)
                        seen_in_next.add(url)

                # Update frontier for next depth
                frontier = next_frontier[:max_pages_total]

                DEBUG_LOGGER.log_message(
                    f"[BFS] Depth {current_depth} complete. "
                    f"Discovered {len(frontier)} new unique pages for next depth."
                )

                current_depth += 1

            # Close shared PW
            if pw_needed:
                await self._close_playwright_context(pw_p, pw_browser, pw_context, log)

        # ---------------- Output formatting ------------- #
        from urllib.parse import urlparse as _urlparse

        if not found_assets:
            base_text = (
                "### LinkTracker: No specific assets found.\n"
                f"Scanned {len(candidate_pages)} pages for extensions: {sorted(list(targets))}.\n"
                f"Required keywords: {keywords}\n"
                f"Required sites: {required_sites or '[none]'}\n"
                f"min_term_overlap: {min_term_overlap}\n"
                f"Engine: {engine}\n"
            )
            lines = [base_text]

            if return_all_js_links and all_js_links:
                lines.append("\n### All JS-Gathered Links (debug)\n")
                for jl in all_js_links:
                    host = _urlparse(jl["page"]).netloc if jl.get("page") else "(unknown)"
                    url = jl["url"]
                    text = jl["text"] or "(no text)"
                    tag = jl["tag"] or "a"
                    lines.append(f"- **[{text}]({url})**")
                    lines.append(f"  - *Tag: <{tag}> | From page: {host}*")

            if return_network_sniff_links and all_network_links:
                lines.append("\n### All Network-Sniffed Assets (debug)\n")
                for nl in all_network_links:
                    host = _urlparse(nl["page"]).netloc if nl.get("page") else "(unknown)"
                    url = nl["url"]
                    text = nl["text"] or "(no text)"
                    tag = nl.get("tag", "network_sniff")
                    size = nl.get("size", "?")
                    lines.append(f"- **[{text}]({url})**")
                    lines.append(f"  - *Tag: <{tag}> | From page: {host} | Size: {size}*")
            if return_database_sniff_hits and all_database_hits:
                lines.append("\n### Database / Content Sniff Hits (debug)\n")
                for dbh in all_database_hits[:100]:
                    kind = dbh.get("kind")
                    url = dbh.get("url")
                    meta = dbh.get("meta") or {}

                    if kind == "content_link":
                        src = meta.get("source", "?")
                        lines.append(f"- `db_link` ({src}) **{url}**")
                    elif kind == "indexeddb_dump":
                        db_name = meta.get("name", "?")
                        stores = meta.get("stores", [])
                        store_str = ", ".join([f"{s['name']}(~{s.get('approx_count')})" for s in stores])
                        lines.append(f"- `indexed_db` **{db_name}**: [{store_str}]")
                    elif kind == "db_config_detected":
                        name = meta.get("name")
                        lines.append(f"- `backend_config` **{name}** detected")
            return "\n".join(lines), {
                "count": 0,
                "keywords_used": keywords,
                "min_term_overlap": min_term_overlap,
                "engine": engine,
                "required_sites": required_sites,
                "js_links": all_js_links,
                "network_sniff_links": all_network_links,
                "runtime_hits": all_runtime_hits,
                "react_hits": all_react_hits,
                "database_hits": all_database_hits,
                "interaction_hits": all_interaction_hits,
                "log": log,
                "queries_run": queries_to_run,
            }

        lines = [f"### LinkTracker Found {len(found_assets)} Assets"]
        lines.append(
            f"_Mode: {mode} | Query: {query} | Engine: {engine} | "
            f"Required Keywords: {keywords} | min_term_overlap: {min_term_overlap} | "
            f"Required Sites: {required_sites or '[none]'}_"
        )
        lines.append("")

        for asset in found_assets:
            lines.append(f"- **[{asset['text']}]({asset['url']})**")
            lines.append(
                f"  - *Size: {asset.get('size','?')} | Status: {asset.get('status','?')} | "
                f"Source: {_urlparse(asset.get('source','')).netloc if asset.get('source') else '(unknown)'}*"
            )

        if return_all_js_links and all_js_links:
            lines.append("\n### All JS-Gathered Links (debug)\n")
            for jl in all_js_links:
                host = _urlparse(jl["page"]).netloc if jl.get("page") else "(unknown)"
                url = jl["url"]
                text = jl["text"] or "(no text)"
                tag = jl["tag"] or "a"
                lines.append(f"- **[{text}]({url})**")
                lines.append(f"  - *Tag: <{tag}> | From page: {host}*")

        if return_network_sniff_links and all_network_links:
            lines.append("\n### All Network-Sniffed Assets (debug)\n")
            for nl in all_network_links:
                host = _urlparse(nl["page"]).netloc if nl.get("page") else "(unknown)"
                url = nl["url"]
                text = nl["text"] or "(no text)"
                tag = nl.get("tag", "network_sniff")
                size = nl.get("size", "?")
                lines.append(f"- **[{text}]({url})**")
                lines.append(f"  - *Tag: <{tag}> | From page: {host} | Size: {size}*")
        if return_react_sniff_hits and all_react_hits:
            lines.append("\n### React / SPA Hits (debug)\n")
            for rh in all_react_hits[:100]:
                url = rh.get("url") or "(no url)"
                route = rh.get("route") or ""
                kind = rh.get("kind") or "react_nav"
                lines.append(f"- `{kind}` **{route}** → {url}")
        if return_runtime_sniff_hits and all_runtime_hits:
            lines.append("\n### Runtime Sniff Hits (debug)\n")
            # Cap output to prevent massive message overflow (e.g. 100 items)
            for hit in all_runtime_hits[:100]:
                url = hit.get("url") or "(no url)"
                payload = hit.get("json") or {}

                # Format a readable description based on the hit type
                desc_parts = []
                if "console" in payload:
                    desc_parts.append(f"Console: {str(payload['console'])[:100]}...")
                elif "ws_frame" in payload:
                    desc_parts.append(f"WebSocket: {str(payload['ws_frame'])[:100]}...")
                elif "request_body" in payload:
                    desc_parts.append("Request Body (JSON)")
                elif "media_events" in payload:
                    evts = payload["media_events"]
                    desc_parts.append(f"Media Events: {len(evts)}")
                elif "storage" in payload:
                    desc_parts.append(f"Storage Items: {len(payload['storage'])}")
                elif "perf_entries" in payload:
                    desc_parts.append(f"Perf Entries: {len(payload['perf_entries'])}")
                else:
                    # Generic fallback for unknown payloads
                    import json as _json
                    try:
                        dump = _json.dumps(payload)
                        desc_parts.append(f"Data: {dump[:100]}...")
                    except:
                        desc_parts.append("Data: (complex object)")

                desc = " | ".join(desc_parts)
                lines.append(f"- `{desc}` found on **{url}**")
        if return_interaction_sniff_hits and all_interaction_hits:
            lines.append("\n### Interaction / CDP Hits (debug)\n")
            for ih in all_interaction_hits[:100]:
                kind = ih.get("kind")
                meta = ih.get("meta") or {}
                url = ih.get("url")

                if kind == "event_listener":
                    node = meta.get("nodeName", "UNK")
                    types = meta.get("types", [])
                    lines.append(f"- `listener` **{node}** {types} on {url}")
                elif kind == "form_definition":
                    ins = meta.get("input_count", 0)
                    method = meta.get("method", "get")
                    lines.append(f"- `form` **{method.upper()}** ({ins} inputs) on {url}")
                elif kind == "overlay_detected":
                    cov = meta.get("coverage", "?")
                    z = meta.get("zIndex", "?")
                    lines.append(f"- `overlay` (z={z}, cov={cov}) on {url}")
                elif kind == "summary":
                    lc = meta.get("listener_count", 0)
                    fc = meta.get("form_count", 0)
                    lines.append(f"- `summary` Listeners: {lc}, Forms: {fc}")
        return "\n".join(lines), {
            "found": len(found_assets),
            "scanned_pages": len(visited_pages),
            "assets": found_assets,
            "keywords_used": keywords,
            "min_term_overlap": min_term_overlap,
            "engine": engine,
            "required_sites": required_sites,
            "js_links": all_js_links,
            "network_sniff_links": all_network_links,
            "runtime_hits": all_runtime_hits,
            "react_hits": all_react_hits,
            "database_hits": all_database_hits,
            "interaction_hits": all_interaction_hits,
            "log": log,
            "queries_run": queries_to_run,
        }

    # ------------------------------------------------------------------ #
    # Predictive sequencing (unchanged)
    # ------------------------------------------------------------------ #
    def _predict_next_in_sequence(self, urls: List[str]) -> List[str]:
        generated = set()
        re_seq = re.compile(r"([0-9]+)(\.[a-z0-9]+)$", re.IGNORECASE)

        for u in urls:
            match = re_seq.search(u)
            if match:
                original_num_str = match.group(1)
                try:
                    width = len(original_num_str)
                    val = int(original_num_str)
                    for i in range(1, 4):
                        next_val = val + i
                        next_str = f"{next_val:0{width}d}"
                        new_url = u[:match.start(1)] + next_str + u[match.end(1):]
                        generated.add(new_url)
                except ValueError:
                    pass

        return list(generated)

    # ------------------------------------------------------------------ #
    # Sites seeding helpers (unchanged)
    # ------------------------------------------------------------------ #
    def _seed_pages_from_required_sites(
        self,
        required_sites,
        queries,
        probe_cap_per_site=5,
        sitemap_cap_per_site=8,
        hub_cap_per_site=6,
    ):
        out: List[str] = []
        synthetic_search_seeds: set[str] = set()
        explicit_site_seeds: set[str] = set()

        norm_sites = []
        for raw in required_sites or []:
            s = (raw or "").strip()
            if not s:
                continue
            norm_sites.append(s.rstrip("/") if "://" in s else "https://" + s.lstrip(".").rstrip("/"))

        for s in norm_sites:
            u = s + "/"
            out.append(u)
            explicit_site_seeds.add(u)

        common_sitemaps = [
            "/sitemap.xml", "/sitemap_index.xml", "/sitemap/sitemap.xml",
            "/sitemap-index.xml", "/sitemap.php", "/sitemap.txt",
        ]
        for s in norm_sites:
            u = s + "/robots.txt"
            out.append(u); explicit_site_seeds.add(u)
            added = 0
            for sm in common_sitemaps:
                if added >= sitemap_cap_per_site:
                    break
                u = s + sm
                out.append(u); explicit_site_seeds.add(u)
                added += 1

        hub_paths = [
            "/tag/", "/tags/", "/category/", "/categories/", "/archive/", "/archives/",
            "/browse/", "/collections/", "/series/", "/authors/", "/topics/", "/search",
        ]
        for s in norm_sites:
            added = 0
            for hp in hub_paths:
                if added >= hub_cap_per_site:
                    break
                u = s + hp
                out.append(u); explicit_site_seeds.add(u)
                added += 1

        def _extra_probes_for_site(base: str, enc_query: str) -> list[str]:
            host = urlparse(base).netloc.lower()
            if "archive.org" in host:
                return [
                    base + f"/search.php?query={enc_query}",
                    base + f"/advancedsearch.php?q={enc_query}",
                    base + (f"/advancedsearch.php?q={enc_query}"
                            f"&fl[]=identifier&fl[]=title&rows=50&page=1&output=json"),
                    base + f"/details/{enc_query}",
                    base + f"/browse.php?field=subject&query={enc_query}",
                ]
            return []

        if queries:
            for s in norm_sites:
                probes_added = 0
                for qv in queries:
                    if probes_added >= probe_cap_per_site:
                        break
                    qv = (qv or "").strip()
                    if not qv:
                        continue
                    enc = quote_plus(qv)

                    probes = [
                        s + f"/search?q={enc}",
                        s + f"/search?query={enc}",
                        s + f"/?s={enc}",
                        s + f"/search/{enc}",
                    ]
                    probes.extend(_extra_probes_for_site(s, enc))

                    for p in probes:
                        out.append(p)
                        synthetic_search_seeds.add(p)
                        probes_added += 1
                        if probes_added >= probe_cap_per_site and "archive.org" not in s:
                            break

        return out, synthetic_search_seeds, explicit_site_seeds

    def _extract_sitemap_urls_from_robots(self, text: str) -> list[str]:
        urls = []
        for line in (text or "").splitlines():
            if line.lower().startswith("sitemap:"):
                u = line.split(":", 1)[1].strip()
                if u.startswith("http"):
                    urls.append(u)
        return urls

    # ------------------------------------------------------------------ #
    # Sync wrapper
    # ------------------------------------------------------------------ #
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asyncio.run(self._execute_async(payload, params=params))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "rare aphex twin interview",
            "timeout": 5,
            "mode": "docs",
            "scan_limit": 5,
            "search_results_cap": 256,
            "search_page_limit": 1,
            "search_per_page": 50,
            "verify": True,
            "extensions": ".pdf,.txt",
            "url_keywords": "archive,download",
            "engine": "duckduckgo",
            "site_require": "",
            "use_js": False,
            "return_all_js_links": False,
            "max_links_per_page": 500,
            "strict_keywords": False,
            "use_network_sniff": False,
            "return_network_sniff_links": False,
            "use_runtime_sniff": False,
            "return_runtime_sniff_hits": False,
            "use_react_sniff": False,
            "return_react_sniff_hits": False,
            "use_database_sniff": False,
            "return_database_sniff_hits": False,
            "use_interaction_sniff": False,
            "return_interaction_sniff_hits": False,
            "min_term_overlap": 1,
            "max_depth": 0,
            "max_pages_total": 32,
            "subpipeline": "",
            "use_database": False,
            "db_path": "link_corpus.db",
            "block_resources": False,
            "blocked_resource_types": "image,stylesheet,font",
            "block_domains": True,
            "blocked_domains": "",
            "db_seed_limit": 250,
            "db_seed_max_age_days": None,
            "db_allow_rescan": False,
            "memory_sources": "",
            "http_retries": 2,
            "http_max_conn_per_host": 8,
            "http_verify_tls": True,
            "http_ca_bundle": "",   # path to bundled cacert.pem if needed
            "use_camoufox": False,
            "camoufox_options": {},
            "pw_headless": True,
            "pw_channel": "",  # e.g. "chrome"
            "pw_proxy": {},  # e.g. {"server":"http://127.0.0.1:8080"}
            "pw_launch_args": [
                "--disable-quic",
                "--disable-http3",
                "--disable-features=UseDnsHttpsSvcb"
            ],
            "searxng_url": "http://127.0.0.1:8080"
        }


BLOCKS.register("linktracker", LinkTrackerBlock)


# ======================= YouTubeDataBlock ==================================


@dataclass
class YouTubeDataBlock(BaseBlock):
    """
    YouTube Data API v3 search block.

    Features:
    - Uses GOOGLE_API_KEY from the environment (or api_key param override)
    - Runs a YouTube search (search.list) for videos
    - Enriches with video details (videos.list: duration, statistics)
    - Returns a markdown list + structured metadata
    - Optionally exports raw results into Memory under an 'export_key'
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os
        import requests
        from typing import List, Dict
        from datetime import timedelta

        # ---------- Params ----------
        query = str(params.get("query", "") or str(payload or "")).strip()
        if not query:
            return "", {"error": "YouTubeDataBlock: empty query"}

        # API key: env first, then optional explicit override
        api_key = params.get("api_key") or os.getenv("GOOGLE_API_KEY")
        if not api_key:
            return (
                "YouTubeDataBlock: Missing API key. "
                "Set the GOOGLE_API_KEY environment variable or pass api_key in params."
            ), {"error": "missing_api_key"}

        max_results = int(params.get("max_results", 5))  # 1–50 per API
        max_results = max(1, min(50, max_results))

        order = str(params.get("order", "relevance"))  # date | rating | relevance | title | viewCount
        safe_search = str(params.get("safe_search", "moderate"))  # none | moderate | strict

        # Optional filters
        channel_id = str(params.get("channel_id", "")).strip() or None
        video_duration = str(params.get("video_duration", "")).strip() or None  # any | short | medium | long
        published_after = str(params.get("published_after", "")).strip() or None  # ISO8601 datetime

        # Memory export
        export_key = str(params.get("export_key", "youtube_results")).strip()
        export_to_memory = bool(params.get("export_to_memory", True))

        # ---------- Helpers ----------
        def _parse_duration_iso8601(d: str) -> int:
            """
            Parse ISO8601 duration (PT#M#S etc.) into seconds.
            Very small custom parser to avoid pulling in dateutil.
            """
            if not d or not d.startswith("PT"):
                return 0
            d = d[2:]  # strip "PT"
            hours = minutes = seconds = 0
            num = ""
            for ch in d:
                if ch.isdigit():
                    num += ch
                else:
                    if not num:
                        continue
                    val = int(num)
                    num = ""
                    if ch == "H":
                        hours = val
                    elif ch == "M":
                        minutes = val
                    elif ch == "S":
                        seconds = val
            return hours * 3600 + minutes * 60 + seconds

        def _fmt_duration(sec: int) -> str:
            if sec <= 0:
                return "?:??"
            td = timedelta(seconds=sec)
            total = int(td.total_seconds())
            h, rem = divmod(total, 3600)
            m, s = divmod(rem, 60)
            if h > 0:
                return f"{h:d}:{m:02d}:{s:02d}"
            return f"{m:d}:{s:02d}"

        # ---------- 1) search.list ----------
        search_url = "https://www.googleapis.com/youtube/v3/search"
        search_params = {
            "part": "snippet",
            "q": query,
            "type": "video",
            "maxResults": max_results,
            "order": order,
            "safeSearch": safe_search,
            "key": api_key,
        }
        if channel_id:
            search_params["channelId"] = channel_id
        if video_duration:
            search_params["videoDuration"] = video_duration
        if published_after:
            search_params["publishedAfter"] = published_after

        try:
            r = requests.get(search_url, params=search_params, timeout=10)
            r.raise_for_status()
            search_data = r.json()
        except Exception as e:
            return f"YouTubeDataBlock: search failed: {e}", {"error": "search_failed", "detail": str(e)}

        items = search_data.get("items") or []
        if not items:
            return f"No YouTube videos found for query: {query}", {
                "count": 0,
                "query": query,
                "order": order,
                "safe_search": safe_search,
            }

        video_ids: List[str] = []
        base_results: Dict[str, Dict[str, Any]] = {}

        for it in items:
            vid = (it.get("id") or {}).get("videoId")
            snip = it.get("snippet") or {}
            if not vid:
                continue
            video_ids.append(vid)
            url = f"https://www.youtube.com/watch?v={vid}"
            base_results[vid] = {
                "id": vid,
                "title": snip.get("title", "").strip(),
                "url": url,
                "channel_title": snip.get("channelTitle", ""),
                "channel_id": snip.get("channelId", ""),
                "published_at": snip.get("publishedAt", ""),
                "description": snip.get("description", ""),
                "thumbnails": snip.get("thumbnails", {}),
            }

        if not video_ids:
            return f"No usable video IDs found for query: {query}", {
                "count": 0,
                "query": query,
            }

        # ---------- 2) videos.list for details ----------
        details_url = "https://www.googleapis.com/youtube/v3/videos"
        details_params = {
            "part": "contentDetails,statistics",
            "id": ",".join(video_ids),
            "key": api_key,
        }

        try:
            r2 = requests.get(details_url, params=details_params, timeout=10)
            r2.raise_for_status()
            details_data = r2.json()
        except Exception as e:
            # If details call fails, still return basic search info
            return (
                "YouTubeDataBlock: Got search results but details call failed. "
                "Returning basic info only.",
                {
                    "count": len(base_results),
                    "query": query,
                    "order": order,
                    "safe_search": safe_search,
                    "results": list(base_results.values()),
                    "error": "details_failed",
                    "detail": str(e),
                },
            )

        for it in details_data.get("items") or []:
            vid = it.get("id")
            if vid not in base_results:
                continue
            content = it.get("contentDetails") or {}
            stats = it.get("statistics") or {}

            dur_iso = content.get("duration", "")
            dur_sec = _parse_duration_iso8601(dur_iso)

            base_results[vid].update(
                {
                    "duration_iso": dur_iso,
                    "duration_seconds": dur_sec,
                    "duration_display": _fmt_duration(dur_sec),
                    "view_count": int(stats.get("viewCount", 0)) if stats.get("viewCount") is not None else None,
                    "like_count": int(stats.get("likeCount", 0)) if stats.get("likeCount") is not None else None,
                    "comment_count": int(stats.get("commentCount", 0)) if stats.get(
                        "commentCount") is not None else None,
                }
            )

        results_list = [base_results[vid] for vid in video_ids if vid in base_results]

        # ---------- Optional Memory export ----------
        if export_to_memory and export_key:
            try:
                store = Memory.load()
                store[export_key] = results_list
                Memory.save(store)
            except Exception:
                # Don't break the block just because Memory isn't available
                pass

        # ---------- Markdown output ----------
        lines: List[str] = []
        lines.append(f"### 🎬 YouTube Results for: `{query}`")
        lines.append(
            f"_Results: {len(results_list)} | Order: {order} | SafeSearch: {safe_search}_"
        )
        lines.append("")

        for v in results_list:
            title = v.get("title") or "(untitled)"
            url = v.get("url")
            chan = v.get("channel_title") or "Unknown channel"
            dur = v.get("duration_display") or "?:??"
            views = v.get("view_count")
            views_str = f"{views:,}" if isinstance(views, int) else "?"
            lines.append(f"- **[{title}]({url})**  \n"
                         f"  ⏱ {dur}  •  👤 {chan}  •  👁️ {views_str} views")

        out = "\n".join(lines)

        meta = {
            "count": len(results_list),
            "query": query,
            "order": order,
            "safe_search": safe_search,
            "export_key": export_key if (export_to_memory and export_key) else None,
            "results": results_list,
        }
        return out, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "Playboi Carti unreleased",
            "max_results": 5,
            "order": "relevance",  # date | rating | relevance | title | viewCount
            "safe_search": "moderate",  # none | moderate | strict
            "channel_id": "",
            "video_duration": "any",  # any | short | medium | long
            "published_after": "",  # RFC3339, e.g. 2023-01-01T00:00:00Z
            "export_key": "youtube_results",
            "export_to_memory": True,
            "engine_note": "Uses GOOGLE_API_KEY env var (YouTube Data API v3)",
        }


BLOCKS.register("youtube", YouTubeDataBlock)


# ======================= VideoLinkTrackerBlock =============================

@dataclass
class VideoLinkTrackerBlock(BaseBlock):
    """
    Bounded, smarter video crawler.

    Modes via 'source' param:
      • source="search"    (default): run web search to find hub pages.
      • source="payload":  parse input payload for hub URLs.
      • source="database": seed crawl from previously saved DB pages/assets.
      • engine="sites":    target specific sites for sitemap/pagination-based crawling.

    Features:
      • DuckDuckGo / Google CSE search with optional site: filters.
      • Site-specific sitemap and pagination crawling (engine="sites").
      • Optional JS rendering via Playwright (use_js=true).
      • Optional Playwright network sniffing (use_network_sniff=true).
      • Ad / tracking filters.
      • Optional shallow second-level crawl (max_depth).
      • Stream-aware detection.
      • Optional HEAD-based Content-Type sniffing (smart_sniff).
      • Hard safety limits (max_pages_total, max_assets).
      • min_term_overlap for keyword matching.
      • subpipeline support.
      • Database integration to avoid re-processing known assets/pages.
      • DB seeding + controlled expansion that converges.
      • Playwright resource + domain blocking.
      • content-based deduplication + cooldown (keeps best/largest asset).
    """

    VIDEO_EXTENSIONS = {
        ".mp4", ".webm", ".mkv", ".mov", ".avi", ".flv", ".wmv", ".m3u8", ".mpd",
        ".ogv", ".ts", ".3gp", ".f4v", ".swf", ".divx", ".xvid", ".m4v",
    }
    VIDEO_PLATFORMS = {
        "youtube.com/embed/", "youtube-nocookie.com/embed/",
        "player.vimeo.com/video/", "dailymotion.com/embed/video/",
        "rumble.com/embed/", "v.redd.it", "/player.html", "/player/",
        "streamable.com/", "gfycat.com/ifr/", "clips.twitch.tv/",
        "tiktok.com/embed/", "bilibili.com/player/", "ok.ru/videoembed/",
    }
    STREAM_HINT_KEYWORDS = {
        "videoplayback", "hls", "dash", "manifest", "master.m3u8",
        "index.m3u8", "playlist.m3u8", "chunklist.m3u8", "video.mpd",
        "stream", "cdn", "transcode", "delivery", "blob",
    }
    VIDEO_CONTENT_PREFIXES = {"video/", "application/vnd.apple.mpegurl", "application/dash+xml"}
    HLS_CONTENT_TYPES = {"application/x-mpegurl", "application/vnd.apple.mpegurl"}
    DASH_CONTENT_TYPES = {"application/dash+xml"}

    AD_HOST_SUBSTRINGS = {
        "doubleclick", "googlesyndication", "adservice", "adserver",
        "adsystem", "adnxs", "trk.", "tracking", "analytics",
        "metrics", "scorecardresearch", "ads.", "ad.", "pixel.", "stat.",
        # [PATCH] Add Video-Specific Ad Hosts
        "cdn.jwplayer.com", "anyclip", "primis", "connatix", "taboola",
        "outbrain", "vidzoo", "spotx", "springserve", "sascdn", "smartadserver"
    }
    AD_PATH_KEYWORDS = {
        "/ads/", "/adserver/", "/banner/", "/banners/", "/promo/",
        "/promotions/", "/tracking/", "/click/", "/impression", "/pixel",
        "/sponsor/", "/advert/", "/popunder/", "/popup/",
    }
    JUNK_FILENAME_KEYWORDS = {
        "sprite", "icon", "favicon", "logo", "tracking",
        "pixel", "blank", "placeholder", "thumbnail", "preview",
        "captcha", "ads", "promo", "bg", "image", ".gif", ".webp",
    }
    IGNORED_EXTENSIONS = {
        ".css", ".js", ".json", ".xml", ".svg", ".png", ".jpg", ".jpeg",
        ".gif", ".ico", ".woff", ".woff2", ".ttf", ".eot", ".map", ".webp",
    }

    _URL_RE = re.compile(r"https?://[^\s\"'<>\\)]+", re.IGNORECASE)

    _VOLATILE_QS = {
        "ui", "psid", "token", "sig", "signature", "expires", "expire",
        "download", "dl", "session", "sess", "key", "auth",
        "utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
    }

    _XVIDEOS_CONTENT_RE = re.compile(
        r"(xvideos\.com_[a-f0-9]{16,}\.(?:mp4|m4v|webm|3gp))",
        re.IGNORECASE,
    )

    def __post_init__(self):
        # DB plumbing
        self.db: Optional[submanagers.DatabaseSubmanager] = None
        self.store: Optional[VideoTrackerStore] = None

        # Sniffers / helpers
        self.js_sniffer = submanagers.JSSniffer(submanagers.JSSniffer.Config(enable_auto_scroll=True,max_scroll_steps=40,scroll_step_delay_ms=500))
        self.network_sniffer = submanagers.NetworkSniffer(submanagers.NetworkSniffer.Config(enable_auto_scroll=True,max_scroll_steps=40,scroll_step_delay_ms=500))
        self.hls_manager = submanagers.HLSSubManager()
        self.runtime_sniffer = submanagers.RuntimeSniffer(submanagers.RuntimeSniffer.Config())
        self.react_sniffer = submanagers.ReactSniffer(
            submanagers.ReactSniffer.Config(
                hook_history_api=True,
                hook_link_clicks=True,
                inspect_react_devtools_hook=True,
            )
        )
        self.database_sniffer = submanagers.DatabaseSniffer(
            submanagers.DatabaseSniffer.Config(
                enable_indexeddb_dump=True,  # Get Metadata
                enable_backend_fingerprint=True,  # Get Tech Stack
                enable_html_link_scan=True,  # Scan HTML for raw links
                enable_backend_link_scan=True  # Scan JS Globals for links
            )
        )
        self.interaction_sniffer = submanagers.InteractionSniffer(
            submanagers.InteractionSniffer.Config(
                enable_cdp_listeners=True,
                enable_overlay_detection=True,
                enable_form_extraction=True
            )
        )

    def _get_visual_signature(self, image_bytes: bytes) -> Optional[dict]:
        """
        Generates a content-aware visual signature:
          - perceptual hash (pHash)
          - edge histogram (structure)
          - HSV color histogram (appearance)
        """
        import cv2
        import numpy as np

        try:
            nparr = np.frombuffer(image_bytes, np.uint8)
            img = cv2.imdecode(nparr, cv2.IMREAD_COLOR)
            if img is None:
                return None

            # ------------------------------
            # Resize for stability
            # ------------------------------
            img_small = cv2.resize(img, (256, 256), interpolation=cv2.INTER_AREA)

            # ------------------------------
            # 1) Perceptual Hash (pHash)
            # ------------------------------
            gray = cv2.cvtColor(img_small, cv2.COLOR_BGR2GRAY)
            dct = cv2.dct(np.float32(gray))
            dct_low = dct[:8, :8]
            med = np.median(dct_low)
            phash = (dct_low > med).astype(np.uint8)

            # ------------------------------
            # 2) Edge Histogram (structure)
            # ------------------------------
            edges = cv2.Canny(gray, 80, 160)
            edge_hist = cv2.calcHist([edges], [0], None, [64], [0, 256])
            cv2.normalize(edge_hist, edge_hist, 0, 1, cv2.NORM_MINMAX)

            # ------------------------------
            # 3) HSV Color Histogram
            # ------------------------------
            hsv = cv2.cvtColor(img_small, cv2.COLOR_BGR2HSV)
            color_hist = cv2.calcHist(
                [hsv],
                [0, 1],
                None,
                [64, 64],
                [0, 180, 0, 256],
            )
            cv2.normalize(color_hist, color_hist, 0, 1, cv2.NORM_MINMAX)

            return {
                "phash": phash,
                "edge_hist": edge_hist,
                "color_hist": color_hist,
            }

        except Exception:
            return None

    def _compare_visual_signatures(self, sig1: dict, sig2: dict) -> float:
        """
        Returns similarity score in [0, 1]
        Combines:
          - pHash similarity (global structure)
          - edge histogram correlation (shapes)
          - color histogram correlation (appearance)
        """
        import cv2
        import numpy as np

        if not sig1 or not sig2:
            return 0.0

        try:
            # ------------------------------
            # pHash similarity (Hamming)
            # ------------------------------
            h1, h2 = sig1["phash"], sig2["phash"]
            hamming = np.count_nonzero(h1 != h2)
            phash_score = 1.0 - (hamming / h1.size)

            # ------------------------------
            # Edge structure similarity
            # ------------------------------
            edge_score = cv2.compareHist(
                sig1["edge_hist"],
                sig2["edge_hist"],
                cv2.HISTCMP_CORREL,
            )

            # ------------------------------
            # Color similarity
            # ------------------------------
            color_score = cv2.compareHist(
                sig1["color_hist"],
                sig2["color_hist"],
                cv2.HISTCMP_CORREL,
            )

            # Normalize correlations → [0,1]
            edge_score = max(0.0, min(1.0, (edge_score + 1) / 2))
            color_score = max(0.0, min(1.0, (color_score + 1) / 2))

            # ------------------------------
            # Weighted fusion
            # ------------------------------
            return (
                    0.45 * phash_score +
                    0.35 * edge_score +
                    0.20 * color_score
            )

        except Exception:
            return 0.0
    # ------------------------------------------------------------------ #
    # URL canonicalization + content-id dedupe
    # ------------------------------------------------------------------ #

    def _canonicalize_url(self, u: str) -> str:
        try:
            pu = urlparse(u)
            host = pu.netloc.lower().split(":")[0]
            path = pu.path
            qs = parse_qsl(pu.query, keep_blank_values=False)
            qs = [(k, v) for k, v in qs if k.lower() not in self._VOLATILE_QS]
            new_query = urlencode(qs, doseq=True)
            return urlunparse((pu.scheme, host, path, pu.params, new_query, ""))
        except Exception:
            return u

    def _get_content_id(self, url: str) -> str:
        u = url or ""
        m = self._XVIDEOS_CONTENT_RE.search(u)
        if m:
            return "xvideos_content_" + m.group(1).lower()
        return self._canonicalize_url(u)

    def _parse_size_to_bytes(self, size_str: str) -> int:
        if not size_str:
            return 0
        s = size_str.strip().upper()
        m = re.search(r"([0-9]+(?:\.[0-9]+)?)\s*(B|KB|MB|GB)", s)
        if not m:
            return 0
        val = float(m.group(1))
        unit = m.group(2)
        mult = {"B": 1, "KB": 1024, "MB": 1024**2, "GB": 1024**3}.get(unit, 1)
        return int(val * mult)

    # ------------------------------------------------------------------ #
    # DB bootstrap
    # ------------------------------------------------------------------ #

    def _init_db_if_needed(self, db_path: str, log: List[str]) -> None:
        if self.db and self.store:
            return
        try:
            cfg = submanagers.DatabaseConfig(path=str(db_path or "video_corpus.db"))
            self.db = submanagers.DatabaseSubmanager(cfg, logger=getattr(self, "logger", None))
            self.store = VideoTrackerStore(db=self.db)
            self.store.ensure_schema()
            log.append(f"[VideoLinkTracker][db] Store ready at {cfg.normalized_path()}")
        except Exception as e:
            log.append(f"[VideoLinkTracker][db] Failed initializing store: {e}")
            self.db = None
            self.store = None

    # ------------------------------------------------------------------ #
    # Keyword / URL heuristics
    # ------------------------------------------------------------------ #

    def _get_keywords_from_query(self, query: str) -> List[str]:
        tokens = [
            t
            for t in re.findall(r"[A-Za-z0-9][A-Za-z0-9_\-]+", query.lower())
            if t not in _STOPWORDS and len(t) > 2
        ]
        return list(dict.fromkeys(tokens))

    def _clean_domain(self, u: str) -> str:
        try:
            netloc = urlparse(u).netloc.lower()
            return netloc.split(":")[0]
        except Exception:
            return ""

    def _clean_path(self, u: str) -> str:
        try:
            return urlparse(u).path.lower()
        except Exception:
            return ""

    def _looks_like_ad(self, netloc: str, path: str) -> bool:
        host = netloc.lower()
        p = path.lower()
        if any(sub in host for sub in self.AD_HOST_SUBSTRINGS):
            return True
        if any(kw in p for kw in self.AD_PATH_KEYWORDS):
            return True
        filename = p.rsplit("/", 1)[-1]
        if any(junk in filename for junk in self.JUNK_FILENAME_KEYWORDS):
            return True
        return False

    def _is_probable_video_url(self, full_url: str, path_lower: str, url_lower: str) -> bool:
        if any(path_lower.endswith(ext) for ext in self.VIDEO_EXTENSIONS):
            return True
        if any(platform in url_lower for platform in self.VIDEO_PLATFORMS):
            return True
        if any(kw in url_lower for kw in self.STREAM_HINT_KEYWORDS):
            return True
        return False

    def _is_content_child_candidate(self, full_url: str, netloc: str, path: str) -> bool:
        p = path.lower()
        if self._looks_like_ad(netloc, p):
            return False

        # [PATCH] Add "/a/" and "/gallery/" to hints
        content_hints = [
            "/details/", "/video/", "/videos/", "/watch/",
            "/title/", "/entry/", "/post/", "/show/", "/episode/",
            "/a/", "/album/", "/gallery/", "/view/", "/g/"
        ]

        # Also allow if the path is basically just a short ID (common on Erome)
        # e.g., site.com/a/12345
        path_parts = p.strip("/").split("/")
        if len(path_parts) == 2 and path_parts[0] in ["a", "v", "g"]:
            return True

        return any(h in p for h in content_hints)

    def _is_search_url(self, u: str) -> bool:
        try:
            pu = urlparse(u)
            path = (pu.path or "").lower()
            q = (pu.query or "").lower()
            if any(tok in path for tok in ["/search", "/results", "/query", "search.php", "/find"]):
                return True
            if any(k + "=" in q for k in ["q", "query", "s", "search", "keyword", "term"]):
                return True
            return False
        except Exception:
            return False

    def _allowed_by_required_sites(self, u: str, sites_list: List[str], global_mode: bool = False) -> bool:
        if global_mode or not sites_list or sites_list == ["*"]:
            return True
        d = self._clean_domain(u)
        return any(req in d for req in sites_list)

    def _term_overlap_ok_check(self, haystack: str, kw_list: List[str], min_overlap: int) -> bool:
        if not kw_list:
            return True
        h = haystack.lower()
        hits = 0
        for k in kw_list:
            if k and k in h:
                hits += 1
                if hits >= min_overlap:
                    return True
        return False

    # ------------------------------------------------------------------ #
    # [PATCH] Content Scoring Logic
    # ------------------------------------------------------------------ #

    def _score_video_asset(self, url: str, text: str, keywords: List[str]) -> int:
        """
        Scoring heuristics:
        + Positive for keyword matches in URL/Text
        + Positive for high-quality container types (.mkv, .m3u8)
        - Heavy penalty for ad-like filenames (trailer, promo, preview)
        - Penalty for missing link text
        """
        score = 0
        u_lower = url.lower()
        t_lower = (text or "").lower()

        # 1. Critical Filters (Immediate penalties)
        negative_hints = {
         "ad_", "advert", "pixel", "tracker", "overlay"
        }
        if any(h in u_lower for h in negative_hints):
            score -= 50
        if any(h in t_lower for h in negative_hints):
            score -= 50

        # 2. Keyword Relevance
        for k in keywords:
            k = k.lower()
            if k in u_lower:
                score += 20
            if k in t_lower:
                score += 10

        # 3. Format preferences
        # .m3u8 often implies a full stream; .mkv implies high quality rip
        if ".m3u8" in u_lower or ".mpd" in u_lower:
            score += 15
        elif ".mkv" in u_lower:
            score += 10
        elif ".mp4" in u_lower:
            score += 5  # Generic, could be ad or content

        # 4. Context heuristics
        if "1080p" in u_lower or "720p" in u_lower:
            score += 5
        if not t_lower:
            score -= 5  # Blind links are riskier

        return score
    # ------------------------------------------------------------------ #
    # Reverse Image/Video Lookup Helpers
    # ------------------------------------------------------------------ #

    async def _extract_frame_from_video(
            self,
            video_input: str,
            ffmpeg_bin: str,
            log: List[str],
    ) -> Optional[bytes]:
        """
        Uses FFmpeg to extract a single RANDOM frame from a video (local path or URL).

        Improvements:
          - Robust ffmpeg/ffprobe resolution (Windows-friendly)
          - Multiple duration probe strategies (format duration, stream duration)
          - Safe timestamp selection for short videos
          - Two extraction attempts: fast-seek (-ss before -i) then accurate (-ss after -i)
          - Uses PNG + image2pipe for reliability
        """
        import os
        import shutil
        import random
        import json
        import asyncio
        from typing import Optional

        video_input = (video_input or "").strip()
        if not video_input:
            log.append("[VideoLinkTracker][ffmpeg] Missing video_input.")
            return None

        # ----------------------------
        # Resolve binaries robustly
        # ----------------------------
        def _resolve_bin(name_or_path: str) -> Optional[str]:
            if not name_or_path:
                return None
            # If it's a file path
            if os.path.exists(name_or_path):
                return os.path.abspath(name_or_path)
            # Try PATH lookup
            found = shutil.which(name_or_path)
            if found:
                return found
            # On Windows callers sometimes pass "ffmpeg" but have ffmpeg.exe
            if not name_or_path.lower().endswith(".exe"):
                found = shutil.which(name_or_path + ".exe")
                if found:
                    return found
            return None

        exe = _resolve_bin(ffmpeg_bin) or _resolve_bin("ffmpeg")
        if not exe:
            log.append(f"[VideoLinkTracker][ffmpeg] FFmpeg binary not found (ffmpeg_bin={ffmpeg_bin!r}).")
            return None

        # Derive ffprobe name from ffmpeg name, but also try PATH lookups
        ffprobe_guess = os.path.join(os.path.dirname(exe), "ffprobe" + (".exe" if exe.lower().endswith(".exe") else ""))
        ffprobe = _resolve_bin(ffprobe_guess) or _resolve_bin("ffprobe")
        if not ffprobe:
            log.append("[VideoLinkTracker][ffmpeg] FFprobe binary not found. Will fall back to non-random timestamp.")
            ffprobe = None

        # ----------------------------
        # Probe duration (best-effort)
        # ----------------------------
        duration: Optional[float] = None

        async def _run_ffprobe(cmd: list[str]) -> tuple[int, bytes, bytes]:
            proc = await asyncio.create_subprocess_exec(
                *cmd,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )
            out, err = await proc.communicate()
            return proc.returncode, out, err

        if ffprobe:
            # Try 1: container/format duration
            probe_cmd_1 = [
                ffprobe, "-v", "error",
                "-select_streams", "v:0",
                "-show_entries", "format=duration",
                "-of", "json",
                video_input,
            ]
            try:
                rc, out, err = await _run_ffprobe(probe_cmd_1)
                if rc == 0 and out:
                    info = json.loads(out.decode(errors="ignore") or "{}")
                    dur_s = (info.get("format") or {}).get("duration")
                    if dur_s is not None:
                        d = float(dur_s)
                        if d > 0:
                            duration = d
            except Exception as e:
                log.append(f"[VideoLinkTracker][ffmpeg] ffprobe(format.duration) exception: {e}")

            # Try 2: stream duration (some formats don’t set format.duration)
            if not duration:
                probe_cmd_2 = [
                    ffprobe, "-v", "error",
                    "-select_streams", "v:0",
                    "-show_entries", "stream=duration",
                    "-of", "json",
                    video_input,
                ]
                try:
                    rc, out, err = await _run_ffprobe(probe_cmd_2)
                    if rc == 0 and out:
                        info = json.loads(out.decode(errors="ignore") or "{}")
                        streams = info.get("streams") or []
                        if streams:
                            dur_s = (streams[0] or {}).get("duration")
                            if dur_s is not None:
                                d = float(dur_s)
                                if d > 0:
                                    duration = d
                except Exception as e:
                    log.append(f"[VideoLinkTracker][ffmpeg] ffprobe(stream.duration) exception: {e}")

            if duration:
                log.append(f"[VideoLinkTracker][ffmpeg] Probed duration={duration:.3f}s")
            else:
                # Useful stderr if probe fails
                try:
                    rc, out, err = await _run_ffprobe(probe_cmd_1)
                    if rc != 0 and err:
                        log.append(
                            f"[VideoLinkTracker][ffmpeg] ffprobe error: {err.decode(errors='ignore').strip()[:500]}")
                except Exception:
                    pass

        # ----------------------------
        # Pick timestamp safely
        # ----------------------------
        # If we can't probe duration, pick a reasonable mid-ish timestamp and hope.
        if not duration or duration <= 0:
            timestamp = 1.0
            log.append("[VideoLinkTracker][ffmpeg] Duration unknown; using timestamp=1.0s fallback.")
        else:
            # Avoid start/end; handle short videos safely.
            # Use a margin that scales down for very short clips.
            margin = min(1.0, duration * 0.05)
            start = margin
            end = max(start, duration - margin)

            # If clip is extremely short, just sample near middle.
            if end - start < 0.25:
                timestamp = max(0.0, duration * 0.5)
            else:
                timestamp = random.uniform(start, end)

            log.append(
                f"[VideoLinkTracker][ffmpeg] Extracting random frame at {timestamp:.3f}s (duration={duration:.2f}s)"
            )

        timestamp_str = f"{timestamp:.3f}"

        # ----------------------------
        # Extract frame (two attempts)
        # ----------------------------
        async def _run_ffmpeg(cmd: list[str]) -> tuple[int, bytes, bytes]:
            proc = await asyncio.create_subprocess_exec(
                *cmd,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE,
            )
            out, err = await proc.communicate()
            return proc.returncode, out, err

        common_out = [
            "-hide_banner", "-loglevel", "error",
            "-an",
            "-frames:v", "1",
            "-f", "image2pipe",
            "-vcodec", "png",
            "pipe:1",
        ]

        # Attempt A: fast seek (-ss before -i)
        cmd_a = [exe, "-ss", timestamp_str, "-i", video_input] + common_out

        # Attempt B: accurate seek (-ss after -i) (often works when A fails)
        cmd_b = [exe, "-i", video_input, "-ss", timestamp_str] + common_out

        # Some URLs are twitchy; a tiny reconnect/timeout can help, but keep it minimal/portable
        # (If you want, you can add: "-rw_timeout", "15000000" for some builds)
        for label, cmd in (("fast", cmd_a), ("accurate", cmd_b)):
            try:
                rc, out, err = await _run_ffmpeg(cmd)
                if rc == 0 and out:
                    return out

                err_txt = (err.decode(errors="ignore") if err else "").strip()
                log.append(
                    f"[VideoLinkTracker][ffmpeg] {label} extract failed (code {rc}). "
                    f"{err_txt[:800]}"
                )
            except Exception as e:
                log.append(f"[VideoLinkTracker][ffmpeg] {label} extract exception: {e}")

        log.append("[VideoLinkTracker][ffmpeg] Failed to extract frame from video (all strategies).")
        return None

    async def _upload_frame_to_host(self, image_bytes: bytes, log: List[str]) -> Optional[str]:
        """
        Uploads bytes to a temporary host (Catbox.moe) to get a public URL
        compatible with search engine 'imgurl' parameters.
        """
        import aiohttp

        # Using Catbox.moe for simplicity (no key needed)
        upload_url = "https://catbox.moe/user/api.php"

        data = aiohttp.FormData()
        data.add_field("reqtype", "fileupload")
        data.add_field("userhash", "")
        data.add_field("fileToUpload", image_bytes, filename="frame.jpg", content_type="image/jpeg")

        try:
            async with aiohttp.ClientSession() as session:
                async with session.post(upload_url, data=data, timeout=15) as resp:
                    if resp.status != 200:
                        log.append(f"[VideoLinkTracker][Upload] Upload failed: {resp.status}")
                        return None

                    text = await resp.text()
                    if text.startswith("http"):
                        return text.strip()
                    else:
                        log.append(f"[VideoLinkTracker][Upload] Unexpected response: {text[:100]}")
                        return None
        except Exception as e:
            log.append(f"[VideoLinkTracker][Upload] Error: {e}")
            return None

    async def _fetch_reverse_image_seeds(
            self,
            image_url: str,
            timeout: float,
            log: List[str],
            max_results: int = 15
    ) -> List[str]:
        """
        Robust Multi-Engine Reverse Image Search (Yandex + Bing Visual Search + Google Lens).
        Uses Playwright/Camoufox to bypass bot detection and render JS results.
        """
        from urllib.parse import quote

        if not image_url:
            return []

        seeds = []
        unique_seeds = set()

        # 1. Setup Engines
        # Yandex is often better for exact video source matches
        yandex_url = f"https://yandex.com/images/search?rpt=imageview&url={quote(image_url)}"
        # Bing Visual Search for additional context / host pages
        bing_url = (
            "https://www.bing.com/images/search"
            f"?view=detailv2&iss=sbi&FORM=SBIIDP&sbisrc=UrlPaste&q=imgurl:{quote(image_url)}"
        )
        # Google Lens for broad context
        google_url = f"https://lens.google.com/uploadbyurl?url={quote(image_url)}"

        # 2. Initialize Playwright (Reusing your robust context opener)
        # We need a full browser because Google/Yandex/Bing heavily rely on JS
        pw_p = pw_browser = pw_context = None

        try:
            DEBUG_LOGGER.log_message(f"[VideoLinkTracker][RevImg] Initializing browser for reverse lookup...")
            pw_p, pw_browser, pw_context = await self._open_playwright_context(
                ua=(
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/120.0.0.0 Safari/537.36"
                ),
                block_resources=True,
                # still allow images; fonts/media/stylesheet can be blocked safely
                blocked_resource_types={"font", "media"},
                block_domains=False,
                blocked_domains=set(),
                log=log,
                use_camoufox=True  # Critical for avoiding Google's/Bing's bot detection
            )

            if not pw_context:
                log.append("[VideoLinkTracker][RevImg] Playwright failed to start. Skipping.")
                return []

            page = await pw_context.new_page()

            # --- ENGINE 1: YANDEX (The "Source Finder") ---
            try:
                DEBUG_LOGGER.log_message(f"[VideoLinkTracker][RevImg] Scanning Yandex Images...")
                await page.goto(yandex_url, timeout=int(timeout * 1000))

                # Wait for some links to appear
                try:
                    await page.wait_for_selector("a[href]", timeout=6000)
                except:
                    pass

                # Extract links specifically from the results area
                yandex_links = await page.evaluate("""
                    () => {
                        const links = [];
                        // Yandex 'similar images' and 'sites' usually appear in specific containers
                        // We grab all external links to be safe
                        document.querySelectorAll('a[href]').forEach(a => {
                            if (a.href.startsWith('http') &&
                                !a.href.includes('yandex.') &&
                                !a.href.includes('google.')) {
                                links.push(a.href);
                            }
                        });
                        return links;
                    }
                """)

                count_before = len(unique_seeds)
                for link in yandex_links:
                    if link not in unique_seeds and link != image_url:
                        unique_seeds.add(link)
                        seeds.append(link)

                DEBUG_LOGGER.log_message(
                    f"[VideoLinkTracker][RevImg] Yandex found {len(unique_seeds) - count_before} new seeds."
                )

            except Exception as e:
                DEBUG_LOGGER.log_message(f"[VideoLinkTracker][RevImg] Yandex scan failed: {e}")

            # --- ENGINE 2: BING VISUAL SEARCH (The "Extra Context Finder") ---
            if len(seeds) < max_results:
                try:
                    DEBUG_LOGGER.log_message(f"[VideoLinkTracker][RevImg] Scanning Bing Visual Search...")
                    await page.goto(bing_url, timeout=int(timeout * 1000))

                    # Try to get past any light consent prompts
                    try:
                        await page.wait_for_selector("a[href]", timeout=6000)
                    except:
                        pass

                    bing_links = await page.evaluate("""
                        () => {
                            const links = [];
                            document.querySelectorAll('a[href]').forEach(a => {
                                const h = a.href;
                                if (h.startsWith('http') &&
                                    !h.includes('bing.com') &&
                                    !h.includes('microsoft.com') &&
                                    !h.includes('google.') &&
                                    !h.includes('yandex.')) {
                                    links.push(h);
                                }
                            });
                            return links;
                        }
                    """)

                    count_before = len(unique_seeds)
                    for link in bing_links:
                        if link not in unique_seeds and link != image_url:
                            unique_seeds.add(link)
                            seeds.append(link)
                            if len(seeds) >= max_results:
                                break

                    DEBUG_LOGGER.log_message(
                        f"[VideoLinkTracker][RevImg] Bing Visual Search found "
                        f"{len(unique_seeds) - count_before} new seeds."
                    )

                except Exception as e:
                    DEBUG_LOGGER.log_message(f"[VideoLinkTracker][RevImg] Bing Visual Search scan failed: {e}")

            # --- ENGINE 3: GOOGLE LENS (The "Context Finder") ---
            if len(seeds) < max_results:
                try:
                    DEBUG_LOGGER.log_message(f"[VideoLinkTracker][RevImg] Scanning Google Lens...")
                    await page.goto(google_url, timeout=int(timeout * 1000))

                    # Handle "Accept Cookies" modal if it appears
                    try:
                        # Common selector for Google consent 'Reject all' or 'Accept all'
                        await page.click('button[aria-label="Reject all"]', timeout=2000)
                    except:
                        pass

                    # Wait for results
                    try:
                        await page.wait_for_selector("a[href]", timeout=6000)
                    except:
                        pass

                    google_links = await page.evaluate("""
                        () => {
                            const links = [];
                            // Target the 'Visual matches' grid links
                            document.querySelectorAll('a[href]').forEach(a => {
                                const h = a.href;
                                if (h.startsWith('http') && 
                                    !h.includes('google.') && 
                                    !h.includes('googleusercontent') &&
                                    !h.includes('gstatic')) {
                                    links.push(h);
                                }
                            });
                            return links;
                        }
                    """)

                    count_before = len(unique_seeds)
                    for link in google_links:
                        if link not in unique_seeds and link != image_url:
                            unique_seeds.add(link)
                            seeds.append(link)
                            if len(seeds) >= max_results:
                                break

                    DEBUG_LOGGER.log_message(
                        f"[VideoLinkTracker][RevImg] Google Lens found "
                        f"{len(unique_seeds) - count_before} new seeds."
                    )

                except Exception as e:
                    DEBUG_LOGGER.log_message(f"[VideoLinkTracker][RevImg] Google Lens scan failed: {e}")

        except Exception as e:
            DEBUG_LOGGER.log_message(f"[VideoLinkTracker][RevImg] Browser error: {e}")

        finally:
            await self._close_playwright_context(pw_p, pw_browser, pw_context, log)

        return seeds[:max_results]

    def _decompress_if_needed(self, url: str, content: bytes) -> str:
        """
        Detects if content is GZIP compressed (via magic bytes or extension)
        and decompresses it. Returns decoded UTF-8 string.
        """
        import gzip

        if not content:
            return ""

        # 1. Check GZIP magic bytes (0x1f 0x8b)
        # This is more reliable than trusting the file extension or headers alone.
        is_gzipped = content.startswith(b"\x1f\x8b")

        # 2. Fallback: If magic bytes fail but URL ends in .gz, try forcing decompression
        if not is_gzipped and url and url.lower().endswith(".gz"):
            is_gzipped = True

        if is_gzipped:
            try:
                content = gzip.decompress(content)
            except Exception:
                # If decompression fails (e.g. corrupt file or false positive),
                # keep original content and try to decode as plain text.
                pass

        try:
            # Decode to string, replacing errors to prevent crashing on bad characters
            return content.decode("utf-8", errors="replace")
        except Exception:
            # If standard decoding fails entirely, return empty
            return ""
    # ------------------------------------------------------------------ #
    # Sitemap / Site Crawling Helpers (now using HTTPSSubmanager)
    # ------------------------------------------------------------------ #

    def _looks_like_sitemap(self, url: str) -> bool:
        u = url.lower()
        return any(u.endswith(x) for x in [".xml", ".xml.gz", "sitemap", "sitemap.xml", "sitemap_index.xml", "feed"])

    def _extract_sitemap_urls_from_robots(self, text: str) -> list[str]:
        urls = []
        for line in (text or "").splitlines():
            if line.lower().startswith("sitemap:"):
                u = line.split(":", 1)[1].strip()
                if u.startswith("http"):
                    urls.append(u)
        return urls

    def _parse_sitemap_any(self, xml_text: str) -> tuple[list[str], list[str]]:
        if not xml_text.strip() or ET is None:
            return [], []
        try:
            root = ET.fromstring(xml_text)
        except Exception:
            return [], []

        ns = ""
        if root.tag.startswith("{"):
            ns = root.tag.split("}", 1)[0] + "}"

        sitemap_urls = []
        page_urls = []

        if root.tag.endswith("sitemapindex"):
            for sm in root.findall(f".//{ns}sitemap/{ns}loc"):
                if sm.text and sm.text.strip().startswith("http"):
                    sitemap_urls.append(sm.text.strip())

        if root.tag.endswith("urlset"):
            for loc in root.findall(f".//{ns}url/{ns}loc"):
                if loc.text and loc.text.strip().startswith("http"):
                    page_urls.append(loc.text.strip())

        return sitemap_urls, page_urls

    def _score_site_url(self, u: str, keywords: list[str]) -> int:
        path = urlparse(u).path.lower()
        url_lower = u.lower()
        score = 0

        for tok, w in [
            ("/watch/", 10), ("/video/", 10), ("/videos/", 9), ("/stream/", 9),
            ("/embed/", 8), ("/player/", 8), ("/details/", 7), ("/post/", 5),
            ("/episode/", 7), ("/show/", 7),
        ]:
            if tok in path:
                score += w

        if self._is_probable_video_url(u, path, url_lower):
            score += 15

        for tok, w in [
            ("/search", -8), ("/tag/", -5), ("/category/", -5), ("/browse", -5),
            ("/archives", -3), ("/index.", -2),
        ]:
            if tok in path:
                score += w

        low = url_lower.replace("%20", " ")
        score += sum(3 for k in keywords if k and k in low)

        return score

    def _archive_ident_to_downloads(self, ident: str) -> list[str]:
        return [
            f"https://archive.org/metadata/{ident}",
            f"https://archive.org/download/{ident}/",
            f"https://archive.org/details/{ident}",
        ]

    async def _crawl_sitemaps_for_site(
        self,
        http: "HTTPSSubmanager",
        root: str,
        sm_urls: list[str],
        timeout: float,  # kept for signature compatibility
        keywords: list[str],
        per_site_cap: int,
        global_seen: set[str],
        log: List[str],
    ) -> list[str]:
        to_visit = list(dict.fromkeys(sm_urls))
        visited_sm = set()
        collected = []

        while to_visit and len(collected) < per_site_cap * 5:
            sm = to_visit.pop(0)
            if sm in visited_sm:
                continue
            visited_sm.add(sm)

            try:
                raw = await http.get_bytes(sm)
            except Exception as e:
                log.append(f"[VideoLinkTracker][sites] Failed fetching sitemap {sm}: {e}")
                continue

            xml = self._decompress_if_needed(sm, raw)
            child_sms, pages = self._parse_sitemap_any(xml)

            for c in child_sms:
                if c not in visited_sm and self._looks_like_sitemap(c):
                    to_visit.append(c)

            for p in pages:
                if p in global_seen:
                    continue
                global_seen.add(p)
                collected.append(p)

        collected.sort(key=lambda u: self._score_site_url(u, keywords), reverse=True)
        return collected[:per_site_cap]

    def _extract_next_page_links(self, soup, base_url: str) -> list[str]:
        out = []
        for a in soup.select(
            "a[rel=next], a.next, a.pagination__next, a:-soup-contains('Next'), a:-soup-contains('Older')"
        ):
            href = a.get("href")
            if href:
                out.append(urljoin(base_url, href))
        return out[:3]

    def _extract_internal_result_links(self, soup, base_url: str, site_host: str) -> list[str]:
        out = []
        selectors = [
            "article a[href]", ".result a[href]", ".search-result a[href]",
            ".item a[href]", "li a[href]", "div.post-content a[href]",
            "h2 a[href]", "h3 a[href]", "h4 a[href]",
        ]
        for a in soup.select(", ".join(selectors)):
            href = a.get("href")
            if not href:
                continue
            full = urljoin(base_url, href)
            try:
                host = urlparse(full).netloc.lower()
            except Exception:
                continue
            if site_host in host:
                out.append(full)
            if len(out) >= 200:
                break
        return list(dict.fromkeys(out))

    def _seed_pages_from_required_sites(
        self,
        required_sites: List[str],
        queries: List[str],
        probe_cap_per_site: int = 5,
        sitemap_cap_per_site: int = 8,
        hub_cap_per_site: int = 6,
    ) -> Tuple[List[str], Set[str], Set[str]]:
        out: List[str] = []
        synthetic_search_seeds: set[str] = set()
        explicit_site_seeds: set[str] = set()

        norm_sites = []
        for raw in required_sites or []:
            s = (raw or "").strip()
            if not s:
                continue
            norm_sites.append(s.rstrip("/") if "://" in s else "https://" + s.lstrip(".").rstrip("/"))

        for s in norm_sites:
            u = s + "/"
            out.append(u)
            explicit_site_seeds.add(u)

        common_sitemaps = [
            "/sitemap.xml", "/sitemap_index.xml", "/sitemap/sitemap.xml",
            "/sitemap-index.xml", "/sitemap.php", "/sitemap.txt", "/feed/", "/rss/",
        ]
        for s in norm_sites:
            u = s + "/robots.txt"
            out.append(u)
            explicit_site_seeds.add(u)
            added = 0
            for sm in common_sitemaps:
                if added >= sitemap_cap_per_site:
                    break
                u = s + sm
                out.append(u)
                explicit_site_seeds.add(u)
                added += 1

        hub_paths = [
            "/tag/", "/tags/", "/category/", "/categories/", "/archive/", "/archives/",
            "/browse/", "/collections/", "/series/", "/authors/", "/topics/", "/search",
            "/videos/", "/player/", "/watch/", "/embed/",
        ]
        for s in norm_sites:
            added = 0
            for hp in hub_paths:
                if added >= hub_cap_per_site:
                    break
                u = s + hp
                out.append(u)
                explicit_site_seeds.add(u)
                added += 1

        def _extra_probes_for_site(base: str, enc_query: str) -> list[str]:
            host = urlparse(base).netloc.lower()
            if "archive.org" in host:
                return [
                    base + f"/search.php?query={enc_query}",
                    base + f"/advancedsearch.php?q={enc_query}",
                    base + (f"/advancedsearch.php?q={enc_query}"
                            f"&fl[]=identifier&fl[]=title&rows=50&page=1&output=json"),
                    base + f"/details/{enc_query}",
                    base + f"/browse.php?field=subject&query={enc_query}",
                ]
            return []

        if queries:
            for s in norm_sites:
                probes_added = 0
                for qv in queries:
                    if probes_added >= probe_cap_per_site:
                        break
                    qv = (qv or "").strip()
                    if not qv:
                        continue
                    enc = quote_plus(qv)

                    probes = [
                        s + f"/search?q={enc}",
                        s + f"/search?query={enc}",
                        s + f"/?s={enc}",
                        s + f"/?k={enc}",
                        s + f"/search/{enc}",
                        s + f"/video/search?q={enc}",
                    ]
                    probes.extend(_extra_probes_for_site(s, enc))

                    for p in probes:
                        out.append(p)
                        synthetic_search_seeds.add(p)
                        probes_added += 1
                        if probes_added >= probe_cap_per_site and "archive.org" not in s:
                            break

        return out, synthetic_search_seeds, explicit_site_seeds

    # ------------------------------------------------------------------ #
    # Playwright shared context
    # ------------------------------------------------------------------ #

    async def _open_playwright_context(
            self,
            ua: str,
            block_resources: bool,
            blocked_resource_types: set[str],
            block_domains: bool,
            blocked_domains: set[str],
            log: List[str],
            *,
            use_camoufox: bool = False,
            camoufox_options: Optional[Dict[str, Any]] = None,

            # NEW:
            pw_launch_args: Optional[List[str]] = None,
            pw_headless: bool = True,
            pw_channel: Optional[str] = None,
            pw_proxy: Optional[Dict[str, Any]] = None,
    ):
        """
        Open a shared Playwright/Camoufox browser context.

        Returns (p_handle, browser, context) where:
          - For plain Playwright:
              p_handle = async_playwright() instance
          - For Camoufox:
              p_handle = AsyncCamoufox instance (so we can __aexit__ it later)
        """

        # ---- small helper for blocked domains ----
        def _host_matches_blocked(host: str) -> bool:
            host = host.split(":", 1)[0].lower()
            for bd in blocked_domains:
                bd = bd.lower()
                if not bd:
                    continue
                if host == bd or host.endswith("." + bd):
                    return True
            return False

        # ---- Camoufox path ----
        if use_camoufox:
            if AsyncCamoufox is None:
                log.append("[PlaywrightCtx] Camoufox requested but not installed; falling back to Chromium.")
            else:
                try:
                    # Default Camoufox launch opts; you can tweak these
                    options = {
                        "headless": True,
                        "block_images": block_resources,
                        "block_webrtc": True,
                        "geoip": False,
                        "humanize": False,
                    }
                    if camoufox_options:
                        options.update(camoufox_options)

                    # Async context manager: we keep the CM instance as p_handle
                    cf_cm = AsyncCamoufox(**options)
                    browser = await cf_cm.__aenter__()  # returns a Playwright-like Browser
                    context = await browser.new_context(user_agent=ua)

                    # Route blocking is exactly like Playwright Firefox
                    if block_resources or block_domains:
                        async def route_blocker(route, request):
                            rtype = (request.resource_type or "").lower()
                            try:
                                host = urlparse(request.url).netloc.lower()
                            except Exception:
                                host = ""

                            if block_domains and _host_matches_blocked(host):
                                await route.abort()
                                return

                            if block_resources and rtype in blocked_resource_types:
                                await route.abort()
                                return

                            await route.continue_()

                        await context.route("**/*", route_blocker)

                    log.append("[PlaywrightCtx] Camoufox context ready.")
                    return cf_cm, browser, context

                except Exception as e:
                    log.append(f"[PlaywrightCtx] Camoufox init failed ({e}); falling back to Chromium.")

        # ---- Standard Playwright (Chromium) path ----
        try:
            from playwright.async_api import async_playwright
        except ImportError:
            log.append("Playwright not installed.")
            return None, None, None

        p = await async_playwright().start()

        launch_opts = {
            "headless": pw_headless,
            "args": list(pw_launch_args or []),
        }
        if pw_channel:
            launch_opts["channel"] = pw_channel
        if pw_proxy:
            launch_opts["proxy"] = pw_proxy

        browser = await p.chromium.launch(**launch_opts)
        context = await browser.new_context(user_agent=ua)

        if block_resources or block_domains:
            async def route_blocker(route, request):
                rtype = (request.resource_type or "").lower()
                try:
                    host = urlparse(request.url).netloc.lower()
                except Exception:
                    host = ""

                if block_domains and _host_matches_blocked(host):
                    await route.abort()
                    return

                if block_resources and rtype in blocked_resource_types:
                    await route.abort()
                    return

                await route.continue_()

            await context.route("**/*", route_blocker)

        log.append("Playwright shared context ready.")
        return p, browser, context

    async def _close_playwright_context(self, p, browser, context, log: List[str]):
        # Close page context
        try:
            if context:
                close_ctx = getattr(context, "close", None)
                if callable(close_ctx):
                    if asyncio.iscoroutinefunction(close_ctx):
                        await close_ctx()
                    else:
                        close_ctx()
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox context: {e}")

        # Close browser
        try:
            if browser:
                close_browser = getattr(browser, "close", None)
                if callable(close_browser):
                    if asyncio.iscoroutinefunction(close_browser):
                        await close_browser()
                    else:
                        close_browser()
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox browser: {e}")

        # Close handle:
        #   - Playwright: p.stop()
        #   - Camoufox: await p.__aexit__(...)
        try:
            if p:
                stop = getattr(p, "stop", None)

                # async_playwright handle
                if stop:
                    if asyncio.iscoroutinefunction(stop):
                        await stop()
                    else:
                        stop()

                else:
                    # AsyncCamoufox (or any other async CM)
                    aexit = getattr(p, "__aexit__", None)
                    if aexit:
                        if asyncio.iscoroutinefunction(aexit):
                            await aexit(None, None, None)
                        else:
                            aexit(None, None, None)

            log.append("Playwright/Camoufox shared context closed.")
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox handle: {e}")

    # ------------------------------------------------------------------ #
    # Network sniff + JS extraction
    # ------------------------------------------------------------------ #

    async def _pw_fetch_with_sniff(self, context, page_url, timeout, log, extensions=None):
        return await asyncio.wait_for(self.network_sniffer.sniff(
            context, page_url,
            timeout=timeout,
            log=log,
            extensions=extensions,
        ), timeout=25)

    async def _pw_fetch_js_links(self, context, page_url, timeout, log, extensions=None):
        return await asyncio.wait_for(self.js_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
            extensions=extensions,
        ), timeout=25)

    async def _pw_fetch_runtime_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.runtime_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
        ), timeout=25)

    async def _pw_fetch_react_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.react_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
        ), timeout=25)


    async def _pw_fetch_database_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.database_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
        ), timeout=25)

    async def _pw_fetch_interaction_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.interaction_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log
        ), timeout=25)

    # ------------------------------------------------------------------ #
    # Search engines (DuckDuckGo + Google CSE)
    # ------------------------------------------------------------------ #

    async def _search_duckduckgo(
            self,
            q: str,
            max_results: int,
            ua: str,
            timeout: float,
            log: List[str],
            page_limit: int = 1,
            per_page: int = 50,
    ) -> List[str]:
        """
        DuckDuckGo HTML search, tuned to avoid bot wall as much as possible.
        This is modeled after the LinkTracker DDG search, but logs into `log`.
        """
        import random
        import aiohttp
        from aiohttp import ClientTimeout
        from bs4 import BeautifulSoup
        from urllib.parse import unquote

        pages: List[str] = []
        seen_urls: set[str] = set()
        did_dump_debug = False

        real_ua = (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/115.0.0.0 Safari/537.36"
        )

        headers = {
            "User-Agent": real_ua,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
            "Accept-Encoding": "gzip, deflate, br",
            "Referer": "https://duckduckgo.com/",
            "Origin": "https://duckduckgo.com",
            "DNT": "1",
            "Upgrade-Insecure-Requests": "1",
            "Sec-Fetch-Site": "same-origin",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Dest": "document",
        }

        q = (q or "").strip()
        if not q:
            log.append("[VideoLinkTracker][DDG] Empty query, skipping search.")
            return []

        max_results = max(1, min(int(max_results), 256))
        page_limit = max(1, min(int(page_limit), 5))
        base_url = "https://html.duckduckgo.com/html/"

        try:
            async with aiohttp.ClientSession(headers=headers) as session:
                for page_idx in range(page_limit):
                    if len(pages) >= max_results:
                        break

                    # Gentle delay between pages
                    if page_idx > 0:
                        st = random.uniform(2.0, 5.0)
                        log.append(f"[VideoLinkTracker][DDG] Sleeping {st:.2f}s between search pages...")
                        await asyncio.sleep(st)

                    offset = page_idx * 30
                    text = ""
                    status = None
                    final_url = base_url

                    try:
                        data = {"q": q, "s": str(offset), "dc": str(offset)}
                        async with session.post(
                                base_url,
                                data=data,
                                timeout=ClientTimeout(total=timeout),
                        ) as resp:
                            status = resp.status
                            final_url = str(resp.url)

                            if status == 403:
                                log.append(f"[VideoLinkTracker][DDG] 403 Forbidden on page {page_idx}.")
                                if not pages and not did_dump_debug:
                                    text = await resp.text()
                                    preview = text[:2000].replace("\n", " ")
                                    log.append(
                                        f"[VideoLinkTracker][DDG][debug] 403 body preview: {preview}"
                                    )
                                    did_dump_debug = True
                                return pages

                            resp.raise_for_status()
                            text = await resp.text()

                    except Exception as e:
                        log.append(
                            f"[VideoLinkTracker][DDG] DuckDuckGo request failed (page {page_idx}): {e}"
                        )
                        if not pages and text and not did_dump_debug:
                            preview = text[:2000].replace("\n", " ")
                            log.append(
                                f"[VideoLinkTracker][DDG][debug] Failed page HTML preview: {preview}"
                            )
                            did_dump_debug = True
                        break

                    # Bot wall detection
                    if "Unfortunately, bots use DuckDuckGo too." in text:
                        log.append("[VideoLinkTracker][DDG] Bot wall detected by DDG.")
                        if not pages and not did_dump_debug:
                            preview = text[:2000].replace("\n", " ")
                            log.append(
                                f"[VideoLinkTracker][DDG][debug] Bot wall preview: {preview}"
                            )
                            did_dump_debug = True
                        break

                    soup = BeautifulSoup(text, "html.parser")
                    found_new = False

                    # Regular result links
                    for a in soup.select("a.result__a"):
                        if len(pages) >= max_results:
                            break
                        href = a.get("href")
                        if not href:
                            continue

                        # Unwrap /redirect?uddg=
                        if "uddg=" in href:
                            try:
                                href = unquote(href.split("uddg=", 1)[1].split("&", 1)[0])
                            except Exception:
                                pass

                        if href.startswith("http") and href not in seen_urls:
                            seen_urls.add(href)
                            pages.append(href)
                            found_new = True

                    # If we got nothing, dump debug once to log
                    if not found_new and not pages and not did_dump_debug:
                        preview = text[:2000].replace("\n", " ")
                        log.append(
                            f"[VideoLinkTracker][DDG][debug] No results on page {page_idx} "
                            f"for query={q!r} (status={status}, url={final_url}). "
                            f"HTML preview: {preview}"
                        )
                        did_dump_debug = True

                    if not found_new:
                        break

        except Exception as e:
            log.append(f"[VideoLinkTracker][DDG] Outer error: {e}")

        return pages[:max_results]

    async def _search_google_cse(
            self,
            q: str,
            n: int,
            timeout: float,
            log: List[str],
            page_limit: int = 1,
    ) -> List[str]:
        """
        Google Custom Search Engine wrapper, modeled after LinkTracker's version.

        Requires env vars:
          - GOOGLE_CSE_ID
          - GOOGLE_API_KEY
        """
        import os
        import json
        import aiohttp
        from aiohttp import ClientTimeout

        cx = os.environ.get("GOOGLE_CSE_ID")
        key = os.environ.get("GOOGLE_API_KEY")

        q = (q or "").strip()
        if not q:
            log.append("[VideoLinkTracker][GoogleCSE] Empty query, skipping search.")
            return []

        if not (cx and key):
            log.append(
                "[VideoLinkTracker][GoogleCSE] Missing GOOGLE_CSE_ID or GOOGLE_API_KEY env vars."
            )
            return []

        max_total = max(1, min(int(n), 100))
        per_page = min(10, max_total)
        max_pages_by_n = (max_total + per_page - 1) // per_page
        pages_to_fetch = max(1, min(int(page_limit) or 1, max_pages_by_n))

        out: List[str] = []
        did_dump_debug = False

        try:
            async with aiohttp.ClientSession() as session:
                for page_idx in range(pages_to_fetch):
                    if len(out) >= max_total:
                        break

                    start = 1 + page_idx * per_page
                    if start > 100:
                        break

                    text = ""
                    status = None

                    try:
                        async with session.get(
                                "https://www.googleapis.com/customsearch/v1",
                                params={
                                    "q": q,
                                    "cx": cx,
                                    "key": key,
                                    "num": per_page,
                                    "start": start,
                                },
                                timeout=ClientTimeout(total=timeout),
                        ) as resp:
                            status = resp.status
                            text = await resp.text()

                            if status != 200:
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    log.append(
                                        f"[VideoLinkTracker][GoogleCSE][debug] HTTP {status} "
                                        f"query={q!r} start={start}. Body preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            try:
                                data = json.loads(text)
                            except json.JSONDecodeError as e:
                                log.append(f"[VideoLinkTracker][GoogleCSE] JSON decode error: {e}")
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    log.append(
                                        f"[VideoLinkTracker][GoogleCSE][debug] Bad JSON preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            err_obj = data.get("error")
                            if err_obj:
                                msg = err_obj.get("message") or "Unknown CSE error"
                                reason = ""
                                errors = err_obj.get("errors") or []
                                if errors and isinstance(errors, list):
                                    reason = errors[0].get("reason") or ""
                                log.append(
                                    f"[VideoLinkTracker][GoogleCSE] API error for query={q!r}, "
                                    f"start={start}: {msg} ({reason})"
                                )
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    log.append(
                                        f"[VideoLinkTracker][GoogleCSE][debug] Error JSON preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            items = data.get("items") or []
                            if not items:
                                log.append(
                                    f"[VideoLinkTracker][GoogleCSE] No items for query={q!r}, "
                                    f"start={start}. Stopping pagination."
                                )
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    log.append(
                                        f"[VideoLinkTracker][GoogleCSE][debug] Empty items JSON preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            for item in items:
                                u = item.get("link")
                                if u:
                                    out.append(u)
                                    if len(out) >= max_total:
                                        break

                    except aiohttp.ClientError as e:
                        log.append(f"[VideoLinkTracker][GoogleCSE] AIOHTTP error: {e}")
                        if not out and text and not did_dump_debug:
                            preview = text[:1500].replace("\n", " ")
                            log.append(
                                f"[VideoLinkTracker][GoogleCSE][debug] ClientError body preview: {preview}"
                            )
                            did_dump_debug = True
                        break

        except Exception as e:
            log.append(f"[VideoLinkTracker][GoogleCSE] General error: {e}")

        return out
    async def _search_searxng(
            self,
            q: str,
            max_results: int,
            timeout: float,
            log: List[str],
            base_url: str,
            page_limit: int = 1,
    ) -> List[str]:
        """
        SearXNG JSON search.

        This assumes you run your own SearXNG instance so you don't care
        about bot walls from upstream engines.

        base_url example:
          http://127.0.0.1:8080
          https://searxng.yourdomain.tld

        You can configure it via:
          - params["searxng_url"]
          - or env var SEARXNG_URL
        """
        import json
        import aiohttp
        from aiohttp import ClientTimeout
        from urllib.parse import urljoin

        q = (q or "").strip()
        if not q:
            log.append("[VideoLinkTracker][SearXNG] Empty query, skipping search.")
            return []

        base_url = (base_url or "").strip().rstrip("/")
        if not base_url:
            log.append("[VideoLinkTracker][SearXNG] Missing base_url (set searxng_url or SEARXNG_URL).")
            return []

        search_url = base_url + "/search"

        max_results = max(1, min(int(max_results), 300))
        page_limit = max(1, min(int(page_limit), 10))

        out: List[str] = []
        seen: set[str] = set()
        did_dump_debug = False

        try:
            timeout_obj = ClientTimeout(total=timeout)
            async with aiohttp.ClientSession(timeout=timeout_obj) as session:
                for page_idx in range(page_limit):
                    if len(out) >= max_results:
                        break

                    pageno = page_idx + 1
                    params = {
                        "q": q,
                        "format": "json",
                        "language": "en",
                        "safesearch": 0,
                        "pageno": pageno,
                        # you can tune categories in your SearXNG instance;
                        # leaving it generic here:
                        "categories": "general",
                    }

                    text = ""
                    status = None
                    try:
                        async with session.get(search_url, params=params) as resp:
                            status = resp.status
                            text = await resp.text()

                            if status != 200:
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    log.append(
                                        f"[VideoLinkTracker][SearXNG][debug] HTTP {status} "
                                        f"query={q!r} pageno={pageno}. Body preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            try:
                                data = json.loads(text)
                            except json.JSONDecodeError as e:
                                log.append(f"[VideoLinkTracker][SearXNG] JSON decode error: {e}")
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    log.append(
                                        f"[VideoLinkTracker][SearXNG][debug] Bad JSON preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            results = data.get("results") or []
                            if not results:
                                log.append(
                                    f"[VideoLinkTracker][SearXNG] No items for query={q!r}, "
                                    f"pageno={pageno}. Stopping pagination."
                                )
                                break

                            found_new = False
                            for item in results:
                                u = item.get("url")
                                if not u:
                                    continue
                                if u in seen:
                                    continue
                                seen.add(u)
                                out.append(u)
                                found_new = True
                                if len(out) >= max_results:
                                    break

                            if not found_new:
                                break

                    except aiohttp.ClientError as e:
                        log.append(f"[VideoLinkTracker][SearXNG] AIOHTTP error: {e}")
                        if not out and text and not did_dump_debug:
                            preview = text[:1500].replace("\n", " ")
                            log.append(
                                f"[VideoLinkTracker][SearXNG][debug] ClientError body preview: {preview}"
                            )
                            did_dump_debug = True
                        break

        except Exception as e:
            log.append(f"[VideoLinkTracker][SearXNG] General error: {e}")

        return out[:max_results]
    def _predict_next_in_sequence(self, urls: List[str]) -> List[str]:
        generated = set()
        re_seq = re.compile(r"([0-9]+)(\.[a-z0-9]+)$", re.IGNORECASE)
        for u in urls:
            m = re_seq.search(u)
            if not m:
                continue
            num_s, ext = m.group(1), m.group(2)
            try:
                width = len(num_s)
                val = int(num_s)
                for i in range(1, 4):
                    nxt = f"{val + i:0{width}d}"
                    new_u = u[:m.start(1)] + nxt + u[m.end(1):]
                    generated.add(new_u)
            except ValueError:
                pass
        return list(generated)

    # ------------------------------------------------------------------ #
    # Main execution (HTTPSSubmanager integrated)
    # ------------------------------------------------------------------ #

    async def _download_asset_to_cache(
            self,
            http: "HTTPSSubmanager",
            url: str,
            cid: str,
            log: List[str],
            *,
            download_dir: str,
            max_bytes: int,
            skip_if_no_cl: bool = True,
    ) -> Optional[str]:
        """
        Download a direct-file asset (mp4/webm/etc.) to disk and return local path.

        Uses HEAD first to respect size caps, then GETs full bytes via http.get_bytes.
        """
        try:
            os.makedirs(download_dir, exist_ok=True)
        except Exception as e:
            log.append(f"[VideoLinkTracker][download] Failed to create dir {download_dir}: {e}")
            return None

        try:
            status, headers = await http.head(url)
        except Exception as e:
            log.append(f"[VideoLinkTracker][download] HEAD failed for {url}: {e}")
            return None

        if status != 200:
            log.append(f"[VideoLinkTracker][download] HEAD non-200 ({status}) for {url}")
            return None

        cl_raw = headers.get("content-length")
        if cl_raw:
            try:
                cl = int(cl_raw)
            except ValueError:
                cl = -1
        else:
            cl = -1

        if cl < 0 and skip_if_no_cl:
            log.append(f"[VideoLinkTracker][download] No Content-Length for {url}, skipping (skip_if_no_cl=True).")
            return None

        effective_size = cl if cl >= 0 else max_bytes + 1
        if effective_size > max_bytes:
            log.append(
                f"[VideoLinkTracker][download] Asset too large ({effective_size} bytes > {max_bytes}) for {url}"
            )
            return None

        # Derive a stable filename from cid + extension
        parsed = urlparse(url)
        filename = (parsed.path.rsplit("/", 1)[-1] or "asset").split("?")[0]
        base, ext = os.path.splitext(filename)
        if not ext:
            ext = ".bin"

        # Use a hash of cid so paths are deterministic
        h = hashlib.sha1(cid.encode("utf-8", "ignore")).hexdigest()[:16]
        safe_name = f"{base[:40]}_{h}{ext}"
        local_path = os.path.join(download_dir, safe_name)

        # If it already exists, assume we have it
        if os.path.exists(local_path):
            return local_path

        try:
            data = await http.get_bytes(url)
        except Exception as e:
            log.append(f"[VideoLinkTracker][download] GET failed for {url}: {e}")
            return None

        if len(data) > max_bytes:
            log.append(
                f"[VideoLinkTracker][download] Download exceeded max_bytes "
                f"({len(data)} > {max_bytes}) for {url}; discarding."
            )
            return None

        try:
            with open(local_path, "wb") as f:
                f.write(data)
        except Exception as e:
            log.append(f"[VideoLinkTracker][download] Failed writing {local_path}: {e}")
            return None

        log.append(f"[VideoLinkTracker][download] Cached {url} -> {local_path}")
        return local_path
    async def _execute_async(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:

        text = str(payload or "")
        inline_ctx: str = ""
        inline_lex: List[str] = []

        # Last [context] block
        try:
            inline_ctx = text.rsplit("[context]\n", 1)[1]
        except Exception:
            inline_ctx = ""

        # Last [lexicon] block (up to the next [tag)
        try:
            lex_part = text.rsplit("[lexicon]\n", 1)[1]
            lex_part = lex_part.split("\n[", 1)[0]
            inline_lex = [w.strip() for w in lex_part.split(",") if w.strip()]
        except Exception:
            inline_lex = []

        # Core text = everything before the blocks
        core = text
        if inline_ctx:
            core = core.rsplit("[context]\n", 1)[0]
        if inline_lex:
            core = core.rsplit("[lexicon]\n", 1)[0]
        core = core.strip()
        # --------- Extract URL seeds from context + lexicon (if present) ---------
        context_urls: List[str] = []
        if inline_ctx:
            ctx_slice = inline_ctx[:20000]   # sanity cap
            for m in self._URL_RE.finditer(ctx_slice):
                context_urls.append(m.group(0))

        lexicon_url_seeds: List[str] = []
        non_url_lex_terms: List[str] = []
        for term in inline_lex:
            t = term.strip()
            if not t:
                continue
            # If it looks like a URL, treat it as URL seed; otherwise as a keyword term
            if self._URL_RE.match(t):
                lexicon_url_seeds.append(t)
            else:
                non_url_lex_terms.append(t)
        query_raw = str(params.get("query", "") or str(payload or "")).strip()
        subpipeline = params.get("subpipeline", None)
        log: List[str] = []

        use_camoufox = bool(params.get("use_camoufox", False))
        camoufox_options = params.get("camoufox_options") or {}
        if not isinstance(camoufox_options, dict):
            camoufox_options = {}
        camoufox_options.update({"i_know_what_im_doing": True})
        # ---- DB control ----
        use_database = bool(params.get("use_database", False))
        db_path = params.get("db_path", "video_corpus.db")
        source = str(params.get("source", "search")).lower()
        engine = str(params.get("engine", "duckduckgo")).lower()

        searxng_url = str(
            params.get("searxng_url")
            or "http://127.0.0.1:8080"
        ).strip()
        if source == "database" and not use_database:
            use_database = True
            log.append("[VideoLinkTracker][db] source=database forces use_database=True.")

        if use_database:
            self._init_db_if_needed(db_path, log)

        # Config
        scan_limit = int(params.get("scan_limit", 3))
        max_pages_total = max(1, int(params.get("max_pages_total", 20)))
        timeout = float(params.get("timeout", 8.0))
        verify_links = bool(params.get("verify", False))

        use_js = bool(params.get("use_js", False))
        return_all_js_links = bool(params.get("return_all_js_links", False))
        max_links_per_page = int(params.get("max_links_per_page", 200))
        search_results_cap = int(params.get("search_results_cap", 256))
        search_page_limit = int(params.get("search_page_limit", 1))
        search_per_page = int(params.get("search_per_page", 50))

        use_network_sniff = bool(params.get("use_network_sniff", False))
        return_network_sniff_links = bool(params.get("return_network_sniff_links", False))

        # NEW: runtime sniffer toggles
        use_runtime_sniff = bool(params.get("use_runtime_sniff", False))
        return_runtime_sniff_hits = bool(params.get("return_runtime_sniff_hits", False))

        use_react_sniff = bool(params.get("use_react_sniff", False))
        return_react_sniff_hits = bool(params.get("return_react_sniff_hits", False))

        use_database_sniff = bool(params.get("use_database_sniff", False))
        return_database_sniff_hits = bool(
            params.get("return_database_sniff_hits", False)
        )

        use_interaction_sniff = bool(params.get("use_interaction_sniff", False))
        return_interaction_sniff_hits = bool(params.get("return_interaction_sniff_hits", False))

        min_term_overlap_raw = int(params.get("min_term_overlap", 1))
        min_term_overlap = max(1, min(min_term_overlap_raw, 12))

        site_require_raw = str(params.get("sites", "") or params.get("site_require", "")).split(",")
        required_sites = [s.strip().lower() for s in site_require_raw if s.strip()]
        global_mode = not required_sites
        if global_mode:
            required_sites = ["*"]

        max_depth = max(0, int(params.get("max_depth", 0)))
        child_page_limit = int(params.get("child_page_limit", 4))
        max_assets = int(params.get("max_assets", 100))
        ua = str(params.get("user_agent", "promptchat/VideoLinkTracker"))
        smart_sniff = bool(params.get("smart_sniff", False))

        output_cooldown_hours = int(params.get("output_cooldown_hours", 48))

        # DB seeding params
        db_seed_sources = str(params.get("db_seed_sources", "pages")).lower()
        db_seed_limit = int(params.get("db_seed_limit", 400))
        db_seed_max_age_days = int(params.get("db_seed_max_age_days", 14))
        db_include_synthetic_seeds = bool(params.get("db_include_synthetic_seeds", False))
        db_seed_per_domain_cap = int(params.get("db_seed_per_domain_cap", 8))

        db_expand_max_per_seed = int(params.get("db_expand_max_per_seed", 4))
        db_expand_ladder_depth = int(params.get("db_expand_ladder_depth", 2))
        db_domain_cap = int(params.get("db_domain_cap", 80))
        extract_urls_from_db_text = bool(params.get("extract_urls_from_db_text", True))
        db_allow_rescan = bool(params.get("db_allow_rescan", False))
        # HTTPSSubmanager tuning
        http_retries = int(params.get("http_retries", 2))
        http_max_conn = int(params.get("http_max_conn_per_host", 8))
        http_verify = bool(params.get("http_verify", True))
        http_ca_bundle = params.get("http_ca_bundle") or None


        # Download / caching
        download_assets = bool(params.get("download_assets", False))
        download_dir = str(params.get("download_dir", "video_cache"))
        max_download_bytes = int(params.get("max_download_bytes", 300 * 1024**2))
        skip_if_no_cl = bool(params.get("skip_if_no_content_length", True))

        # PW blocking params
        block_resources = bool(params.get("block_resources", False))
        blocked_resource_types = {
            t.strip().lower()
            for t in str(params.get("blocked_resource_types", "")).split(",")
            if t.strip()
        } or {"image", "stylesheet", "font"}

        block_domains = bool(params.get("block_domains", True))
        user_blocked_domains = {
            d.strip().lower()
            for d in str(params.get("blocked_domains", "")).split(",")
            if d.strip()
        }
        default_blocked_domains = {
            "google-analytics.com", "googletagmanager.com", "doubleclick.net",
            "facebook.com", "facebook.net", "twitter.com", "scorecardresearch.com",
            "quantserve.com", "hotjar.com", "segment.io", "mixpanel.com",
            "cloudflareinsights.com", "stats.g.doubleclick.net",
            "adservice.google.com", "ads.yahoo.com", "adsafeprotected.com",
        }
        blocked_domains: set[str] = set()
        if block_domains:
            blocked_domains = default_blocked_domains.union(user_blocked_domains)

        pw_launch_args = params.get("pw_launch_args") or []
        if isinstance(pw_launch_args, str):
            # allow comma-separated string
            pw_launch_args = [a.strip() for a in pw_launch_args.split(",") if a.strip()]
        if not isinstance(pw_launch_args, list):
            pw_launch_args = []

        pw_headless = bool(params.get("pw_headless", True))
        pw_channel = params.get("pw_channel", None)  # e.g. "chrome"
        pw_proxy = params.get("pw_proxy", None)  # e.g. {"server":"http://127.0.0.1:8080"}

        # Keywords
        keywords: List[str] = self._get_keywords_from_query(query_raw)
        if not keywords and query_raw:
            keywords = [query_raw.lower()]
        # Add non-URL lexicon terms as natural keyword seasoning
        for term in non_url_lex_terms:
            lt = term.lower()
            if lt and lt not in keywords:
                keywords.append(lt)

        # Subpipeline
        pipeline_result: Any = query_raw
        pipeline_queries: List[str] = []
        pipeline_urls: List[str] = []

        if subpipeline:
            subpipe_out: Any = self.run_sub_pipeline(
                initial_value=query_raw,
                pipeline_param_name="subpipeline",
                parent_params=params,
                collect=True,
            )
            if isinstance(subpipe_out, dict) and subpipe_out.get("__subpipeline__"):
                pipeline_result = subpipe_out.get("final")
                pipeline_queries = list(subpipe_out.get("queries") or [])
                pipeline_urls = list(subpipe_out.get("urls") or [])
            else:
                pipeline_result = subpipe_out

        # Naturally merge URL seeds from [context] and [lexicon] into pipeline URLs
        extra_seed_urls: List[str] = []
        if context_urls:
            extra_seed_urls.extend(context_urls)
        if lexicon_url_seeds:
            extra_seed_urls.extend(lexicon_url_seeds)

        if extra_seed_urls:
            if not pipeline_urls:
                pipeline_urls = []
            pipeline_urls.extend(extra_seed_urls)
        # =========================================================================
        # <--- NEW: Memory Sources Ingestion (SocketPipe Bridge)
        # =========================================================================
        memory_sources_raw = str(params.get("memory_sources", "")).strip()

        if memory_sources_raw:
            try:
                mem_data = Memory.load()
                # Split "socketpipe_links, socketpipe_domains" into keys
                keys_to_read = [k.strip() for k in memory_sources_raw.split(",") if k.strip()]

                for key in keys_to_read:
                    data = mem_data.get(key)
                    if not data:
                        continue

                    # Handle lists (standard SocketPipe output) or single items
                    items = data if isinstance(data, list) else [data]

                    for item in items:
                        candidate = None

                        # 1. Extract string from Dict or raw String
                        if isinstance(item, dict):
                            # Try standard SocketPipe keys
                            candidate = item.get("url") or item.get("domain") or item.get("text")
                        elif isinstance(item, (str, int, float)):
                            candidate = str(item)

                        if not candidate:
                            continue

                        cand_str = str(candidate).strip()
                        if not cand_str:
                            continue

                        # 2. CLASSIFY: URL vs Keyword

                        # A) It's definitely a URL (http/https)
                        if "://" in cand_str or cand_str.startswith(("http:", "https:")):
                            pipeline_urls.append(cand_str)

                        # B) It looks like a domain (has dot, no spaces) -> Treat as Seed URL
                        elif "." in cand_str and " " not in cand_str and not cand_str.startswith("."):
                            # Prepend protocol to make it actionable
                            pipeline_urls.append(f"https://{cand_str}")

                        # C) It's just text -> Treat as Lexicon Keyword
                        else:
                            # Adds to list used for relevancy scoring
                            non_url_lex_terms.append(cand_str)

            except Exception as e:
                # Log but don't crash
                msg = f"[LinkTracker] Error reading memory sources '{memory_sources_raw}': {e}"
                print(msg)
        # Triage initial URLs
        candidate_pages: List[str] = []
        direct_asset_urls: List[str] = []
        queries_to_run: List[str] = []
        skip_search_engine_for_payload = False
        seed_visual_sig = None

        def _allowed_by_required_sites_check(u: str) -> bool:
            return self._allowed_by_required_sites(u, required_sites, global_mode)

        def _augment_search_query(q: str, required_sites_for_search: List[str]) -> str:
            sq = q.strip()
            site_clauses = []
            if not global_mode:
                for raw in required_sites_for_search or []:
                    s = (raw or "").strip().lower()
                    if not s or s == "*":
                        continue
                    if "://" in s:
                        s = s.split("://", 1)[1]
                    s = s.split("/", 1)[0].lstrip(".")
                    if s:
                        site_clauses.append(f"site:{s}")

            if site_clauses:
                sites_expr = " OR ".join(site_clauses)
                sq = f"({sites_expr}) {sq}" if sq else f"({sites_expr})"

            q_lower = sq.lower()
            if not any(x in q_lower for x in ["video", "mp4", "m3u8"]):
                sq = f"{sq} (video OR mp4 OR m3u8 OR stream)".strip()
            return sq
        # ------------------ Reverse Image/Video Lookup Logic ------------------ #
        rev_input_url = str(params.get("reverse_image_url", None)).strip()
        ffmpeg_bin_path = str(params.get("ffmpeg_bin", "")).strip()

        # Auto-detect from payload if it looks like a media file OR a local path
        if not rev_input_url and isinstance(payload, str):
            pl_clean = payload.strip()
            # Check 1: Is it an existing local file?
            if os.path.isfile(pl_clean):
                rev_input_url = pl_clean
            # Check 2: Is it a URL with media extension?
            elif pl_clean.lower().startswith("http") and pl_clean.lower().endswith(
                    tuple(self.VIDEO_EXTENSIONS) + (".jpg", ".png", ".webp", ".jpeg")):
                rev_input_url = pl_clean

        if rev_input_url:
            search_seed_url = None
            is_video = False
            is_image = False
            img_bytes = None

            # 1. Determine if input is video (Local/URL extension)
            if rev_input_url.lower().startswith("http"):
                try:
                    async with submanagers.HTTPSSubmanager(timeout=5.0) as checker:
                        status, headers = await checker.head(rev_input_url)
                        ctype = (headers.get("Content-Type", "") or "").lower()

                        if any(x in ctype for x in self.VIDEO_CONTENT_PREFIXES) or "video" in ctype:
                            is_video = True
                        elif "image" in ctype:
                            is_image = True
                        elif "text/html" in ctype:
                            DEBUG_LOGGER.log_message(
                                f"[VideoLinkTracker] Input is a web page ({rev_input_url}). Skipping visual signature.")
                except Exception as e:
                    log.append(f"[VideoLinkTracker][Verify] HEAD check failed: {e}")
            else:
                # Local file logic
                if any(rev_input_url.lower().endswith(ext) for ext in self.VIDEO_EXTENSIONS):
                    is_video = True
                elif rev_input_url.lower().endswith((".jpg", ".png", ".webp", ".jpeg")):
                    is_image = True
            # 2. If it is an image:
            if is_image:
                DEBUG_LOGGER.log_message(f"[VideoLinkTracker] Input is image: {rev_input_url}")
                if rev_input_url.lower().startswith("http"):
                    async with submanagers.HTTPSSubmanager(timeout=timeout) as downloader:
                        img_bytes = await downloader.get_bytes(rev_input_url)
                    search_seed_url = rev_input_url
                else:
                    with open(rev_input_url, "rb") as f:
                        img_bytes = f.read()
                    search_seed_url = await self._upload_frame_to_host(img_bytes, log)

                if img_bytes:
                    seed_visual_sig = self._get_visual_signature(img_bytes)

            # 3. If it is a video (Local or URL):
            if is_video:
                DEBUG_LOGGER.log_message(f"[VideoLinkTracker] Input is video. Extracting frame from: {rev_input_url}")

                # FFmpeg handles local paths and URLs here
                frame_bytes = await self._extract_frame_from_video(rev_input_url, ffmpeg_bin_path, log)

                if frame_bytes:
                    seed_visual_sig = self._get_visual_signature(frame_bytes)
                    public_img = await self._upload_frame_to_host(frame_bytes, log)
                    if public_img:
                        DEBUG_LOGGER.log_message(f"[VideoLinkTracker] Generated search thumbnail: {public_img}")
                        search_seed_url = public_img
                    else:
                        DEBUG_LOGGER.log_message("[VideoLinkTracker] Failed to upload video frame.")
                else:
                    DEBUG_LOGGER.log_message("[VideoLinkTracker] Failed to extract video frame.")

            # 4. Perform Reverse Search
            if search_seed_url:
                DEBUG_LOGGER.log_message(f"[VideoLinkTracker] Triggering Visual Search for: {search_seed_url}")
                rev_seeds = await self._fetch_reverse_image_seeds(
                    search_seed_url,
                    timeout=timeout,
                    log=log,
                    max_results=max_pages_total
                )
                for url in rev_seeds:
                    if not (global_mode or _allowed_by_required_sites_check(url)):
                        continue

                    path = self._clean_path(url)
                    low = url.lower()

                    if self._is_probable_video_url(url, path, low):
                        direct_asset_urls.append(url)  # <-- critical
                    else:
                        candidate_pages.append(url)

        # ===================== source=database =====================
        if source == "database":
            if not self.store:
                DEBUG_LOGGER.log_message("[VideoLinkTracker][db] Store missing; cannot use database source.")
            else:
                DEBUG_LOGGER.log_message("[VideoLinkTracker] Running Advanced Database Intelligence...")

                seeds = self.store.load_database_seeds(
                    sources=db_seed_sources,
                    limit=db_seed_limit,
                    max_age_days=db_seed_max_age_days,
                    include_synthetic=db_include_synthetic_seeds,
                    per_domain_cap=db_seed_per_domain_cap,
                )
                DEBUG_LOGGER.log_message(
                    f"[VideoLinkTracker][db] Loaded {len(seeds)} seed URLs "
                    f"(sources={db_seed_sources}, max_age_days={db_seed_max_age_days}, include_synthetic={db_include_synthetic_seeds})."
                )

                known_asset_urls = [s['url'] for s in seeds if s.get('kind') == 'asset']
                known_asset_urls.extend(self.store.fetch_recent_good_asset_urls(limit=100))

                predicted_urls = self._predict_next_in_sequence(known_asset_urls)
                if predicted_urls:
                    DEBUG_LOGGER.log_message(f"[db] Generated {len(predicted_urls)} predictive sequence URLs (fuzzing).")
                    direct_asset_urls.extend(predicted_urls)

                proven_hubs = self.store.fetch_proven_hubs(required_sites, min_hits=1)
                if proven_hubs:
                    DEBUG_LOGGER.log_message(f"[db] Identified {len(proven_hubs)} high-yield hubs for re-crawling.")
                    candidate_pages.extend(proven_hubs)

                db_pages, db_assets = self.store.expand_db_seed_urls(
                    seeds,
                    max_per_seed=db_expand_max_per_seed,
                    ladder_depth=db_expand_ladder_depth,
                    per_domain_cap=db_domain_cap,
                    max_pages_out=250,
                    max_assets_out=300,
                    known_url_fn=lambda u: self.store.asset_exists_by_canon_or_cid(
                        self._canonicalize_url(u), self._get_content_id(u)
                    ),
                    clean_domain_fn=self._clean_domain,
                    clean_path_fn=self._clean_path,
                    is_probable_video_url_fn=self._is_probable_video_url,
                    archive_ident_to_downloads_fn=self._archive_ident_to_downloads,
                )
                DEBUG_LOGGER.log_message(f"[VideoLinkTracker][db] Expanded seeds -> {len(db_pages)} pages, {len(db_assets)} direct assets.")

                if extract_urls_from_db_text:
                    hidden_from_text = self.store.extract_urls_from_db_text(
                        limit_rows=db_seed_limit,
                        max_urls=600,
                        include_synthetic=db_include_synthetic_seeds,
                        url_regex=self._URL_RE,
                    )
                    if hidden_from_text:
                        DEBUG_LOGGER.log_message(f"[VideoLinkTracker][db] Extracted {len(hidden_from_text)} hidden URLs from prior manifest/JSON text.")
                    for hu in hidden_from_text:
                        hp = self._clean_path(hu)
                        if self._is_probable_video_url(hu, hp, hu.lower()):
                            direct_asset_urls.append(hu)
                        else:
                            candidate_pages.append(hu)

                candidate_pages.extend(db_pages)
                direct_asset_urls.extend(db_assets)

                skip_search_engine_for_payload = False
                queries_to_run = ["<database seeds + prediction + hubs>"]

                candidate_pages = list(dict.fromkeys(candidate_pages))
                direct_asset_urls = list(dict.fromkeys(direct_asset_urls))

        # ------------------ pipeline urls / queries ------------------
        if pipeline_urls:
            skip_search_engine_for_payload = False

            # Deduplicate inputs
            unique_urls = list(dict.fromkeys([str(u).strip() for u in pipeline_urls if str(u).strip()]))

            DEBUG_LOGGER.log_message(f"[VideoLinkTracker] Processing {len(unique_urls)} direct URLs from memory/pipeline.")

            for u in unique_urls:
                if global_mode or _allowed_by_required_sites_check(u):
                    path = self._clean_path(u)
                    url_lower = u.lower()

                    if self._is_probable_video_url(u, path, url_lower):
                        direct_asset_urls.append(u)
                        continue

                    if any(path.endswith(ext) for ext in self.IGNORED_EXTENSIONS):
                        continue

                    candidate_pages.append(u)

            candidate_pages = candidate_pages[:max_pages_total]

        if (not skip_search_engine_for_payload) and pipeline_queries:
            for qv in pipeline_queries:
                qv_s = str(qv).strip()
                if qv_s:
                    queries_to_run.append(qv_s)

        if not pipeline_urls and not pipeline_queries and source != "database":
            if isinstance(pipeline_result, list) and pipeline_result:
                for qv in pipeline_result:
                    qv_s = str(qv).strip()
                    if qv_s:
                        queries_to_run.append(qv_s)
            else:
                base_q: Optional[str] = None
                if isinstance(pipeline_result, str) and pipeline_result.strip():
                    base_q = pipeline_result.strip()
                elif query_raw:
                    base_q = query_raw
                if base_q:
                    queries_to_run.append(base_q)

        if not queries_to_run and query_raw and not skip_search_engine_for_payload:
            queries_to_run = [query_raw]

        queries_to_run = list(dict.fromkeys(queries_to_run))
        current_display_query = queries_to_run[0] if queries_to_run else query_raw

        # Search discovery
        explicit_site_seeds: set[str] = set()
        synthetic_search_seeds: set[str] = set()
        sites_seed_pages: List[str] = []
        use_sites_engine = False

        if not skip_search_engine_for_payload and queries_to_run and source != "database":
            ua_search = ua
            seen_search_urls: set[str] = set()

            if source == "payload":
                log.append("Reading hub pages from payload...")
                payload_str = str(payload)
                urls_from_payload = re.findall(r"#.*?(https?://[^\s<\]]+)", payload_str)
                urls_from_payload.extend(re.findall(r"\[.*?\]\((https?://[^\s)]+)\)", payload_str))
                if not urls_from_payload:
                    urls_from_payload.extend(re.findall(r"\b(https?://[^\s<\]]+)\b", payload_str))

                seen_payload_urls = set()
                for u in urls_from_payload:
                    u = u.strip().rstrip(")")
                    if u not in seen_payload_urls:
                        if global_mode or _allowed_by_required_sites_check(u):
                            candidate_pages.append(u)
                            seen_payload_urls.add(u)

                log.append(f"Found {len(candidate_pages)} unique URLs in payload.")
                if scan_limit > 0:
                    candidate_pages = candidate_pages[:scan_limit]

            elif engine == "sites" and required_sites and not global_mode:
                log.append(f"Preparing site-specific crawl seeds for: {', '.join(required_sites)}")
                seed_pages, syn_seeds, exp_seeds = self._seed_pages_from_required_sites(
                    required_sites=required_sites,
                    queries=queries_to_run,
                    probe_cap_per_site=max(8, len(queries_to_run) * 3),
                    sitemap_cap_per_site=12,
                    hub_cap_per_site=10,
                )
                synthetic_search_seeds = syn_seeds
                explicit_site_seeds = exp_seeds
                sites_seed_pages = seed_pages
                use_sites_engine = True

            elif engine == "duckduckgo":
                for qv in queries_to_run:
                    sq = _augment_search_query(qv, required_sites)
                    DEBUG_LOGGER.log_message(f"Searching DuckDuckGo for: {sq}")
                    urls = await self._search_duckduckgo(
                        sq,
                        max_results=search_results_cap,
                        ua=ua_search,
                        timeout=timeout,
                        log=log,
                        page_limit=search_page_limit,
                        per_page=search_per_page,
                    )
                    for u in urls:
                        if len(candidate_pages) >= max_pages_total:
                            break
                        if not u or u in seen_search_urls:
                            continue
                        if _allowed_by_required_sites_check(u):
                            candidate_pages.append(u)
                            seen_search_urls.add(u)

            elif engine == "google_cse":
                for qv in queries_to_run:
                    sq = _augment_search_query(qv, required_sites)
                    DEBUG_LOGGER.log_message(f"Searching Google CSE for: {sq}")
                    urls = await self._search_google_cse(
                        sq,
                        n=search_results_cap,
                        timeout=timeout,
                        log=log,
                        page_limit=search_page_limit,
                    )
                    for u in urls:
                        if len(candidate_pages) >= max_pages_total:
                            break
                        if not u or u in seen_search_urls:
                            continue
                        if _allowed_by_required_sites_check(u):
                            candidate_pages.append(u)
                            seen_search_urls.add(u)
            elif engine == "searxng":
                if not searxng_url:
                    log.append(
                        "[VideoLinkTracker][SearXNG] engine='searxng' but no searxng_url or SEARXNG_URL configured."
                    )
                else:
                    for qv in queries_to_run:
                        sq = _augment_search_query(qv, required_sites)
                        DEBUG_LOGGER.log_message(f"Searching SearXNG at {searxng_url} for: {sq}")
                        urls = await self._search_searxng(
                            sq,
                            max_results=search_results_cap,
                            timeout=timeout,
                            log=log,
                            base_url=searxng_url,
                            page_limit=search_page_limit,
                        )
                        for u in urls:
                            if len(candidate_pages) >= max_pages_total:
                                break
                            if not u:
                                continue
                            if _allowed_by_required_sites_check(u):
                                if u not in seen_search_urls:
                                    candidate_pages.append(u)
                                    seen_search_urls.add(u)
            else:
                if engine not in ("sites",):
                    log.append(f"[search] Unknown engine={engine!r}; no search performed.")

        # ---- Crawl state & HTTPSSubmanager ----
        final_found_assets_by_content_id: Dict[str, Dict[str, Any]] = {}
        seen_asset_urls: set[str] = set()
        visited_pages: set[str] = set()
        all_js_links: List[Dict[str, str]] = []
        all_network_links: List[Dict[str, str]] = []
        all_runtime_hits: List[Dict[str, Any]] = []
        all_react_hits: List[Dict[str, Any]] = []  # [PATCH] Initialize accumulator
        all_database_hits: List[Dict[str, Any]] = []
        all_interaction_hits: List[Dict[str, Any]] = []
        recently_returned_identifiers = set()
        if source == "database" and use_database and output_cooldown_hours > 0 and self.store:
            recently_returned_identifiers = self.store.get_recently_returned(output_cooldown_hours)

        def _should_persist_page(u: str) -> bool:
            if engine == "sites":
                if u in explicit_site_seeds or u in synthetic_search_seeds:
                    return False
                if self._is_search_url(u):
                    return False
            return True

        pw_needed = (
                use_js or
                use_network_sniff or
                use_runtime_sniff or
                use_react_sniff or
                use_database_sniff or
                use_interaction_sniff
        )
        pw_p = pw_browser = pw_context = None

        ua_http = ua if ua else "promptchat/VideoLinkTracker"

        # Shared HTTPS engine for this run
        async with submanagers.HTTPSSubmanager(
            user_agent=ua_http,
            timeout=timeout,
            retries=http_retries,
            max_conn_per_host=http_max_conn,
            verify=http_verify,
            ca_bundle=http_ca_bundle,
        ) as http:

            # If engine="sites", site-specific robots/sitemap/hub crawl
            if use_sites_engine and sites_seed_pages:
                log.append(f"Finding hub pages via site-specific crawling for: {', '.join(required_sites)}")
                per_site_cap = max(5, max_pages_total // max(1, len(required_sites)))
                global_seen_for_sitemaps = set()

                for site_domain in required_sites:
                    if site_domain == "*":
                        continue
                    root = f"https://{site_domain.strip().lstrip('.')}".rstrip("/") + "/"
                    host = urlparse(root).netloc.lower()

                    robots_url = root + "robots.txt"
                    try:
                        robots_txt = await http.get_text(robots_url)
                    except Exception as e:
                        robots_txt = ""
                        log.append(f"[VideoLinkTracker][sites] Error fetching robots.txt {robots_url}: {e}")

                    sm_urls = self._extract_sitemap_urls_from_robots(robots_txt)
                    if not sm_urls:
                        sm_urls = [u for u in sites_seed_pages if "sitemap" in u and site_domain in u][:8]

                    best_from_sitemaps = await self._crawl_sitemaps_for_site(
                        http=http,
                        root=root,
                        sm_urls=sm_urls,
                        timeout=timeout,
                        keywords=keywords,
                        per_site_cap=per_site_cap,
                        global_seen=global_seen_for_sitemaps,
                        log=log,
                    )

                    hub_like = [u for u in sites_seed_pages if site_domain in u and self._is_search_url(u)]
                    expanded_from_hubs: List[str] = []

                    for hub in hub_like[:3]:
                        try:
                            html_hub = await http.get_text(hub)
                            soup = BeautifulSoup(html_hub or "", "html.parser") if BeautifulSoup else None
                            if not soup:
                                continue

                            expanded_from_hubs.extend(self._extract_internal_result_links(soup, hub, host))

                            for nxt in self._extract_next_page_links(soup, hub):
                                html_nxt = await http.get_text(nxt)
                                soup_nxt = BeautifulSoup(html_nxt or "", "html.parser") if BeautifulSoup else None
                                if not soup_nxt:
                                    continue
                                expanded_from_hubs.extend(self._extract_internal_result_links(soup_nxt, nxt, host))
                        except Exception as e:
                            log.append(f"[VideoLinkTracker][sites] Error expanding hub {hub}: {e}")

                    expanded_from_hubs = list(dict.fromkeys(expanded_from_hubs))
                    expanded_from_hubs.sort(key=lambda u: self._score_site_url(u, keywords), reverse=True)
                    expanded_from_hubs = expanded_from_hubs[:per_site_cap]

                    merged = list(dict.fromkeys(
                        [root] + best_from_sitemaps + expanded_from_hubs +
                        [u for u in sites_seed_pages if site_domain in u]
                    ))
                    merged.sort(key=lambda u: self._score_site_url(u, keywords), reverse=True)

                    for u in merged:
                        if len(candidate_pages) >= max_pages_total:
                            break
                        if _allowed_by_required_sites_check(u):
                            candidate_pages.append(u)

                candidate_pages = list(dict.fromkeys(candidate_pages))[:max_pages_total]

            # Direct assets via HEAD
            if direct_asset_urls:
                for u in direct_asset_urls:
                    canon = self._canonicalize_url(u)
                    cid = self._get_content_id(u)
                    # ... all your existing dedupe + DB cooldown checks ...

                    status = "unverified"
                    size = "?"
                    content_type = ""

                    if verify_links:
                        try:
                            h_status, headers = await http.head(canon)
                            content_type = (headers.get("content-type") or "").lower()
                            if h_status == 200:
                                status = "200 OK"
                                cl = headers.get("content-length")
                                if cl:
                                    size = f"{int(cl) // 1024} KB"
                            else:
                                status = f"Dead ({h_status})"
                        except Exception:
                            status = "Timeout/Error"

                    if not verify_links or "OK" in status:
                        filename = self._clean_path(canon).rsplit("/", 1)[-1] or "[asset]"
                        asset = {
                            "text": filename[:100],
                            "url": canon,
                            "source_page": "<urls>",
                            "size": size,
                            "status": status,
                            "tag": "direct_asset",
                        }

                        is_hls_manifest = canon.lower().endswith(".m3u8") or (
                                content_type in self.HLS_CONTENT_TYPES
                        )

                        # HLS capture (you already had this)
                        if is_hls_manifest and self.hls_manager:
                            try:
                                hls_res = await self.hls_manager.capture_hls_stream(
                                    http, canon, timeout=timeout, log=log
                                )
                                if hls_res:
                                    asset["hls_stream_id"] = hls_res.stream_id
                                    asset["hls_manifest_path"] = hls_res.manifest_path
                                    if hls_res.variant_manifest_path:
                                        asset["hls_variant_manifest_path"] = hls_res.variant_manifest_path
                                    if hls_res.segment_paths:
                                        asset["hls_segment_paths"] = hls_res.segment_paths[:10]

                                        # OPTIONAL: local root dir for all segments
                                        try:
                                            import os as _os
                                            asset["local_hls_root"] = _os.path.dirname(
                                                hls_res.segment_paths[0]
                                            )
                                        except Exception:
                                            pass
                            except Exception as e:
                                log.append(f"[VideoLinkTracker][HLS] Error capturing direct asset {canon}: {e}")

                        # NEW: download non-HLS direct files
                        if download_assets and not is_hls_manifest:
                            local_path = await self._download_asset_to_cache(
                                http,
                                canon,
                                cid,
                                log,
                                download_dir=download_dir,
                                max_bytes=max_download_bytes,
                                skip_if_no_cl=skip_if_no_cl,
                            )
                            if local_path:
                                asset["local_path"] = local_path

                        new_b = self._parse_size_to_bytes(size)
                        old = final_found_assets_by_content_id.get(cid)
                        if not old or new_b > self._parse_size_to_bytes(old.get("size", "")):
                            asset["content_id"] = cid
                            final_found_assets_by_content_id[cid] = asset

                        if use_database and self.store:
                            self.store.upsert_asset(
                                asset,
                                canonical_url=canon,
                                content_id=cid,
                                synthetic_tags={
                                    "direct_asset",
                                    "db_seed",
                                    "db_expand",
                                    "db_manifest",
                                    "synthetic",
                                },
                            )

            pw_p = pw_browser = pw_context = None
            try:
                if pw_needed:
                    ua_pw = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/VideoTracker"
                    pw_p, pw_browser, pw_context = await self._open_playwright_context(
                        ua=ua_pw,
                        block_resources=block_resources,
                        blocked_resource_types=blocked_resource_types,
                        block_domains=block_domains,
                        blocked_domains=blocked_domains,
                        log=log,
                        use_camoufox=use_camoufox,
                        camoufox_options=camoufox_options,
                        pw_launch_args=pw_launch_args,  # NEW
                        pw_headless=pw_headless,  # NEW
                        pw_channel=pw_channel,  # NEW
                        pw_proxy=pw_proxy,  # NEW
                    )
            except:
                # ALWAYS close Camoufox/Playwright if we opened it
                if pw_needed and (pw_p or pw_browser or pw_context):
                    await self._close_playwright_context(pw_p, pw_browser, pw_context, log)
                pw_p = pw_browser = pw_context = None
            async def _process_page(page_url: str, depth: int, smart_sniff_param: bool) -> Dict[str, Any]:
                local_log: List[str] = []
                local_js_links: List[Dict[str, str]] = []
                local_network_links: List[Dict[str, str]] = []
                local_runtime_hits: List[Dict[str, Any]] = []
                local_assets: List[Dict[str, Any]] = []
                local_react_hits: List[Dict[str,Any]] = []
                local_database_hits: List[Dict[str, Any]] = []
                local_interaction_hits: List[Dict[str, Any]] = []
                next_pages: List[str] = []
                self.network_sniffer.http = http
                DEBUG_LOGGER.log_message(f"[BFS] processing page: {page_url} (depth={depth})")
                try:
                    links_on_page: List[Dict[str, str]] = []
                    html = ""

                    sniff_items: List[Dict[str, str]] = []
                    sniff_json_hits: List[Dict[str, Any]] = []
                    sniff_parent_pages: List[str] = []

                    # ======================= SEQUENTIAL SNIFFER EXECUTION =======================
                    # We run sniffers one by one to avoid 100% CPU/Network usage (DDoS self-inflicted).

                    # 1. NETWORK SNIFFER (Priority #1)
                    # This is the heaviest sniffer. We give it the full timeout and run it first.
                    if use_network_sniff and pw_context:
                        try:
                            # Run alone to prevent resource contention
                            res_net = await self._pw_fetch_with_sniff(pw_context, page_url, timeout, local_log)

                            if isinstance(res_net, tuple) or isinstance(res_net, str):
                                s_html = res_net[0] if isinstance(res_net, tuple) else res_net
                                s_items = res_net[1] if isinstance(res_net, tuple) and len(res_net) > 1 else []
                                s_json = res_net[2] if isinstance(res_net, tuple) and len(
                                    res_net) > 2 else []  # Catch JSON hits if any

                                # Capture HTML if we don't have it yet
                                if s_html and len(s_html) > 100:
                                    html = s_html

                                for si in s_items:
                                    u = si.get("url", "")
                                    if u:
                                        # Add to local debug lists
                                        local_network_links.append({
                                            "page": page_url, "url": u, "text": si.get("text", ""),
                                            "tag": si.get("tag", "network_sniff"),
                                            "content_type": si.get("content_type", "?")
                                        })
                                        # Add to processing queue for asset evaluation
                                        links_on_page.append({"url": u, "text": si.get("text"), "tag": "network_sniff"})

                                        # Heuristic: Check for parent paths for crawling
                                        try:
                                            parsed = urlparse(u)
                                            if "/" in parsed.path:
                                                parent = f"{parsed.scheme}://{parsed.netloc}{parsed.path.rsplit('/', 1)[0]}/"
                                                if _allowed_by_required_sites_check(parent):
                                                    next_pages.append(parent)
                                        except:
                                            pass
                        except Exception as e:
                            local_log.append(f"Network sniffer failed: {e}")

                    # 2. RUNTIME SNIFFER (Priority #2)
                    # Good for capturing DOM state if Network failed, or getting console logs.
                    if use_runtime_sniff and pw_context:
                        try:
                            res_runtime = await self._pw_fetch_runtime_hits(pw_context, page_url, timeout / 2,
                                                                            local_log)
                            if isinstance(res_runtime, tuple):
                                rt_html, rt_hits = res_runtime
                                if rt_html and not html:
                                    html = rt_html

                                if rt_hits:
                                    local_runtime_hits.extend(rt_hits)

                                    # ✅ Promote runtime URLs into link processing
                                    for hit in rt_hits:
                                        u = (hit.get("url") or "").strip()
                                        if not u:
                                            continue
                                        if not _allowed_by_required_sites_check(u):
                                            continue

                                        # Treat runtime URLs as candidates for asset evaluation
                                        links_on_page.append({"url": u, "text": "[Runtime]", "tag": "runtime_sniff"})

                                        # Optional: add parent pages for BFS exploration
                                        try:
                                            parsed = urlparse(u)
                                            if parsed.scheme and parsed.netloc and "/" in parsed.path:
                                                parent = f"{parsed.scheme}://{parsed.netloc}{parsed.path.rsplit('/', 1)[0]}/"
                                                if _allowed_by_required_sites_check(parent):
                                                    next_pages.append(parent)
                                        except Exception:
                                            pass

                        except Exception as e:
                            local_log.append(f"Runtime sniffer failed: {e}")
                    # 3. SPECIALIZED SNIFFERS (Sequential Fallbacks)
                    # Run these only if enabled. They reuse the context but won't fight for bandwidth.

                    if use_react_sniff and pw_context:
                        try:
                            res_react = await self._pw_fetch_react_hits(pw_context, page_url, timeout / 2, local_log)
                            if isinstance(res_react, tuple):
                                r_html, r_hits = res_react
                                if r_html and not html: html = r_html
                                if r_hits:
                                    local_react_hits.extend(r_hits)
                                    for rh in r_hits:
                                        if rh.get("url") and _allowed_by_required_sites_check(rh.get("url")):
                                            next_pages.append(rh.get("url"))
                        except:
                            pass

                    if use_database_sniff and pw_context:
                        try:
                            res_db = await self._pw_fetch_database_hits(pw_context, page_url, timeout / 2, local_log)
                            if isinstance(res_db, tuple):
                                d_html, d_hits = res_db
                                if d_html and not html: html = d_html
                                if d_hits:
                                    local_database_hits.extend(d_hits)
                                    for hit in d_hits:
                                        if hit.get("kind") == "content_link" and hit.get("url"):
                                            links_on_page.append(
                                                {"url": hit.get("url"), "text": "[DB Content]", "tag": "db_link"})
                        except:
                            pass

                    if use_interaction_sniff and pw_context:
                        try:
                            res_interaction = await self._pw_fetch_interaction_hits(pw_context, page_url, timeout / 2,
                                                                                    local_log)
                            if isinstance(res_interaction, tuple):
                                i_html, i_hits = res_interaction
                                if i_html and not html: html = i_html
                                if i_hits: local_interaction_hits.extend(i_hits)
                        except:
                            pass

                    if use_js and pw_context:
                        try:
                            res_js = await self._pw_fetch_js_links(pw_context, page_url, timeout / 2, local_log)
                            if isinstance(res_js, tuple):
                                j_html, j_links = res_js
                                if j_html and not html: html = j_html
                                if j_links:
                                    links_on_page.extend(j_links)
                                    for jl in j_links:
                                        local_js_links.append(
                                            {"page": page_url, "url": jl.get("url"), "text": jl.get("text"),
                                             "tag": "js_link"})
                        except:
                            pass
                    # 3) Plain HTML via HTTPSSubmanager
                    if not html:
                        try:
                            html = await http.get_text(page_url)
                        except Exception as e:
                            local_log.append(f"Error fetching {page_url} (plain HTML): {e}")
                            if use_database and self.store and _should_persist_page(page_url):
                                self.store.mark_page_scanned(page_url)
                            return {
                                "page": page_url,
                                "assets": local_assets,
                                "next_pages": next_pages,
                                "js_links": local_js_links,
                                "network_links": local_network_links,
                                "runtime_hits": local_runtime_hits,
                                "react_hits": local_react_hits,  # [PATCH] Return hits
                                "database_hits": local_database_hits,
                                "interaction_hits": local_interaction_hits,
                                "log": local_log,
                            }

                    soup = BeautifulSoup(html or "", "html.parser") if BeautifulSoup else None
                    if not soup:
                        return {
                            "page": page_url,
                            "assets": local_assets,
                            "next_pages": next_pages,
                            "js_links": local_js_links,
                            "network_links": local_network_links,
                            "runtime_hits": local_runtime_hits,
                            "react_hits": local_react_hits,  # [PATCH] Return hits
                            "database_hits": local_database_hits,
                            "interaction_hits": local_interaction_hits,
                            "log": local_log + ["BeautifulSoup missing - cannot parse HTML."],
                        }

                    page_title = ""
                    try:
                        if soup.title and soup.title.string:
                            page_title = soup.title.string
                    except Exception:
                        page_title = ""

                    page_haystack = (page_title or "") + " " + page_url
                    page_has_keywords = self._term_overlap_ok_check(page_haystack, keywords, min_term_overlap)

                    # Gather links
                    link_count = 0
                    for tag_name in ["a", "video", "source", "iframe", "embed"]:
                        for el in soup.find_all(tag_name):
                            url = None
                            text = ""
                            if tag_name == "a" and el.get("href"):
                                url = el["href"]
                                text = el.get_text(strip=True)
                            elif tag_name in ["video", "iframe", "embed"] and el.get("src"):
                                url = el["src"]
                                text = el.get("title", "") or el.get("alt", "")
                            elif tag_name == "source" and el.get("src"):
                                url = el["src"]
                                text = el.get("title", "") or el.get("alt", "")

                            if url:
                                links_on_page.append({"url": url, "text": text, "tag": tag_name})
                                link_count += 1
                                if link_count >= max_links_per_page:
                                    break
                        if link_count >= max_links_per_page:
                            break

                    # Scan links for video assets
                    for link in links_on_page:
                        raw_link = link["url"]
                        full_url = urljoin(page_url, raw_link)
                        raw = full_url
                        canon = self._canonicalize_url(raw)
                        cid = self._get_content_id(raw)

                        parsed_asset_url = urlparse(canon)
                        asset_netloc = parsed_asset_url.netloc
                        asset_path = parsed_asset_url.path.lower()
                        asset_url_lower = canon.lower()
                        tag_type = link.get("tag", "")

                        # Rule 1: If it's a <video> or <source> tag, TRUST IT.
                        # Don't require it to look like .mp4
                        if tag_type in ["video", "source"]:
                            is_video = True

                        # Rule 2: If it's a Network Sniff hit, TRUST IT.
                        # The sniffer already validated it was media traffic.
                        elif tag_type in ("network_sniff", "db_link", "runtime_sniff"):
                            is_video = True

                        # Rule 3: Otherwise, run the standard heuristics (for <a> tags)
                        else:
                            is_video = self._is_probable_video_url(canon, asset_path, asset_url_lower)
                        if self._looks_like_ad(asset_netloc, asset_path):
                            continue

                        tag = link.get("tag") or ""
                        is_sniff_or_db = (
                                tag == "network_sniff"
                                or tag == "runtime_sniff"
                                or tag == "db_link"
                                or tag in ("direct_asset", "db_seed", "db_expand", "db_manifest", "synthetic")
                        )
                        if not is_sniff_or_db:
                            if not self._allowed_by_required_sites(canon, required_sites, global_mode):
                                continue

                        if source == "database" and (
                            canon in recently_returned_identifiers or cid in recently_returned_identifiers
                        ):
                            continue

                        if use_database and self.store:
                            if self.store.asset_exists_by_canon_or_cid(canon, cid):
                                continue

                        if canon in seen_asset_urls:
                            continue
                        seen_asset_urls.add(canon)
                        if not is_video:
                            is_video = self._is_probable_video_url(canon, asset_path, asset_url_lower)

                        if (not is_video) and smart_sniff_param:
                            try:
                                h_status, headers = await http.head(canon)
                                content_type = (headers.get("content-type") or "").lower()

                                if h_status == 200:
                                    if (
                                            any(content_type.startswith(pfx) for pfx in self.VIDEO_CONTENT_PREFIXES)
                                            or content_type in self.HLS_CONTENT_TYPES
                                            or content_type in self.DASH_CONTENT_TYPES
                                    ):
                                        is_video = True

                                    # Runtime links are often opaque; allow some “known good” hints too
                                    if ("m3u8" in canon.lower()) or ("mpd" in canon.lower()):
                                        is_video = True
                            except Exception:
                                pass


                        is_visual_match = False
                        similarity = None

                        if seed_visual_sig is not None:
                            # only attempt frame extraction if URL looks plausibly video-ish
                            looks_videoish = (
                                    any(asset_path.endswith(ext) for ext in self.VIDEO_EXTENSIONS)
                                    or "m3u8" in asset_url_lower
                                    or "mpd" in asset_url_lower
                                    or any(k in asset_url_lower for k in self.STREAM_HINT_KEYWORDS)
                                    or tag_type in ("network_sniff", "runtime_sniff", "db_link", "video", "source")
                            )
                            if looks_videoish:
                                discovery_frame = await self._extract_frame_from_video(
                                    canon,
                                    ffmpeg_bin_path,
                                    local_log
                                )

                                if discovery_frame:
                                    discovery_sig = self._get_visual_signature(discovery_frame)
                                    similarity = self._compare_visual_signatures(seed_visual_sig, discovery_sig)

                                    if similarity > 0.75:
                                        is_visual_match = True
                                        DEBUG_LOGGER.log_message(
                                            f"[VideoLinkTracker][Image] Visual match! score={similarity:.2f} url={canon}"
                                        )
                                else:
                                    local_log.append(f"[VideoLinkTracker][Image] Could not extract frame for: {canon}")

                        asset_text = link.get("text", "")
                        asset_score = self._score_video_asset(canon, asset_text, keywords)
                        trusted_hit = tag_type in ("network_sniff", "runtime_sniff", "db_link")
                        if is_visual_match:
                            asset_score += 100

                        if trusted_hit:
                            asset_score = max(asset_score, 0)  # don't allow trusted hits to go negative
                            asset_score += 25  # optional: push them above borderline noise

                        if asset_score < 0:
                            local_log.append(f"Skipped low-score asset ({asset_score}): {canon}")
                            continue

                        if not (source == "database" and is_sniff_or_db):
                            if keywords and not page_has_keywords and link.get("tag") != "network_sniff":
                                haystack = (link.get("text", "") or "").lower() + " " + asset_url_lower.replace("%20", " ")
                                if not self._term_overlap_ok_check(haystack, keywords, min_term_overlap):
                                    if seed_visual_sig is not None:
                                        if similarity is not None and not is_visual_match:
                                            continue
                                    else:
                                        continue
                        else:
                            if seed_visual_sig is not None:
                                if similarity is not None and not is_visual_match:
                                    continue

                        status = "unverified"
                        size = "?"
                        content_type = ""
                        do_head = verify_links or smart_sniff_param
                        trusted_hit = tag_type in ("network_sniff", "runtime_sniff", "db_link")
                        # --- REFINED VERIFICATION GATE ---
                        if do_head:
                            try:
                                h_status, headers = await http.head(canon)
                                content_type = (headers.get("content-type") or "").lower()

                                # 1. Hard Filter: Is it obviously NOT a video? (Junk extensions)
                                path_low = canon.lower().split('?')[0]
                                is_junk = any(path_low.endswith(ext) for ext in self.IGNORED_EXTENSIONS)

                                if h_status == 200 and not is_junk:
                                    if cl := headers.get("content-length"):
                                        size = f"{int(cl) // 1024} KB"

                                    # Check if MIME type or Extension matches video patterns
                                    is_video_mime = any(
                                        content_type.startswith(pfx) for pfx in self.VIDEO_CONTENT_PREFIXES)
                                    is_video_ext = any(path_low.endswith(ext) for ext in self.VIDEO_EXTENSIONS)

                                    # 2. Strict Sniffing: If smart_sniff is ON, we only accept video signals
                                    if smart_sniff_param:
                                        if is_video_mime or is_video_ext:
                                            status = "200 OK"
                                        else:
                                            status = f"Filtered (Type: {content_type})"
                                    else:
                                        # If smart_sniff is OFF, we rely on the sniffer's judgment but still block junk
                                        status = "200 OK"
                                else:
                                    status = f"Dead/Junk ({h_status})"

                            except Exception:
                                # If HEAD fails, only trust it if it looks like a video URL
                                if trusted_hit and any(canon.lower().endswith(ext) for ext in self.VIDEO_EXTENSIONS):
                                    status = "200 OK (Sniffed)"
                                else:
                                    status = "Timeout/Error"

                        if not verify_links or "OK" in status:
                            display_text = (link.get("text", "") or asset_path.rsplit("/", 1)[-1] or "[video asset]")[:100]
                            asset = {
                                "text": display_text,
                                "url": canon,
                                "source_page": page_url,
                                "size": size,
                                "status": status,
                                "tag": link["tag"],
                                "content_id": cid,
                            }
                            asset["score"] = str(asset_score)
                            DEBUG_LOGGER.log_message(
                                f"[BFS] FOUND ASSET on {page_url}: Score: {asset['score']} Text: {asset['text']} URL: ({asset['url']})")

                            is_hls_manifest = canon.lower().endswith(".m3u8") or (
                                    content_type in self.HLS_CONTENT_TYPES
                            )
                            if is_hls_manifest and self.hls_manager:
                                try:
                                    hls_res = await self.hls_manager.capture_hls_stream(
                                        http, canon, timeout=timeout, log=local_log
                                    )
                                    if hls_res:
                                        asset["hls_stream_id"] = hls_res.stream_id
                                        asset["hls_manifest_path"] = hls_res.manifest_path
                                        if hls_res.variant_manifest_path:
                                            asset["hls_variant_manifest_path"] = hls_res.variant_manifest_path
                                        if hls_res.segment_paths:
                                            asset["hls_segment_paths"] = hls_res.segment_paths[:10]
                                            try:
                                                import os as _os
                                                asset["local_hls_root"] = _os.path.dirname(
                                                    hls_res.segment_paths[0]
                                                )
                                            except Exception:
                                                pass
                                except Exception as e:
                                    local_log.append(
                                        f"[VideoLinkTracker][HLS] Error capturing HLS for {canon}: {e}"
                                    )

                            # NEW: download normal file-like assets
                            if download_assets and not is_hls_manifest:
                                local_path = await self._download_asset_to_cache(
                                    http,
                                    canon,
                                    cid,
                                    local_log,
                                    download_dir=download_dir,
                                    max_bytes=max_download_bytes,
                                    skip_if_no_cl=skip_if_no_cl,
                                )
                                if local_path:
                                    asset["local_path"] = local_path

                            local_assets.append(asset)

                            if use_database and self.store:
                                self.store.upsert_asset(
                                    asset,
                                    canonical_url=canon,
                                    content_id=cid,
                                    synthetic_tags={
                                        "direct_asset",
                                        "db_seed",
                                        "db_expand",
                                        "db_manifest",
                                        "synthetic",
                                    },
                                )

                    # Next-level pages
                    if depth < max_depth:
                        for link in links_on_page:
                            raw_link = link.get("url") or ""
                            if not raw_link:
                                continue
                            full_url = urljoin(page_url, raw_link)
                            if not _allowed_by_required_sites_check(full_url):
                                continue
                            if link.get("tag") in ["iframe", "embed"]:
                                # Always queue iframes for the next depth,
                                # regardless of keywords or extensions.
                                # This allows the crawler to "step inside" the player.
                                if _allowed_by_required_sites_check(full_url):
                                    next_pages.append(full_url)
                                continue
                            lpath = urlparse(full_url).path.lower()
                            if any(lpath.endswith(ext) for ext in self.IGNORED_EXTENSIONS):
                                continue
                            if self._is_probable_video_url(full_url, lpath, full_url.lower()):
                                continue
                            clean_url_for_matching = unquote(full_url).lower()
                            if keywords and not page_has_keywords:
                                haystack = f"{page_title} {link.get('text', '')} {clean_url_for_matching}".lower()
                                if not self._term_overlap_ok_check(haystack, keywords, min_term_overlap):
                                    continue

                            if engine == "sites":
                                if self._is_search_url(full_url) and full_url not in explicit_site_seeds:
                                    continue

                            if self._is_content_child_candidate(full_url, urlparse(full_url).netloc, urlparse(full_url).path):
                                if len(next_pages) < child_page_limit:
                                    next_pages.append(full_url)
                            elif len(next_pages) < child_page_limit // 2:
                                next_pages.append(full_url)

                    if depth < max_depth and sniff_parent_pages:
                        for parent_url in sniff_parent_pages:
                            if _allowed_by_required_sites_check(parent_url):
                                if len(next_pages) < child_page_limit:
                                    next_pages.append(parent_url)

                    if use_database and self.store and _should_persist_page(page_url):
                        self.store.mark_page_scanned(page_url)

                except Exception as e:
                    local_log.append(f"Error scanning {page_url}: {e}")
                    if use_database and self.store and _should_persist_page(page_url):
                        self.store.mark_page_scanned(page_url)

                return {
                    "page": page_url,
                    "assets": local_assets,
                    "next_pages": list(dict.fromkeys(next_pages)),
                    "js_links": local_js_links,
                    "network_links": local_network_links,
                    "runtime_hits": local_runtime_hits,
                    "react_hits": local_react_hits,
                    "database_hits": local_database_hits,
                    "interaction_hits": local_interaction_hits,
                    "log": local_log,
                }

            # BFS frontier
            frontier: List[str] = []
            site_buckets = {s: [] for s in required_sites if s != "*"}

            for u in candidate_pages:
                if not _allowed_by_required_sites_check(u):
                    continue
                if required_sites and not global_mode:
                    d = self._clean_domain(u)
                    for s in required_sites:
                        if s != "*" and s in d:
                            site_buckets[s].append(u)
                            break
                else:
                    frontier.append(u)

            if required_sites and not global_mode:
                per_site_cap = max(3, max_pages_total // max(1, len(required_sites)))
                for s, bucket in site_buckets.items():
                    bucket.sort(key=lambda u: self._score_site_url(u, keywords), reverse=True)
                    frontier.extend(bucket[:per_site_cap])

            frontier = list(dict.fromkeys(frontier))[:max_pages_total]
            current_depth = 0

            # (you can define this just above the while loop)
            logged_rescan_notice = False

            # --- BFS LOOP START ---
            while frontier and current_depth <= max_depth and len(final_found_assets_by_content_id) < max_assets:


                DEBUG_LOGGER.log_message(
                    f"[VideoLinkTracker][BFS] --- Starting Depth {current_depth} | "
                    f"Frontier Size: {len(frontier)} | Visited: {len(visited_pages)} ---"
                )

                batch: List[str] = []
                # Calculate remaining slots to strictly enforce page limit
                slots_left = max_pages_total

                for u in frontier:
                    if len(batch) >= slots_left:
                        break

                    if u in visited_pages:
                        continue

                    # Respect DB "page_scanned" flag
                    if use_database and self.store and self.store.page_scanned(u):
                        if not (db_allow_rescan and source == "database"):
                            visited_pages.add(u)
                            continue
                        if not logged_rescan_notice:
                            DEBUG_LOGGER.log_message("[VideoLinkTracker][db] Rescan enabled.")
                            logged_rescan_notice = True

                    batch.append(u)
                    # CRITICAL: Mark visited immediately so we don't re-queue it in next_frontier
                    visited_pages.add(u)

                if not batch:
                    DEBUG_LOGGER.log_message(
                        f"[VideoLinkTracker][BFS] No valid URLs in batch at depth {current_depth}.")
                    break

                DEBUG_LOGGER.log_message(f"[VideoLinkTracker][BFS] Processing batch of {len(batch)} URLs...")

                if use_camoufox:
                    results: List[Dict[str, Any]] = []
                    for url in batch:
                        try:
                            res = await _process_page(url, current_depth, smart_sniff)
                            results.append(res)
                        except Exception as e:
                            DEBUG_LOGGER.log_message(f"[VideoLinkTracker][Camoufox] Fatal error on {url}: {e}")
                            continue
                else:
                    # Parallel execution for standard Playwright
                    results = await asyncio.gather(
                        *[_process_page(url, current_depth, smart_sniff) for url in batch]
                    )

                next_frontier_candidates: List[str] = []
                for res in results:
                    # Per-page logging handled in _process_page, but we aggregate lists here
                    log.extend(res["log"])
                    all_js_links.extend(res["js_links"])
                    all_network_links.extend(res["network_links"])
                    all_runtime_hits.extend(res.get("runtime_hits", []))
                    all_react_hits.extend(res.get("react_hits", []))  # [PATCH]
                    all_database_hits.extend(res.get("database_hits", []))
                    all_interaction_hits.extend(res.get("interaction_hits", []))
                    for asset in res["assets"]:
                        cid = asset.get("content_id") or self._get_content_id(asset.get("url", ""))
                        new_b = self._parse_size_to_bytes(asset.get("size", ""))
                        old = final_found_assets_by_content_id.get(cid)
                        if not old or new_b > self._parse_size_to_bytes(old.get("size", "")):
                            final_found_assets_by_content_id[cid] = asset

                    # Only collect next pages if we haven't hit max depth
                    if current_depth < max_depth:
                        if res.get("next_pages"):
                            next_frontier_candidates.extend(res["next_pages"])

                # Deduplicate and filter next frontier against visited
                next_frontier = []
                seen_in_next = set()

                for url in next_frontier_candidates:
                    if url not in visited_pages and url not in seen_in_next:
                        next_frontier.append(url)
                        seen_in_next.add(url)

                # Cap the next frontier to prevent exponential explosion
                # (e.g., if one page returns 5000 links, we don't want to queue them all)
                frontier = next_frontier[:max_pages_total]

                DEBUG_LOGGER.log_message(
                    f"[VideoLinkTracker][BFS] Depth {current_depth} complete. "
                    f"Found {len(frontier)} new unique pages for next depth."
                )

                current_depth += 1

            if pw_needed:
                await self._close_playwright_context(pw_p, pw_browser, pw_context, log)

        # ---- Assemble output ----
        display_sites = (
            "[payload]" if source == "payload"
            else ("[all]" if global_mode else ", ".join(required_sites))
        )

        found_assets = list(final_found_assets_by_content_id.values())
        found_assets.sort(
            key=lambda a: (
                a.get("score", 0),
                self._parse_size_to_bytes(a.get("size", "0"))
            ),
            reverse=True
        )

        # cooldown on output, then mark returned
        if source == "database" and output_cooldown_hours > 0 and use_database and self.store:
            filtered = []
            for a in found_assets:
                canon = a.get("url", "")
                cid = a.get("content_id") or self._get_content_id(canon)
                if canon in recently_returned_identifiers or cid in recently_returned_identifiers:
                    continue
                filtered.append(a)

            found_assets = filtered

            for a in found_assets:
                canon = a.get("url", "")
                cid = a.get("content_id") or self._get_content_id(canon)
                self.store.mark_returned_identifier(canon)
                self.store.mark_returned_identifier(cid)

        if not found_assets:
            base_text = (
                f"### VideoTracker: No video assets found.\n"
                f"Source: {source} | Scanned {display_sites} for query: {current_display_query}\n"
                f"Required keywords: {keywords}\n"
                f"min_term_overlap: {min_term_overlap}\n"
                f"Engine: {engine}\n"
            )
            lines = [base_text]

            if return_all_js_links and all_js_links:
                lines.append("\n### All JS-Gathered Links (debug)\n")
                for jl in all_js_links:
                    host = urlparse(jl["page"]).netloc if jl.get("page") else "(unknown)"
                    lines.append(f"- <{jl.get('tag')}> [{jl.get('text')}]({jl.get('url')}) @ {host}")

            if return_network_sniff_links and all_network_links:
                lines.append("\n### All Network-Sniffed Video Links (debug)\n")
                for nl in all_network_links:
                    host = urlparse(nl.get("page", "")).netloc if nl.get("page") else "(unknown)"
                    lines.append(
                        f"- <{nl.get('tag', 'network_sniff')}> "
                        f"[{nl.get('text')}]({nl.get('url')}) @ {host} "
                        f"(ctype={nl.get('content_type', '?')})"
                       )
            if return_react_sniff_hits and all_react_hits:
                lines.append("\n### React / SPA Hits (debug)\n")
                for rh in all_react_hits[:100]:
                    url = rh.get("url") or "(no url)"
                    route = rh.get("route") or ""
                    kind = rh.get("kind") or "react_nav"
                    lines.append(f"- `{kind}` **{route}** → {url}")
            if return_database_sniff_hits and all_database_hits:
                lines.append("\n### Database / Content Sniff Hits (debug)\n")
                for dbh in all_database_hits[:100]:
                    kind = dbh.get("kind")
                    url = dbh.get("url")
                    meta = dbh.get("meta") or {}

                    if kind == "content_link":
                        src = meta.get("source", "?")
                        lines.append(f"- `db_link` ({src}) **{url}**")
                    elif kind == "indexeddb_dump":
                        db_name = meta.get("name", "?")
                        stores = meta.get("stores", [])
                        store_str = ", ".join([f"{s['name']}(~{s.get('approx_count')})" for s in stores])
                        lines.append(f"- `indexed_db` **{db_name}**: [{store_str}]")
                    elif kind == "db_config_detected":
                        name = meta.get("name")
                        lines.append(f"- `backend_config` **{name}** detected")
            if return_runtime_sniff_hits and all_runtime_hits:
                lines.append("\n### Runtime Sniff Hits (debug)\n")
                # Cap output to prevent massive message overflow (e.g. 100 items)
                for hit in all_runtime_hits[:100]:
                    url = hit.get("url") or "(no url)"
                    payload = hit.get("json") or {}

                    # Format a readable description based on the hit type
                    desc_parts = []
                    if "console" in payload:
                        desc_parts.append(f"Console: {str(payload['console'])[:100]}...")
                    elif "ws_frame" in payload:
                        desc_parts.append(f"WebSocket: {str(payload['ws_frame'])[:100]}...")
                    elif "request_body" in payload:
                        desc_parts.append("Request Body (JSON)")
                    elif "media_events" in payload:
                        evts = payload["media_events"]
                        desc_parts.append(f"Media Events: {len(evts)}")
                    elif "storage" in payload:
                        desc_parts.append(f"Storage Items: {len(payload['storage'])}")
                    elif "perf_entries" in payload:
                        desc_parts.append(f"Perf Entries: {len(payload['perf_entries'])}")
                    else:
                        # Generic fallback for unknown payloads
                        import json as _json
                        try:
                            dump = _json.dumps(payload)
                            desc_parts.append(f"Data: {dump[:100]}...")
                        except:
                            desc_parts.append("Data: (complex object)")

                    desc = " | ".join(desc_parts)
                    lines.append(f"- `{desc}` found on **{url}**")

            if return_interaction_sniff_hits and all_interaction_hits:
                lines.append("\n### Interaction / CDP Hits (debug)\n")
                for ih in all_interaction_hits[:100]:
                    kind = ih.get("kind")
                    meta = ih.get("meta") or {}
                    url = ih.get("url")

                    if kind == "event_listener":
                        node = meta.get("nodeName", "UNK")
                        types = meta.get("types", [])
                        lines.append(f"- `listener` **{node}** {types} on {url}")
                    elif kind == "form_definition":
                        ins = meta.get("input_count", 0)
                        method = meta.get("method", "get")
                        lines.append(f"- `form` **{method.upper()}** ({ins} inputs) on {url}")
                    elif kind == "overlay_detected":
                        cov = meta.get("coverage", "?")
                        z = meta.get("zIndex", "?")
                        lines.append(f"- `overlay` (z={z}, cov={cov}) on {url}")
                    elif kind == "summary":
                        lc = meta.get("listener_count", 0)
                        fc = meta.get("form_count", 0)
                        lines.append(f"- `summary` Listeners: {lc}, Forms: {fc}")
            lines.append(f"\n### Log:\n" + "\n".join(log))
            return "\n".join(lines), {
                "count": 0,
                "keywords_used": keywords,
                "min_term_overlap": min_term_overlap,
                "sites": [] if global_mode else required_sites,
                "global_mode": global_mode,
                "log": log,
                "js_links": all_js_links,
                "network_sniff_links": all_network_links,
                "runtime_hits": all_runtime_hits,
                "react_hits": all_react_hits,
                "database_hits": all_database_hits,
                "interaction_hits": all_interaction_hits,
                "source": source,
                "subpipeline": subpipeline,
                "engine": engine,
            }

        lines = [f"### VideoTracker Found {len(found_assets)} Assets"]
        lines.append(
            f"_Source: {source} | Query: {current_display_query} | Sites: {display_sites} | "
            f"Keywords: {keywords} | min_term_overlap: {min_term_overlap} | "
            f"Pages: {len(visited_pages)} | Engine: {engine}_"
        )
        lines.append("")

        for asset in found_assets:
            lines.append(f"- **[{asset['text']}]({asset['url']})**")
            lines.append(
                f"  - *Tag: <{asset['tag']}> | "
                f"Source: {urlparse(asset.get('source_page','')).netloc if asset.get('source_page') else ''} | "
                f"Status: {asset['status']} | Size: {asset.get('size', '?')} | "
                f"content_id={asset.get('content_id','')}*"
            )

        if return_all_js_links and all_js_links:
            lines.append("\n### All JS-Gathered Links (debug)\n")
            for jl in all_js_links:
                host = urlparse(jl["page"]).netloc if jl.get("page") else "(unknown)"
                lines.append(f"- <{jl.get('tag')}> [{jl.get('text')}]({jl.get('url')}) @ {host}")

        if return_network_sniff_links and all_network_links:
            lines.append("\n### All Network-Sniffed Video Links (debug)\n")
            for nl in all_network_links:
                host = urlparse(nl.get("page", "")).netloc if nl.get("page") else "(unknown)"
                lines.append(
                    f"- <{nl.get('tag', 'network_sniff')}> "
                    f"[{nl.get('text')}]({nl.get('url')}) @ {host} "
                    f"(ctype={nl.get('content_type', '?')})"
                )

        lines.append(f"\n### Log:\n" + "\n".join(log))

        return "\n".join(lines), {
            "found": len(found_assets),
            "scanned_sites": [] if global_mode else required_sites,
            "global_mode": global_mode,
            "assets": found_assets,
            "keywords_used": keywords,
            "min_term_overlap": min_term_overlap,
            "pages_processed": len(visited_pages),
            "js_links": all_js_links,
            "network_sniff_links": all_network_links,
            "runtime_hits": all_runtime_hits,
            "database_hits": all_database_hits,
            "interaction_hits": all_interaction_hits,
            "source": source,
            "subpipeline": subpipeline,
            "engine": engine,
        }

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asyncio.run(self._execute_async(payload, params=params))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "lil uzi vert live performance",
            "source": "search",  # "search", "payload", "database"
            "sites": "",
            "scan_limit": 5,
            "timeout": 8.0,
            "user_agent": "promptchat/VideoLinkTracker",
            "engine": "duckduckgo",  # "duckduckgo", "google_cse", "sites"
            "verify": False,
            "use_js": False,
            "smart_sniff": False,
            "return_all_js_links": False,
            "max_depth": 0,
            "child_page_limit": 4,
            "max_pages_total": 20,
            "max_links_per_page": 200,
            "max_assets": 100,
            "use_network_sniff": False,
            "return_network_sniff_links": False,
            "use_runtime_sniff": False,
            "return_runtime_sniff_hits": False,
            "use_react_sniff": False,
            "return_react_sniff_hits": False,
            "use_database_sniff": False,
            "return_database_sniff_hits": False,
            "use_interaction_sniff": False,
            "return_interaction_sniff_hits": False,
            "min_term_overlap": 1,
            "subpipeline": "",

            # DB
            "use_database": False,
            "db_path": "video_corpus.db",

            # convergent database seeding controls
            "db_seed_sources": "pages",
            "db_seed_limit": 400,
            "db_seed_max_age_days": 14,
            "db_include_synthetic_seeds": False,
            "db_seed_per_domain_cap": 8,
            "memory_souces":"",
            "db_expand_max_per_seed": 4,
            "db_expand_ladder_depth": 2,
            "db_domain_cap": 80,
            "db_allow_rescan": False,

            "extract_urls_from_db_text": True,

            # Cooldown
            "output_cooldown_hours": 48,

            # Playwright block
            "block_resources": False,
            "blocked_resource_types": "image,stylesheet,font",
            "block_domains": True,
            "blocked_domains": "",

            # Search tuning
            "search_results_cap": 256,
            "search_page_limit": 1,
            "search_per_page": 50,

            # HTTPSSubmanager tuning
            "http_retries": 2,
            "http_max_conn_per_host": 8,
            "http_verify": True,
            "http_ca_bundle": "",  # e.g. certifi bundle path inside PyInstaller exe

            "use_camoufox": False,
            "camoufox_options": {},

            "download_assets": False,            # NEW: actually fetch media bytes
            "download_dir": "video_cache",       # NEW: base dir to stash files
            "max_download_bytes": 300 * 1024**2, # NEW: 300 MB per asset safety cap
            "skip_if_no_content_length": True,   # NEW: avoid unknown-size downloads
            "searxng_url": "http://127.0.0.1:8080",
            "reverse_image_url": "",
            "ffmpeg_bin": "",
            "pw_headless": True,
            "pw_channel": "",  # e.g. "chrome"
            "pw_proxy": {},  # e.g. {"server":"http://127.0.0.1:8080"}
            "pw_launch_args": [
                "--disable-quic",
                "--disable-http3",
                "--disable-features=UseDnsHttpsSvcb"
            ],
        }


BLOCKS.register("videotracker", VideoLinkTrackerBlock)


# ======================= TorOnionBlock =============================

@dataclass
class TorOnionBlock(BaseBlock):
    """
    Onion discovery using ONLY:
      - DuckDuckGo (onion mirror) via Tor
      - Crawling DDG result pages and extracting .onion links
    """

    # Official DuckDuckGo .onion HTML endpoint
    DDG_ONION = (
        "https://duckduckgogg42xjoc72x3sjasowoarfbgcmvfimaftt6twagswzczad.onion/html/"
    )

    # ---------------- Tor Session ----------------

    def _make_tor_session(self, tor_host="127.0.0.1", tor_port=9050,
                          timeout=10.0, user_agent=None):
        import requests
        session = requests.Session()
        proxy = f"socks5h://{tor_host}:{tor_port}"
        session.proxies = {"http": proxy, "https": proxy}
        if user_agent:
            session.headers.update({"User-Agent": user_agent})
        session._tor_timeout = timeout
        return session

    def _is_onion_url(self, url: str) -> bool:
        from urllib.parse import urlparse
        try:
            host = urlparse(url).netloc.lower()
            return ".onion" in host
        except:
            return False

    # ---------------- DuckDuckGo HTML Search ----------------

    def _search_ddg(self, session, query, max_results, timeout, log):
        import requests
        from bs4 import BeautifulSoup
        from urllib.parse import unquote

        urls = []
        try:
            resp = session.get(self.DDG_ONION, params={"q": query}, timeout=timeout)
            resp.raise_for_status()
        except Exception as e:
            log.append(f"[TorOnion] DuckDuckGo search failed: {e}")
            return urls

        soup = BeautifulSoup(resp.text, "html.parser")

        for a in soup.select(".result__a"):
            href = a.get("href")
            if not href:
                continue

            # decode DDG redirect-style URLs
            if "uddg=" in href:
                try:
                    href = unquote(href.split("uddg=")[1].split("&")[0])
                except Exception:
                    pass

            urls.append(href)
            if len(urls) >= max_results:
                break

        log.append(f"[TorOnion] DuckDuckGo returned {len(urls)} result URLs.")
        return urls

    # ---------------- HTML Fetch ----------------

    def _fetch_html(self, session, url, timeout, sleep_between, log):
        import time, requests
        try:
            if sleep_between > 0:
                time.sleep(sleep_between)
            r = session.get(url, timeout=timeout)
            r.raise_for_status()
            return r.text
        except Exception as e:
            log.append(f"[TorOnion] Error fetching {url}: {e}")
            return None

    # ---------------- Onion Extraction ----------------

    def _extract_onions(self, html, base_url):
        from bs4 import BeautifulSoup
        from urllib.parse import urljoin
        import re

        soup = BeautifulSoup(html, "html.parser")
        out = set()

        # 1. Normal <a href> scanning
        for a in soup.find_all("a", href=True):
            href = a["href"].strip()
            if ".onion" in href:
                full = urljoin(base_url, href)
                if ".onion" in full:
                    out.add(full)

        # 2. Regex scanning
        pattern = re.compile(
            r"(https?://)?([a-z2-7]{16,56}\.onion)([^\s'\"<>]*)",
            re.IGNORECASE
        )
        for m in pattern.finditer(html):
            scheme, host, tail = m.groups()
            scheme = scheme or "http://"
            url = (scheme + host + tail).rstrip(").,;\"'")
            out.add(url)

        return out

    # ---------------- Execute ----------------

    def execute(self, payload, *, params):
        query = params.get("query") or payload
        query = str(query).strip()
        mode = (params.get("mode") or "list").lower()

        tor_host = params.get("tor_host", "127.0.0.1")
        tor_port = int(params.get("tor_port", 9050))
        timeout = float(params.get("timeout", 10.0))
        user_agent = params.get("user_agent", "Mozilla/5.0 TorOnionBlock/1.0")

        scan_limit = int(params.get("scan_limit", 10))
        max_onions = int(params.get("max_onions", 50))
        sleep_between = float(params.get("sleep_between", 0.0))

        log = []

        # Step 1: Create Tor session
        session = self._make_tor_session(tor_host, tor_port, timeout, user_agent)

        # Step 2: Search DuckDuckGo
        result_urls = self._search_ddg(session, query, scan_limit, timeout, log)

        onions = set()

        # Step 3: Crawl DDG result pages
        for url in result_urls:
            if self._is_onion_url(url):
                onions.add(url)

            html = self._fetch_html(session, url, timeout, sleep_between, log)
            if html:
                onions |= self._extract_onions(html, url)

        onions = sorted(onions)[:max_onions]

        if not onions:
            return (
                f"### TorOnionBlock: No .onion addresses found\n- Query: `{query}`",
                {"query": query, "onions": [], "log": log},
            )

        # Output: list mode
        if mode == "list":
            out = f"### TorOnionBlock: Found {len(onions)} .onion addresses\n"
            out += f"_Query: `{query}`_\n\n"
            out += "\n".join(f"- `{o}`" for o in onions)
            return out, {"query": query, "onions": onions, "log": log}

        # Output: preview mode
        previews = []
        for o in onions:
            previews.append(self._preview(session, o, timeout, sleep_between, log))

        return previews, {
            "query": query,
            "onions": onions,
            "previews": previews,
            "log": log,
        }

    # ---------------- Preview Helper ----------------

    def _preview(self, session, url, timeout, sleep_between, log):
        html = self._fetch_html(session, url, timeout, sleep_between, log)
        if not html:
            return {"url": url, "title": "(unreachable)", "snippet": ""}

        from bs4 import BeautifulSoup
        soup = BeautifulSoup(html, "html.parser")
        title = soup.title.string.strip() if soup.title else "(no title)"
        text = soup.get_text(" ", strip=True)[:600]
        return {"url": url, "title": title, "snippet": text}

    # ---------------- Parameter Info ----------------

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "privacy email",
            "mode": "list",  # list | preview
            "scan_limit": 10,  # number of DDG result URLs to crawl
            "max_onions": 50,  # maximum onion URLs to return
            "tor_host": "127.0.0.1",  # Tor SOCKS proxy host
            "tor_port": 9050,  # Tor SOCKS proxy port (9150 for Tor Browser)
            "timeout": 10.0,  # per-request timeout
            "sleep_between": 0.0,  # delay between fetches
            "user_agent": "Mozilla/5.0 TorOnionBlock/1.0",
        }


BLOCKS.register("toronion", TorOnionBlock)


# ======================= DirectLinkTrackerBlock =============================


@dataclass
class DirectLinkTrackerBlock(BaseBlock):
    """
    Expand from direct content links (file hosters / detail pages / folders).
    Now uses:
      - DirectLinkTrackerStore (DB-backed) through DatabaseSubmanager
      - HTTPSSubmanager for all network I/O (except Playwright sniffers)

    DB usage:
      - params["use_database"]=True activates store
      - store is backed by DatabaseSubmanager (shared, thread-safe)
    """

    JUNK_FILENAME_KEYWORDS = {
        "sprite", "icon", "favicon", "logo", "tracking", "pixel",
        "blank", "placeholder",
    }

    IGNORED_EXTENSIONS = {
        ".css", ".js", ".json", ".xml", ".svg", ".png", ".jpg", ".jpeg",
        ".gif", ".ico", ".woff", ".woff2", ".ttf", ".eot", ".map"
    }

    _URL_RE = re.compile(r"https?://[^\s\"'<>\\)]+", re.IGNORECASE)

    MEGA_HOSTS = {"mega.nz", "www.mega.nz", "mega.co.nz", "www.mega.co.nz"}
    MEGA_PATH_MARKERS = ("/file/", "/folder/", "/embed/", "/#F!", "/#!")

    _PILLOWS_ID_RE = re.compile(
        r"(?:/f/|/api/get/|/get/)([a-f0-9]{24,64})|"
        r"\b([a-f0-9]{32})\b",
        re.IGNORECASE
    )

    def __post_init__(self):
        self.js_sniffer = submanagers.JSSniffer(
            submanagers.JSSniffer.Config(enable_auto_scroll=True, max_scroll_steps=40, scroll_step_delay_ms=500)
        )
        self.network_sniffer = submanagers.NetworkSniffer(
            submanagers.NetworkSniffer.Config(enable_auto_scroll=True, max_scroll_steps=40, scroll_step_delay_ms=500)
        )
        self.react_sniffer = submanagers.ReactSniffer(
            submanagers.ReactSniffer.Config(
                hook_history_api=True,
                hook_link_clicks=True,
                inspect_react_devtools_hook=True,
                enable_fiber_traversal=True,
                enable_router_inspection=True,
                enable_state_url_scan=True
            )
        )
        self.database_sniffer = submanagers.DatabaseSniffer(
            submanagers.DatabaseSniffer.Config(
                enable_indexeddb_dump=True,  # Metadata/Schema only
                enable_backend_fingerprint=True,
                enable_html_link_scan=True,
                enable_backend_link_scan=True,
                backend_scan_depth=2
            )
        )
        self.interaction_sniffer = submanagers.InteractionSniffer(
            submanagers.InteractionSniffer.Config(
                enable_cdp_listeners=True,
                enable_overlay_detection=True,
                enable_form_extraction=True
            )
        )
    # ------------------------------------------------------------------ #
    # small helpers
    # ------------------------------------------------------------------ #
    def _looks_nonempty_size(self, cl: Optional[str]) -> bool:
        try:
            if not cl:
                return True
            return int(cl) > 16 * 1024
        except Exception:
            return True

    def _extract_ids_from_text(self, text: str) -> Set[str]:
        ids = set()
        for m in self._PILLOWS_ID_RE.finditer(text or ""):
            g1, g2 = m.group(1), m.group(2)
            if g1:
                ids.add(g1)
            if g2:
                ids.add(g2)
        return ids

    def _extract_froste_song_id(self, u: str) -> Optional[str]:
        try:
            p = urlparse(u)
            parts = [x for x in (p.path or "").split("/") if x]
            if len(parts) >= 2 and parts[-2] == "song":
                return parts[-1]
        except Exception:
            pass
        return None

    def _extract_urls_from_index_line(self, line: str) -> List[str]:
        if not line:
            return []
        urls = self._URL_RE.findall(line)
        cleaned = []
        for u in urls:
            u = u.strip().rstrip(").,;\"'")
            if u:
                cleaned.append(u)
        return cleaned

    def _label_from_index_line(self, line: str, url: str) -> str:
        line = (line or "").strip()
        if url and url in line:
            line_wo_url = line.replace(url, "").strip()
        else:
            line_wo_url = line

        for sep in [" - ", " | ", "\t", "  "]:
            if sep in line_wo_url:
                left = line_wo_url.split(sep, 1)[0].strip()
                if left:
                    return left[:100]

        try:
            return url.rsplit("/", 1)[-1][:100]
        except Exception:
            return (line_wo_url or url or "[asset]")[:100]

    def _extract_keywords_from_query(self, query: str) -> List[str]:
        return [w.strip().lower() for w in (query or "").split() if w.strip()]

    def _resolve_query_text(self, payload: Any, params: Dict[str, Any]) -> str:
        q = str(params.get("query", "") or "").strip()
        if q:
            return q
        if isinstance(payload, str):
            p = payload.strip()
            if p and not p.startswith("http"):
                return p
        return ""

    def _extract_direct_id(self, u: str) -> Optional[str]:
        try:
            p = urlparse(u)
            parts = [x for x in (p.path or "").split("/") if x]
            if len(parts) >= 2 and parts[-2] in {"f", "file"}:
                return parts[-1]
        except Exception:
            pass
        return None

    def _expand_direct_seed(self, seed_url: str) -> List[str]:
        out: List[str] = []
        try:
            p = urlparse(seed_url)
            base = f"{p.scheme}://{p.netloc}"
            fid = self._extract_direct_id(seed_url)

            out.append(seed_url)

            if fid:
                out.append(f"{base}/f/")

                if "pillows.su" in p.netloc.lower():
                    api_base = base.replace("://pillows.su", "://api.pillows.su")
                    out.extend([
                        f"{api_base}/api/get/{fid}",
                        f"{api_base}/api/get/{fid}.ogg",
                        f"{api_base}/api/get/{fid}.mp3",
                        f"{api_base}/api/get/{fid}.wav",
                        f"{api_base}/api/get/{fid}.flac",
                        f"{api_base}/api/metadata/{fid}.json",
                        f"{api_base}/api/metadata/{fid}.txt",
                    ])

            if "pillows.su" in p.netloc.lower():
                out.extend([
                    f"{base}/onlyfiles.txt",
                    f"{base}/recent",
                    f"{base}/search",
                ])

            if "music.froste.lol" in p.netloc.lower():
                sid = self._extract_froste_song_id(seed_url)
                if sid:
                    out.extend([
                        f"{base}/song/{sid}/file",
                        f"{base}/song/{sid}/download",
                    ])
                out.extend([
                    f"{base}/",
                    f"{base}/recent",
                    f"{base}/songs",
                    f"{base}/search",
                    f"{base}/artists",
                    f"{base}/albums",
                    f"{base}/trending",
                ])
        except Exception:
            pass

        seen = set()
        cleaned: List[str] = []
        for u in out:
            if u and u not in seen:
                seen.add(u)
                cleaned.append(u)
        return cleaned

    def _clean_domain(self, u: str) -> str:
        try:
            return urlparse(u).netloc.lower().split(":")[0]
        except Exception:
            return ""

    def _clean_path(self, u: str) -> str:
        try:
            return urlparse(u).path.lower()
        except Exception:
            return ""

    def _is_mega_link(self, u: str) -> bool:
        try:
            pu = urlparse(u)
            host = (pu.netloc or "").lower().split(":")[0]
            path = (pu.path or "").lower()
            frag = (pu.fragment or "").lower()
            full_low = u.lower()

            if host in self.MEGA_HOSTS:
                if any(m in path for m in self.MEGA_PATH_MARKERS):
                    return True
                if frag.startswith(("f!", "!")) or "file/" in frag or "folder/" in frag:
                    return True
                return True
            if "mega.nz/#" in full_low or "mega.co.nz/#" in full_low:
                return True
            return False
        except Exception:
            return False

    def _predict_next_in_sequence(self, urls: List[str]) -> List[str]:
        generated = set()
        re_seq = re.compile(r"([0-9]+)(\.[a-z0-9]+)$", re.IGNORECASE)
        for u in urls:
            m = re_seq.search(u)
            if not m:
                continue
            num_s, ext = m.group(1), m.group(2)
            try:
                width = len(num_s)
                val = int(num_s)
                for i in range(1, 4):
                    nxt = f"{val + i:0{width}d}"
                    new_u = u[:m.start(1)] + nxt + u[m.end(1):]
                    generated.add(new_u)
            except ValueError:
                pass
        return list(generated)

    def _parent_dir_url(self, u: str) -> Optional[str]:
        try:
            pu = urlparse(u)
            path = pu.path or "/"
            if "/" not in path.strip("/"):
                return f"{pu.scheme}://{pu.netloc}/"
            parent = path.rsplit("/", 1)[0] + "/"
            return f"{pu.scheme}://{pu.netloc}{parent}"
        except Exception:
            return None

    def _looks_like_content_page(self, u: str) -> bool:
        p = self._clean_path(u)
        for tok in [
            "/f/", "/file/", "/folder/", "/view/", "/download/",
            "/d/", "/details/", "/item/",
            "/song/", "/album/", "/artist/", "/playlist/",
        ]:
            if tok in p:
                return True
        if re.search(r"/[a-z0-9]{6,}$", p):
            return True
        return False

    def _pillows_id_from_f_url(self, u: str) -> Optional[str]:
        try:
            p = urlparse(u)
            parts = [x for x in (p.path or "").split("/") if x]
            if len(parts) >= 2 and parts[-2] in {"f", "file"}:
                return parts[-1]
        except Exception:
            pass
        return None

    def _extract_seed_urls(self, payload: Any, params: Dict[str, Any]) -> List[str]:
        seeds: List[str] = []

        if isinstance(params.get("urls"), list):
            seeds.extend([str(x).strip() for x in params["urls"] if str(x).strip()])

        if isinstance(payload, str):
            seeds.extend(self._URL_RE.findall(payload))
        elif isinstance(payload, list):
            seeds.extend([str(x).strip() for x in payload if str(x).strip()])

        q = str(params.get("query", "") or "").strip()
        if q.startswith("http"):
            seeds.append(q)

        out = []
        seen = set()
        for u in seeds:
            if u and u not in seen:
                seen.add(u)
                out.append(u)
        return out

    # ------------------------------------------------------------------ #
    # Playwright shared context (unchanged)
    # ------------------------------------------------------------------ #
    async def _open_playwright_context(
        self,
        ua: str,
        block_resources: bool,
        blocked_resource_types: set[str],
        block_domains: bool,
        blocked_domains: set[str],
        log: List[str],
        *,
        use_camoufox: bool = False,
        camoufox_options: Optional[Dict[str, Any]] = None,
    ):
        def _host_matches_blocked(host: str) -> bool:
            host = host.split(":", 1)[0].lower()
            for bd in blocked_domains:
                bd = bd.lower()
                if not bd:
                    continue
                if host == bd or host.endswith("." + bd):
                    return True
            return False

        if use_camoufox:
            if AsyncCamoufox is None:
                log.append("[PlaywrightCtx] Camoufox requested but not installed; falling back to Chromium.")
            else:
                try:
                    options = {
                        "headless": True,
                        "block_images": block_resources,
                        "block_webrtc": True,
                        "geoip": False,
                        "humanize": False,
                    }
                    if camoufox_options:
                        options.update(camoufox_options)

                    cf_cm = AsyncCamoufox(**options)
                    browser = await cf_cm.__aenter__()
                    context = await browser.new_context(user_agent=ua)

                    if block_resources or block_domains:
                        async def route_blocker(route, request):
                            rtype = (request.resource_type or "").lower()
                            try:
                                host = urlparse(request.url).netloc.lower()
                            except Exception:
                                host = ""

                            if block_domains and _host_matches_blocked(host):
                                await route.abort()
                                return
                            if block_resources and rtype in blocked_resource_types:
                                await route.abort()
                                return
                            await route.continue_()

                        await context.route("**/*", route_blocker)

                    log.append("[PlaywrightCtx] Camoufox context ready.")
                    return cf_cm, browser, context

                except Exception as e:
                    log.append(f"[PlaywrightCtx] Camoufox init failed ({e}); falling back to Chromium.")

        try:
            from playwright.async_api import async_playwright
        except ImportError:
            log.append("Playwright not installed.")
            return None, None, None

        p = await async_playwright().start()
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context(user_agent=ua)

        if block_resources or block_domains:
            async def route_blocker(route, request):
                rtype = (request.resource_type or "").lower()
                try:
                    host = urlparse(request.url).netloc.lower()
                except Exception:
                    host = ""

                if block_domains and _host_matches_blocked(host):
                    await route.abort()
                    return
                if block_resources and rtype in blocked_resource_types:
                    await route.abort()
                    return
                await route.continue_()

            await context.route("**/*", route_blocker)

        log.append("Playwright shared context ready.")
        return p, browser, context

    async def _close_playwright_context(self, p, browser, context, log: List[str]):
        try:
            if context:
                close_ctx = getattr(context, "close", None)
                if callable(close_ctx):
                    if asyncio.iscoroutinefunction(close_ctx):
                        await close_ctx()
                    else:
                        close_ctx()
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox context: {e}")

        try:
            if browser:
                close_browser = getattr(browser, "close", None)
                if callable(close_browser):
                    if asyncio.iscoroutinefunction(close_browser):
                        await close_browser()
                    else:
                        close_browser()
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox browser: {e}")

        try:
            if p:
                stop = getattr(p, "stop", None)
                if stop:
                    if asyncio.iscoroutinefunction(stop):
                        await stop()
                    else:
                        stop()
                else:
                    aexit = getattr(p, "__aexit__", None)
                    if aexit:
                        if asyncio.iscoroutinefunction(aexit):
                            await aexit(None, None, None)
                        else:
                            aexit(None, None, None)
            log.append("Playwright/Camoufox shared context closed.")
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox handle: {e}")

    async def _pw_fetch_with_sniff(self, context, page_url, timeout, log, extensions=None):
        return await self.network_sniffer.sniff(
            context, page_url, timeout=timeout, log=log, extensions=extensions,
        )

    async def _pw_fetch_js_links(self, context, page_url, timeout, log, extensions=None):
        return await self.js_sniffer.sniff(
            context, page_url, timeout=timeout, log=log, extensions=extensions,
        )

    async def _pw_fetch_react_links(self, context, page_url, timeout, log, extensions=None):
        return await self.react_sniffer.sniff(
            context, page_url, timeout=timeout, log=log, extensions=extensions,
        )

    async def _pw_fetch_database_links(self, context, page_url, timeout, log):
        return await self.database_sniffer.sniff(
            context, page_url, timeout=timeout, log=log
        )

    async def _pw_fetch_interaction_links(self, context, page_url, timeout, log):
        return await self.interaction_sniffer.sniff(
            context, page_url, timeout=timeout, log=log
        )
    # ------------------------------------------------------------------ #
    # HTTPS helpers
    # ------------------------------------------------------------------ #
    async def _http_get_html(self, http: submanagers.HTTPSSubmanager, url: str) -> str:
        return await http.get_text(url)

    async def _http_head(self, http: submanagers.HTTPSSubmanager, url: str) -> Tuple[Optional[int], Dict[str, str]]:
        return await http.head(url)

    async def _try_fetch_metadata(self, http: submanagers.HTTPSSubmanager, meta_url: str) -> Dict[str, Any]:
        try:
            txt = await http.get_text(meta_url)
            if not txt:
                return {}
            s = txt.strip()
            if not (s.startswith("{") and s.endswith("}")):
                # some endpoints return JSON without perfect trimming; still try loads if it starts with {
                if not s.startswith("{"):
                    return {}
            return json.loads(txt)
        except Exception:
            return {}

    # ------------------------------------------------------------------ #
    # Main execution
    # ------------------------------------------------------------------ #
    async def _execute_async(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        seed_urls = self._extract_seed_urls(payload, params)
        query_text = self._resolve_query_text(payload, params)

        use_camoufox = bool(params.get("use_camoufox", False))
        camoufox_options = params.get("camoufox_options") or {}
        if not isinstance(camoufox_options, dict):
            camoufox_options = {}
        camoufox_options.update({"i_know_what_im_doing": True})

        # ---------------- DB (Store + DatabaseSubmanager) ----------------
        use_database = bool(params.get("use_database", False))
        db_path = str(params.get("db_path", "link_corpus.db") or "link_corpus.db")
        db_sm = None
        store: Optional[DirectLinkTrackerStore] = None

        if use_database:
            db_sm = submanagers.DatabaseSubmanager(submanagers.DatabaseConfig(path=db_path))
            store = DirectLinkTrackerStore(db=db_sm)
            store.ensure_schema()

        # ---------------- Config ----------------
        mode = str(params.get("mode", "docs")).lower()

        default_pages = 200 if any("pillows.su" in s for s in seed_urls) else (len(seed_urls) or 5)
        max_pages_total = max(1, int(params.get("max_pages_total", default_pages)))

        default_depth = 2 if any("pillows.su" in s for s in seed_urls) else 1
        max_depth = max(0, int(params.get("max_depth", default_depth)))

        timeout = float(params.get("timeout", 6.0))
        verify_links = bool(params.get("verify", True))

        # TLS verify for HTTPSSubmanager (separate from verify_links)
        tls_verify = bool(params.get("tls_verify", True))
        ca_bundle = params.get("ca_bundle") or None

        use_js = bool(params.get("use_js", False))
        use_network_sniff = bool(params.get("use_network_sniff", False))
        return_all_js_links = bool(params.get("return_all_js_links", False))
        return_network_sniff_links = bool(params.get("return_network_sniff_links", False))
        use_react_sniff = bool(params.get("use_react_sniff", False))
        return_react_sniff_links = bool(params.get("return_react_sniff_links", False))
        use_database_sniff = bool(params.get("use_database_sniff", False))
        return_database_sniff_links = bool(params.get("return_database_sniff_links", False))
        use_interaction_sniff = bool(params.get("use_interaction_sniff", False))
        return_interaction_sniff_links = bool(params.get("return_interaction_sniff_links", False))
        max_links_per_page = int(params.get("max_links_per_page", 800))

        min_term_overlap = max(1, int(params.get("min_term_overlap", 1)))

        custom_ext = str(params.get("extensions", "")).split(",")
        expand_direct = bool(params.get("expand_direct", True))
        best_n = int(params.get("best_n", 50))

        # --- Keyword handling ---
        url_keywords = str(params.get("url_keywords", "")).split(",")
        keywords = [k.strip().lower() for k in url_keywords if k.strip()]

        strict_keywords = bool(params.get("strict_keywords", False))
        if query_text:
            if strict_keywords:
                whole = query_text.lower().strip()
                if whole and whole not in keywords:
                    keywords.append(whole)
            else:
                for w in self._extract_keywords_from_query(query_text):
                    if w not in keywords:
                        keywords.append(w)

        # Required sites optional
        site_require_raw = str(params.get("site_require", "")).split(",")
        required_sites = [s.strip().lower() for s in site_require_raw if s.strip()]

        def _allowed_by_required_sites(u: str) -> bool:
            if not required_sites:
                return True
            d = self._clean_domain(u)
            return any(req in d for req in required_sites)

        def _term_overlap_ok(haystack: str) -> bool:
            if not keywords:
                return True
            h = haystack.lower()
            hits = 0
            for k in keywords:
                if k and k in h:
                    hits += 1
                    if hits >= min_term_overlap:
                        return True
            return False

        def _score_for_keywords(haystack: str) -> int:
            if not keywords:
                return 0
            h = haystack.lower()
            return sum(1 for k in keywords if k and k in h)

        # Targets based on mode
        targets: Set[str] = set()
        if mode == "media":
            targets.update([".mp3", ".wav", ".flac", ".m4a", ".ogg"])
        elif mode == "docs":
            targets.update([".pdf", ".epub", ".mobi", ".doc", ".docx", ".txt"])
        elif mode == "archives":
            targets.update([".zip", ".rar", ".7z", ".tar", ".gz"])

        for e in custom_ext:
            e = e.strip()
            if not e:
                continue
            if not e.startswith("."):
                e = "." + e
            targets.add(e.lower())

        if not targets:
            targets.update([".pdf", ".epub", ".mobi", ".doc", ".docx", ".txt"])

        # logging + state
        log: List[str] = []
        found_assets: List[Dict[str, Any]] = []
        seen_asset_urls: set[str] = set()
        visited_pages: set[str] = set()
        all_js_links: List[Dict[str, str]] = []
        all_network_links: List[Dict[str, str]] = []
        all_react_links: List[Dict[str, Any]] = []
        all_database_links: List[Dict[str, Any]] = []  # [PATCH]
        all_interaction_links: List[Dict[str, Any]] = []
        # ---------------- Shared Playwright context if needed ----------------
        pw_needed = use_js or use_network_sniff or use_react_sniff or use_database_sniff or use_interaction_sniff
        pw_p = pw_browser = pw_context = None
        if pw_needed:
            block_resources = bool(params.get("block_resources", False))
            blocked_resource_types = {
                t.strip().lower()
                for t in str(params.get("blocked_resource_types", "")).split(",")
                if t.strip()
            } or {"image", "stylesheet", "font"}

            block_domains = bool(params.get("block_domains", True))
            user_blocked_domains = {
                d.strip().lower()
                for d in str(params.get("blocked_domains", "")).split(",")
                if d.strip()
            }
            default_blocked_domains = {
                "google-analytics.com", "googletagmanager.com", "doubleclick.net",
                "facebook.com", "facebook.net", "twitter.com", "scorecardresearch.com",
                "quantserve.com", "hotjar.com", "segment.io", "mixpanel.com",
                "cloudflareinsights.com", "stats.g.doubleclick.net",
                "adservice.google.com", "ads.yahoo.com", "adsafeprotected.com",
            }
            blocked_domains: set[str] = default_blocked_domains.union(user_blocked_domains) if block_domains else set()

            try:
                ua_pw = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/DirectLinkTracker"
                pw_p, pw_browser, pw_context = await self._open_playwright_context(
                    ua=ua_pw,
                    block_resources=block_resources,
                    blocked_resource_types=blocked_resource_types,
                    block_domains=block_domains,
                    blocked_domains=blocked_domains,
                    log=log,
                    use_camoufox=use_camoufox,
                    camoufox_options=camoufox_options,
                )
            except Exception:
                if pw_p or pw_browser or pw_context:
                    await self._close_playwright_context(pw_p, pw_browser, pw_context, log)

        # ---------------- Page processor (uses HTTPSSubmanager) ----------------
        async def _process_page(http: submanagers.HTTPSSubmanager, page_url: str, depth: int) -> Dict[str, Any]:
            local_log: List[str] = []
            local_assets: List[Dict[str, Any]] = []
            local_js_links: List[Dict[str, str]] = []
            local_network_links: List[Dict[str, str]] = []
            local_react_links: List[Dict[str, Any]] = []
            local_database_links: List[Dict[str, Any]] = []
            local_interaction_links: List[Dict[str, Any]] = []
            next_pages: List[str] = []

            html = ""
            links_on_page: List[Dict[str, str]] = []
            sniff_items: List[Dict[str, str]] = []

            try:
                # 1) Network sniff (Playwright)
                if use_network_sniff and pw_context:
                    sniff_html, sniff_items, sniff_json = await self._pw_fetch_with_sniff(
                        pw_context, page_url, timeout, local_log, targets
                    )
                    html = sniff_html or html
                    for si in sniff_items:
                        u = si.get("url")
                        if not u:
                            continue
                        local_network_links.append({
                            "page": page_url, "url": u,
                            "text": si.get("text", ""), "tag": si.get("tag", "network_sniff"),
                            "size": si.get("size", "?")
                        })
                        local_js_links.append({
                            "page": page_url, "url": u,
                            "text": si.get("text", ""), "tag": si.get("tag", "network_sniff")
                        })

                # 2) JS gather (Playwright)
                if use_js and pw_context:
                    js_html, js_links = await self._pw_fetch_js_links(pw_context, page_url, timeout, local_log)
                    if js_html:
                        html = js_html
                    links_on_page.extend(js_links)
                    for jl in js_links:
                        local_js_links.append({
                            "page": page_url,
                            "url": jl.get("url", ""),
                            "text": jl.get("text", ""),
                            "tag": jl.get("tag", ""),
                        })
                if use_react_sniff and pw_context:
                    r_html, r_hits = await self._pw_fetch_react_links(pw_context, page_url, timeout, local_log)
                    if r_html and not html:
                        html = r_html

                    for rh in r_hits:
                        local_react_links.append(rh)
                        u = rh.get("url")
                        if u:
                            # Promote React-found URLs to the main discovery queue
                            links_on_page.append({
                                "url": u,
                                "text": f"[React:{rh.get('kind')}] {rh.get('route', '')}",
                                "tag": "react_sniff"
                            })
                if use_database_sniff and pw_context:
                    d_html, d_links = await self._pw_fetch_database_links(pw_context, page_url, timeout, local_log)
                    if d_html and not html:
                        html = d_html

                    for entry in d_links:
                        local_database_links.append(entry)
                        # If entry is a content_link, promote it for file extension verification
                        if entry.get("kind") == "content_link":
                            u = entry.get("url")
                            if u:
                                links_on_page.append({
                                    "url": u,
                                    "text": f"[DB_Link:{entry['meta'].get('source', 'storage')}]",
                                    "tag": "database_sniff"
                                })
                if use_interaction_sniff and pw_context:
                    # Note: CDP features only trigger if pw_context is Chromium
                    i_html, i_links = await self._pw_fetch_interaction_links(pw_context, page_url, timeout, local_log)
                    if i_html and not html:
                        html = i_html

                    for entry in i_links:
                        local_interaction_links.append(entry)
                        # We don't automatically promote interaction nodes to 'links_on_page'
                        # because they are often nodes (buttons/divs), not URLs.
                        # However, we log them for barrier analysis.
                # 3) Plain fetch via HTTPSSubmanager if needed
                if not html:
                    html = await self._http_get_html(http, page_url)

                # metadata handling
                if page_url.endswith(".json") and "/api/metadata/" in page_url:
                    meta = await self._try_fetch_metadata(http, page_url)
                    if meta:
                        local_js_links.append({
                            "page": page_url,
                            "url": page_url,
                            "text": f"[metadata] {meta.get('title') or meta.get('name') or ''}".strip(),
                            "tag": "metadata"
                        })
                        harvested_ids = self._extract_ids_from_text(str(meta))
                        for hid in harvested_ids:
                            base = page_url.split("/api/metadata/")[0].replace("://api.", "://")
                            api_base = base.replace("://pillows.su", "://api.pillows.su")
                            next_pages.append(f"{base}/f/{hid}")
                            next_pages.append(f"{api_base}/api/get/{hid}")

                # onlyfiles.txt shortcut
                if page_url.endswith("onlyfiles.txt"):
                    try:
                        for line in (html or "").splitlines():
                            line = line.strip()
                            if not line:
                                continue

                            urls_in_line = self._extract_urls_from_index_line(line)
                            if not urls_in_line:
                                continue

                            for u2 in urls_in_line:
                                if not u2.startswith("http"):
                                    continue
                                if not _allowed_by_required_sites(u2):
                                    continue

                                host2 = self._clean_domain(u2)
                                path2 = self._clean_path(u2)

                                label2 = self._label_from_index_line(line, u2)
                                hay2 = f"{label2} {u2} {line} {page_url}"

                                if keywords and not _term_overlap_ok(hay2):
                                    if len(next_pages) < 20:
                                        next_pages.append(u2)
                                    continue

                                # pillows onlyfiles -> synthesize api/get + ext
                                if ("pillows.su" in host2 or "pillowcase.su" in host2) and ("/f/" in path2 or "/file/" in path2):
                                    fid2 = self._pillows_id_from_f_url(u2)
                                    if fid2:
                                        base = f"{urlparse(u2).scheme}://{urlparse(u2).netloc}"
                                        api_base = base.replace("://pillows.su", "://api.pillows.su") \
                                                      .replace("://pillowcase.su", "://api.pillows.su")

                                        for ext in targets:
                                            asset_url = f"{api_base}/api/get/{fid2}{ext}"
                                            synth_hay = f"{label2} {asset_url} {line} {page_url}"
                                            score2 = _score_for_keywords(synth_hay)

                                            asset = {
                                                "text": label2,
                                                "url": asset_url,
                                                "source": page_url,
                                                "size": "?",
                                                "status": "indexed",
                                                "tag": "onlyfiles_synth",
                                                "score": score2,
                                                "onlyfiles": True,
                                            }

                                            if (not keywords) or (score2 >= min_term_overlap):
                                                local_assets.append(asset)
                                                if store:
                                                    store.upsert_asset(asset)
                                        continue

                                # normal file URL in onlyfiles
                                if any(path2.endswith(ext) for ext in targets):
                                    score2 = _score_for_keywords(hay2)
                                    asset = {
                                        "text": label2,
                                        "url": u2,
                                        "source": page_url,
                                        "size": "?",
                                        "status": "indexed",
                                        "tag": "onlyfiles",
                                        "score": score2,
                                        "onlyfiles": True,
                                    }
                                    if (not keywords) or (score2 >= min_term_overlap):
                                        local_assets.append(asset)
                                        if store:
                                            store.upsert_asset(asset)
                                else:
                                    next_pages.append(u2)

                    except Exception as e:
                        local_log.append(f"onlyfiles parse error: {e}")

                    if store:
                        try:
                            store.mark_page_scanned(page_url)
                        except Exception:
                            pass

                    return {
                        "page": page_url,
                        "assets": local_assets,
                        "next_pages": next_pages,
                        "js_links": local_js_links,
                        "network_links": local_network_links,
                        "react_links": local_react_links,
                        "database_links": local_database_links,
                        "interaction_links": local_interaction_links,
                        "log": local_log
                    }

                soup = BeautifulSoup(html or "", "html.parser")

                title = ""
                if soup.title and soup.title.string:
                    title = soup.title.string.strip()

                # collect <a> hrefs
                link_count = 0
                for a in soup.find_all("a", href=True):
                    links_on_page.append({
                        "url": a["href"],
                        "text": a.get_text(strip=True),
                        "tag": "a",
                    })
                    link_count += 1
                    if link_count >= max_links_per_page:
                        break

                # harvest ids after <a>
                harvested_ids = self._extract_ids_from_text(html)
                for lk in links_on_page:
                    harvested_ids |= self._extract_ids_from_text(lk.get("url", ""))

                for hid in harvested_ids:
                    if "pillows.su" in self._clean_domain(page_url):
                        base = f"{urlparse(page_url).scheme}://{urlparse(page_url).netloc}"
                        api_base = base.replace("://pillows.su", "://api.pillows.su")
                        next_pages.append(f"{base}/f/{hid}")
                        next_pages.append(f"{api_base}/api/get/{hid}")
                        next_pages.append(f"{api_base}/api/metadata/{hid}.json")

                # Scan for assets in links
                for link in links_on_page:
                    raw = link.get("url", "")
                    full_url = urljoin(page_url, raw)
                    if not full_url.startswith("http"):
                        continue
                    if not _allowed_by_required_sites(full_url):
                        continue

                    path = self._clean_path(full_url)
                    is_mega = self._is_mega_link(full_url)

                    if not is_mega and any(path.endswith(ext) for ext in self.IGNORED_EXTENSIONS):
                        continue
                    if not is_mega and not any(path.endswith(ext) for ext in targets):
                        continue

                    if store and store.is_asset_url(full_url):
                        continue

                    status = "unverified"
                    size = "?"
                    if verify_links and not is_mega:
                        st, hdrs = await self._http_head(http, full_url)
                        if st != 200:
                            continue

                        cl = (hdrs.get("Content-Length") or hdrs.get("content-length"))
                        ctype = (hdrs.get("Content-Type") or hdrs.get("content-type") or "").lower()

                        if not self._looks_nonempty_size(cl):
                            continue

                        if mode == "media" and ("audio" not in ctype and "octet-stream" not in ctype):
                            continue

                        status = "200 OK"
                        if cl:
                            try:
                                size = f"{int(cl) // 1024} KB"
                            except Exception:
                                size = "?"

                    elif is_mega:
                        status = "MEGA link"

                    text = (link.get("text") or path.rsplit("/", 1)[-1] or "[asset]")[:100]
                    hay = f"{text} {full_url} {title} {page_url}"
                    score = _score_for_keywords(hay)

                    asset = {
                        "text": text,
                        "url": full_url,
                        "source": page_url,
                        "size": size,
                        "status": status,
                        "tag": "mega" if is_mega else link.get("tag", "a"),
                        "score": score,
                    }
                    local_assets.append(asset)
                    if store:
                        store.upsert_asset(asset)

                # include sniffed items as assets too
                for item in sniff_items:
                    u = item.get("url")
                    if not u or not _allowed_by_required_sites(u):
                        continue
                    pth = self._clean_path(u)
                    if not any(pth.endswith(ext) for ext in targets):
                        continue
                    if store and store.is_asset_url(u):
                        continue

                    status = "sniffed"
                    size = item.get("size", "?")
                    if verify_links:
                        st, _hdrs = await self._http_head(http, u)
                        if st != 200:
                            continue
                        status = "200 OK"

                    hay = f"{item.get('text','')} {u} {title} {page_url}"
                    score = _score_for_keywords(hay)

                    asset = {
                        "text": (item.get("text") or u.rsplit("/", 1)[-1] or "[asset]")[:100],
                        "url": u,
                        "source": page_url,
                        "size": size,
                        "status": status,
                        "tag": "network_sniff",
                        "score": score,
                    }
                    local_assets.append(asset)
                    if store:
                        store.upsert_asset(asset)

                # Next pages
                if depth < max_depth:
                    base_host = self._clean_domain(page_url)
                    for link in links_on_page:
                        raw = link.get("url", "")
                        nxt = urljoin(page_url, raw)
                        if not nxt.startswith("http"):
                            continue
                        if not _allowed_by_required_sites(nxt):
                            continue
                        if self._clean_domain(nxt) != base_host:
                            continue
                        if any(self._clean_path(nxt).endswith(ext) for ext in targets):
                            continue
                        if not self._looks_like_content_page(nxt):
                            continue

                        if keywords:
                            nxt_hay = (link.get("text", "") + " " + nxt).lower()
                            if _term_overlap_ok(nxt_hay):
                                next_pages.append(nxt)
                            else:
                                if len(next_pages) < 20:
                                    next_pages.append(nxt)
                        else:
                            next_pages.append(nxt)

                    parent = self._parent_dir_url(page_url)
                    if parent and parent.startswith("http") and _allowed_by_required_sites(parent):
                        next_pages.append(parent)

            except Exception as e:
                local_log.append(f"Error scanning {page_url}: {e}")

            if store:
                try:
                    store.mark_page_scanned(page_url)
                except Exception:
                    pass

            return {
                "page": page_url,
                "assets": local_assets,
                "next_pages": next_pages,
                "js_links": local_js_links,
                "network_links": local_network_links,
                "log": local_log
            }

        # ------------------------------------------------------------------ #
        # initial frontier
        # ------------------------------------------------------------------ #
        frontier: List[str] = []
        for s in seed_urls:
            if not _allowed_by_required_sites(s):
                continue
            if expand_direct:
                frontier.extend(self._expand_direct_seed(s) or [])
            else:
                frontier.append(s)

        for p in self._predict_next_in_sequence(frontier):
            if _allowed_by_required_sites(p):
                frontier.append(p)

        for s in list(frontier):
            parent = self._parent_dir_url(s)
            if parent and _allowed_by_required_sites(parent):
                frontier.append(parent)

        frontier = list(dict.fromkeys(frontier))[:max_pages_total]

        # ------------------------------------------------------------------ #
        # HTTPSSubmanager lifetime (shared pool for the entire run)
        # ------------------------------------------------------------------ #
        async with submanagers.HTTPSSubmanager(
            user_agent="Mozilla/5.0 PromptChat/DirectLinkTracker",
            timeout=timeout,
            retries=int(params.get("http_retries", 2)),
            max_conn_per_host=int(params.get("http_max_conn_per_host", 8)),
            max_total_conn=int(params.get("http_max_total_conn", 0)),
            verify=tls_verify,
            ca_bundle=ca_bundle,
            max_bytes=int(params.get("http_max_bytes", 4_000_000)),
            max_html_chars=int(params.get("http_max_html_chars", 600_000)),
            allow_redirects=bool(params.get("http_allow_redirects", True)),
            enable_cookies=bool(params.get("http_enable_cookies", True)),
            proxy=params.get("proxy") or None,
            proxy_pool=params.get("proxy_pool") or None,
        ) as http:

            current_depth = 0
            while frontier and current_depth <= max_depth and len(visited_pages) < max_pages_total:
                remaining = max_pages_total - len(visited_pages)
                batch: List[str] = []

                for u in frontier:
                    if len(batch) >= remaining:
                        break
                    if u in visited_pages:
                        continue

                    if store and store.is_page_scanned(u):
                        visited_pages.add(u)
                        log.append(f"Skipping page {u} (already scanned in DB)")
                        continue

                    batch.append(u)

                if not batch:
                    break

                results = await asyncio.gather(*[_process_page(http, u, current_depth) for u in batch])
                next_frontier: List[str] = []

                for res in results:
                    visited_pages.add(res["page"])
                    log.extend(res["log"])
                    all_js_links.extend(res["js_links"])
                    all_network_links.extend(res["network_links"])
                    all_react_links.extend(res.get("react_links", []))
                    all_database_links.extend(res.get("database_links", []))
                    all_interaction_links.extend(res.get("interaction_links", []))
                    for a in res["assets"]:
                        u = a.get("url", "")
                        if u and u not in seen_asset_urls:
                            seen_asset_urls.add(u)
                            found_assets.append(a)

                    for nxt in res["next_pages"]:
                        if nxt not in visited_pages:
                            next_frontier.append(nxt)

                current_depth += 1
                frontier = list(dict.fromkeys(next_frontier))[:max_pages_total]

        if pw_needed:
            await self._close_playwright_context(pw_p, pw_browser, pw_context, log)

        # close DB connection (DatabaseSubmanager) at end of run
        if db_sm:
            try:
                db_sm.close()
            except Exception:
                pass
        clean_url_for_matching = unquote(a.get('url','')).lower()
        if keywords:
            for a in found_assets:
                if a.get("onlyfiles"):
                    hay = f"{a.get('text','')} {clean_url_for_matching } {a.get('source','')}"
                    a["score"] = _score_for_keywords(hay)

            found_assets.sort(key=lambda a: a.get("score", 0), reverse=True)

            if found_assets and found_assets[0].get("score", 0) == 0:
                log.append("No keyword hits; falling back to unfiltered ordering.")

        # canonical dedupe (pillows format variants)
        def _pillows_canonical_key(u: str) -> str:
            return re.sub(r"\.(mp3|ogg|wav|flac|m4a)$", "", (u or "").lower())

        deduped: List[Dict[str, Any]] = []
        seen_keys: Set[str] = set()
        for a in found_assets:
            key = _pillows_canonical_key(a.get("url", ""))
            if key in seen_keys:
                continue
            seen_keys.add(key)
            deduped.append(a)
        found_assets = deduped

        if best_n and best_n > 0:
            found_assets = found_assets[:best_n]

        from urllib.parse import urlparse as _urlparse

        if not found_assets:
            base_text = (
                "### DirectLinkTracker: No specific assets found.\n"
                f"Seeded from {len(seed_urls)} direct URLs.\n"
                f"Query: {query_text or '[none]'}\n"
                f"Scanned {len(visited_pages)} pages for extensions: {sorted(list(targets))}.\n"
                f"Keywords used: {keywords}\n"
                f"Required sites: {required_sites or '[none]'}\n"
                f"min_term_overlap: {min_term_overlap}\n"
                f"max_depth: {max_depth}\n"
                f"expand_direct: {expand_direct}\n"
                f"use_database: {use_database} (db_path={db_path if use_database else 'n/a'})\n"
            )
            lines = [base_text]

            if return_all_js_links and all_js_links:
                lines.append("\n### All JS-Gathered Links (debug)\n")
                for jl in all_js_links:
                    host = _urlparse(jl["page"]).netloc if jl.get("page") else "(unknown)"
                    lines.append(f"- **[{jl.get('text') or '(no text)'}]({jl.get('url')})**")
                    lines.append(f"  - *Tag: <{jl.get('tag') or 'a'}> | From page: {host}*")

            if return_network_sniff_links and all_network_links:
                lines.append("\n### All Network-Sniffed Assets (debug)\n")
                for nl in all_network_links:
                    host = _urlparse(nl["page"]).netloc if nl.get("page") else "(unknown)"
                    lines.append(f"- **[{nl.get('text') or '(no text)'}]({nl.get('url')})**")
                    lines.append(
                        f"  - *Tag: <{nl.get('tag', 'network_sniff')}> | From page: {host} | Size: {nl.get('size', '?')}*"
                    )
            if return_react_sniff_links and all_react_links:
                lines.append("\n### React / SPA Sniffed Hits (debug)\n")
                for rh in all_react_links[:100]:
                    kind = rh.get("kind", "nav")
                    route = rh.get("route") or ""
                    url = rh.get("url") or ""
                    lines.append(f"- `{kind}` **{route}** → {url}")

            if return_database_sniff_links and all_database_links:
                lines.append("\n### Database & Persistence Layer Links (debug)\n")
                for dbl in all_database_links[:50]:
                    kind = dbl.get("kind")
                    meta = dbl.get("meta") or {}
                    if kind == "content_link":
                        lines.append(f"- `db_url` ({meta.get('class')}) **{dbl['url']}**")
                    elif kind == "indexeddb_dump":
                        lines.append(f"- `storage` **{meta.get('name')}** stores found")
            if return_interaction_sniff_links and all_interaction_links:
                lines.append("\n### Interactivity & UI Barriers (debug)\n")
                for il in all_interaction_links[:50]:
                    kind = il.get("kind")
                    meta = il.get("meta") or {}
                    if kind == "event_listener":
                        lines.append(f"- `js_event` **{meta.get('nodeName')}** listens for: {meta.get('types')}")
                    elif kind == "overlay_detected":
                        lines.append(
                            f"- `barrier` **{meta.get('tagName')}** covers {meta.get('coverage')} of screen (z-index: {meta.get('zIndex')})")
            return "\n".join(lines), {
                "count": 0,
                "seed_urls": seed_urls,
                "query": query_text,
                "keywords_used": keywords,
                "min_term_overlap": min_term_overlap,
                "required_sites": required_sites,
                "js_links": all_js_links,
                "network_sniff_links": all_network_links,
                "log": log,
                "use_database": use_database,
                "db_path": (db_path if use_database else None),
            }

        lines = [f"### DirectLinkTracker Found {len(found_assets)} Assets"]
        lines.append(
            f"_Mode: {mode} | Query: {query_text or '[none]'} | Seed: {seed_urls[0] if seed_urls else '[none]'} | "
            f"Keywords: {keywords} | min_term_overlap: {min_term_overlap} | "
            f"Required Sites: {required_sites or '[none]'} | max_depth: {max_depth} | "
            f"expand_direct: {expand_direct} | best_n: {best_n} | "
            f"use_database: {use_database} (db_path={db_path if use_database else 'n/a'})_"
        )
        lines.append("")

        for asset in found_assets:
            score = asset.get("score", 0)
            lines.append(f"- **[{asset['text']}]({asset['url']})**" + (f"  *(score={score})*" if keywords else ""))
            lines.append(
                f"  - *Size: {asset['size']} | Status: {asset['status']} | "
                f"Source: {_urlparse(asset['source']).netloc}*"
            )

        if return_all_js_links and all_js_links:
            lines.append("\n### All JS-Gathered Links (debug)\n")
            for jl in all_js_links:
                host = _urlparse(jl["page"]).netloc if jl.get("page") else "(unknown)"
                lines.append(f"- **[{jl.get('text') or '(no text)'}]({jl.get('url')})**")
                lines.append(f"  - *Tag: <{jl.get('tag') or 'a'}> | From page: {host}*")

        if return_network_sniff_links and all_network_links:
            lines.append("\n### All Network-Sniffed Assets (debug)\n")
            for nl in all_network_links:
                host = _urlparse(nl["page"]).netloc if nl.get("page") else "(unknown)"
                lines.append(f"- **[{nl.get('text') or '(no text)'}]({nl.get('url')})**")
                lines.append(
                    f"  - *Tag: <{nl.get('tag', 'network_sniff')}> | From page: {host} | Size: {nl.get('size', '?')}*"
                )
        if return_react_sniff_links and all_react_links:
            lines.append("\n### React / SPA Sniffed Hits (debug)\n")
            for rh in all_react_links[:100]:
                kind = rh.get("kind", "nav")
                route = rh.get("route") or ""
                url = rh.get("url") or ""
                lines.append(f"- `{kind}` **{route}** → {url}")
        if return_database_sniff_links and all_database_links:
            lines.append("\n### Database & Persistence Layer Links (debug)\n")
            for dbl in all_database_links[:50]:
                kind = dbl.get("kind")
                meta = dbl.get("meta") or {}
                if kind == "content_link":
                    lines.append(f"- `db_url` ({meta.get('class')}) **{dbl['url']}**")
                elif kind == "indexeddb_dump":
                    lines.append(f"- `storage` **{meta.get('name')}** stores found")
        if return_interaction_sniff_links and all_interaction_links:

            lines.append("\n### Interactivity & UI Barriers (debug)\n")
            for il in all_interaction_links[:50]:
                kind = il.get("kind")
                meta = il.get("meta") or {}
                if kind == "event_listener":
                    lines.append(f"- `js_event` **{meta.get('nodeName')}** listens for: {meta.get('types')}")
                elif kind == "overlay_detected":
                    lines.append(
                        f"- `barrier` **{meta.get('tagName')}** covers {meta.get('coverage')} of screen (z-index: {meta.get('zIndex')})")
        return "\n".join(lines), {
            "found": len(found_assets),
            "seed_urls": seed_urls,
            "query": query_text,
            "scanned_pages": len(visited_pages),
            "assets": found_assets,
            "keywords_used": keywords,
            "min_term_overlap": min_term_overlap,
            "required_sites": required_sites,
            "expand_direct": expand_direct,
            "best_n": best_n,
            "js_links": all_js_links,
            "network_sniff_links": all_network_links,
            "log": log,
            "use_database": use_database,
            "db_path": (db_path if use_database else None),
        }

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asyncio.run(self._execute_async(payload, params=params))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "urls": ["https://pillows.su/f/5ddab82d178fa5cde9f55823aaa30329"],
            "query": "aphex twin interview pdf",
            "timeout": 6,
            "mode": "docs",
            "extensions": ".pdf,.txt",
            "url_keywords": "",
            "strict_keywords": False,
            "verify": True,
            "tls_verify": True,
            "ca_bundle": None,

            "max_depth": 2,
            "max_pages_total": 200,
            "max_links_per_page": 800,

            "use_js": False,
            "use_network_sniff": False,
            "use_react_sniff": False,
            "use_database_sniff": False,
            "use_interaction_sniff":False,
            "return_react_sniff_links":False,
            "return_all_js_links": False,
            "return_network_sniff_links": False,
            "return_database_sniff_links": False,
            "return_interaction_sniff_links": False,

            "min_term_overlap": 1,
            "site_require": "",

            "use_database": False,
            "db_path": "link_corpus.db",

            "block_resources": False,
            "blocked_resource_types": "image,stylesheet,font",
            "block_domains": True,
            "blocked_domains": "",

            "expand_direct": True,
            "best_n": 50,

            "use_camoufox": False,
            "camoufox_options": {},

            # HTTPSSubmanager optional knobs
            "http_retries": 2,
            "http_max_conn_per_host": 8,
            "http_max_total_conn": 0,
            "http_max_bytes": 4_000_000,
            "http_max_html_chars": 600_000,
            "http_allow_redirects": True,
            "http_enable_cookies": True,
            "proxy": None,
            "proxy_pool": None,
        }


BLOCKS.register("directlinktracker", DirectLinkTrackerBlock)

# ======================= SocketPipe (packet ingest + deep scraping) =======================

@dataclass
class SocketPipeBlock(BaseBlock):
    """
    SocketPipeBlock

    Ingests JSON "packet_event" messages from a local socket and performs
    advanced scraping to feed other blocks.

    Sources:
      - UDP listener ("udp_listen"): external program sends JSON per datagram
      - TCP client  ("tcp_client"): connects to a stream server (JSONL)

    For each run:
      - Reads up to max_packets events (non-blocking / short timeouts).
      - Recursively walks analysis/metadata/summary for text.
      - Extracts:
          • URLs
          • Domains (from URLs + fields like SNI/host/server_name)
          • IP addresses
          • Emails (if present in payload)
          • Keywords / search terms
      - Computes aggregate stats (types, protocols, ports, domains, IPs).
      - Writes into Memory:
          • links_key         (list of {url, source, first_seen})
          • lexicon_key       (top single-word terms)
          • domains_key       (sorted list of domains)
          • ips_key           (sorted list of IPs)
          • search_terms_key  (top multi-word "search-like" phrases)
          • events_key        (raw recent events, truncated)
    """

    _sock: Any = field(default=None, init=False)
    _mode: str = field(default="", init=False)
    _addr: Any = field(default=None, init=False)
    _tcp_buffer: bytes = field(default=b"", init=False)

    # ------------------- basic text helpers -------------------

    @staticmethod
    def _iter_text_fields(obj: Any):
        """Recursively yield all string fields from nested dict/list structures."""
        if isinstance(obj, str):
            yield obj
        elif isinstance(obj, dict):
            for v in obj.values():
                yield from SocketPipeBlock._iter_text_fields(v)
        elif isinstance(obj, (list, tuple, set)):
            for v in obj:
                yield from SocketPipeBlock._iter_text_fields(v)

    @staticmethod
    def _extract_urls(text: str) -> list[str]:
        url_re = re.compile(r"https?://[^\s\"'<>\\)]+", re.IGNORECASE)
        return url_re.findall(text or "")

    @staticmethod
    def _extract_ips(text: str) -> list[str]:
        """
        Very simple IPv4 extractor; doesn't try to validate ranges deeply.
        """
        ip_re = re.compile(r"\b(?:[0-9]{1,3}\.){3}[0-9]{1,3}\b")
        return ip_re.findall(text or "")

    @staticmethod
    def _extract_emails(text: str) -> list[str]:
        email_re = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}", re.IGNORECASE)
        return email_re.findall(text or "")

    @staticmethod
    def _tokenize(text: str) -> list[str]:
        # very simple tokenizer
        tokens = re.findall(r"[A-Za-z0-9][A-Za-z0-9_\-]+", text.lower())
        stopwords = {
            "the", "and", "or", "for", "to", "of", "a", "an", "on", "in", "is",
            "it", "this", "that", "at", "by", "from", "with", "as", "be",
            "are", "was", "were", "not", "no", "yes", "you", "me", "we",
            "they", "he", "she", "them", "his", "her", "our", "your",
            "have", "has", "had", "but", "if", "then", "than", "there",
            "here", "over", "under", "into", "out", "up", "down",
        }
        return [t for t in tokens if len(t) > 2 and t not in stopwords]

    @staticmethod
    def _extract_host_candidates(ev: dict) -> list[str]:
        """
        Pull likely host/domain fields from event (analysis + metadata).
        Looks at common keys: host, hostname, sni, server_name, domain, etc.
        """
        host_keys = {
            "host", "hostname", "server_name", "servername", "sni", "sni_hostname",
            "domain", "query_name", "qname", "target_host",
        }
        hosts: set[str] = set()

        def _walk(obj: Any):
            if isinstance(obj, dict):
                for k, v in obj.items():
                    kl = str(k).lower()
                    if kl in host_keys and isinstance(v, str):
                        hosts.add(v.strip())
                    _walk(v)
            elif isinstance(obj, (list, tuple, set)):
                for v in obj:
                    _walk(v)

        _walk(ev)
        return list(hosts)

    @staticmethod
    def _domain_from_url_or_host(u: str) -> str:
        u = (u or "").strip()
        if not u:
            return ""
        try:
            if u.startswith("http://") or u.startswith("https://"):
                from urllib.parse import urlparse
                netloc = urlparse(u).netloc
            else:
                # treat as bare hostname
                netloc = u
            # Strip port
            host = netloc.split("@")[-1].split(":", 1)[0].lower()
            # cheap public-ish suffix trimming: keep last 2-3 labels
            parts = [p for p in host.split(".") if p]
            if len(parts) >= 3 and len(parts[-1]) <= 3:
                return ".".join(parts[-3:])
            elif len(parts) >= 2:
                return ".".join(parts[-2:])
            else:
                return host
        except Exception:
            return ""

    @staticmethod
    def _looks_like_html(s: str) -> bool:
        if not s:
            return False
        t = s.lstrip().lower()
        # quick/cheap signals
        return (
            "<html" in t
            or "<!doctype" in t
            or "<a " in t
            or "<script" in t
            or "<link" in t
            or "<img" in t
            or ("</" in t and "<" in t)
        )

    @staticmethod
    def _extract_base_url(ev: dict) -> str:
        """
        Best-effort base URL for resolving relative links.
        Looks for common keys like url/request_url/response_url in event.
        Falls back to host candidate -> https://host/
        """
        url_keys = {
            "url", "request_url", "response_url", "page_url", "origin_url", "full_url"
        }
        found = ""

        def _walk(obj: Any):
            nonlocal found
            if found:
                return
            if isinstance(obj, dict):
                for k, v in obj.items():
                    if found:
                        return
                    kl = str(k).lower()
                    if kl in url_keys and isinstance(v, str) and v.startswith(("http://", "https://")):
                        found = v.strip()
                        return
                    _walk(v)
            elif isinstance(obj, (list, tuple, set)):
                for v in obj:
                    _walk(v)

        _walk(ev)

        if found:
            return found

        # fallback: host candidate
        hosts = SocketPipeBlock._extract_host_candidates(ev)
        if hosts:
            h = hosts[0].strip()
            if h:
                # assume https for modern traffic; adjust if your router knows scheme
                if not h.startswith(("http://", "https://")):
                    return f"https://{h}/"
                return h
        return ""

    @staticmethod
    def _extract_links_from_html(html: str, *, base_url: str = "") -> list[str]:
        """
        Extract href/src/action/data-src/srcset/CSS url(...) links from an HTML-ish blob.
        Resolves relative links using base_url when possible.
        """
        if not html:
            return []

        from urllib.parse import urljoin

        out: list[str] = []
        seen: set[str] = set()

        # 1) raw absolute URLs
        for u in SocketPipeBlock._extract_urls(html):
            if u not in seen:
                seen.add(u)
                out.append(u)

        # 2) attribute-style links
        #    capture quoted OR unquoted until whitespace or >
        attr_re = re.compile(
            r"""(?is)\b(?:href|src|action|data-src)\s*=\s*(?:
                    ["']([^"']+)["'] |
                    ([^\s>]+)
                )""",
            re.VERBOSE,
        )

        def _push(raw: str):
            if not raw:
                return
            raw = raw.strip()
            # ignore anchors / javascript / mailto
            low = raw.lower()
            if low.startswith(("#", "javascript:", "mailto:", "data:")):
                return
            # srcset can be "url1 1x, url2 2x"
            if " " in raw and ("," in raw):
                parts = [p.strip().split(" ")[0] for p in raw.split(",") if p.strip()]
            else:
                parts = [raw]

            for p in parts:
                if not p:
                    continue
                if p.startswith(("http://", "https://")):
                    u = p
                elif base_url:
                    u = urljoin(base_url, p)
                else:
                    # no base; keep only if it looks like a domain-ish path
                    u = p
                if u and u not in seen and u.startswith(("http://", "https://")):
                    seen.add(u)
                    out.append(u)

        for m in attr_re.finditer(html):
            _push(m.group(1) or m.group(2) or "")

        # 3) srcset explicitly (common)
        srcset_re = re.compile(r"""(?is)\bsrcset\s*=\s*["']([^"']+)["']""")
        for m in srcset_re.finditer(html):
            _push(m.group(1) or "")

        # 4) CSS url(...)
        css_url_re = re.compile(r"""(?is)\burl\(\s*['"]?([^'")]+)['"]?\s*\)""")
        for m in css_url_re.finditer(html):
            _push(m.group(1) or "")

        return out
    # ------------------- socket setup -------------------

    def _ensure_socket(self, host: str, port: int, mode: str, recv_timeout: float, log: list[str]) -> None:
        """
        Lazily create/recreate socket if needed.

        mode:
          - "udp_listen": bind UDP socket to (host, port) and recvfrom()
          - "tcp_client": connect to TCP server at (host, port) and recv()
        """
        import socket

        if (
            self._sock is not None
            and self._mode == mode
            and self._addr == (host, port)
        ):
            self._sock.settimeout(recv_timeout)
            return

        # Recreate
        if self._sock is not None:
            try:
                self._sock.close()
            except Exception:
                pass
            self._sock = None

        try:
            if mode == "udp_listen":
                s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                s.bind((host, port))
                s.settimeout(recv_timeout)
                self._sock = s
                self._mode = mode
                self._addr = (host, port)
                log.append(f"[SocketPipe] Bound UDP listener on {host}:{port}")
            elif mode == "tcp_client":
                s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                s.settimeout(recv_timeout)
                s.connect((host, port))
                self._sock = s
                self._mode = mode
                self._addr = (host, port)
                log.append(f"[SocketPipe] Connected TCP client to {host}:{port}")
            else:
                log.append(f"[SocketPipe] Unknown mode={mode!r}; no socket created.")
        except Exception as e:
            log.append(f"[SocketPipe] Socket setup failed: {e}")
            self._sock = None

    # ------------------- event reading -------------------

    def _read_events(
        self,
        host: str,
        port: int,
        mode: str,
        recv_timeout: float,
        total_timeout: float,
        max_packets: int,
        log: list[str],
    ) -> list[dict]:
        import socket
        import time as _time
        import json as _json

        self._ensure_socket(host, port, mode, recv_timeout, log)
        if self._sock is None:
            return []

        events: list[dict] = []
        start = _time.time()

        def _try_parse_json_line(line_bytes: bytes):
            try:
                line = line_bytes.decode("utf-8", errors="ignore").strip()
                if not line:
                    return None
                obj = _json.loads(line)
                if isinstance(obj, dict):
                    return obj
                return None
            except Exception:
                return None

        while len(events) < max_packets and (_time.time() - start) < total_timeout:
            try:
                if mode == "udp_listen":
                    data, addr = self._sock.recvfrom(65535)
                    if not data:
                        break
                    log.append(f"[SocketPipe] UDP packet from {addr[0]}:{addr[1]} ({len(data)} bytes)")

                    for part in data.splitlines():
                        obj = _try_parse_json_line(part)
                        if obj is not None:
                            events.append(obj)
                            if len(events) >= max_packets:
                                break
                elif mode == "tcp_client":
                    chunk = self._sock.recv(65535)
                    if not chunk:
                        log.append("[SocketPipe] TCP peer closed connection.")
                        break
                    self._tcp_buffer += chunk
                    while b"\n" in self._tcp_buffer:
                        line, self._tcp_buffer = self._tcp_buffer.split(b"\n", 1)
                        obj = _try_parse_json_line(line)
                        if obj is not None:
                            events.append(obj)
                            if len(events) >= max_packets:
                                break
                else:
                    break

            except socket.timeout:
                # normal: no more data within recv_timeout
                break
            except BlockingIOError:
                break
            except Exception as e:
                log.append(f"[SocketPipe] Error receiving data: {e}")
                break

        return events

    # ------------------- advanced event summary -------------------

    @staticmethod
    def _guess_protocol(ev: dict) -> str:
        """
        Try to guess a "protocol" label from analysis/metadata fields.
        """
        candidates = []

        def _walk(obj: Any):
            if isinstance(obj, dict):
                for k, v in obj.items():
                    kl = str(k).lower()
                    if kl in {"protocol", "proto", "l7", "l4", "transport", "app_proto"} and isinstance(v, str):
                        candidates.append(v.lower())
                    _walk(v)
            elif isinstance(obj, (list, tuple, set)):
                for v in obj:
                    _walk(v)

        _walk(ev)
        if candidates:
            # prefer first but normalize a bit
            c = candidates[0]
            if "tls" in c:
                return "tls"
            if "http" in c:
                return "http"
            if "dns" in c:
                return "dns"
            if "quic" in c:
                return "quic"
            if "tcp" in c:
                return "tcp"
            if "udp" in c:
                return "udp"
            return c
        return "unknown"

    @staticmethod
    def _guess_ports(ev: dict) -> tuple[str, str]:
        """
        Try to find source/dest port fields from event.
        """
        sport_keys = {"sport", "src_port", "source_port", "client_port"}
        dport_keys = {"dport", "dst_port", "destination_port", "server_port"}
        sport = dport = ""

        def _walk(obj: Any):
            nonlocal sport, dport
            if isinstance(obj, dict):
                for k, v in obj.items():
                    kl = str(k).lower()
                    if isinstance(v, (str, int)):
                        val = str(v)
                        if not sport and kl in sport_keys:
                            sport = val
                        if not dport and kl in dport_keys:
                            dport = val
                    _walk(v)
            elif isinstance(obj, (list, tuple, set)):
                for v in obj:
                    _walk(v)

        _walk(ev)
        return sport, dport

    @staticmethod
    def _build_event_summary(ev: dict) -> str:
        ev_type = ev.get("type", "event")
        summary = ev.get("summary", "") or ""
        proto = SocketPipeBlock._guess_protocol(ev)
        hosts = SocketPipeBlock._extract_host_candidates(ev)
        sport, dport = SocketPipeBlock._guess_ports(ev)

        host_str = hosts[0] if hosts else ""
        parts = [ev_type]
        if proto and proto != "unknown":
            parts.append(proto)
        if host_str:
            parts.append(f"host={host_str}")
        if dport:
            parts.append(f"dport={dport}")
        if sport:
            parts.append(f"sport={sport}")
        if summary:
            parts.append(f"summary={summary[:80]}")

        return " | ".join(parts)

    # ------------------- execute -------------------

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import time
        from collections import Counter

        host = str(params.get("host", "127.0.0.1"))
        port = int(params.get("port", 9999))
        mode = str(params.get("mode", "udp_listen")).lower()  # udp_listen | tcp_client

        recv_timeout = float(params.get("recv_timeout", 0.25))  # per recv
        total_timeout = float(params.get("total_timeout", 1.0))  # whole block
        max_packets = int(params.get("max_packets", 64))

        # Memory keys
        links_key = str(params.get("links_key", "socketpipe_links"))
        lexicon_key = str(params.get("lexicon_key", "socketpipe_lexicon"))
        domains_key = str(params.get("domains_key", "socketpipe_domains"))
        ips_key = str(params.get("ips_key", "socketpipe_ips"))
        search_terms_key = str(params.get("search_terms_key", "socketpipe_search_terms"))
        events_key = str(params.get("events_key", "socketpipe_last_events"))

        max_urls_return = int(params.get("max_urls_return", 32))
        max_lexicon_terms = int(params.get("max_lexicon_terms", 64))
        max_domains_terms = int(params.get("max_domains_terms", 64))
        max_ips_terms = int(params.get("max_ips_terms", 64))
        max_search_terms = int(params.get("max_search_terms", 32))
        max_events_store = int(params.get("max_events_store", 128))

        log: list[str] = []

        events = self._read_events(
            host=host,
            port=port,
            mode=mode,
            recv_timeout=recv_timeout,
            total_timeout=total_timeout,
            max_packets=max_packets,
            log=log,
        )

        if not events:
            out = (
                f"### 📡 SocketPipe: No events received\n"
                f"_Mode: {mode} | Host: {host} | Port: {port} | "
                f"max_packets={max_packets} | total_timeout={total_timeout:.2f}s_\n"
            )
            if log:
                out += "\n### Log\n" + "\n".join(log)
            return out, {
                "count": 0,
                "host": host,
                "port": port,
                "mode": mode,
                "log": log,
            }

        # ---- deep scrape: collect text, URLs, IPs, emails, hosts, protocols ----
        all_text_chunks: list[str] = []
        all_urls_set: set[str] = set()
        all_ips_set: set[str] = set()
        all_emails_set: set[str] = set()
        all_domains_set: set[str] = set()
        type_counter: Counter = Counter()
        proto_counter: Counter = Counter()
        dport_counter: Counter = Counter()

        for ev in events:
            if not isinstance(ev, dict):
                continue

            ev_type = ev.get("type", "event")
            type_counter[ev_type] += 1

            proto = self._guess_protocol(ev)
            proto_counter[proto] += 1

            sport, dport = self._guess_ports(ev)
            if dport:
                dport_counter[dport] += 1

            # Prefer analysis/metadata/summary if present
            analysis = ev.get("analysis")
            metadata = ev.get("metadata")
            summary = ev.get("summary", "")

            # Host/domain fields directly from structured data
            host_candidates = self._extract_host_candidates(ev)
            for h in host_candidates:
                d = self._domain_from_url_or_host(h)
                if d:
                    all_domains_set.add(d)

            # Walk text fields
            base_url = self._extract_base_url(ev)

            for t in self._iter_text_fields({"analysis": analysis, "metadata": metadata, "summary": summary}):
                if not t:
                    continue
                all_text_chunks.append(t)

                # URLs (plain text)
                for u in self._extract_urls(t):
                    all_urls_set.add(u)
                    d = self._domain_from_url_or_host(u)
                    if d:
                        all_domains_set.add(d)

                # HTML blob link scraping (NEW)
                if self._looks_like_html(t):
                    for u in self._extract_links_from_html(t, base_url=base_url):
                        all_urls_set.add(u)
                        d = self._domain_from_url_or_host(u)
                        if d:
                            all_domains_set.add(d)

                # IPs
                for ip in self._extract_ips(t):
                    all_ips_set.add(ip)

                # Emails
                for em in self._extract_emails(t):
                    all_emails_set.add(em)
        all_text = " ".join(all_text_chunks)
        tokens = self._tokenize(all_text)
        word_freq = Counter(tokens)
        top_terms = [w for (w, _) in word_freq.most_common(max_lexicon_terms)]

        # --- "search terms": multi-word ngrams that look like search queries ---
        search_terms: list[str] = []
        if all_text_chunks:
            # naive: take sentences that contain spaces and some of our top terms
            import re as _re
            sent_split = _re.split(r"[\n\r]+|(?<=[.!?])\s+", all_text)
            candidates = []
            for s in sent_split:
                s = s.strip()
                if not s:
                    continue
                if len(s) < 12 or s.count(" ") < 2:
                    continue
                # Rough heuristic: must contain at least 1 top term
                lower = s.lower()
                if any(t in lower for t in top_terms[:10]):
                    candidates.append(s)
            # rank by length and occurrence of top terms
            def _score(s: str) -> int:
                base = len(s)
                lower = s.lower()
                hit = sum(1 for t in top_terms[:10] if t in lower)
                return hit * 1000 + base

            ranked = sorted(candidates, key=_score, reverse=True)
            seen = set()
            for s in ranked:
                if s in seen:
                    continue
                seen.add(s)
                search_terms.append(s[:200])
                if len(search_terms) >= max_search_terms:
                    break

        # ---- write to Memory for other blocks ----
        try:
            store = Memory.load()
            now_ts = time.time()

            # Links: merge with existing list, keep deduped & bounded
            existing_links = store.get(links_key)
            if isinstance(existing_links, list):
                existing_urls = {str(x.get("url")) for x in existing_links if isinstance(x, dict) and x.get("url")}
            else:
                existing_links = []
                existing_urls = set()

            new_link_objs = []
            for u in all_urls_set:
                if u in existing_urls:
                    continue
                new_link_objs.append(
                    {
                        "url": u,
                        "source": "socketpipe",
                        "first_seen": now_ts,
                    }
                )

            combined_links = existing_links + new_link_objs
            max_links_store = int(params.get("max_links_store", 4096))
            if max_links_store > 0 and len(combined_links) > max_links_store:
                combined_links = combined_links[-max_links_store:]
            store[links_key] = combined_links

            # Lexicon
            store[lexicon_key] = top_terms

            # Domains
            domains_sorted = sorted(all_domains_set)
            if max_domains_terms > 0:
                domains_sorted = domains_sorted[:max_domains_terms]
            store[domains_key] = domains_sorted

            # IPs
            ips_sorted = sorted(all_ips_set)
            if max_ips_terms > 0:
                ips_sorted = ips_sorted[:max_ips_terms]
            store[ips_key] = ips_sorted

            # Search-like terms
            store[search_terms_key] = search_terms

            # Last events (truncated for debug)
            if max_events_store > 0:
                if len(events) > max_events_store:
                    store[events_key] = events[-max_events_store:]
                else:
                    store[events_key] = events

            Memory.save(store)

            log.append(
                f"[SocketPipe] Stored {len(new_link_objs)} new links, "
                f"{len(top_terms)} lexicon terms, {len(domains_sorted)} domains, "
                f"{len(ips_sorted)} IPs, {len(search_terms)} search_terms, {len(events)} events."
            )
        except Exception as e:
            log.append(f"[SocketPipe] Memory save failed: {e}")

        # ---- human-readable markdown output with rich log ----
        urls_list = sorted(all_urls_set)
        shown_urls = urls_list[:max_urls_return]
        domains_list = sorted(all_domains_set)
        ips_list = sorted(all_ips_set)

        # Top stats
        top_types = ", ".join(f"{k}:{v}" for k, v in type_counter.most_common(5))
        top_protos = ", ".join(f"{k}:{v}" for k, v in proto_counter.most_common(5))
        top_ports = ", ".join(f"{k}:{v}" for k, v in dport_counter.most_common(5))

        # Sample event summaries
        sample_summaries = [
            self._build_event_summary(ev)
            for ev in events[: min(5, len(events))]
        ]

        lines: list[str] = []
        lines.append(f"### 📡 SocketPipe Ingest")
        lines.append(
            f"_Mode: {mode} | Host: {host} | Port: {port} | "
            f"Events: {len(events)} | Unique URLs: {len(all_urls_set)} | "
            f"Domains: {len(all_domains_set)} | IPs: {len(all_ips_set)}_"
        )
        lines.append("")
        lines.append(f"**Types:** {top_types or '(none)'}")
        lines.append(f"**Protocols (guessed):** {top_protos or '(none)'}")
        lines.append(f"**Dst Ports:** {top_ports or '(none)'}")
        lines.append("")

        if domains_list:
            lines.append("**Top domains:**")
            for d in domains_list[:10]:
                lines.append(f"- {d}")
            if len(domains_list) > 10:
                lines.append(f"... (+{len(domains_list) - 10} more)")
            lines.append("")

        if ips_list:
            lines.append("**Top IPs:**")
            for ip in ips_list[:10]:
                lines.append(f"- {ip}")
            if len(ips_list) > 10:
                lines.append(f"... (+{len(ips_list) - 10} more)")
            lines.append("")

        if shown_urls:
            lines.append("**Sample URLs:**")
            for u in shown_urls:
                lines.append(f"- {u}")
            if len(urls_list) > len(shown_urls):
                lines.append(f"... (+{len(urls_list) - len(shown_urls)} more)")
            lines.append("")

        if search_terms:
            lines.append("**Search-like strings:**")
            for s in search_terms[:5]:
                lines.append(f"- {s}")
            if len(search_terms) > 5:
                lines.append(f"... (+{len(search_terms) - 5} more)")
            lines.append("")

        if sample_summaries:
            lines.append("**Sample event summaries:**")
            for s in sample_summaries:
                lines.append(f"- {s}")
            lines.append("")

        if all_emails_set:
            emails_list = sorted(all_emails_set)
            lines.append("**Emails seen (first few):**")
            for em in emails_list[:5]:
                lines.append(f"- {em}")
            if len(emails_list) > 5:
                lines.append(f"... (+{len(emails_list) - 5} more)")
            lines.append("")

        if log:
            lines.append("### Internal Log")
            lines.extend(log)

        out = "\n".join(lines)

        meta = {
            "count": len(events),
            "host": host,
            "port": port,
            "mode": mode,
            "unique_urls": len(all_urls_set),
            "urls_sample": shown_urls,
            "domains": domains_list[:max_domains_terms],
            "ips": ips_list[:max_ips_terms],
            "lexicon_terms": top_terms,
            "search_terms": search_terms,
            "links_key": links_key,
            "lexicon_key": lexicon_key,
            "domains_key": domains_key,
            "ips_key": ips_key,
            "search_terms_key": search_terms_key,
            "events_key": events_key,
            "type_counts": dict(type_counter),
            "proto_counts": dict(proto_counter),
            "dport_counts": dict(dport_counter),
            "log": log,
        }
        return out, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "host": "127.0.0.1",
            "port": 9999,
            "mode": "udp_listen",   # "udp_listen" | "tcp_client"
            "recv_timeout": 0.25,   # per recv() timeout
            "total_timeout": 1.0,   # max time spent in block
            "max_packets": 64,

            # Memory keys for other blocks
            "links_key": "socketpipe_links",
            "lexicon_key": "socketpipe_lexicon",
            "domains_key": "socketpipe_domains",
            "ips_key": "socketpipe_ips",
            "search_terms_key": "socketpipe_search_terms",
            "events_key": "socketpipe_last_events",

            # Storage / output bounds
            "max_urls_return": 32,
            "max_lexicon_terms": 64,
            "max_domains_terms": 64,
            "max_ips_terms": 64,
            "max_search_terms": 32,
            "max_links_store": 4096,
            "max_events_store": 128,
        }


BLOCKS.register("socketpipe", SocketPipeBlock)

# ======================= PageTrackerBlock ==================================

@dataclass
class PageTrackerBlock(BaseBlock):
    """
    Async, search + crawl + similar-page finder.

    Similar to LinkTrackerBlock, but instead of extracting file assets,
    this block focuses on discovering pages (URLs) that look relevant
    to the query and/or lexicon terms.

      • Supports DuckDuckGo / Google CSE / SearXNG / sites / database engines.
      • Integrates with DatabaseSubmanager + LinkTrackerStore for seeds.
      • Uses JS / Network / Runtime sniffers via Playwright/Camoufox.
      • Returns a ranked list of pages (URLs + titles + hosts).
    """

    JUNK_FILENAME_KEYWORDS = {
        "sprite", "icon", "favicon", "logo", "tracking", "pixel", "blank", "placeholder",
    }

    IGNORED_EXTENSIONS = {
        ".css", ".js", ".json", ".xml", ".svg", ".png", ".jpg", ".jpeg",
        ".gif", ".ico", ".woff", ".woff2", ".ttf", ".eot", ".map"
    }

    _URL_RE = re.compile(r"https?://[^\s\"'<>\\)]+", re.IGNORECASE)

    MEGA_HOSTS = {"mega.nz", "www.mega.nz", "mega.co.nz", "www.mega.co.nz"}
    MEGA_PATH_MARKERS = ("/file/", "/folder/", "/embed/", "/#F!", "/#!")
    MEGA_QUERY_MARKERS = ("mega.nz",)  # fallback

    def __post_init__(self):
        # Store/submanager are initialized per-run when use_database=True
        self.db: Optional[submanagers.DatabaseSubmanager] = None
        self.store: Optional[PageTrackerStore] = None
        self.js_sniffer = submanagers.JSSniffer(
            submanagers.JSSniffer.Config(
                enable_auto_scroll=True,
                max_scroll_steps=40,
                scroll_step_delay_ms=500,
            )
        )
        self.network_sniffer = submanagers.NetworkSniffer(
            submanagers.NetworkSniffer.Config(
                enable_auto_scroll=True,
                max_scroll_steps=40,
                scroll_step_delay_ms=500,
            )
        )
        self.runtime_sniffer = submanagers.RuntimeSniffer(
            submanagers.RuntimeSniffer.Config()
        )
        self.react_sniffer = submanagers.ReactSniffer(
            submanagers.ReactSniffer.Config(
                hook_history_api=True,
                hook_link_clicks=True,
                inspect_react_devtools_hook=True,
            )
        )
        self.database_sniffer = submanagers.DatabaseSniffer(
            submanagers.DatabaseSniffer.Config(
                enable_indexeddb_dump=True,
                enable_backend_fingerprint=True,
                enable_html_link_scan=True,
                enable_backend_link_scan=True
            )
        )
        self.interaction_sniffer = submanagers.InteractionSniffer(
            submanagers.InteractionSniffer.Config(
                enable_cdp_listeners=True,
                enable_overlay_detection=True,
                enable_form_extraction=True
            )
        )
    # ------------------------------------------------------------------ #
    # Database lifecycle (Submanager + Store)
    # ------------------------------------------------------------------ #
    def _initialize_database(self, db_path: str, logger=None) -> None:
        """
        Create and open DBSubmanager + LinkTrackerStore, install schema.
        Idempotent.
        """
        if self.db and self.store:
            return

        cfg = submanagers.DatabaseConfig(path=str(db_path or "link_corpus.db"))
        self.db = submanagers.DatabaseSubmanager(cfg, logger=logger)
        self.db.open()

        self.store = PageTrackerStore(db=self.db)
        self.store.ensure_schema()
    # ------------------------------------------------------------------ #
    # URL helpers
    # ------------------------------------------------------------------ #
    def _is_mega_link(self, u: str) -> bool:
        try:
            pu = urlparse(u)
            host = (pu.netloc or "").lower().split(":")[0]
            path = (pu.path or "").lower()
            frag = (pu.fragment or "").lower()
            full_low = u.lower()

            if host in self.MEGA_HOSTS:
                if any(m in path for m in self.MEGA_PATH_MARKERS):
                    return True
                if frag.startswith("f!") or frag.startswith("!") or "file/" in frag or "folder/" in frag:
                    return True
                return True
            if "mega.nz/#" in full_low or "mega.co.nz/#" in full_low:
                return True

            return False
        except Exception:
            return False

    # ------------------------------------------------------------------ #
    # Search engines
    # ------------------------------------------------------------------ #
    async def _search_searxng(
        self,
        q: str,
        max_results: int,
        timeout: float,
        base_url: Optional[str] = None,
        page_limit: int = 1,
    ) -> List[str]:
        """
        Query a SearXNG instance and return a list of result URLs.

        - Uses ?format=json
        - Respects max_results and page_limit
        - base_url can be passed via params['searxng_url'] or SEARXNG_URL env var.
        """
        import os, json

        # Where is SearXNG?
        base_url = (
            base_url
            or os.environ.get("SEARXNG_URL")
            or "http://127.0.0.1:8080"
        ).rstrip("/")

        search_url = base_url + "/search"

        max_results = max(1, min(int(max_results), 256))
        page_limit = max(1, min(int(page_limit), 5))

        out: List[str] = []
        did_dump_debug = False

        try:
            async with aiohttp.ClientSession() as session:
                for page_idx in range(page_limit):
                    if len(out) >= max_results:
                        break

                    # SearXNG pagination: 'pageno' is 1-based
                    params = {
                        "q": q,
                        "format": "json",
                        "pageno": str(page_idx + 1),
                    }

                    text = ""
                    status = None

                    try:
                        async with session.get(
                            search_url,
                            params=params,
                            timeout=aiohttp.ClientTimeout(total=timeout),
                        ) as resp:
                            status = resp.status
                            text = await resp.text()

                            # Classic misconfig case: JSON disabled -> 403 HTML
                            if status == 403:
                                if not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    DEBUG_LOGGER.log_message(
                                        f"[PageTracker][SearXNG][debug] HTTP 403 "
                                        f"query={q!r} pageno={page_idx + 1}. Body preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            if status != 200:
                                if not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    DEBUG_LOGGER.log_message(
                                        f"[PageTracker][SearXNG][debug] HTTP {status} "
                                        f"query={q!r} pageno={page_idx + 1}. Body preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            try:
                                data = json.loads(text)
                            except json.JSONDecodeError as e:
                                DEBUG_LOGGER.log_message(
                                    f"[PageTracker][SearXNG] JSON decode error: {e}"
                                )
                                if not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    DEBUG_LOGGER.log_message(
                                        f"[PageTracker][SearXNG][debug] Bad JSON preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            results = data.get("results") or []
                            if not results:
                                # No more pages.
                                break

                            for item in results:
                                u = item.get("url")
                                if u:
                                    out.append(u)
                                    if len(out) >= max_results:
                                        break

                    except aiohttp.ClientError as e:
                        DEBUG_LOGGER.log_message(
                            f"[PageTracker][SearXNG] AIOHTTP error: {e}"
                        )
                        if not did_dump_debug and text:
                            preview = text[:1500].replace("\n", " ")
                            DEBUG_LOGGER.log_message(
                                f"[PageTracker][SearXNG][debug] ClientError body preview: {preview}"
                            )
                            did_dump_debug = True
                        break

        except Exception as e:
            DEBUG_LOGGER.log_message(
                f"[PageTracker][SearXNG] General error: {e}"
            )

        return out[:max_results]

    async def _search_duckduckgo(
        self,
        q: str,
        max_results: int,
        ua: str,
        timeout: float,
        page_limit: int = 1,
        per_page: int = 50,
    ) -> List[str]:
        import random

        pages: List[str] = []
        seen_urls: set[str] = set()
        did_dump_debug = False

        real_ua = (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/115.0.0.0 Safari/537.36"
        )

        headers = {
            "User-Agent": real_ua,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
            "Accept-Language": "en-US,en;q=0.9",
            "Accept-Encoding": "gzip, deflate, br",
            "Referer": "https://duckduckgo.com/",
            "Origin": "https://duckduckgo.com",
            "DNT": "1",
            "Upgrade-Insecure-Requests": "1",
            "Sec-Fetch-Site": "same-origin",
            "Sec-Fetch-Mode": "navigate",
            "Sec-Fetch-Dest": "document",
        }

        max_results = max(1, min(int(max_results), 256))
        page_limit = max(1, min(int(page_limit), 5))
        base_url = "https://html.duckduckgo.com/html/"

        try:
            async with aiohttp.ClientSession(headers=headers) as session:
                for page_idx in range(page_limit):
                    if len(pages) >= max_results:
                        break

                    if page_idx > 0:
                        st = random.uniform(2.0, 5.0)
                        DEBUG_LOGGER.log_message(
                            f"[PageTracker] Sleeping {st:.2f}s between search pages..."
                        )
                        await asyncio.sleep(st)

                    offset = page_idx * 30
                    text = ""
                    status = None
                    final_url = base_url

                    try:
                        data = {"q": q, "s": str(offset), "dc": str(offset)}
                        async with session.post(
                            base_url,
                            data=data,
                            timeout=aiohttp.ClientTimeout(total=timeout),
                        ) as resp:
                            status = resp.status
                            final_url = str(resp.url)

                            if status == 403:
                                DEBUG_LOGGER.log_message(
                                    f"[PageTracker] 403 Forbidden on page {page_idx}."
                                )
                                if not pages and not did_dump_debug:
                                    text = await resp.text()
                                    preview = text[:2000].replace("\n", " ")
                                    DEBUG_LOGGER.log_message(
                                        f"[PageTracker][DDG][debug] 403 body preview: {preview}"
                                    )
                                    did_dump_debug = True
                                return pages

                            resp.raise_for_status()
                            text = await resp.text()

                    except Exception as e:
                        DEBUG_LOGGER.log_message(
                            f"[PageTracker] DuckDuckGo request failed (page {page_idx}): {e}"
                        )
                        if not pages and text and not did_dump_debug:
                            preview = text[:2000].replace("\n", " ")
                            DEBUG_LOGGER.log_message(
                                f"[PageTracker][DDG][debug] Failed page HTML preview: {preview}"
                            )
                            did_dump_debug = True
                        break

                    if "Unfortunately, bots use DuckDuckGo too." in text:
                        DEBUG_LOGGER.log_message(
                            "[PageTracker] Bot detected by DDG."
                        )
                        if not pages and not did_dump_debug:
                            preview = text[:2000].replace("\n", " ")
                            DEBUG_LOGGER.log_message(
                                f"[PageTracker][DDG][debug] Bot wall preview: {preview}"
                            )
                            did_dump_debug = True
                        break

                    soup = BeautifulSoup(text, "html.parser")
                    found_new = False

                    for a in soup.select("a.result__a"):
                        if len(pages) >= max_results:
                            break
                        href = a.get("href")
                        if not href:
                            continue
                        if "uddg=" in href:
                            try:
                                href = unquote(
                                    href.split("uddg=", 1)[1].split("&", 1)[0]
                                )
                            except Exception:
                                pass

                        if href.startswith("http") and href not in seen_urls:
                            seen_urls.add(href)
                            pages.append(href)
                            found_new = True

                    if not found_new and not pages and not did_dump_debug:
                        preview = text[:2000].replace("\n", " ")
                        DEBUG_LOGGER.log_message(
                            f"[PageTracker][DDG][debug] No results on page {page_idx} for query={q!r} "
                            f"(status={status}, url={final_url}). HTML preview: {preview}"
                        )
                        did_dump_debug = True

                    if not found_new:
                        break

        except Exception as e:
            DEBUG_LOGGER.log_message(
                f"[PageTracker] DDG outer error: {e}"
            )

        return pages[:max_results]

    async def _search_google_cse(
        self,
        q: str,
        n: int,
        timeout: float,
        page_limit: int = 1,
    ) -> List[str]:
        import os, json

        cx = os.environ.get("GOOGLE_CSE_ID")
        key = os.environ.get("GOOGLE_API_KEY")
        if not (cx and key):
            DEBUG_LOGGER.log_message(
                "[PageTracker][GoogleCSE] Missing GOOGLE_CSE_ID or GOOGLE_API_KEY env vars."
            )
            return []

        max_total = max(1, min(int(n), 100))
        per_page = min(10, max_total)
        max_pages_by_n = (max_total + per_page - 1) // per_page
        pages_to_fetch = max(1, min(int(page_limit) or 1, max_pages_by_n))

        out: List[str] = []
        did_dump_debug = False

        try:
            async with aiohttp.ClientSession() as session:
                for page_idx in range(pages_to_fetch):
                    if len(out) >= max_total:
                        break

                    start = 1 + page_idx * per_page
                    if start > 100:
                        break

                    text = ""
                    status = None

                    try:
                        async with session.get(
                            "https://www.googleapis.com/customsearch/v1",
                            params={
                                "q": q,
                                "cx": cx,
                                "key": key,
                                "num": per_page,
                                "start": start,
                            },
                            timeout=aiohttp.ClientTimeout(total=timeout),
                        ) as resp:
                            status = resp.status
                            text = await resp.text()

                            if status != 200:
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    DEBUG_LOGGER.log_message(
                                        f"[PageTracker][GoogleCSE][debug] HTTP {status} "
                                        f"query={q!r} start={start}. Body preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            try:
                                data = json.loads(text)
                            except json.JSONDecodeError as e:
                                DEBUG_LOGGER.log_message(
                                    f"[PageTracker][GoogleCSE] JSON decode error: {e}"
                                )
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    DEBUG_LOGGER.log_message(
                                        f"[PageTracker][GoogleCSE][debug] Bad JSON preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            err_obj = data.get("error")
                            if err_obj:
                                msg = err_obj.get("message") or "Unknown CSE error"
                                reason = ""
                                errors = err_obj.get("errors") or []
                                if errors and isinstance(errors, list):
                                    reason = errors[0].get("reason") or ""
                                DEBUG_LOGGER.log_message(
                                    f"[PageTracker][GoogleCSE] API error for query={q!r}, "
                                    f"start={start}: {msg} ({reason})"
                                )
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    DEBUG_LOGGER.log_message(
                                        f"[PageTracker][GoogleCSE][debug] Error JSON preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            items = data.get("items") or []
                            if not items:
                                DEBUG_LOGGER.log_message(
                                    f"[PageTracker][GoogleCSE] No items for query={q!r}, "
                                    f"start={start}. Stopping pagination."
                                )
                                if not out and not did_dump_debug:
                                    preview = text[:1500].replace("\n", " ")
                                    DEBUG_LOGGER.log_message(
                                        f"[PageTracker][GoogleCSE][debug] Empty items JSON preview: {preview}"
                                    )
                                    did_dump_debug = True
                                break

                            for item in items:
                                u = item.get("link")
                                if u:
                                    out.append(u)
                                    if len(out) >= max_total:
                                        break

                    except aiohttp.ClientError as e:
                        DEBUG_LOGGER.log_message(
                            f"[PageTracker][GoogleCSE] AIOHTTP error: {e}"
                        )
                        if not out and text and not did_dump_debug:
                            preview = text[:1500].replace("\n", " ")
                            DEBUG_LOGGER.log_message(
                                f"[PageTracker][GoogleCSE][debug] ClientError body preview: {preview}"
                            )
                            did_dump_debug = True
                        break

        except Exception as e:
            DEBUG_LOGGER.log_message(
                f"[PageTracker][GoogleCSE] General error: {e}"
            )

        return out

    # ------------------------------------------------------------------ #
    # Sitemap helpers
    # ------------------------------------------------------------------ #
    def _looks_like_sitemap(self, url: str) -> bool:
        u = url.lower()
        return any(
            u.endswith(x)
            for x in [".xml", ".xml.gz", "sitemap", "sitemap.xml", "sitemap_index.xml"]
        )

    def _decompress_if_needed(self, url: str, raw: bytes) -> str:
        if not raw:
            return ""
        if url.lower().endswith(".gz"):
            try:
                raw = gzip.decompress(raw)
            except Exception:
                return ""
        try:
            return raw.decode("utf-8", errors="ignore")
        except Exception:
            return ""

    def _parse_sitemap_any(self, xml_text: str) -> tuple[list[str], list[str]]:
        if not xml_text.strip():
            return [], []
        try:
            root = ET.fromstring(xml_text)
        except Exception:
            return [], []

        ns = ""
        if root.tag.startswith("{"):
            ns = root.tag.split("}", 1)[0] + "}"

        sitemap_urls = []
        page_urls = []

        if root.tag.endswith("sitemapindex"):
            for sm in root.findall(f".//{ns}sitemap/{ns}loc"):
                if sm.text and sm.text.strip().startswith("http"):
                    sitemap_urls.append(sm.text.strip())

        if root.tag.endswith("urlset"):
            for loc in root.findall(f".//{ns}url/{ns}loc"):
                if loc.text and loc.text.strip().startswith("http"):
                    page_urls.append(loc.text.strip())

        return sitemap_urls, page_urls

    # ------------------------------------------------------------------ #
    # Scoring / pagination helpers
    # ------------------------------------------------------------------ #
    def _score_site_url(self, u: str, keywords: list[str], targets: set[str]) -> int:
        path = urlparse(u).path.lower()
        score = 0

        for tok, w in [
            ("/details/", 8),
            ("/item/", 6),
            ("/watch/", 4),
            ("/download/", 9),
            ("/track/", 4),
            ("/file/", 4),
            ("/audio/", 3),
            ("/video/", 3),
            ("/docs/", 2),
        ]:
            if tok in path:
                score += w

        for tok, w in [
            ("/search", -6),
            ("/tag/", -3),
            ("/category/", -3),
            ("/browse", -3),
            ("/archives", -2),
        ]:
            if tok in path:
                score += w

        if any(path.endswith(ext) for ext in targets):
            score += 10

        low = u.lower().replace("%20", " ")
        score += sum(2 for k in keywords if k and k in low)

        return score

    def _extract_next_page_links(self, soup, base_url: str) -> list[str]:
        out = []
        for a in soup.select(
            "a[rel=next], a.next, a:-soup-contains('Next'), a:-soup-contains('Older')"
        ):
            href = a.get("href")
            if href:
                out.append(urljoin(base_url, href))
        return out[:3]

    def _extract_internal_result_links(
        self, soup, base_url: str, site_host: str
    ) -> list[str]:
        out = []
        containers = soup.select(
            "article a[href], .result a[href], .search-result a[href], "
            ".item a[href], li a[href]"
        )
        for a in containers:
            href = a.get("href")
            if not href:
                continue
            full = urljoin(base_url, href)
            host = urlparse(full).netloc.lower()
            if site_host in host:
                out.append(full)
            if len(out) >= 200:
                break
        return list(dict.fromkeys(out))

    def _archive_ident_to_downloads(self, ident: str) -> list[str]:
        return [
            f"https://archive.org/metadata/{ident}",
            f"https://archive.org/download/{ident}/",
            f"https://archive.org/details/{ident}",
        ]

    async def _crawl_sitemaps_for_site(
        self,
        http: submanagers.HTTPSSubmanager,
        root: str,
        sm_urls: list[str],
        keywords: list[str],
        targets: set[str],
        per_site_cap: int,
        global_seen: set[str],
    ) -> list[str]:
        to_visit = list(dict.fromkeys(sm_urls))
        visited_sm = set()
        collected = []

        while to_visit and len(collected) < per_site_cap * 5:
            sm = to_visit.pop(0)
            if sm in visited_sm:
                continue
            visited_sm.add(sm)

            raw = await http.get_bytes(sm)
            xml = self._decompress_if_needed(sm, raw)
            child_sms, pages = self._parse_sitemap_any(xml)

            for c in child_sms:
                if c not in visited_sm and self._looks_like_sitemap(c):
                    to_visit.append(c)

            for p in pages:
                if p in global_seen:
                    continue
                global_seen.add(p)
                collected.append(p)

        collected.sort(
            key=lambda u: self._score_site_url(u, keywords, targets), reverse=True
        )
        return collected[:per_site_cap]

    # ------------------------------------------------------------------ #
    # Playwright shared context manager
    # ------------------------------------------------------------------ #
    async def _open_playwright_context(
        self,
        ua: str,
        block_resources: bool,
        blocked_resource_types: set[str],
        block_domains: bool,
        blocked_domains: set[str],
        log: List[str],
        *,
        use_camoufox: bool = False,
        camoufox_options: Optional[Dict[str, Any]] = None,
    ):
        """
        Open a shared Playwright/Camoufox browser context.

        Returns (p_handle, browser, context) where:
          - For plain Playwright:
              p_handle = async_playwright() instance
          - For Camoufox:
              p_handle = AsyncCamoufox instance (so we can __aexit__ it later)
        """

        def _host_matches_blocked(host: str) -> bool:
            host = host.split(":", 1)[0].lower()
            for bd in blocked_domains:
                bd = bd.lower()
                if not bd:
                    continue
                if host == bd or host.endswith("." + bd):
                    return True
            return False

        # ---- Camoufox path ----
        if use_camoufox:
            if AsyncCamoufox is None:
                log.append(
                    "[PlaywrightCtx] Camoufox requested but not installed; falling back to Chromium."
                )
            else:
                try:
                    options = {
                        "headless": True,
                        "block_images": block_resources,
                        "block_webrtc": True,
                        "geoip": False,
                        "humanize": False,
                    }
                    if camoufox_options:
                        options.update(camoufox_options)

                    cf_cm = AsyncCamoufox(**options)
                    browser = await cf_cm.__aenter__()
                    context = await browser.new_context(user_agent=ua)

                    if block_resources or block_domains:
                        async def route_blocker(route, request):
                            rtype = (request.resource_type or "").lower()
                            try:
                                host = urlparse(request.url).netloc.lower()
                            except Exception:
                                host = ""

                            if block_domains and _host_matches_blocked(host):
                                await route.abort()
                                return

                            if block_resources and rtype in blocked_resource_types:
                                await route.abort()
                                return

                            await route.continue_()

                        await context.route("**/*", route_blocker)

                    log.append("[PlaywrightCtx] Camoufox context ready.")
                    return cf_cm, browser, context

                except Exception as e:
                    log.append(
                        f"[PlaywrightCtx] Camoufox init failed ({e}); falling back to Chromium."
                    )

        # ---- Standard Playwright (Chromium) path ----
        try:
            from playwright.async_api import async_playwright
        except ImportError:
            log.append("Playwright not installed.")
            return None, None, None

        p = await async_playwright().start()
        browser = await p.chromium.launch(headless=True)
        context = await browser.new_context(user_agent=ua)

        if block_resources or block_domains:
            async def route_blocker(route, request):
                rtype = (request.resource_type or "").lower()
                try:
                    host = urlparse(request.url).netloc.lower()
                except Exception:
                    host = ""

                if block_domains and _host_matches_blocked(host):
                    await route.abort()
                    return

                if block_resources and rtype in blocked_resource_types:
                    await route.abort()
                    return

                await route.continue_()

            await context.route("**/*", route_blocker)

        log.append("Playwright shared context ready.")
        return p, browser, context

    async def _close_playwright_context(self, p, browser, context, log: List[str]):
        try:
            if context:
                close_ctx = getattr(context, "close", None)
                if callable(close_ctx):
                    if asyncio.iscoroutinefunction(close_ctx):
                        await close_ctx()
                    else:
                        close_ctx()
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox context: {e}")

        try:
            if browser:
                close_browser = getattr(browser, "close", None)
                if callable(close_browser):
                    if asyncio.iscoroutinefunction(close_browser):
                        await close_browser()
                    else:
                        close_browser()
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox browser: {e}")

        try:
            if p:
                stop = getattr(p, "stop", None)

                if stop:
                    if asyncio.iscoroutinefunction(stop):
                        await stop()
                    else:
                        stop()
                else:
                    aexit = getattr(p, "__aexit__", None)
                    if aexit:
                        if asyncio.iscoroutinefunction(aexit):
                            await aexit(None, None, None)
                        else:
                            aexit(None, None, None)

            log.append("Playwright/Camoufox shared context closed.")
        except Exception as e:
            log.append(f"Error closing Playwright/Camoufox handle: {e}")

    async def _pw_fetch_with_sniff(self, context, page_url, timeout, log, extensions=None):
        return await self.network_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
            extensions=extensions,
        )

    async def _pw_fetch_js_links(self, context, page_url, timeout, log, extensions=None):
        return await asyncio.wait_for(self.js_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
            extensions=extensions,
        ), timeout=25)
    async def _pw_fetch_runtime_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.runtime_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
        ), timeout=25)
    async def _pw_fetch_react_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.react_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
        ), timeout=25)

    async def _pw_fetch_database_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.database_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log,
        ), timeout=25)

    async def _pw_fetch_interaction_hits(self, context, page_url, timeout, log):
        return await asyncio.wait_for(self.interaction_sniffer.sniff(
            context,
            page_url,
            timeout=timeout,
            log=log
        ), timeout=25)
    # ------------------------------------------------------------------ #
    # Main execution (Async)
    # ------------------------------------------------------------------ #
    async def _execute_async(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        # --------- Natural ChatBlock-style parsing of context / lexicon ---------
        text = str(payload or "")

        inline_ctx: str = ""
        inline_lex: List[str] = []

        try:
            inline_ctx = text.rsplit("[context]\n", 1)[1]
        except Exception:
            inline_ctx = ""

        try:
            lex_part = text.rsplit("[lexicon]\n", 1)[1]
            lex_part = lex_part.split("\n[", 1)[0]
            inline_lex = [w.strip() for w in lex_part.split(",") if w.strip()]
        except Exception:
            inline_lex = []

        core = text
        if inline_ctx:
            core = core.rsplit("[context]\n", 1)[0]
        if inline_lex:
            core = core.rsplit("[lexicon]\n", 1)[0]
        core = core.strip()

        query_raw = str(params.get("query", "") or str(payload or "")).strip()
        subpipeline = params.get("subpipeline", None)

        # --------- Extract URL seeds from context + lexicon ---------
        context_urls: List[str] = []
        if inline_ctx:
            ctx_slice = inline_ctx[:20000]
            for m in self._URL_RE.finditer(ctx_slice):
                context_urls.append(m.group(0))

        lexicon_url_seeds: List[str] = []
        non_url_lex_terms: List[str] = []
        for term in inline_lex:
            t = term.strip()
            if not t:
                continue
            if self._URL_RE.match(t):
                lexicon_url_seeds.append(t)
            else:
                non_url_lex_terms.append(t)

        use_camoufox = bool(params.get("use_camoufox", False))
        camoufox_options = params.get("camoufox_options") or {}
        if not isinstance(camoufox_options, dict):
            camoufox_options = {}
        camoufox_options.update({"i_know_what_im_doing": True})

        # ------------------- DB setup ------------------- #
        use_database = bool(params.get("use_database", False))
        db_path = params.get("db_path", "link_corpus.db")
        if use_database:
            self._initialize_database(
                db_path, logger=getattr(self, "logger", None)
            )

        store = self.store

        # ----------------- Subpipeline ------------------ #
        pipeline_result: Any = query_raw
        pipeline_queries: List[str] = []
        pipeline_urls: List[str] = []

        if subpipeline:
            subpipe_out: Any = self.run_sub_pipeline(
                initial_value=query_raw,
                pipeline_param_name="subpipeline",
                parent_params=params,
                collect=True,
            )

            if isinstance(subpipe_out, dict) and subpipe_out.get("__subpipeline__"):
                pipeline_result = subpipe_out.get("final")
                pipeline_queries = list(subpipe_out.get("queries") or [])
                pipeline_urls = list(subpipe_out.get("urls") or [])
            else:
                pipeline_result = subpipe_out

        extra_seed_urls: List[str] = []
        if context_urls:
            extra_seed_urls.extend(context_urls)
        if lexicon_url_seeds:
            extra_seed_urls.extend(lexicon_url_seeds)

        if extra_seed_urls:
            if not pipeline_urls:
                pipeline_urls = []
            pipeline_urls.extend(extra_seed_urls)

        # =========================================================================
        # Memory Sources Ingestion (SocketPipe Bridge)
        # =========================================================================
        memory_source_url_count = 0
        memory_sources_raw = str(params.get("memory_sources", "")).strip()

        if memory_sources_raw:
            try:
                mem_data = Memory.load()
                keys_to_read = [
                    k.strip()
                    for k in memory_sources_raw.split(",")
                    if k.strip()
                ]

                for key in keys_to_read:
                    data = mem_data.get(key)
                    if not data:
                        continue

                    items = data if isinstance(data, list) else [data]

                    for item in items:
                        candidate = None

                        if isinstance(item, dict):
                            candidate = (
                                item.get("url")
                                or item.get("domain")
                                or item.get("text")
                            )
                        elif isinstance(item, (str, int, float)):
                            candidate = str(item)

                        if not candidate:
                            continue

                        cand_str = str(candidate).strip()
                        if not cand_str:
                            continue

                        if "://" in cand_str or cand_str.startswith(
                            ("http:", "https:")
                        ):
                            pipeline_urls.append(cand_str)
                        elif "." in cand_str and " " not in cand_str and not cand_str.startswith(
                            "."
                        ):
                            pipeline_urls.append(f"https://{cand_str}")
                        else:
                            non_url_lex_terms.append(cand_str)

            except Exception as e:
                msg = (
                    f"[PageTracker] Error reading memory sources "
                    f"'{memory_sources_raw}': {e}"
                )
                DEBUG_LOGGER.log_message(msg)
        DEBUG_LOGGER.log_message(f"[PageTracker][memory] Ingested {len(pipeline_urls)} unique URL(s)")
        # ------------------- Config --------------------- #
        mode = str(params.get("mode", "pages")).lower()
        scan_limit = int(params.get("scan_limit", 5))
        max_pages_total = max(1, int(params.get("max_pages_total", scan_limit)))

        timeout = float(params.get("timeout", 5.0))
        engine = str(params.get("engine", "duckduckgo")).lower()

        use_js = bool(params.get("use_js", False))
        return_all_js_links = bool(params.get("return_all_js_links", False))
        max_links_per_page = int(params.get("max_links_per_page", 500))
        search_results_cap = int(params.get("search_results_cap", 256))

        search_page_limit = int(params.get("search_page_limit", 1))
        search_per_page = int(params.get("search_per_page", 50))

        use_network_sniff = bool(params.get("use_network_sniff", False))
        return_network_sniff_links = bool(
            params.get("return_network_sniff_links", False)
        )

        use_runtime_sniff = bool(params.get("use_runtime_sniff", False))
        return_runtime_sniff_hits = bool(
            params.get("return_runtime_sniff_hits", False)
        )
        use_react_sniff = bool(params.get("use_react_sniff", False))
        return_react_sniff_hits = bool(
            params.get("return_react_sniff_hits", False)
        )
        use_database_sniff = bool(params.get("use_database_sniff", False))
        return_database_sniff_hits = bool(
            params.get("return_database_sniff_hits", False)
        )
        use_interaction_sniff = bool(params.get("use_interaction_sniff", False))
        return_interaction_sniff_hits = bool(params.get("return_interaction_sniff_hits", False))

        min_term_overlap_raw = int(params.get("min_term_overlap", 1))
        min_term_overlap = max(1, min_term_overlap_raw)

        custom_ext = str(params.get("extensions", "")).split(",")
        keywords_in_url = str(params.get("url_keywords", "")).split(",")
        site_require_raw = str(params.get("site_require", "")).split(",")
        required_sites = [s.strip().lower() for s in site_require_raw if s.strip()]
        max_depth = max(0, int(params.get("max_depth", 0)))

        http_retries = int(params.get("http_retries", 2))
        http_max_conn_per_host = int(
            params.get("http_max_conn_per_host", 8)
        )
        http_verify_tls = bool(params.get("http_verify_tls", True))
        http_ca_bundle = params.get("http_ca_bundle", None)

        db_allow_rescan = bool(params.get("db_allow_rescan", False))

        block_resources = bool(params.get("block_resources", False))
        blocked_resource_types = {
            t.strip().lower()
            for t in str(
                params.get("blocked_resource_types", "")
            ).split(",")
            if t.strip()
        } or {"image", "stylesheet", "font"}

        block_domains = bool(params.get("block_domains", True))
        user_blocked_domains = {
            d.strip().lower()
            for d in str(params.get("blocked_domains", "")).split(",")
            if d.strip()
        }

        default_blocked_domains = {
            "google-analytics.com",
            "googletagmanager.com",
            "doubleclick.net",
            "facebook.com",
            "facebook.net",
            "twitter.com",
            "scorecardresearch.com",
            "quantserve.com",
            "hotjar.com",
            "segment.io",
            "mixpanel.com",
            "cloudflareinsights.com",
            "stats.g.doubleclick.net",
            "adservice.google.com",
            "ads.yahoo.com",
            "adsafeprotected.com",
        }

        blocked_domains: set[str] = set()
        if block_domains:
            blocked_domains = default_blocked_domains.union(
                user_blocked_domains
            )

        # ------------------- Targets -------------------- #
        targets: set[str] = set()
        # Targets still used for scoring and some site heuristics;
        # they no longer gate "asset" extraction (since we now extract pages).
        for e in custom_ext:
            e = e.strip()
            if not e:
                continue
            if not e.startswith("."):
                e = "." + e
            targets.add(e.lower())

        # ------------------- Keywords ------------------- #
        keywords: List[str] = [
            k.strip().lower() for k in keywords_in_url if k.strip()
        ]
        strict_keywords = bool(params.get("strict_keywords", False))

        if query_raw:
            if strict_keywords:
                whole = query_raw.lower().strip()
                if whole and whole not in keywords:
                    keywords.append(whole)
            else:
                for qt in [
                    w.strip().lower() for w in query_raw.split() if w.strip()
                ]:
                    if qt not in keywords:
                        keywords.append(qt)

        for term in non_url_lex_terms:
            lt = term.lower()
            if lt and lt not in keywords:
                keywords.append(lt)

        # -------------------- Helpers ------------------- #
        def _clean_domain(u: str) -> str:
            try:
                return urlparse(u).netloc.lower().split(":")[0]
            except Exception:
                return ""

        def _allowed_by_required_sites(u: str) -> bool:
            if not required_sites:
                return True
            d = _clean_domain(u)
            return any(req in d for req in required_sites)

        def _term_overlap_ok(haystack: str) -> bool:
            if not keywords:
                return True
            h = haystack.lower()
            hits = 0
            for k in keywords:
                if k and k in h:
                    hits += 1
                    if hits >= min_term_overlap:
                        return True
            return False

        def _clean_path(u: str) -> str:
            try:
                return urlparse(u).path.lower()
            except Exception:
                return ""

        def _augment_search_query(q: str, mode: str, required_sites: List[str]) -> str:
            sq = q.strip()
            site_clauses = []
            for raw in required_sites or []:
                s = (raw or "").strip().lower()
                if not s:
                    continue
                if "://" in s:
                    s = s.split("://", 1)[1]
                s = s.split("/", 1)[0].lstrip(".")
                if s:
                    site_clauses.append(f"site:{s}")

            if site_clauses:
                sites_expr = " OR ".join(site_clauses)
                sq = f"({sites_expr}) {sq}" if sq else f"({sites_expr})"

            q_lower = sq.lower()
            if mode == "media":
                if not any(x in q_lower for x in ["mp3", "flac", "m4a", "ogg"]):
                    sq = f"{sq} (mp3 OR flac OR m4a OR ogg)".strip()
            elif mode == "docs":
                if "filetype:pdf" not in q_lower:
                    sq = f"{sq} filetype:pdf".strip()
            return sq

        def _is_search_url(u: str) -> bool:
            try:
                pu = urlparse(u)
                path = (pu.path or "").lower()
                q = (pu.query or "").lower()
                if any(
                    tok in path
                    for tok in ["/search", "/results", "/query", "search.php"]
                ):
                    return True
                if any(
                    k + "=" in q
                    for k in ["q", "query", "s", "search", "keyword"]
                ):
                    return True
                return False
            except Exception:
                return False

        def _dedupe(seq: List[str]) -> List[str]:
            seen = set()
            out_ = []
            for s in seq:
                if s not in seen:
                    seen.add(s)
                    out_.append(s)
            return out_

        # -------------------- Triage -------------------- #
        candidate_pages: List[str] = []
        direct_asset_urls: List[str] = []
        queries_to_run: List[str] = []
        skip_search_engine = False

        if pipeline_urls:
            skip_search_engine = False
            unique_urls = _dedupe(
                [str(u).strip() for u in pipeline_urls if str(u).strip()]
            )

            for u in unique_urls:
                if not _allowed_by_required_sites(u):
                    continue
                path = _clean_path(u)

                if self._is_mega_link(u):
                    direct_asset_urls.append(u)
                    continue

                if any(path.endswith(ext) for ext in self.IGNORED_EXTENSIONS):
                    continue

                candidate_pages.append(u)

            candidate_pages = candidate_pages[:max_pages_total]

        if (not skip_search_engine) and pipeline_queries:
            for qv in pipeline_queries:
                qv_s = str(qv).strip()
                if qv_s:
                    queries_to_run.append(qv_s)

        if not pipeline_urls and not pipeline_queries:
            if isinstance(pipeline_result, list) and pipeline_result:
                for qv in pipeline_result:
                    qv_s = str(qv).strip()
                    if qv_s:
                        queries_to_run.append(qv_s)
            else:
                base_q: Optional[str] = None
                if (
                    isinstance(pipeline_result, str)
                    and pipeline_result.strip()
                ):
                    base_q = pipeline_result.strip()
                elif query_raw:
                    base_q = query_raw
                if base_q:
                    queries_to_run.append(base_q)

        if not queries_to_run and query_raw and not skip_search_engine:
            queries_to_run = [query_raw]

        queries_to_run = _dedupe(queries_to_run)
        query = queries_to_run[0] if queries_to_run else query_raw

        # ---------------- Search discovery --------------- #
        explicit_site_seeds: set[str] = set()
        synthetic_search_seeds: set[str] = set()

        if not skip_search_engine and queries_to_run:
            ua_search = (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "PromptChat/PageTracker"
            )
            seen_search_urls: set[str] = set()

            # -------- Engine: database -------- #
            if engine == "database":
                if not use_database or not self.store:
                    DEBUG_LOGGER.log_message(
                        "[PageTracker][db] engine=database requires use_database=True."
                    )
                else:
                    DEBUG_LOGGER.log_message(
                        "[PageTracker] Running Database Intelligence..."
                    )

                    db_seed_limit = int(params.get("db_seed_limit", 250))

                    # [PATCH] Use fetch_seed_pages from PageTrackerStore
                    # This respects site requirements and keywords automatically
                    db_pages = self.store.fetch_seed_pages(
                        limit=db_seed_limit,
                        required_sites=required_sites,
                        keywords=keywords if strict_keywords else None,
                        min_score=0
                    )

                    candidate_pages.extend(db_pages)

                    # Dedupe
                    candidate_pages = list(dict.fromkeys(candidate_pages))[:max_pages_total]

                    DEBUG_LOGGER.log_message(
                        f"[PageTracker][db] Loaded {len(db_pages)} seed pages from history."
                    )

            # -------- Engine: sites -------- #
            if engine == "sites" and required_sites:
                seed_pages, syn_seeds, exp_seeds = self._seed_pages_from_required_sites(
                    required_sites=required_sites,
                    queries=queries_to_run,
                    probe_cap_per_site=max(8, len(queries_to_run) * 3),
                    sitemap_cap_per_site=12,
                    hub_cap_per_site=10,
                )
                synthetic_search_seeds = syn_seeds
                explicit_site_seeds = exp_seeds

                per_site_cap = max(
                    5, max_pages_total // max(1, len(required_sites))
                )
                global_seen = set()

                ua_http_sites = (
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "PromptChat/PageTracker"
                )
                async with submanagers.HTTPSSubmanager(
                    user_agent=ua_http_sites,
                    timeout=timeout,
                    retries=http_retries,
                    max_conn_per_host=http_max_conn_per_host,
                    verify=http_verify_tls,
                    ca_bundle=http_ca_bundle,
                ) as http_sites:
                    for site in required_sites:
                        root = (
                            f"https://{site.strip().lstrip('.')}".rstrip("/")
                            + "/"
                        )
                        host = urlparse(root).netloc.lower()

                        robots_url = root + "robots.txt"
                        try:
                            robots_txt = await http_sites.get_text(robots_url)
                        except Exception:
                            robots_txt = ""
                        sm_urls = self._extract_sitemap_urls_from_robots(
                            robots_txt
                        )

                        if not sm_urls:
                            sm_urls = [
                                u
                                for u in seed_pages
                                if "sitemap" in u and site in u
                            ][:8]

                        best_from_sitemaps = await self._crawl_sitemaps_for_site(
                            http=http_sites,
                            root=root,
                            sm_urls=sm_urls,
                            keywords=keywords,
                            targets=targets,
                            per_site_cap=per_site_cap,
                            global_seen=global_seen,
                        )

                        hub_like = [
                            u
                            for u in seed_pages
                            if site in u and _is_search_url(u)
                        ]
                        expanded_from_hubs: list[str] = []

                        for hub in hub_like[:3]:
                            try:
                                html_hub = await http_sites.get_text(hub)
                                soup_ = BeautifulSoup(
                                    html_hub or "", "html.parser"
                                )

                                expanded_from_hubs.extend(
                                    self._extract_internal_result_links(
                                        soup_, hub, host
                                    )
                                )

                                for nxt in self._extract_next_page_links(
                                    soup_, hub
                                ):
                                    html_nxt = await http_sites.get_text(nxt)
                                    soup_nxt = BeautifulSoup(
                                        html_nxt or "", "html.parser"
                                    )
                                    expanded_from_hubs.extend(
                                        self._extract_internal_result_links(
                                            soup_nxt, nxt, host
                                        )
                                    )
                            except Exception:
                                pass

                        expanded_from_hubs = list(
                            dict.fromkeys(expanded_from_hubs)
                        )
                        expanded_from_hubs.sort(
                            key=lambda u: self._score_site_url(
                                u, keywords, targets
                            ),
                            reverse=True,
                        )
                        expanded_from_hubs = expanded_from_hubs[:per_site_cap]

                        merged = list(
                            dict.fromkeys(
                                [root]
                                + best_from_sitemaps
                                + expanded_from_hubs
                                + [u for u in seed_pages if site in u]
                            )
                        )
                        merged.sort(
                            key=lambda u: self._score_site_url(
                                u, keywords, targets
                            ),
                            reverse=True,
                        )

                        for u in merged:
                            if len(candidate_pages) >= max_pages_total:
                                break
                            if _allowed_by_required_sites(
                                u
                            ) and (not keywords or _term_overlap_ok(u)):
                                candidate_pages.append(u)

                candidate_pages = list(
                    dict.fromkeys(candidate_pages)
                )[:max_pages_total]

            # -------- Engine: duckduckgo -------- #
            elif engine == "duckduckgo":
                for qv in queries_to_run:
                    sq = _augment_search_query(qv, mode, required_sites)
                    try:
                        urls = await self._search_duckduckgo(
                            sq,
                            max_results=search_results_cap,
                            ua=ua_search,
                            timeout=timeout,
                            page_limit=search_page_limit,
                            per_page=search_per_page,
                        )
                    except Exception as e:
                        DEBUG_LOGGER.log_message(
                            f"[PageTracker][search][ddg] error for {sq!r}: {e}"
                        )
                        urls = []

                    for u in urls:
                        if len(candidate_pages) >= max_pages_total:
                            break
                        if not u or u in seen_search_urls:
                            continue
                        if not _allowed_by_required_sites(u):
                            continue
                        candidate_pages.append(u)
                        seen_search_urls.add(u)

            # -------- Engine: google_cse -------- #
            elif engine == "google_cse":
                for qv in queries_to_run:
                    sq = _augment_search_query(qv, mode, required_sites)
                    try:
                        urls = await self._search_google_cse(
                            sq,
                            n=search_results_cap,
                            timeout=timeout,
                            page_limit=search_page_limit,
                        )
                    except Exception as e:
                        DEBUG_LOGGER.log_message(
                            f"[PageTracker][search][cse] error for {sq!r}: {e}"
                        )
                        urls = []

                    for u in urls:
                        if len(candidate_pages) >= max_pages_total:
                            break
                        if not u or u in seen_search_urls:
                            continue
                        if not _allowed_by_required_sites(u):
                            continue
                        candidate_pages.append(u)
                        seen_search_urls.add(u)

            # -------- Engine: searxng -------- #
            elif engine == "searxng":
                searxng_url = params.get("searxng_url") or None
                for qv in queries_to_run:
                    sq = _augment_search_query(qv, mode, required_sites)
                    try:
                        urls = await self._search_searxng(
                            sq,
                            max_results=search_results_cap,
                            timeout=timeout,
                            base_url=searxng_url,
                            page_limit=search_page_limit,
                        )
                    except Exception as e:
                        DEBUG_LOGGER.log_message(
                            f"[PageTracker][search][searxng] error for {sq!r}: {e}"
                        )
                        urls = []

                    for u in urls:
                        if len(candidate_pages) >= max_pages_total:
                            break
                        if not u or u in seen_search_urls:
                            continue
                        if not _allowed_by_required_sites(u):
                            continue
                        candidate_pages.append(u)
                        seen_search_urls.add(u)

        # ---------------- Crawl state ------------------ #
        found_pages: List[Dict[str, Any]] = []
        seen_page_urls: set[str] = set()
        visited_pages: set[str] = set()

        log: List[str] = []
        all_js_links: List[Dict[str, str]] = []
        all_network_links: List[Dict[str, str]] = []
        all_runtime_hits: List[Dict[str, Any]] = []
        all_react_hits: List[Dict[str, Any]] = []
        all_database_hits: List[Dict[str, Any]] = []
        all_interaction_hits: List[Dict[str, Any]] = []
        ua_http = (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/PageTracker"
        )

        async with submanagers.HTTPSSubmanager(
            user_agent=ua_http,
            timeout=timeout,
            retries=http_retries,
            max_conn_per_host=http_max_conn_per_host,
            verify=http_verify_tls,
            ca_bundle=http_ca_bundle,
        ) as http:
            def _should_persist_page(u: str) -> bool:
                if engine != "sites":
                    return True
                if u in explicit_site_seeds or u in synthetic_search_seeds:
                    return False
                if _is_search_url(u):
                    return False
                return True

            pw_needed = (
                    use_js or
                    use_network_sniff or
                    use_runtime_sniff or
                    use_react_sniff or
                    use_database_sniff or
                    use_interaction_sniff  # <--- Added
            )
            pw_p = pw_browser = pw_context = None
            try:
                if pw_needed:
                    ua_pw = (
                        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                        "PromptChat/PageTracker"
                    )
                    pw_p, pw_browser, pw_context = await self._open_playwright_context(
                        ua=ua_pw,
                        block_resources=block_resources,
                        blocked_resource_types=blocked_resource_types,
                        block_domains=block_domains,
                        blocked_domains=blocked_domains,
                        log=log,
                        use_camoufox=use_camoufox,
                        camoufox_options=camoufox_options,
                    )
            except Exception:
                if pw_needed and (pw_p or pw_browser or pw_context):
                    await self._close_playwright_context(
                        pw_p, pw_browser, pw_context, log
                    )

            async def _process_page(
                page_url: str,
                depth: int,
                http: submanagers.HTTPSSubmanager,
            ) -> Dict[str, Any]:
                local_log: List[str] = []
                local_js_links: List[Dict[str, str]] = []
                local_network_links: List[Dict[str, str]] = []
                local_runtime_hits: List[Dict[str, Any]] = []
                local_react_hits: List[Dict[str, Any]] = []
                local_pages: List[Dict[str, Any]] = []
                local_database_hits: List[Dict[str, Any]] = []
                local_interaction_hits: List[Dict[str, Any]] = []
                next_pages: List[str] = []
                self.network_sniffer.http = http
                try:
                    links_on_page: List[Dict[str, str]] = []
                    html = ""

                    sniff_items: List[Dict[str, str]] = []
                    sniff_parent_pages: List[str] = []

                    # 1) Network sniff
                    if use_network_sniff and pw_context:
                        sniff_html = ""
                        sniff_json = None

                        sniff_result = await self._pw_fetch_with_sniff(
                            pw_context, page_url, timeout, local_log, targets
                        )

                        if isinstance(sniff_result, tuple):
                            if len(sniff_result) == 3:
                                sniff_html, sniff_items, sniff_json = sniff_result
                            elif len(sniff_result) == 2:
                                sniff_html, sniff_items = sniff_result
                            elif len(sniff_result) == 1:
                                sniff_html = sniff_result[0]
                        else:
                            sniff_html = sniff_result

                        html = sniff_html or html

                        if "archive.org/metadata/" in page_url:
                            try:
                                meta = (
                                    json.loads(html)
                                    if html.strip().startswith("{")
                                    else {}
                                )
                                files = meta.get("files") or []
                                identifier = (
                                    meta.get("metadata") or {}
                                ).get("identifier", "")
                                for f in files:
                                    name = f.get("name", "")
                                    if not name:
                                        continue
                            except Exception:
                                pass

                        try:
                            if sniff_json:
                                for hit in sniff_json:
                                    data = hit.get("json") or {}
                                    docs = (
                                        (
                                            (data.get("response") or {}).get(
                                                "docs"
                                            )
                                        )
                                        or []
                                    )
                                    for d in docs:
                                        ident = d.get("identifier")
                                        if ident:
                                            for u2 in self._archive_ident_to_downloads(
                                                ident
                                            ):
                                                if _allowed_by_required_sites(
                                                    u2
                                                ):
                                                    links_on_page.append(
                                                        {
                                                            "url": u2,
                                                            "text": "[Archive identifier]",
                                                            "tag": "archive_ident",
                                                        }
                                                    )
                        except Exception as e:
                            local_log.append(
                                f"JSON sniff parse error on {page_url}: {e}"
                            )

                        for si in sniff_items:
                            url_hit = si.get("url", "")
                            if not url_hit:
                                continue
                            local_network_links.append(
                                {
                                    "page": page_url,
                                    "url": url_hit,
                                    "text": si.get("text", ""),
                                    "tag": si.get("tag", "network_sniff"),
                                    "size": si.get("size", "?"),
                                }
                            )
                            local_js_links.append(
                                {
                                    "page": page_url,
                                    "url": url_hit,
                                    "text": si.get("text", ""),
                                    "tag": si.get("tag", "network_sniff"),
                                }
                            )

                            try:
                                parsed = urlparse(url_hit)
                                path = parsed.path or ""
                                if "/" in path:
                                    parent_path = path.rsplit("/", 1)[0] + "/"
                                    parent_url = f"{parsed.scheme}://{parsed.netloc}{parent_path}"
                                    if _allowed_by_required_sites(
                                        parent_url
                                    ):
                                        sniff_parent_pages.append(parent_url)
                            except Exception:
                                pass

                    # 1b) Runtime sniff
                    if use_runtime_sniff and pw_context:
                        rt_html = ""
                        rt_hits: list[dict[str, Any]] = []

                        rt_result = await self._pw_fetch_runtime_hits(
                            pw_context, page_url, timeout, local_log
                        )

                        if isinstance(rt_result, tuple):
                            if len(rt_result) == 3:
                                rt_html, _rt_items, rt_hits = rt_result
                            elif len(rt_result) == 2:
                                rt_html, rt_hits = rt_result
                            elif len(rt_result) == 1:
                                rt_html = rt_result[0]
                        else:
                            rt_html = rt_result

                        if rt_html and not html:
                            html = rt_html
                        if rt_hits:
                            local_runtime_hits.extend(rt_hits)

                    if use_database_sniff and pw_context:
                        try:
                            db_html, db_hits = await self._pw_fetch_database_hits(
                                pw_context,
                                page_url,
                                timeout,
                                local_log,
                            )
                            # Use this HTML if previous sniffers failed to get it
                            if db_html and not html:
                                html = db_html

                            if db_hits:
                                local_database_hits.extend(db_hits)

                                # Optional: If we found content links, treat them as outgoing links
                                for hit in db_hits:
                                    if hit.get("kind") == "content_link":
                                        u = hit.get("url")
                                        if u:
                                            # Add to js_links so it appears in debug output
                                            local_js_links.append({
                                                "page": page_url,
                                                "url": u,
                                                "text": "[DB Content Link]",
                                                "tag": "db_link"
                                            })
                        except Exception as e:
                            local_log.append(f"[PageTracker][DB] Error sniffing {page_url}: {e}")
                    # 2) JS render/gather
                    if use_js and pw_context:
                        js_html, js_links = await self._pw_fetch_js_links(
                            pw_context, page_url, timeout, local_log
                        )
                        if js_html:
                            html = js_html
                        links_on_page.extend(js_links)

                        if not js_links:
                            preview = (html or "")[:2000].replace(
                                "\n", " "
                            )
                            local_log.append(
                                f"[debug] JS DOM preview (first 2000 chars): {preview}"
                            )

                        for jl in js_links:
                            local_js_links.append(
                                {
                                    "page": page_url,
                                    "url": jl.get("url", ""),
                                    "text": jl.get("text", ""),
                                    "tag": jl.get("tag", ""),
                                }
                            )
                    if use_react_sniff and pw_context:
                        try:
                            react_html, react_hits = await self._pw_fetch_react_hits(
                                pw_context,
                                page_url,
                                timeout,
                                local_log,
                            )
                        except Exception as e:
                            local_log.append(f"[PageTracker][React] Error sniffing {page_url}: {e}")
                            react_html, react_hits = "", []

                        # Prefer React HTML if we still don't have any DOM snapshot
                        if react_html and not html:
                            html = react_html

                        if react_hits:
                            local_react_hits.extend(react_hits)

                            # OPTIONAL: treat React routes as candidate pages
                            for rh in react_hits:
                                try:
                                    rh_url = str(rh.get("url") or "").strip()
                                    if not rh_url:
                                        continue
                                    if not _allowed_by_required_sites(rh_url):
                                        continue

                                    rpath = urlparse(rh_url).path.lower()
                                    if any(rpath.endswith(ext) for ext in self.IGNORED_EXTENSIONS):
                                        continue

                                    # Basic keyword filter
                                    if keywords:
                                        haystack = (rh.get("route") or "") + " " + rh_url
                                        if not _term_overlap_ok(haystack):
                                            continue

                                    score = self._score_site_url(rh_url, keywords, targets)
                                    local_pages.append(
                                        {
                                            "title": f"[react-route] {rh.get('route') or '[no title]'}"[:200],
                                            "url": rh_url,
                                            "source": page_url,
                                            "depth": depth + 1,
                                            "score": score,
                                        }
                                    )

                                    # Also allow BFS to walk those URLs
                                    if depth < max_depth:
                                        next_pages.append(rh_url)
                                except Exception:
                                    # Never let a weird React hit break the crawl
                                    continue
                    if use_interaction_sniff and pw_context:
                        try:
                            int_html, int_hits = await self._pw_fetch_interaction_hits(
                                pw_context,
                                page_url,
                                timeout,
                                local_log
                            )
                            # Use this HTML if previous sniffers failed
                            if int_html and not html:
                                html = int_html

                            if int_hits:
                                local_interaction_hits.extend(int_hits)
                        except Exception as e:
                            local_log.append(f"[PageTracker][Interaction] Error sniffing {page_url}: {e}")
                    # 3) Plain HTML
                    if not html:
                        try:
                            html = await http.get_text(page_url)
                            if not html:
                                raise RuntimeError("Empty HTML")
                        except Exception as e:
                            local_log.append(
                                f"Error fetching {page_url}: {e}"
                            )
                            if use_database and self.store and _should_persist_page(page_url):
                                self.store.mark_scan_complete(page_url)
                            return {
                                "page": page_url,
                                "pages": local_pages,
                                "next_pages": next_pages,
                                "js_links": local_js_links,
                                "network_links": local_network_links,
                                "runtime_hits": local_runtime_hits,
                                "react_hits": local_react_hits,
                                "database_hits": local_database_hits,
                                "interaction_hits": local_interaction_hits,
                                "log": local_log,
                            }

                    soup = BeautifulSoup(html or "", "html.parser")

                    page_title = ""
                    try:
                        if soup.title and soup.title.string:
                            page_title = soup.title.string
                    except Exception:
                        page_title = ""

                    page_haystack = (page_title or "") + " " + page_url
                    page_has_keywords = _term_overlap_ok(page_haystack)

                    # The main page itself can be a match
                    if (
                        _allowed_by_required_sites(page_url)
                        and (not keywords or page_has_keywords)
                    ):
                        score = self._score_site_url(
                            page_url, keywords, targets
                        )
                        local_pages.append(
                            {
                                "title": (page_title or "[no title]")[:200],
                                "url": page_url,
                                "source": None,
                                "depth": depth,
                                "score": score,
                            }
                        )

                    link_count = 0
                    for a in soup.find_all("a", href=True):
                        links_on_page.append(
                            {
                                "url": a["href"],
                                "text": a.get_text(strip=True),
                                "tag": "a",
                            }
                        )
                        link_count += 1
                        if link_count >= max_links_per_page:
                            break

                    # Now treat some outgoing links as candidate *pages*
                    for link in links_on_page:
                        raw_link = link["url"]
                        full_url = urljoin(page_url, raw_link)
                        path = urlparse(full_url).path.lower()

                        if not _allowed_by_required_sites(full_url):
                            continue
                        if any(
                            path.endswith(ext) for ext in self.IGNORED_EXTENSIONS
                        ):
                            continue
                        clean_url_for_matching = unquote(full_url).lower()

                        if keywords:
                            haystack = (
                                (link.get("text") or "") + " " + clean_url_for_matching
                            )
                            if not _term_overlap_ok(haystack):
                                continue

                        score = self._score_site_url(
                            full_url, keywords, targets
                        )
                        # [PATCH] Construct page data object
                        page_item = {
                            "title": (link.get("text") or "[no title]")[:200],
                            "url": full_url,
                            "source": page_url,
                            "depth": depth + 1,
                            "score": score,
                            "status": "found"
                        }

                        local_pages.append(page_item)

                        # [PATCH] Persist immediately to PageTrackerStore
                        if use_database and self.store:
                            self.store.upsert_page(page_item)

                    # Next-level pages
                    if depth < max_depth:
                        for link in links_on_page:
                            raw_link = link.get("url") or ""
                            if not raw_link:
                                continue
                            full_url = urljoin(page_url, raw_link)
                            if not _allowed_by_required_sites(full_url):
                                continue

                            lpath = urlparse(full_url).path.lower()
                            if any(
                                lpath.endswith(ext)
                                for ext in self.IGNORED_EXTENSIONS
                            ):
                                continue

                            if keywords and not page_has_keywords:
                                haystack = (
                                    link.get("text") or ""
                                ) + " " + full_url
                                if not _term_overlap_ok(haystack):
                                    continue

                            if engine == "sites":
                                if _is_search_url(full_url) and full_url not in explicit_site_seeds:
                                    continue

                            next_pages.append(full_url)

                    if depth < max_depth and sniff_parent_pages:
                        for parent_url in sniff_parent_pages:
                            if _allowed_by_required_sites(parent_url):
                                next_pages.append(parent_url)

                    if use_database and store and _should_persist_page(
                        page_url
                    ):
                        store.mark_scan_complete(page_url)

                except Exception as e:
                    local_log.append(f"Error scanning {page_url}: {e}")
                    if use_database and store and _should_persist_page(
                        page_url
                    ):
                        try:
                            store.mark_scan_complete(page_url)
                        except Exception as ee:
                            local_log.append(
                                f"Error marking page scanned {page_url}: {ee}"
                            )

                return {
                    "page": page_url,
                    "pages": local_pages,
                    "next_pages": next_pages,
                    "js_links": local_js_links,
                    "network_links": local_network_links,
                    "react_hits": local_react_hits,
                    "runtime_hits": local_runtime_hits,
                    "database_hits": local_database_hits,
                    "interaction_hits": all_interaction_hits,
                    "log": local_log,
                }

            # ---------------- BFS frontier ----------------- #
            frontier: List[str] = []
            site_buckets = {s: [] for s in required_sites} if required_sites else {}

            for u in candidate_pages:
                if not _allowed_by_required_sites(u):
                    continue
                if required_sites:
                    d = _clean_domain(u)
                    for s in required_sites:
                        if s in d:
                            site_buckets[s].append(u)
                            break
                else:
                    frontier.append(u)

            if required_sites:
                per_site_cap = max(
                    3, max_pages_total // len(required_sites)
                )
                for s, bucket in site_buckets.items():
                    frontier.extend(bucket[:per_site_cap])

            frontier = list(dict.fromkeys(frontier))[:max_pages_total]
            current_depth = 0

            logged_rescan_notice = False

            while frontier and current_depth <= max_depth:

                DEBUG_LOGGER.log_message(
                    f"[PageTracker][BFS] --- Starting Depth {current_depth} | "
                    f"Frontier Size: {len(frontier)} | Visited: {len(visited_pages)}/{max_pages_total} ---"
                )

                remaining_page_slots = max_pages_total
                batch: List[str] = []

                for u in frontier:
                    if len(batch) >= remaining_page_slots:
                        break
                    if u in visited_pages:
                        continue

                    if use_database and self.store and self.store.is_recently_scanned(u):
                        if not (db_allow_rescan and params.get("source", "database") == "database"):
                            visited_pages.add(u)
                            continue

                        if not logged_rescan_notice:
                            DEBUG_LOGGER.log_message(
                                "[PageTracker][db] Rescan enabled: "
                                "processing previously scanned pages from database."
                            )
                            logged_rescan_notice = True

                    batch.append(u)
                    # CRITICAL: Mark visited immediately to prevent circular re-queueing in the same depth
                    visited_pages.add(u)

                if not batch:
                    DEBUG_LOGGER.log_message(
                        f"[PageTracker][BFS] Depth {current_depth}: No unique pages to process. stopping.")
                    break

                DEBUG_LOGGER.log_message(
                    f"[PageTracker][BFS] Processing depth {current_depth} batch of {len(batch)} URLs...")

                if use_camoufox:
                    results: List[Dict[str, Any]] = []
                    for url in batch:
                        try:
                            res = await _process_page(url, current_depth, http)
                            results.append(res)
                        except Exception as e:
                            DEBUG_LOGGER.log_message(f"[PageTracker][Camoufox] Fatal error on {url}: {e}")
                            continue
                else:
                    results = await asyncio.gather(
                        *[_process_page(url, current_depth, http) for url in batch]
                    )

                next_frontier_candidates: List[str] = []

                for res in results:
                    # Per-page logging
                    log.extend(res.get("log", []))
                    all_js_links.extend(res.get("js_links", []))
                    all_network_links.extend(res.get("network_links", []))
                    all_runtime_hits.extend(res.get("runtime_hits", []))
                    all_react_hits.extend(res.get("react_hits", []))
                    all_database_hits.extend(res.get("database_hits", []))
                    all_interaction_hits.extend(res.get("interaction_hits", []))
                    # Collect found pages
                    for p in res.get("pages", []):
                        p_url = p.get("url")
                        if p_url and p_url not in seen_page_urls:
                            seen_page_urls.add(p_url)
                            found_pages.append(p)
                            DEBUG_LOGGER.log_message(f"[PageTracker][BFS] FOUND PAGE: {p_url}")

                    # Gather potential pages for the next hop
                    if current_depth < max_depth:
                        next_frontier_candidates.extend(res.get("next_pages", []))

                # Filter candidates against visited and current depth to build the clean frontier
                next_frontier = []
                seen_in_next = set()
                for url in next_frontier_candidates:
                    if url not in visited_pages and url not in seen_in_next:
                        next_frontier.append(url)
                        seen_in_next.add(url)

                # Cap the frontier size to the total remaining limit to avoid memory bloat
                frontier = next_frontier[:max_pages_total]

                DEBUG_LOGGER.log_message(
                    f"[PageTracker][BFS] Depth {current_depth} complete. "
                    f"Discovered {len(frontier)} new unique pages for next hop."
                )

                current_depth += 1

            if pw_needed:
                await self._close_playwright_context(pw_p, pw_browser, pw_context, log)

        # ---------------- Output formatting ------------- #
        from urllib.parse import urlparse as _urlparse

        # De-duplicate final pages, prefer higher score
        final_map: Dict[str, Dict[str, Any]] = {}
        for p in found_pages:
            u = p["url"]
            score = p.get("score", 0)
            if u not in final_map or score > final_map[u].get("score", 0):
                final_map[u] = p
        final_list = sorted(
            final_map.values(), key=lambda x: x.get("score", 0), reverse=True
        )

        if not final_list:
            base_text = (
                "### PageTracker: No similar pages found.\n"
                f"Scanned {len(candidate_pages)} candidate seeds.\n"
                f"Required keywords: {keywords}\n"
                f"Required sites: {required_sites or '[none]'}\n"
                f"min_term_overlap: {min_term_overlap}\n"
                f"Engine: {engine}\n"
            )
            lines = [base_text]

            if return_all_js_links and all_js_links:
                lines.append("\n### All JS-Gathered Links (debug)\n")
                for jl in all_js_links:
                    host = (
                        _urlparse(jl["page"]).netloc
                        if jl.get("page")
                        else "(unknown)"
                    )
                    url = jl["url"]
                    text = jl["text"] or "(no text)"
                    tag = jl["tag"] or "a"
                    lines.append(f"- **[{text}]({url})**")
                    lines.append(
                        f"  - *Tag: <{tag}> | From page: {host}*"
                    )

            if return_network_sniff_links and all_network_links:
                lines.append("\n### All Network-Sniffed Links (debug)\n")
                for nl in all_network_links:
                    host = (
                        _urlparse(nl["page"]).netloc
                        if nl.get("page")
                        else "(unknown)"
                    )
                    url = nl["url"]
                    text = nl["text"] or "(no text)"
                    tag = nl.get("tag", "network_sniff")
                    size = nl.get("size", "?")
                    lines.append(f"- **[{text}]({url})**")
                    lines.append(
                        f"  - *Tag: <{tag}> | From page: {host} | Size: {size}*"
                    )

            return "\n".join(lines), {
                "count": 0,
                "keywords_used": keywords,
                "min_term_overlap": min_term_overlap,
                "engine": engine,
                "required_sites": required_sites,
                "js_links": all_js_links,
                "network_sniff_links": all_network_links,
                "runtime_hits": all_runtime_hits,
                "react_hits": all_react_hits,
                "interaction_hits": all_interaction_hits,
                "log": log,
                "queries_run": queries_to_run,
            }

        lines = [f"### PageTracker Found {len(final_list)} Similar Pages"]
        lines.append(
            f"_Mode: {mode} | Query: {query} | Engine: {engine} | "
            f"Required Keywords: {keywords} | min_term_overlap: {min_term_overlap} | "
            f"Required Sites: {required_sites or '[none]'}_"
        )
        lines.append("")

        for page in final_list:
            title = page["title"]
            url = page["url"]
            score = page.get("score", 0)
            host = _urlparse(url).netloc
            depth = page.get("depth", 0)
            lines.append(f"- **[{title}]({url})**")
            lines.append(
                f"  - *Host: {host} | Score: {score} | Depth: {depth}*"
            )

        if return_all_js_links and all_js_links:
            lines.append("\n### All JS-Gathered Links (debug)\n")
            for jl in all_js_links:
                host = (
                    _urlparse(jl["page"]).netloc
                    if jl.get("page")
                    else "(unknown)"
                )
                url = jl["url"]
                text = jl["text"] or "(no text)"
                tag = jl["tag"] or "a"
                lines.append(f"- **[{text}]({url})**")
                lines.append(
                    f"  - *Tag: <{tag}> | From page: {host}*"
                )

        if return_network_sniff_links and all_network_links:
            lines.append("\n### All Network-Sniffed Links (debug)\n")
            for nl in all_network_links:
                host = (
                    _urlparse(nl["page"]).netloc
                    if nl.get("page")
                    else "(unknown)"
                )
                url = nl["url"]
                text = nl["text"] or "(no text)"
                tag = nl.get("tag", "network_sniff")
                size = nl.get("size", "?")
                lines.append(f"- **[{text}]({url})**")
                lines.append(
                    f"  - *Tag: <{tag}> | From page: {host} | Size: {size}*"
                )
        if return_react_sniff_hits and all_react_hits:
            lines.append("\n### React / SPA Hits (debug)\n")
            for rh in all_react_hits[:100]:
                url = rh.get("url") or "(no url)"
                route = rh.get("route") or ""
                kind = rh.get("kind") or "react_nav"
                lines.append(f"- `{kind}` **{route}** → {url}")
        if return_runtime_sniff_hits and all_runtime_hits:
            lines.append("\n### Runtime Sniff Hits (debug)\n")
            # Cap output to prevent massive message overflow (e.g. 100 items)
            for hit in all_runtime_hits[:100]:
                url = hit.get("url") or "(no url)"
                payload = hit.get("json") or {}

                # Format a readable description based on the hit type
                desc_parts = []
                if "console" in payload:
                    desc_parts.append(f"Console: {str(payload['console'])[:100]}...")
                elif "ws_frame" in payload:
                    desc_parts.append(f"WebSocket: {str(payload['ws_frame'])[:100]}...")
                elif "request_body" in payload:
                    desc_parts.append("Request Body (JSON)")
                elif "media_events" in payload:
                    evts = payload["media_events"]
                    desc_parts.append(f"Media Events: {len(evts)}")
                elif "storage" in payload:
                    desc_parts.append(f"Storage Items: {len(payload['storage'])}")
                elif "perf_entries" in payload:
                    desc_parts.append(f"Perf Entries: {len(payload['perf_entries'])}")
                else:
                    # Generic fallback for unknown payloads
                    import json as _json
                    try:
                        dump = _json.dumps(payload)
                        desc_parts.append(f"Data: {dump[:100]}...")
                    except:
                        desc_parts.append("Data: (complex object)")

                desc = " | ".join(desc_parts)
                lines.append(f"- `{desc}` found on **{url}**")
        if return_database_sniff_hits and all_database_hits:
            lines.append("\n### Database / Content Sniff Hits (debug)\n")
            for dbh in all_database_hits[:100]:
                kind = dbh.get("kind")
                url = dbh.get("url")
                meta = dbh.get("meta") or {}

                if kind == "content_link":
                    src = meta.get("source", "?")
                    lines.append(f"- `db_link` ({src}) **{url}**")
                elif kind == "indexeddb_dump":
                    db_name = meta.get("name", "?")
                    stores = meta.get("stores", [])
                    store_str = ", ".join([f"{s['name']}(~{s.get('approx_count')})" for s in stores])
                    lines.append(f"- `indexed_db` **{db_name}**: [{store_str}]")
                elif kind == "db_config_detected":
                    name = meta.get("name")
                    lines.append(f"- `backend_config` **{name}** detected")
        if return_interaction_sniff_hits and all_interaction_hits:
            lines.append("\n### Interaction / CDP Hits (debug)\n")
            for ih in all_interaction_hits[:100]:
                kind = ih.get("kind")
                meta = ih.get("meta") or {}
                url = ih.get("url")

                if kind == "event_listener":
                    node = meta.get("nodeName", "UNK")
                    types = meta.get("types", [])
                    lines.append(f"- `listener` **{node}** {types} on {url}")
                elif kind == "form_definition":
                    ins = meta.get("input_count", 0)
                    method = meta.get("method", "get")
                    lines.append(f"- `form` **{method.upper()}** ({ins} inputs) on {url}")
                elif kind == "overlay_detected":
                    cov = meta.get("coverage", "?")
                    z = meta.get("zIndex", "?")
                    lines.append(f"- `overlay` (z={z}, cov={cov}) on {url}")
                elif kind == "summary":
                    lc = meta.get("listener_count", 0)
                    fc = meta.get("form_count", 0)
                    lines.append(f"- `summary` Listeners: {lc}, Forms: {fc}")
        return "\n".join(lines), {
            "found": len(final_list),
            "scanned_pages": len(visited_pages),
            "pages": final_list,
            "keywords_used": keywords,
            "min_term_overlap": min_term_overlap,
            "engine": engine,
            "required_sites": required_sites,
            "js_links": all_js_links,
            "network_sniff_links": all_network_links,
            "runtime_hits": all_runtime_hits,
            "react_hits": all_react_hits,
            "database_hits": all_database_hits,
            "interaction_hits": all_interaction_hits,
            "log": log,
            "queries_run": queries_to_run,
        }

    # ------------------------------------------------------------------ #
    # Predictive sequencing (unchanged)
    # ------------------------------------------------------------------ #
    def _predict_next_in_sequence(self, urls: List[str]) -> List[str]:
        generated = set()
        re_seq = re.compile(r"([0-9]+)(\.[a-z0-9]+)$", re.IGNORECASE)

        for u in urls:
            match = re_seq.search(u)
            if match:
                original_num_str = match.group(1)
                try:
                    width = len(original_num_str)
                    val = int(original_num_str)
                    for i in range(1, 4):
                        next_val = val + i
                        next_str = f"{next_val:0{width}d}"
                        new_url = (
                            u[: match.start(1)] + next_str + u[match.end(1) :]
                        )
                        generated.add(new_url)
                except ValueError:
                    pass

        return list(generated)

    # ------------------------------------------------------------------ #
    # Sites seeding helpers (unchanged)
    # ------------------------------------------------------------------ #
    def _seed_pages_from_required_sites(
        self,
        required_sites,
        queries,
        probe_cap_per_site=5,
        sitemap_cap_per_site=8,
        hub_cap_per_site=6,
    ):
        out: List[str] = []
        synthetic_search_seeds: set[str] = set()
        explicit_site_seeds: set[str] = set()

        norm_sites = []
        for raw in required_sites or []:
            s = (raw or "").strip()
            if not s:
                continue
            norm_sites.append(
                s.rstrip("/") if "://" in s else "https://" + s.lstrip(".").rstrip("/")
            )

        for s in norm_sites:
            u = s + "/"
            out.append(u)
            explicit_site_seeds.add(u)

        common_sitemaps = [
            "/sitemap.xml",
            "/sitemap_index.xml",
            "/sitemap/sitemap.xml",
            "/sitemap-index.xml",
            "/sitemap.php",
            "/sitemap.txt",
        ]
        for s in norm_sites:
            u = s + "/robots.txt"
            out.append(u)
            explicit_site_seeds.add(u)
            added = 0
            for sm in common_sitemaps:
                if added >= sitemap_cap_per_site:
                    break
                u = s + sm
                out.append(u)
                explicit_site_seeds.add(u)
                added += 1

        hub_paths = [
            "/tag/",
            "/tags/",
            "/category/",
            "/categories/",
            "/archive/",
            "/archives/",
            "/browse/",
            "/collections/",
            "/series/",
            "/authors/",
            "/topics/",
            "/search",
        ]
        for s in norm_sites:
            added = 0
            for hp in hub_paths:
                if added >= hub_cap_per_site:
                    break
                u = s + hp
                out.append(u)
                explicit_site_seeds.add(u)
                added += 1

        def _extra_probes_for_site(base: str, enc_query: str) -> list[str]:
            host = urlparse(base).netloc.lower()
            if "archive.org" in host:
                return [
                    base + f"/search.php?query={enc_query}",
                    base + f"/advancedsearch.php?q={enc_query}",
                    base
                    + (
                        f"/advancedsearch.php?q={enc_query}"
                        f"&fl[]=identifier&fl[]=title&rows=50&page=1&output=json"
                    ),
                    base + f"/details/{enc_query}",
                    base + f"/browse.php?field=subject&query={enc_query}",
                ]
            return []

        if queries:
            for s in norm_sites:
                probes_added = 0
                for qv in queries:
                    if probes_added >= probe_cap_per_site:
                        break
                    qv = (qv or "").strip()
                    if not qv:
                        continue
                    enc = quote_plus(qv)

                    probes = [
                        s + f"/search?q={enc}",
                        s + f"/search?query={enc}",
                        s + f"/?s={enc}",
                        s + f"/search/{enc}",
                    ]
                    probes.extend(_extra_probes_for_site(s, enc))

                    for p in probes:
                        out.append(p)
                        synthetic_search_seeds.add(p)
                        probes_added += 1
                        if (
                            probes_added >= probe_cap_per_site
                            and "archive.org" not in s
                        ):
                            break

        return out, synthetic_search_seeds, explicit_site_seeds

    def _extract_sitemap_urls_from_robots(self, text: str) -> list[str]:
        urls = []
        for line in (text or "").splitlines():
            if line.lower().startswith("sitemap:"):
                u = line.split(":", 1)[1].strip()
                if u.startswith("http"):
                    urls.append(u)
        return urls

    # ------------------------------------------------------------------ #
    # Sync wrapper
    # ------------------------------------------------------------------ #
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asyncio.run(self._execute_async(payload, params=params))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "rare aphex twin interview",
            "timeout": 5,
            "mode": "pages",
            "scan_limit": 5,
            "search_results_cap": 256,
            "search_page_limit": 1,
            "search_per_page": 50,
            "verify": False,  # not used for pages
            "extensions": "",
            "url_keywords": "archive,download",
            "engine": "duckduckgo",
            "site_require": "",
            "use_js": False,
            "return_all_js_links": False,
            "max_links_per_page": 500,
            "strict_keywords": False,
            "use_network_sniff": False,
            "return_network_sniff_links": False,
            "use_runtime_sniff": False,
            "return_runtime_sniff_hits": False,
            "use_react_sniff": False,
            "return_react_sniff_hits": False,
            "use_database_sniff": False,
            "return_database_sniff_hits": False,
            "use_interaction_sniff": False,
            "return_interaction_sniff_hits": False,
            "min_term_overlap": 1,
            "max_depth": 0,
            "max_pages_total": 32,
            "subpipeline": "",
            "use_database": False,
            "db_path": "link_corpus.db",
            "block_resources": False,
            "blocked_resource_types": "image,stylesheet,font",
            "block_domains": True,
            "blocked_domains": "",
            "db_seed_limit": 250,
            "db_seed_max_age_days": None,
            "db_allow_rescan": False,
            "memory_sources": "",
            "http_retries": 2,
            "http_max_conn_per_host": 8,
            "http_verify_tls": True,
            "http_ca_bundle": "",
            "use_camoufox": False,
            "camoufox_options": {},
            "searxng_url": "http://127.0.0.1:8080",
        }


BLOCKS.register("pagetracker", PageTrackerBlock)

# ======================= LinkCrawlerBlock ==================================

@dataclass
class LinkCrawlerBlock(BaseBlock):
    """
    LinkCrawlerBlock

    Uses:
      - HTTPSSubmanager (shared aiohttp engine, retries, cooldowns, per-host semaphores)
      - DatabaseSubmanager (via LinkCrawlerStore)

    Behavior:
      - Memory-level dedupe.
      - If use_database=True:
          * Suppresses URLs previously emitted (cross-run).
          * Skips re-fetching seed URLs recently fetched (TTL).

    Reverse-image seed discovery (NEW):
      - Provide either:
          params["image_url"]  (best), OR
          params["image_path"] (fallback; filename-based discovery)
      - Produces seed URLs via SearXNG JSON (preferred) or DDG HTML (fallback),
        then continues the existing shallow crawl logic.
    """

    _HREF_RE = re.compile(r"""href=["'](.*?)["']""", re.IGNORECASE)
    _TEXT_TOKEN_RE = re.compile(r"[a-z0-9]{3,}")

    _CONTENT_HINTS = {
        "video", "watch", "player", "embed", "download", "gallery", "album",
        "archive", "clip", "movie", "film", "series", "episode", "season",
        "mp4", "mkv", "m3u8", "webm"
    }

    _JUNK_HINTS = {
        "login", "signin", "signup", "register", "forgot", "password",
        "terms", "privacy", "policy", "contact", "about", "dmca",
        "facebook.com", "twitter.com", "linkedin.com", "mailto:", "javascript:"
    }

    _DOC_HINTS = {
        "pdf", "ebook", "epub", "paper", "whitepaper", "research", "report",
        "document", "documentation", "manual", "guide", "spec", "datasheet",
        "arxiv", "doi", "slides", "ppt", "pptx"
    }

    _MEDIA_HINTS = {
        "video", "watch", "player", "embed", "download", "stream", "play",
        "m3u8", "mpd", "dash", "hls", "mp4", "mkv", "webm", "mov",
        "mp3", "flac", "m4a", "wav", "ogg", "aac", "ts"
    }

    _IMAGE_HINTS = {
        "image", "img", "photo", "jpg", "jpeg", "png", "gif", "webp", "avif",
        "gallery", "thumbnail", "thumb", "cdn", "media"
    }

    _DOC_EXT_RE = re.compile(r"\.(pdf|epub|mobi|djvu|doc|docx|ppt|pptx|xls|xlsx|txt|rtf)$", re.IGNORECASE)
    _MEDIA_EXT_RE = re.compile(r"\.(mp4|mkv|mov|avi|wmv|flv|webm|m3u8|mpd|ts|m4a|mp3|flac|wav|ogg|aac)$", re.IGNORECASE)
    _IMAGE_EXT_RE = re.compile(r"\.(jpg|jpeg|png|gif|webp|avif|bmp|tiff|svg)$", re.IGNORECASE)

    # ------------------ time helpers (CRITICAL PATCH) ------------------

    @staticmethod
    def _now() -> float:
        import time as _time
        return _time.time()

    @staticmethod
    def _ms_since(t0: float) -> int:
        import time as _time
        return int((_time.time() - t0) * 1000)

    # ------------------ Query Augmentation ------------------

    def _augment_query_by_mode(self, q: str, mode: str) -> str:
        q = (q or "").strip()
        mode = (mode or "search").lower().strip()

        if mode == "docs":
            if "filetype:" not in q.lower():
                q = f'{q} (pdf OR filetype:pdf OR doc OR docx OR ppt OR pptx)'
            return q.strip()

        if mode == "media":
            low = q.lower()
            if not any(x in low for x in ("m3u8", "mp4", "webm", "mpd", "mp3", "flac")):
                q = f'{q} (m3u8 OR mp4 OR webm OR mpd OR mp3 OR flac)'
            return q.strip()

        if mode == "images":
            low = q.lower()
            if not any(x in low for x in ("jpg", "jpeg", "png", "webp", "image", "gallery")):
                q = f'{q} (jpg OR png OR webp OR image OR gallery)'
            return q.strip()

        return q

    def _looks_like_image_url(self, u: str) -> bool:
        u = (u or "").lower()
        return bool(self._IMAGE_EXT_RE.search(u)) or any(x in u for x in ("image", "img", "photo"))

    def _looks_like_video_url(self, u: str) -> bool:
        u = (u or "").lower()
        return bool(self._MEDIA_EXT_RE.search(u)) or any(u.endswith(x) for x in (".m3u8", ".mpd"))

    # ------------------ Parsing Logic ------------------

    def _extract_links(self, html: str, base_url: str, mode: str = "search") -> Tuple[List[str], List[str]]:
        all_links: set[str] = set()
        content_candidates: set[str] = set()

        mode = (mode or "search").lower().strip()

        if mode == "docs":
            hint_set = self._DOC_HINTS
            ext_re = self._DOC_EXT_RE
        elif mode == "media":
            hint_set = self._MEDIA_HINTS
            ext_re = self._MEDIA_EXT_RE
        elif mode == "images":
            hint_set = self._IMAGE_HINTS
            ext_re = self._IMAGE_EXT_RE
        else:
            hint_set = self._CONTENT_HINTS
            ext_re = self._MEDIA_EXT_RE

        for m in self._HREF_RE.finditer(html or ""):
            raw = m.group(1)
            if not raw or raw.startswith(("#", "javascript:", "mailto:", "tel:")):
                continue

            try:
                full_url = urljoin(base_url, raw)
                parsed = urlparse(full_url)
                if parsed.scheme not in ("http", "https"):
                    continue

                u_lower = full_url.lower()
                if any(bad in u_lower for bad in self._JUNK_HINTS):
                    continue

                all_links.add(full_url)

                score = 0
                path_lower = (parsed.path or "").lower()

                if any(hint in u_lower for hint in hint_set):
                    score += 2
                if ext_re.search(path_lower):
                    score += 6
                if any(tok in path_lower for tok in ("/watch", "/player", "/embed", "/download", "/view", "/details")):
                    score += 1

                if mode in ("docs", "media", "images") and score <= 0:
                    continue

                if score > 0:
                    content_candidates.add(full_url)

            except Exception:
                continue

        return list(all_links), list(content_candidates)

    def _extract_lexicon(self, html: str) -> List[str]:
        from collections import Counter
        text = re.sub(r"<[^>]+>", " ", html or "")
        text = re.sub(r"\s+", " ", text).lower()

        words = self._TEXT_TOKEN_RE.findall(text)
        stops = {
            "the", "and", "that", "this", "with", "from", "your", "have", "are",
            "for", "not", "but", "what", "can"
        }
        filtered = [w for w in words if w not in stops]

        counts = Counter(filtered)
        return [w for w, _c in counts.most_common(20)]

    # ------------------ DB wiring ------------------

    def _make_store(self, db_path: str) -> "LinkCrawlerStore":
        cfg = submanagers.DatabaseConfig(path=db_path)
        db = submanagers.DatabaseSubmanager(cfg, logger=DEBUG_LOGGER)
        store = LinkCrawlerStore(db=db)
        store.ensure_schema()
        return store

    # ------------------ Reverse-image helpers (NEW) ------------------

    async def _coerce_reverse_image_inputs(
        self,
        *,
        image_url: str,
        image_path: str,
        timeout: float,
        log: List[str],
        ffmpeg_bin: str = "ffmpeg",
    ) -> Tuple[str, str, List[str]]:
        """
        Coerce reverse-image inputs into either:
          - a usable remote URL (image_url), OR
          - a usable local image path (image_path)
        Handles:
          - local video -> extract first frame via ffmpeg
          - remote non-image -> download to temp, then extract if video-like
        """
        import tempfile
        import subprocess
        from urllib.parse import urlparse

        temp_files: List[str] = []

        image_url = (image_url or "").strip()
        image_path = (image_path or "").strip()

        IMG_EXTS = (".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp", ".tiff", ".avif", ".svg")
        VID_EXTS = (".mp4", ".mkv", ".mov", ".avi", ".webm", ".wmv", ".flv", ".m4v", ".gif")

        def _is_http_url(u: str) -> bool:
            try:
                p = urlparse(u)
                return p.scheme in ("http", "https") and bool(p.netloc)
            except Exception:
                return False

        def _looks_like_image_file(path: str) -> bool:
            return (path or "").lower().endswith(IMG_EXTS)

        def _looks_like_video_file(path: str) -> bool:
            low = (path or "").lower()
            return low.endswith(VID_EXTS) or any(x in low for x in (".m3u8", ".mpd"))

        def _looks_like_image_url(u: str) -> bool:
            low = (u or "").lower()
            return low.endswith(IMG_EXTS) or bool(self._IMAGE_EXT_RE.search(low))

        async def _download_to_temp(url: str) -> str:
            import aiohttp

            parsed = urlparse(url)
            base = os.path.basename(parsed.path or "")
            ext = os.path.splitext(base)[1].lower()
            if not ext or len(ext) > 8:
                ext = ".bin"

            fd, outp = tempfile.mkstemp(prefix="revimg_", suffix=ext)
            os.close(fd)
            temp_files.append(outp)

            try:
                async with aiohttp.ClientSession() as session:
                    async with session.get(
                        url,
                        timeout=aiohttp.ClientTimeout(total=timeout),
                        headers={"User-Agent": "Mozilla/5.0 PromptChat/LinkCrawler"},
                    ) as resp:
                        resp.raise_for_status()
                        with open(outp, "wb") as f:
                            while True:
                                chunk = await resp.content.read(1024 * 64)
                                if not chunk:
                                    break
                                f.write(chunk)
            except Exception as e:
                log.append(f"[Crawler][RevImg] download failed url={url!r}: {e}")
                return ""

            return outp

        def _ffmpeg_extract_first_frame(src_path: str) -> str:
            fd, outp = tempfile.mkstemp(prefix="revimg_frame_", suffix=".png")
            os.close(fd)
            temp_files.append(outp)

            cmd = [ffmpeg_bin, "-y", "-i", src_path, "-frames:v", "1", outp]
            try:
                p = subprocess.run(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=max(5, int(timeout)),
                    check=False,
                )
                if p.returncode != 0 or not os.path.exists(outp) or os.path.getsize(outp) <= 0:
                    err = (p.stderr or b"")[:800].decode("utf-8", "ignore")
                    log.append(f"[Crawler][RevImg] ffmpeg extract failed rc={p.returncode} err={err}")
                    return ""
            except Exception as e:
                log.append(f"[Crawler][RevImg] ffmpeg error: {e}")
                return ""

            return outp

        # 1) Prefer local path if valid
        if image_path:
            if not os.path.exists(image_path):
                log.append(f"[Crawler][RevImg] image_path does not exist: {image_path}")
                image_path = ""
            else:
                if _looks_like_image_file(image_path):
                    return "", image_path, temp_files
                if _looks_like_video_file(image_path):
                    frame = _ffmpeg_extract_first_frame(image_path)
                    if frame:
                        log.append(f"[Crawler][RevImg] extracted frame -> {frame}")
                        return "", frame, temp_files
                # Last resort: assume image anyway
                return "", image_path, temp_files

        # 2) URL input
        if image_url and _is_http_url(image_url):
            # If it already looks like an image URL, keep it
            if _looks_like_image_url(image_url):
                return image_url, "", temp_files

            # Otherwise download and try to coerce into an image
            tmp = await _download_to_temp(image_url)
            if not tmp:
                return image_url, "", temp_files

            if _looks_like_image_file(tmp):
                return "", tmp, temp_files

            frame = _ffmpeg_extract_first_frame(tmp)
            if frame:
                return "", frame, temp_files

            return "", tmp, temp_files

        return "", "", temp_files

    async def _reverse_image_search_seeds(
            self,
            *,
            image_url: str,
            image_path: str,
            engine: str,
            limit: int,
            timeout: float,
            log: List[str],
            searxng_url: str,
    ) -> List[str]:
        """
        Enhanced reverse-image discovery.
        1. If image_path is provided, uploads to Catbox.moe to get a public URL.
        2. Builds targeted footprint queries for Yandex, Google, and Bing.
        3. Fetches seeds via SearXNG.
        """
        import aiohttp
        engine = (engine or "both").lower().strip()
        limit = max(1, int(limit or 10))

        # 1. Catbox Upload (if local path exists)
        if image_path and os.path.exists(image_path) and not image_url:
            log.append(f"[Crawler][RevImg] Uploading {os.path.basename(image_path)} to Catbox...")
            try:
                async with aiohttp.ClientSession() as session:
                    data = aiohttp.FormData()
                    data.add_field("reqtype", "fileupload")
                    # Anonymous upload (no userhash required)
                    with open(image_path, "rb") as f:
                        data.add_field("fileToUpload", f, filename=os.path.basename(image_path))
                        async with session.post("https://catbox.moe/user/api.php", data=data, timeout=timeout) as resp:
                            if resp.status == 200:
                                image_url = (await resp.text()).strip()
                                log.append(f"[Crawler][RevImg] Catbox URL: {image_url}")
                            else:
                                log.append(f"[Crawler][RevImg] Catbox upload failed: {resp.status}")
            except Exception as e:
                log.append(f"[Crawler][RevImg] Catbox error: {e}")

        queries: List[str] = []

        # 2. Targeted Footprint Queries
        if image_url:
            # Footprint: Search for the URL itself across big visual engines
            queries.append(f'"{image_url}"')
            queries.append(f'site:yandex.com "{image_url}"')
            queries.append(f'site:bing.com "{image_url}"')
            queries.append(f'site:google.com "{image_url}"')
            # Visual mirrors
            queries.append(f'"{image_url}" (source OR original OR mirror)')

        # Fallback Filename logic (still useful for Yandex/Bing indexing)
        if image_path:
            fn = os.path.basename(image_path)
            queries.append(f'"{fn}"')
            stem = os.path.splitext(fn)[0]
            if stem and len(stem) > 4:
                queries.append(f'"{stem}" source')

        if not queries:
            log.append("[Crawler][RevImg] No usable seeds after coercion.")
            return []

        # 3. Multi-Engine Harvest via SearXNG
        seeds: List[str] = []
        seen: Set[str] = set()
        per_query = max(15, limit * 2)

        for q in queries:
            found = await self._search_searxng_json(searxng_url, q, per_query, timeout, log)
            for u in found:
                u = (u or "").strip()
                # Filter engine noise
                if not u or u in seen or any(
                        x in u.lower() for x in ("google.com/search", "bing.com/images", "yandex.ru/images")):
                    continue
                seen.add(u)
                seeds.append(u)
                if len(seeds) >= limit: break
            if len(seeds) >= limit: break

        log.append(f"[Crawler][RevImg] Seeds discovered: {len(seeds)}")
        return seeds[:limit]
    # ------------------ Search Helpers ------------------

    async def _search_duckduckgo_html(self, query: str, limit: int, log: List[str]) -> List[str]:
        import aiohttp
        urls: List[str] = []
        try:
            async with aiohttp.ClientSession() as session:
                pages = (limit // 30) + 1
                for i in range(pages):
                    data = {"q": query, "b": "", "kl": "us-en", "s": str(i * 30)}
                    headers = {
                        "User-Agent": (
                            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                            "AppleWebKit/537.36 (KHTML, like Gecko) "
                            "Chrome/91.0.4472.124 Safari/537.36"
                        )
                    }
                    async with session.post("https://html.duckduckgo.com/html/", data=data, headers=headers) as resp:
                        if resp.status != 200:
                            break
                        text = await resp.text()
                        for m in re.finditer(r'class="result__a" href="(.*?)"', text):
                            u = m.group(1)
                            if "uddg=" in u:
                                try:
                                    u = unquote(u.split("uddg=")[1].split("&")[0])
                                except Exception:
                                    pass
                            urls.append(u)
                            if len(urls) >= limit:
                                return urls
            log.append(f"[Crawler][DDG] Found {len(urls)} results.")
        except Exception as e:
            log.append(f"[Crawler][DDG] Error: {e}")
        return urls[:limit]

    async def _search_searxng_json(self, base_url: str, query: str, limit: int, timeout: float, log: List[str]) -> List[str]:
        import aiohttp
        import json

        urls: List[str] = []
        base_url = (base_url or "").strip() or "http://127.0.0.1:8080"

        search_url = base_url.rstrip("/") + "/search"
        max_pages = min(6, (limit // 10) + 1)

        try:
            async with aiohttp.ClientSession() as session:
                for page_idx in range(1, max_pages + 1):
                    if len(urls) >= limit:
                        break
                    params = {"q": query, "format": "json", "pageno": str(page_idx)}
                    try:
                        async with session.get(
                            search_url,
                            params=params,
                            timeout=aiohttp.ClientTimeout(total=timeout)
                        ) as resp:
                            if resp.status == 403:
                                log.append(f"[Crawler][SearXNG] HTTP 403 on page {page_idx}. Stopping.")
                                break
                            if resp.status != 200:
                                log.append(f"[Crawler][SearXNG] HTTP {resp.status} on page {page_idx}.")
                                break

                            data = json.loads(await resp.text())
                            results = data.get("results", []) or []
                            if not results:
                                break

                            for res in results:
                                u = res.get("url")
                                if u:
                                    urls.append(u)
                                if len(urls) >= limit:
                                    break

                    except Exception as req_err:
                        log.append(f"[Crawler][SearXNG] Request error page {page_idx}: {req_err}")
                        break

            log.append(f"[Crawler][SearXNG] Found {len(urls)} results for query={query!r}.")
        except Exception as e:
            log.append(f"[Crawler][SearXNG] General Error: {e}")

        return urls[:limit]

    async def _search_google_cse(self, query: str, limit: int, log: List[str]) -> List[str]:
        import aiohttp
        cx = os.environ.get("GOOGLE_CSE_ID")
        key = os.environ.get("GOOGLE_API_KEY")
        if not cx or not key:
            log.append("[Crawler][GoogleCSE] Missing GOOGLE_CSE_ID or GOOGLE_API_KEY.")
            return []

        urls: List[str] = []
        base_url = "https://www.googleapis.com/customsearch/v1"
        limit = min(limit, 100)

        try:
            async with aiohttp.ClientSession() as session:
                for start_index in range(1, limit + 1, 10):
                    params = {"q": query, "cx": cx, "key": key, "num": "10", "start": str(start_index)}
                    async with session.get(base_url, params=params) as resp:
                        if resp.status != 200:
                            log.append(f"[Crawler][GoogleCSE] API Error: {resp.status}")
                            break
                        data = await resp.json()
                        items = data.get("items", []) or []
                        if not items:
                            break
                        for item in items:
                            link = item.get("link")
                            if link:
                                urls.append(link)
                        if len(urls) >= limit:
                            break
            log.append(f"[Crawler][GoogleCSE] Found {len(urls)} results.")
        except Exception as e:
            log.append(f"[Crawler][GoogleCSE] Error: {e}")

        return urls[:limit]

    # ------------------ Execution ------------------

    async def _execute_async(self, payload: Any, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        log: List[str] = []

        query = str(params.get("query", "") or str(payload or "")).strip()
        engine = str(params.get("engine", "duckduckgo")).lower().strip()
        mode = str(params.get("mode", "search") or "search").lower().strip()

        max_results = int(params.get("max_results", 20))
        searxng_url = str(params.get("searxng_url", "") or "").strip()
        http_timeout = float(params.get("timeout", 10.0))

        retries = int(params.get("retries", 2))
        max_bytes = int(params.get("max_bytes", 4_000_000))
        verify = bool(params.get("verify", True))
        proxy = str(params.get("proxy", "") or "").strip() or None
        user_agent = str(params.get("user_agent", "Mozilla/5.0 PromptChat/LinkCrawler"))

        links_key = str(params.get("links_key", "scraped_links"))
        domains_key = str(params.get("domains_key", "scraped_domains"))
        lexicon_key = str(params.get("lexicon_key", "scraped_lexicon"))

        use_database = bool(params.get("use_database", False))
        db_path = str(params.get("db_path", "link_corpus.db"))
        seed_ttl_seconds = float(params.get("seed_ttl_seconds", 6 * 3600))

        ffmpeg_bin = str(params.get("ffmpeg_bin", "ffmpeg") or "ffmpeg")

        DEBUG_LOGGER.log_message(
            f"[Crawler] start | query={query!r} mode={mode} engine={engine} "
            f"max_results={max_results} timeout={http_timeout} retries={retries} "
            f"use_database={use_database} ffmpeg_bin={ffmpeg_bin!r} links_key={links_key!r}"
        )

        store: Optional["LinkCrawlerStore"] = None
        if use_database:
            try:
                store = self._make_store(db_path)
                log.append(f"[Crawler][DB] Enabled db_path={db_path} seed_ttl_seconds={seed_ttl_seconds:.0f}")
                DEBUG_LOGGER.log_message(f"[Crawler][DB] init ok | db_path={db_path}")
            except Exception as e:
                store = None
                use_database = False
                log.append(f"[Crawler][DB] Init failed: {e} (continuing without DB)")
                DEBUG_LOGGER.log_message(f"[Crawler][DB] init FAILED: {e} (DB disabled)")

        # 1) Gather seeds
        seed_urls: List[str] = []

        image_url = str(params.get("image_url", "") or "").strip()
        image_path = str(params.get("image_path", "") or "").strip()
        reverse_engine = str(params.get("reverse_engine", "both") or "both").lower().strip()
        reverse_max_results = int(params.get("reverse_max_results", max_results))
        reverse_timeout = float(params.get("reverse_timeout", max(20.0, http_timeout)))

        if params.get("seeds"):
            raw_seeds = str(params.get("seeds")).split(",")
            seed_urls = [s.strip() for s in raw_seeds if s.strip()]
            log.append(f"[Crawler] Using {len(seed_urls)} explicit seeds.")
            DEBUG_LOGGER.log_message(f"[Crawler] seeds=explicit count={len(seed_urls)}")

        elif image_url or image_path:
            DEBUG_LOGGER.log_message(
                f"[Crawler] reverse-image seeds | engine={reverse_engine} "
                f"image_url={'YES' if bool(image_url) else 'NO'} image_path={'YES' if bool(image_path) else 'NO'} "
                f"limit={reverse_max_results} timeout={reverse_timeout} ffmpeg_bin={ffmpeg_bin!r}"
            )

            coerced_url, coerced_path, temp_files = await self._coerce_reverse_image_inputs(
                image_url=image_url,
                image_path=image_path,
                timeout=reverse_timeout,
                log=log,
                ffmpeg_bin=ffmpeg_bin,
            )

            if not coerced_url and not coerced_path:
                log.append("[Crawler][RevImg] Could not coerce image_url/image_path into usable input.")
                return "No operation.", {"error": "reverse_image_input_invalid", "log": log}

            seed_urls = await self._reverse_image_search_seeds(
                image_url=coerced_url,
                image_path=coerced_path,
                engine=reverse_engine,
                limit=reverse_max_results,
                timeout=reverse_timeout,
                log=log,
                searxng_url=searxng_url,
            )

            if temp_files:
                try:
                    for fp in temp_files:
                        if fp and os.path.exists(fp):
                            os.remove(fp)
                except Exception as e:
                    log.append(f"[Crawler][RevImg] temp cleanup error: {e}")

            if not seed_urls:
                log.append("[Crawler][RevImg] No seeds found from reverse-image search.")
                DEBUG_LOGGER.log_message("[Crawler][RevImg] no seeds found")

        elif query:
            search_q = self._augment_query_by_mode(query, mode)
            DEBUG_LOGGER.log_message(f"[Crawler] search | engine={engine} mode={mode} q={search_q!r}")

            if engine == "searxng":
                seed_urls = await self._search_searxng_json(searxng_url, search_q, max_results, http_timeout, log)
            elif engine == "google_cse":
                seed_urls = await self._search_google_cse(search_q, max_results, log)
            else:
                seed_urls = await self._search_duckduckgo_html(search_q, max_results, log)

        else:
            log.append("[Crawler] No query, seeds, or image provided.")
            DEBUG_LOGGER.log_message("[Crawler] no-op: missing query and seeds and image")
            return "No operation.", {"log": log}

        DEBUG_LOGGER.log_message(f"[Crawler] seeds collected | count={len(seed_urls)}")

        # 2) Shallow crawl (TTL gating via DB) using HTTPSSubmanager
        collected_links: Set[str] = set()
        collected_domains: Set[str] = set()
        collected_lexicon: Set[str] = set()

        for s in seed_urls:
            if not s:
                continue
            collected_links.add(s)
            try:
                collected_domains.add(urlparse(s).netloc)
            except Exception:
                pass

        now_ts = self._now()
        seeds_to_fetch = seed_urls

        if store:
            try:
                seeds_to_fetch = [
                    s for s in seed_urls
                    if store.seed_should_fetch(s, ttl_seconds=seed_ttl_seconds, now_ts=now_ts)
                ]
                skipped = len(seed_urls) - len(seeds_to_fetch)
                if skipped:
                    msg = f"[Crawler][DB] Skipping {skipped} seed(s) due to TTL."
                    log.append(msg)
                    DEBUG_LOGGER.log_message(msg)
            except Exception as e:
                log.append(f"[Crawler][DB] TTL gating failed: {e} (continuing without gating)")
                seeds_to_fetch = seed_urls

        DEBUG_LOGGER.log_message(f"[Crawler] fetch plan | total_seeds={len(seed_urls)} to_fetch={len(seeds_to_fetch)}")

        sem = asyncio.Semaphore(int(params.get("max_concurrency", 12)))

        async with submanagers.HTTPSSubmanager(
            user_agent=user_agent,
            timeout=http_timeout,
            retries=retries,
            max_bytes=max_bytes,
            proxy=proxy,
            verify=verify,
            ca_bundle=str(params.get("ca_bundle", "") or "").strip() or None,
            allow_redirects=True,
            enable_cookies=bool(params.get("enable_cookies", True)),
        ) as http:

            async def fetch_and_parse(url: str):
                DEBUG_LOGGER.log_message(f"[Crawler][Page] crawling seed={url}")
                async with sem:
                    t0 = self._now()
                    try:
                        status_h, hdrs = await http.head(url)
                        ctype = (hdrs.get("Content-Type") or hdrs.get("content-type") or "").lower()

                        if store:
                            try:
                                store.seed_mark_fetched(url, status=int(status_h or 0), now_ts=self._now())
                            except Exception as e:
                                DEBUG_LOGGER.log_message(f"[Crawler][DB] seed_mark_fetched failed url={url} err={e}")

                        DEBUG_LOGGER.log_message(
                            f"[Crawler][Page] head status={status_h} ms={self._ms_since(t0)} ctype={ctype[:60]!r}"
                        )

                        if ctype and ("text/html" not in ctype):
                            DEBUG_LOGGER.log_message(f"[Crawler][Page] skip non-html seed={url} ctype={ctype[:80]!r}")
                            return

                        html = await http.get_text(url)
                        if not html:
                            DEBUG_LOGGER.log_message(f"[Crawler][Page] empty html seed={url}")
                            return

                        final_url = url  # safe default
                        _links, candidates = self._extract_links(html, final_url, mode=mode)
                        lex = self._extract_lexicon(html)

                        DEBUG_LOGGER.log_message(
                            f"[Crawler][Page] parsed seed={url} hrefs_total={len(_links)} "
                            f"candidates_scored={len(candidates)} lexicon_terms={len(lex)}"
                        )

                        for w in lex:
                            collected_lexicon.add(w)

                        for c in candidates:
                            collected_links.add(c)
                            try:
                                collected_domains.add(urlparse(c).netloc)
                            except Exception:
                                pass

                    except Exception as e:
                        DEBUG_LOGGER.log_message(f"[Crawler][Page] ERROR seed={url} err={e}")

            await asyncio.gather(*[fetch_and_parse(u) for u in seeds_to_fetch])

        DEBUG_LOGGER.log_message(
            f"[Crawler] crawl done | collected_links={len(collected_links)} domains={len(collected_domains)} lex={len(collected_lexicon)}"
        )

        # 3) Write to Memory (dedupe via Memory + optional DB)
        store_obj = Memory.load()
        if not isinstance(store_obj, dict):
            store_obj = {}

        existing_links = store_obj.get(links_key, [])
        if not isinstance(existing_links, list):
            existing_links = []

        existing_urls = {str(x.get("url")) for x in existing_links if isinstance(x, dict) and x.get("url")}

        new_link_objs: List[Dict[str, Any]] = []
        suppressed_by_db = 0
        ts = self._now()

        for u in collected_links:
            if not u:
                continue

            if store:
                try:
                    if store.has_emitted(u):
                        suppressed_by_db += 1
                        continue
                except Exception:
                    # if DB read fails, don’t kill the run
                    pass

            if u in existing_urls:
                if store:
                    try:
                        store.mark_emitted(u, mode=mode, query=query, now_ts=ts)
                    except Exception:
                        pass
                continue

            new_link_objs.append({
                "url": u,
                "source": "linkcrawler",
                "query": query,
                "mode": mode,
                "first_seen": ts,
            })

            if store:
                try:
                    store.mark_emitted(u, mode=mode, query=query, now_ts=ts)
                except Exception:
                    pass

        combined_links = existing_links + new_link_objs
        if len(combined_links) > 2000:
            combined_links = combined_links[-2000:]
        store_obj[links_key] = combined_links

        existing_domains = store_obj.get(domains_key, [])
        if not isinstance(existing_domains, list):
            existing_domains = []
        dom_set = set(existing_domains)
        dom_set.update(collected_domains)
        store_obj[domains_key] = sorted(list(dom_set))[:500]

        existing_lex = store_obj.get(lexicon_key, [])
        if not isinstance(existing_lex, list):
            existing_lex = []
        lex_set = set(existing_lex)
        lex_set.update(collected_lexicon)
        store_obj[lexicon_key] = list(lex_set)[:200]

        Memory.save(store_obj)

        DEBUG_LOGGER.log_message(
            f"[Crawler] memory write | existing={len(existing_links)} new_added={len(new_link_objs)} "
            f"suppressed_by_db={suppressed_by_db} links_key={links_key!r}"
        )

        # 4) Reporting
        lines = [
            "### 🕷️ LinkCrawler Report",
            f"_Query: '{query}' | Mode: {mode} | Engine: {engine} | Seeds: {len(seed_urls)} | Fetched: {len(seeds_to_fetch)}_",
            "",
            f"**Candidates Found (raw):** {len(collected_links)}",
            f"**New Links Added to Memory:** {len(new_link_objs)}",
            f"**Domains Scanned:** {len(collected_domains)}",
            f"**DB Cache:** {'ON' if use_database else 'OFF'}",
            f"**ffmpeg_bin:** {ffmpeg_bin}",
        ]
        if use_database:
            lines.append(f"**db_path:** {db_path}")
            lines.append(f"**Suppressed By DB:** {suppressed_by_db}")

        lines.append("")
        lines.append("**Sample New Links (added to Memory):**")
        for o in new_link_objs[:10]:
            lines.append(f"- {o['url']}")

        if log:
            lines.append("\n**Log:**")
            lines.extend(log)

        return "\n".join(lines), {
            "found_count": len(collected_links),
            "new_added": len(new_link_objs),
            "suppressed_by_db": suppressed_by_db,
            "memory_key": links_key,
            "mode": mode,
            "engine": engine,
            "seed_count": len(seed_urls),
            "fetched_seed_count": len(seeds_to_fetch),
            "use_database": use_database,
            "db_path": db_path if use_database else None,
            "ffmpeg_bin": ffmpeg_bin,
            "log": log,
        }

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asyncio.run(self._execute_async(payload, params))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "Scraping query",
            "mode": "search / docs / media / images",
            "seeds": "Comma-separated list of starting URLs (optional override)",
            "engine": "duckduckgo / searxng / google_cse",
            "searxng_url": "http://127.0.0.1:8080",
            "max_results": 20,
            "timeout": 10.0,
            "max_concurrency": 12,

            # HTTPSSubmanager knobs
            "retries": 2,
            "max_bytes": 4_000_000,
            "verify": True,
            "proxy": "",
            "ca_bundle": "",
            "user_agent": "Mozilla/5.0 PromptChat/LinkCrawler",
            "enable_cookies": True,

            "links_key": "scraped_links",
            "domains_key": "scraped_domains",
            "lexicon_key": "scraped_lexicon",

            # Reverse-image (seed discovery)
            "image_url": "Remote image URL for reverse-image seed discovery (best)",
            "image_path": "Local file path for reverse-image seed discovery (fallback; filename/stem)",
            "reverse_engine": "both / google / bing (affects query augmentation only)",
            "reverse_max_results": 20,
            "reverse_timeout": 20.0,

            "ffmpeg_bin": "ffmpeg",

            # DB
            "use_database": False,
            "db_path": "link_corpus.db",
            "seed_ttl_seconds": 21600,
        }


# register
BLOCKS.register("linkcrawler", LinkCrawlerBlock)


# ======================= URLScraperBlock ==================================

@dataclass
class URLScraperBlock(BaseBlock):
    """
    URLScraperBlock
    ---------------
    Reads one or more Memory keys (memory_sources), extracts URL candidates,
    canonicalizes/dedupes them, and OVERWRITES those SAME Memory keys with
    the cleaned URL list.

    This is meant to sit between LinkCrawler -> PageTracker:
      - LinkCrawler writes Memory["linkcrawler_urls"] = [...]
      - URLScraper reads Memory["linkcrawler_urls"], cleans, writes it back
      - PageTracker reads Memory["linkcrawler_urls"] and gets clean URLs

    Outputs:
      - urls_clean (merged across keys)
      - urls_rejected (with reasons)
      - canonical_map (original -> canonical)
      - per_key_stats
    """

    # Fast URL extraction (good enough for messy logs)
    _URL_RE = re.compile(r"https?://[^\s\"'<>\\)\]]+", re.IGNORECASE)

    # Common trash extensions that aren’t "pages"
    DEFAULT_IGNORED_EXTENSIONS = {
        ".css", ".js", ".json", ".xml", ".svg",
        ".png", ".jpg", ".jpeg", ".gif", ".webp", ".ico",
        ".woff", ".woff2", ".ttf", ".eot", ".map",
        ".mp4", ".webm", ".m4v", ".mp3", ".m4a", ".wav", ".flac", ".ogg",
        ".zip", ".rar", ".7z", ".tar", ".gz", ".bz2", ".xz",
    }

    # Params to always drop (tracking / affiliate noise)
    DEFAULT_DROP_QUERY_KEYS = {
        # utm
        "utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
        "utm_id", "utm_name", "utm_reader", "utm_viz_id",
        # ad platforms
        "gclid", "dclid", "gbraid", "wbraid", "fbclid", "msclkid",
        "ttclid", "twclid", "yclid", "mc_cid", "mc_eid",
        # generic trackers
        "ref", "ref_src", "ref_url", "spm", "spm_id_from",
        "igshid", "si", "feature", "app", "mkt_tok",
        # common session-ish keys
        "session", "sessionid", "sid", "phpsessid", "jsessionid",
    }

    # Paths that often represent index documents
    INDEX_FILENAMES = {
        "index.html", "index.htm", "default.asp", "default.aspx",
        "index.php", "home.html", "home.htm",
    }

    # Lowercase host and optionally strip common mobile subdomains
    DEFAULT_STRIP_SUBDOMAINS = {
        "m", "mobile", "amp",
    }

    def __post_init__(self):
        pass

    # ------------------------------
    # Public execution
    # ------------------------------
    async def _execute_async(
        self, payload: Any, *, params: Dict[str, Any]
    ) -> Tuple[str, Dict[str, Any]]:
        memory_sources_raw = str(params.get("memory_sources", "") or "").strip()
        keys = [k.strip() for k in memory_sources_raw.split(",") if k.strip()]

        if not keys:
            txt = "[context]\n\n[lexicon]\n\n"
            return txt, {"count": 0, "error": "URLScraper requires params['memory_sources']"}

        # Tuning knobs
        max_url_len = int(params.get("max_url_len", 4096))
        strip_fragments = bool(params.get("strip_fragments", True))
        force_https = bool(params.get("force_https", False))
        keep_www = bool(params.get("keep_www", True))
        sort_query = bool(params.get("sort_query", True))
        drop_tracking_params = bool(params.get("drop_tracking_params", True))
        drop_query_keys_raw = params.get("drop_query_keys", "")
        write_sidecars = bool(params.get("write_sidecars", True))
        normalize_slash = bool(params.get("normalize_slash", True))
        drop_default_ports = bool(params.get("drop_default_ports", True))
        strip_known_subdomains = bool(params.get("strip_known_subdomains", False))

        # Filtering controls
        ignored_exts_raw = params.get("ignored_extensions", "")
        blocked_domains_raw = params.get("blocked_domains", "")

        ignored_exts = self._parse_csv_set(ignored_exts_raw) or set(self.DEFAULT_IGNORED_EXTENSIONS)
        blocked_domains = self._parse_csv_set(blocked_domains_raw)

        drop_query_keys = set(self.DEFAULT_DROP_QUERY_KEYS)
        if isinstance(drop_query_keys_raw, str) and drop_query_keys_raw.strip():
            drop_query_keys |= {x.strip().lower() for x in drop_query_keys_raw.split(",") if x.strip()}

        # Load memory
        try:
            mem = Memory.load()
        except Exception as e:
            txt = "[context]\n\n[lexicon]\n\n"
            return txt, {"count": 0, "error": f"Memory.load failed: {e}"}

        all_clean: List[str] = []
        all_rejected: List[Dict[str, Any]] = []
        all_map: Dict[str, str] = {}
        per_key_stats: Dict[str, Dict[str, Any]] = {}

        for key in keys:
            raw = mem.get(key)
            if not raw:
                per_key_stats[key] = {"in": 0, "candidates": 0, "accepted": 0, "rejected": 0}
                # Also overwrite missing/empty to empty list to stabilize pipelines
                mem[key] = []
                if write_sidecars:
                    mem[f"{key}_rejected"] = []
                    mem[f"{key}_canonical_map"] = {}
                    mem[f"{key}_stats"] = per_key_stats[key]
                continue

            # 1) extract candidates
            candidates = self._extract_url_candidates(raw)
            in_count = self._estimate_in_count(raw)

            # 2) canonicalize / dedupe
            clean_list: List[str] = []
            rejected: List[Dict[str, Any]] = []
            cmap: Dict[str, str] = {}
            seen = set()

            for original in candidates:
                rec = self._canonicalize(
                    original=original,
                    max_url_len=max_url_len,
                    ignored_exts=ignored_exts,
                    blocked_domains=blocked_domains,
                    strip_fragments=strip_fragments,
                    force_https=force_https,
                    keep_www=keep_www,
                    sort_query=sort_query,
                    drop_tracking_params=drop_tracking_params,
                    drop_query_keys=drop_query_keys,
                    normalize_slash=normalize_slash,
                    drop_default_ports=drop_default_ports,
                    strip_known_subdomains=strip_known_subdomains,
                )

                if rec["status"] != "accepted":
                    rejected.append({"url": original, "reason": rec.get("reason", "rejected")})
                    continue

                canon = rec["canonical"]
                cmap[original] = canon

                if canon in seen:
                    continue
                seen.add(canon)
                clean_list.append(canon)

            # 3) OVERWRITE the same key
            mem[key] = clean_list

            # 4) sidecars
            st = {
                "in": int(in_count),
                "candidates": len(candidates),
                "accepted": len(clean_list),
                "rejected": len(rejected),
            }
            per_key_stats[key] = st

            if write_sidecars:
                mem[f"{key}_rejected"] = rejected
                mem[f"{key}_canonical_map"] = cmap
                mem[f"{key}_stats"] = st

            all_clean.extend(clean_list)
            all_rejected.extend(rejected)
            all_map.update(cmap)

        # Save memory back
        try:
            Memory.save(mem)
        except Exception as e:
            DEBUG_LOGGER.log_message(f"[URLScraper] Memory.save failed: {e}")

        merged_clean = list(dict.fromkeys(all_clean))

        DEBUG_LOGGER.log_message(
            f"[URLScraper] keys={keys} merged_accepted={len(merged_clean)} merged_rejected={len(all_rejected)}"
        )

        out_text = "[context]\n" + "\n".join(merged_clean) + "\n\n[lexicon]\n\n"
        meta = {
            "count": len(merged_clean),
            "urls_clean": merged_clean,
            "urls_rejected": all_rejected,
            "canonical_map": all_map,
            "per_key_stats": per_key_stats,
            "memory_sources": keys,
            # for collectors
            "urls": merged_clean,
        }
        return out_text, meta

    # Sync wrapper
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asyncio.run(self._execute_async(payload, params=params))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "memory_sources": "scraped_links",
            "max_url_len": 4096,
            "strip_fragments": True,
            "force_https": False,
            "keep_www": True,
            "sort_query": True,
            "drop_tracking_params": True,
            "drop_query_keys": "",  # extra keys
            "write_sidecars": True,
            "normalize_slash": True,
            "drop_default_ports": True,
            "strip_known_subdomains": False,  # strip m./amp./mobile if True
            "ignored_extensions": "",          # csv override
            "blocked_domains": "",             # csv
        }

    # ------------------------------
    # Candidate extraction
    # ------------------------------
    def _estimate_in_count(self, raw: Any) -> int:
        # Just a rough number so stats are stable
        if raw is None:
            return 0
        if isinstance(raw, list):
            return len(raw)
        return 1

    def _extract_url_candidates(self, raw: Any) -> List[str]:
        out: List[str] = []
        seen = set()

        def push(s: str):
            s = (s or "").strip()
            if not s:
                return
            # If it looks like a URL, keep
            if s.startswith(("http://", "https://")):
                if s not in seen:
                    seen.add(s)
                    out.append(s)
                return
            # If it's a blob of text, scan for URLs
            for m in self._URL_RE.finditer(s[:250_000]):
                u = m.group(0)
                if u and u not in seen:
                    seen.add(u)
                    out.append(u)

        def walk(x: Any):
            if x is None:
                return
            if isinstance(x, str):
                push(x)
                return
            if isinstance(x, (int, float)):
                push(str(x))
                return
            if isinstance(x, dict):
                # prioritize known URL-ish fields
                for k in ("url", "href", "link", "final_url", "source_url", "page", "request_url"):
                    v = x.get(k)
                    if isinstance(v, str) and v.strip():
                        push(v)
                # sometimes dicts store text blobs
                for k in ("text", "html", "body", "snippet"):
                    v = x.get(k)
                    if isinstance(v, str) and v.strip():
                        push(v)
                # and nested
                for v in x.values():
                    if isinstance(v, (list, dict)):
                        walk(v)
                return
            if isinstance(x, list):
                for it in x:
                    walk(it)
                return
            # fallback stringify
            push(str(x))

        walk(raw)
        return out

    # ------------------------------
    # Canonicalization
    # ------------------------------
    def _canonicalize(
        self,
        *,
        original: str,
        max_url_len: int,
        ignored_exts: set[str],
        blocked_domains: set[str],
        strip_fragments: bool,
        force_https: bool,
        keep_www: bool,
        sort_query: bool,
        drop_tracking_params: bool,
        drop_query_keys: set[str],
        normalize_slash: bool,
        drop_default_ports: bool,
        strip_known_subdomains: bool,
    ) -> Dict[str, Any]:
        s = (original or "").strip()
        if not s:
            return {"status": "rejected", "reason": "empty"}

        if len(s) > max_url_len:
            return {"status": "rejected", "reason": "too_long"}

        if not s.startswith(("http://", "https://")):
            # try to salvage "www.foo.com/path"
            if s.startswith("www."):
                s = "https://" + s
            else:
                return {"status": "rejected", "reason": "not_http"}

        try:
            pu = urlparse(s)
        except Exception:
            return {"status": "rejected", "reason": "malformed"}

        scheme = (pu.scheme or "https").lower()
        netloc = (pu.netloc or "").strip()
        path = pu.path or ""
        query = pu.query or ""
        frag = pu.fragment or ""

        if not netloc:
            return {"status": "rejected", "reason": "missing_host"}

        # Split host:port
        host = netloc.lower()
        port = ""
        if ":" in host:
            host, port = host.rsplit(":", 1)

        host = host.strip(".")
        if not host:
            return {"status": "rejected", "reason": "bad_host"}

        # Blocked domain matching (exact or suffix)
        if blocked_domains:
            for bd in blocked_domains:
                bd = bd.lower().strip()
                if not bd:
                    continue
                if host == bd or host.endswith("." + bd):
                    return {"status": "rejected", "reason": "blocked_domain"}

        # Optionally strip m./amp./mobile.
        if strip_known_subdomains:
            parts = host.split(".")
            if len(parts) >= 3 and parts[0] in self.DEFAULT_STRIP_SUBDOMAINS:
                host = ".".join(parts[1:])

        # Normalize www.
        if not keep_www and host.startswith("www."):
            host = host[4:]

        # Scheme normalization
        if force_https:
            scheme = "https"

        # Default port stripping
        if drop_default_ports and port:
            if (scheme == "http" and port == "80") or (scheme == "https" and port == "443"):
                port = ""

        netloc2 = host + (f":{port}" if port else "")

        # Path normalization
        path = self._safe_unquote_path(path)

        # Drop index filenames (index.html etc.)
        low_path = path.lower()
        if low_path.endswith(tuple("/" + x for x in self.INDEX_FILENAMES)):
            path = path[: path.rfind("/")] + "/"

        # Collapse multiple slashes, remove dot segments
        if normalize_slash:
            path = re.sub(r"/{2,}", "/", path)
            path = self._remove_dot_segments(path)

        # File extension filtering
        ext = ""
        try:
            if "." in path.rsplit("/", 1)[-1]:
                ext = "." + path.rsplit(".", 1)[-1].lower()
        except Exception:
            ext = ""

        if ext and ext in ignored_exts:
            return {"status": "rejected", "reason": f"ignored_ext:{ext}"}

        # Fragment handling
        if strip_fragments:
            frag = ""

        # Query normalization
        if query:
            try:
                qsl = parse_qsl(query, keep_blank_values=True)
            except Exception:
                qsl = []

            q_out = []
            for k, v in qsl:
                kl = (k or "").strip().lower()
                if drop_tracking_params and kl in drop_query_keys:
                    continue
                # strip empty tracking-like values
                if drop_tracking_params and kl.startswith("utm_"):
                    continue
                q_out.append((k, v))

            if sort_query and q_out:
                # stable sort by key then value
                q_out.sort(key=lambda kv: (kv[0].lower(), kv[1]))

            query = urlencode(q_out, doseq=True)

        canonical = urlunparse((scheme, netloc2, path or "/", "", query, frag))

        if len(canonical) > max_url_len:
            return {"status": "rejected", "reason": "too_long_after_canon"}

        return {"status": "accepted", "canonical": canonical}

    def _safe_unquote_path(self, path: str) -> str:
        # Unquote only "safe" parts to reduce %2F weirdness
        try:
            # keep '/' as delimiter; unquote everything else
            parts = path.split("/")
            parts2 = [unquote(p) for p in parts]
            # re-quote minimally (spaces etc.)
            parts3 = [quote(p, safe=":@+$,;=-._~") for p in parts2]
            return "/".join(parts3)
        except Exception:
            return path or "/"

    def _remove_dot_segments(self, path: str) -> str:
        # RFC-ish dot segment removal
        if not path:
            return "/"
        segs = []
        for seg in path.split("/"):
            if seg == "" or seg == ".":
                continue
            if seg == "..":
                if segs:
                    segs.pop()
                continue
            segs.append(seg)
        out = "/" + "/".join(segs)
        if path.endswith("/") and not out.endswith("/"):
            out += "/"
        return out

    def _parse_csv_set(self, raw: Any) -> set[str]:
        if not raw:
            return set()
        if isinstance(raw, set):
            return raw
        if isinstance(raw, list):
            return {str(x).strip().lower() for x in raw if str(x).strip()}
        if isinstance(raw, str):
            return {x.strip().lower() for x in raw.split(",") if x.strip()}
        return set()

# Register
BLOCKS.register("urlscraper", URLScraperBlock)

# ======================= URLExpanderBlock ==================================

@dataclass
class URLExpanderBlock(BaseBlock):
    """
    URLExpanderBlock
    ----------------
    Reads one or more Memory keys (memory_sources), extracts URL candidates,
    EXPANDS them (follows redirects / shorteners), canonicalizes lightly,
    and OVERWRITES those SAME Memory keys with the expanded URL list.

    Outputs:
      - urls_expanded (merged across keys)
      - urls_rejected (with reasons)
      - expand_map (original -> expanded)
      - per_key_stats
    """

    _URL_RE = re.compile(r"https?://[^\s\"'<>\\)\]]+", re.IGNORECASE)

    # tracking keys to drop (after expansion)
    DEFAULT_DROP_QUERY_KEYS = {
        "utm_source", "utm_medium", "utm_campaign", "utm_term", "utm_content",
        "utm_id", "utm_name", "utm_reader", "utm_viz_id",
        "gclid", "dclid", "gbraid", "wbraid", "fbclid", "msclkid",
        "ttclid", "twclid", "yclid", "mc_cid", "mc_eid",
        "ref", "ref_src", "ref_url", "spm", "spm_id_from",
        "igshid", "si", "feature", "app", "mkt_tok",
        "session", "sessionid", "sid", "phpsessid", "jsessionid",
    }

    def __post_init__(self):
        pass

    # ------------------------------
    # Public execution
    # ------------------------------
    async def _execute_async(
        self, payload: Any, *, params: Dict[str, Any]
    ) -> Tuple[str, Dict[str, Any]]:

        memory_sources_raw = str(params.get("memory_sources", "") or "").strip()
        keys = [k.strip() for k in memory_sources_raw.split(",") if k.strip()]

        if not keys:
            txt = "[context]\n\n[lexicon]\n\n"
            return txt, {"count": 0, "error": "URLExpander requires params['memory_sources']"}

        # ---- HTTPSSubmanager knobs ----
        timeout = float(params.get("timeout", 6.0))
        ua_http = str(params.get("user_agent", "Mozilla/5.0 PromptChat/URLExpander"))
        http_retries = int(params.get("http_retries", 2))
        http_max_conn = int(params.get("http_max_conn_per_host", 8))
        http_verify_tls = bool(params.get("http_verify_tls", True))
        http_ca_bundle = params.get("http_ca_bundle") or None

        # ---- Expander knobs ----
        max_url_len = int(params.get("max_url_len", 4096))
        max_hops = int(params.get("max_hops", 8))
        use_head_first = bool(params.get("use_head_first", True))
        allow_get_fallback = bool(params.get("allow_get_fallback", True))

        # HTML-based expansion (optional but very useful)
        parse_meta_refresh = bool(params.get("parse_meta_refresh", True))
        extract_canonical = bool(params.get("extract_canonical", True))
        max_html_chars = int(params.get("max_html_chars", 200_000))

        # Post-expand normalization
        strip_fragments = bool(params.get("strip_fragments", True))
        drop_tracking_params = bool(params.get("drop_tracking_params", True))
        drop_query_keys_raw = str(params.get("drop_query_keys", "") or "").strip()
        sort_query = bool(params.get("sort_query", True))
        force_https = bool(params.get("force_https", False))
        keep_www = bool(params.get("keep_www", True))

        write_sidecars = bool(params.get("write_sidecars", True))

        drop_query_keys = set(self.DEFAULT_DROP_QUERY_KEYS)
        if drop_query_keys_raw:
            drop_query_keys |= {x.strip().lower() for x in drop_query_keys_raw.split(",") if x.strip()}

        # Load memory
        try:
            mem = Memory.load()
        except Exception as e:
            txt = "[context]\n\n[lexicon]\n\n"
            return txt, {"count": 0, "error": f"Memory.load failed: {e}"}

        all_expanded: List[str] = []
        all_rejected: List[Dict[str, Any]] = []
        all_map: Dict[str, str] = {}
        per_key_stats: Dict[str, Dict[str, Any]] = {}

        async with submanagers.HTTPSSubmanager(
            user_agent=ua_http,
            timeout=timeout,
            retries=http_retries,
            max_conn_per_host=http_max_conn,
            verify=http_verify_tls,
            ca_bundle=http_ca_bundle,
        ) as http:

            for key in keys:
                raw = mem.get(key)

                if not raw:
                    st = {"in": 0, "candidates": 0, "accepted": 0, "rejected": 0, "expanded": 0}
                    per_key_stats[key] = st
                    mem[key] = []
                    if write_sidecars:
                        mem[f"{key}_rejected"] = []
                        mem[f"{key}_expand_map"] = {}
                        mem[f"{key}_stats"] = st
                    continue

                candidates = self._extract_url_candidates(raw)
                in_count = self._estimate_in_count(raw)

                expanded_list: List[str] = []
                rejected: List[Dict[str, Any]] = []
                emap: Dict[str, str] = {}
                seen = set()

                # Expand sequentially (safer for shorteners); you can parallelize later if you want.
                for original in candidates:
                    rec = await self._expand_one(
                        http=http,
                        original=original,
                        max_url_len=max_url_len,
                        max_hops=max_hops,
                        use_head_first=use_head_first,
                        allow_get_fallback=allow_get_fallback,
                        parse_meta_refresh=parse_meta_refresh,
                        extract_canonical=extract_canonical,
                        max_html_chars=max_html_chars,
                        strip_fragments=strip_fragments,
                        drop_tracking_params=drop_tracking_params,
                        drop_query_keys=drop_query_keys,
                        sort_query=sort_query,
                        force_https=force_https,
                        keep_www=keep_www,
                    )

                    if rec["status"] != "accepted":
                        rejected.append({"url": original, "reason": rec.get("reason", "rejected")})
                        continue

                    final_u = rec["expanded"]
                    emap[original] = final_u

                    if final_u in seen:
                        continue
                    seen.add(final_u)
                    expanded_list.append(final_u)

                # OVERWRITE the same key
                mem[key] = expanded_list

                st = {
                    "in": int(in_count),
                    "candidates": len(candidates),
                    "accepted": len(expanded_list),
                    "rejected": len(rejected),
                    "expanded": len(emap),
                }
                per_key_stats[key] = st

                if write_sidecars:
                    mem[f"{key}_rejected"] = rejected
                    mem[f"{key}_expand_map"] = emap
                    mem[f"{key}_stats"] = st

                all_expanded.extend(expanded_list)
                all_rejected.extend(rejected)
                all_map.update(emap)

        # Save memory back
        try:
            Memory.save(mem)
        except Exception as e:
            DEBUG_LOGGER.log_message(f"[URLExpander] Memory.save failed: {e}")

        merged = list(dict.fromkeys(all_expanded))
        DEBUG_LOGGER.log_message(
            f"[URLExpander] keys={keys} merged_accepted={len(merged)} merged_rejected={len(all_rejected)}"
        )

        out_text = "[context]\n" + "\n".join(merged) + "\n\n[lexicon]\n\n"
        meta = {
            "count": len(merged),
            "urls_expanded": merged,
            "urls_rejected": all_rejected,
            "expand_map": all_map,
            "per_key_stats": per_key_stats,
            "memory_sources": keys,
            "urls": merged,
        }
        return out_text, meta

    # Sync wrapper
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asyncio.run(self._execute_async(payload, params=params))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "memory_sources": "scraped_links",
            "timeout": 6.0,
            "user_agent": "Mozilla/5.0 PromptChat/URLExpander",

            # HTTPS engine tuning
            "http_retries": 2,
            "http_max_conn_per_host": 8,
            "http_verify_tls": True,
            "http_ca_bundle": "",

            # Expander knobs
            "max_url_len": 4096,
            "max_hops": 8,
            "use_head_first": True,
            "allow_get_fallback": True,

            # HTML redirect / canonical
            "parse_meta_refresh": True,
            "extract_canonical": True,
            "max_html_chars": 200000,

            # Post-expand normalization
            "strip_fragments": True,
            "drop_tracking_params": True,
            "drop_query_keys": "",   # extra csv keys
            "sort_query": True,
            "force_https": False,
            "keep_www": True,

            "write_sidecars": True,
        }

    # ------------------------------
    # Candidate extraction (same spirit as URLScraper)
    # ------------------------------
    def _estimate_in_count(self, raw: Any) -> int:
        if raw is None:
            return 0
        if isinstance(raw, list):
            return len(raw)
        return 1

    def _extract_url_candidates(self, raw: Any) -> List[str]:
        out: List[str] = []
        seen = set()

        def push(s: str):
            s = (s or "").strip()
            if not s:
                return
            if s.startswith(("http://", "https://")):
                if s not in seen:
                    seen.add(s)
                    out.append(s)
                return
            for m in self._URL_RE.finditer(s[:250_000]):
                u = m.group(0)
                if u and u not in seen:
                    seen.add(u)
                    out.append(u)

        def walk(x: Any):
            if x is None:
                return
            if isinstance(x, str):
                push(x)
                return
            if isinstance(x, (int, float)):
                push(str(x))
                return
            if isinstance(x, dict):
                for k in ("url", "href", "link", "final_url", "source_url", "page", "request_url"):
                    v = x.get(k)
                    if isinstance(v, str) and v.strip():
                        push(v)
                for k in ("text", "html", "body", "snippet"):
                    v = x.get(k)
                    if isinstance(v, str) and v.strip():
                        push(v)
                for v in x.values():
                    if isinstance(v, (list, dict)):
                        walk(v)
                return
            if isinstance(x, list):
                for it in x:
                    walk(it)
                return
            push(str(x))

        walk(raw)
        return out

    # ------------------------------
    # Expansion core
    # ------------------------------
    async def _expand_one(
        self,
        *,
        http: Any,  # submanagers.HTTPSSubmanager
        original: str,
        max_url_len: int,
        max_hops: int,
        use_head_first: bool,
        allow_get_fallback: bool,
        parse_meta_refresh: bool,
        extract_canonical: bool,
        max_html_chars: int,
        strip_fragments: bool,
        drop_tracking_params: bool,
        drop_query_keys: set[str],
        sort_query: bool,
        force_https: bool,
        keep_www: bool,
    ) -> Dict[str, Any]:

        s = (original or "").strip()
        if not s:
            return {"status": "rejected", "reason": "empty"}
        if len(s) > max_url_len:
            return {"status": "rejected", "reason": "too_long"}
        if not s.startswith(("http://", "https://")):
            return {"status": "rejected", "reason": "not_http"}

        # We do a bounded redirect chase ourselves so we can stop early.
        cur = s
        visited = set()

        for hop in range(max_hops + 1):
            if cur in visited:
                return {"status": "rejected", "reason": "redirect_loop"}
            visited.add(cur)

            # Try HEAD first (fast)
            if use_head_first:
                nxt = await self._try_expand_via_head(http, cur)
                if nxt and nxt != cur:
                    cur = nxt
                    continue

            # Fallback to GET + potential HTML hints
            if allow_get_fallback:
                nxt, html = await self._try_expand_via_get(http, cur, max_html_chars=max_html_chars)
                if nxt and nxt != cur:
                    cur = nxt
                    continue

                # If no redirect, optionally parse meta-refresh / canonical from HTML
                if html and (parse_meta_refresh or extract_canonical):
                    hinted = self._html_hint_url(
                        html=html,
                        base_url=cur,
                        parse_meta_refresh=parse_meta_refresh,
                        extract_canonical=extract_canonical,
                    )
                    if hinted and hinted != cur:
                        cur = hinted
                        continue

            # No more progress
            break

        # Post-normalize (tracking params, fragments, scheme, www)
        cur2 = self._post_normalize(
            cur,
            strip_fragments=strip_fragments,
            drop_tracking_params=drop_tracking_params,
            drop_query_keys=drop_query_keys,
            sort_query=sort_query,
            force_https=force_https,
            keep_www=keep_www,
        )

        if not cur2 or len(cur2) > max_url_len:
            return {"status": "rejected", "reason": "bad_final_url"}

        return {"status": "accepted", "expanded": cur2}

    async def _try_expand_via_head(self, http: Any, url: str) -> Optional[str]:
        """
        Uses the shared session (if available) to capture final URL after redirects.
        Falls back to submanager.head if we can't access the session.
        """
        # Best path: use the submanager's live session so we can read resp.url.
        sess = getattr(http, "_session", None)
        if sess:
            try:
                async with sess.request(
                    "HEAD",
                    url,
                    allow_redirects=True,
                    timeout=getattr(http, "timeout", 6.0),
                ) as resp:
                    final = str(resp.url)
                    return final
            except Exception:
                return None

        # Fallback: submanager.head (may not expose final URL)
        try:
            _st, hdrs = await http.head(url)
            loc = (hdrs or {}).get("Location")
            if loc:
                return urljoin(url, loc)
        except Exception:
            return None
        return None

    async def _try_expand_via_get(self, http: Any, url: str, *, max_html_chars: int) -> Tuple[Optional[str], str]:
        sess = getattr(http, "_session", None)
        if sess:
            try:
                async with sess.request(
                    "GET",
                    url,
                    allow_redirects=True,
                    timeout=getattr(http, "timeout", 6.0),
                    headers={"Accept": "text/html,application/xhtml+xml,*/*;q=0.8"},
                ) as resp:
                    final = str(resp.url)
                    # Only sample HTML-ish bodies (bounded)
                    ctype = (resp.headers.get("Content-Type") or "").lower()
                    if "html" in ctype or ctype == "" or "text/" in ctype:
                        txt = await resp.text(errors="ignore")
                        if len(txt) > max_html_chars:
                            txt = txt[:max_html_chars]
                        return final, txt
                    return final, ""
            except Exception:
                return None, ""

        # If we can't access session, use get_text (but we lose final URL knowledge)
        try:
            html = await http.get_text(url)
            if len(html) > max_html_chars:
                html = html[:max_html_chars]
            return url, html
        except Exception:
            return None, ""

    def _html_hint_url(
        self,
        *,
        html: str,
        base_url: str,
        parse_meta_refresh: bool,
        extract_canonical: bool,
    ) -> Optional[str]:
        try:
            soup = BeautifulSoup(html or "", "html.parser")

            # meta refresh: <meta http-equiv="refresh" content="0; url=/next">
            if parse_meta_refresh:
                m = soup.find("meta", attrs={"http-equiv": re.compile(r"refresh", re.I)})
                if m:
                    content = (m.get("content") or "").strip()
                    # naive parse "0; url=..."
                    if "url=" in content.lower():
                        try:
                            part = content.split("url=", 1)[1].strip(" '\"")
                            if part:
                                return urljoin(base_url, part)
                        except Exception:
                            pass

            # canonical: <link rel="canonical" href="...">
            if extract_canonical:
                c = soup.find("link", attrs={"rel": re.compile(r"canonical", re.I)})
                if c:
                    href = (c.get("href") or "").strip()
                    if href:
                        return urljoin(base_url, href)

        except Exception:
            return None
        return None

    def _post_normalize(
        self,
        url: str,
        *,
        strip_fragments: bool,
        drop_tracking_params: bool,
        drop_query_keys: set[str],
        sort_query: bool,
        force_https: bool,
        keep_www: bool,
    ) -> str:
        try:
            pu = urlparse(url)
        except Exception:
            return url

        scheme = (pu.scheme or "https").lower()
        netloc = (pu.netloc or "").strip()
        path = pu.path or ""
        query = pu.query or ""
        frag = pu.fragment or ""

        if force_https:
            scheme = "https"

        # www handling
        host = netloc
        port = ""
        if ":" in host:
            host, port = host.rsplit(":", 1)
        host = host.lower().strip(".")
        if not keep_www and host.startswith("www."):
            host = host[4:]
        netloc = host + (f":{port}" if port else "")

        if strip_fragments:
            frag = ""

        if query and drop_tracking_params:
            try:
                qsl = parse_qsl(query, keep_blank_values=True)
            except Exception:
                qsl = []
            q2 = []
            for k, v in qsl:
                kl = (k or "").strip().lower()
                if kl in drop_query_keys or kl.startswith("utm_"):
                    continue
                q2.append((k, v))
            if sort_query and q2:
                q2.sort(key=lambda kv: (kv[0].lower(), kv[1]))
            query = urlencode(q2, doseq=True)

        return urlunparse((scheme, netloc, path or "/", "", query, frag))


# Register
BLOCKS.register("urlexpander", URLExpanderBlock)


# ======================= LinkContentCrawlerBlock ============================

@dataclass
class LinkContentCrawlerBlock(BaseBlock):
    """
    Advanced version implementing the 3 high-impact URL-param features:

    ✅ 1) Canonicalization with tracking-param drop + sorted query
    ✅ 2) Identity rules per host/path (keep only key params)
    ✅ 3) Volatile signed-link handling + redaction (drop/mask sensitive tokens)

    Notes:
      - Dedupe keys are based on canonical_url (stable form).
      - Memory stores both raw_url (redacted) and canonical_url.
      - "Volatile" URLs are those containing signed/token params; canonical_url removes those
        (unless identity rules require them, which you usually won’t).
    """

    _HREF_RE = re.compile(r"""href=["'](.*?)["']""", re.IGNORECASE)
    _URL_RE = re.compile(r"https?://[^\s\"'<>\\)\]]+", re.IGNORECASE)

    VIDEO_EXTS = (".mp4", ".webm", ".mkv", ".mov", ".avi", ".wmv", ".flv", ".m3u8", ".mpd", ".ts")
    AUDIO_EXTS = (".mp3", ".m4a", ".wav", ".flac", ".ogg", ".aac")
    IMAGE_EXTS = (".jpg", ".jpeg", ".png", ".gif", ".webp", ".avif", ".bmp", ".tiff", ".svg")
    DOC_EXTS   = (".pdf", ".epub", ".mobi", ".djvu", ".doc", ".docx", ".ppt", ".pptx", ".xls", ".xlsx", ".txt", ".rtf")

    CONTENT_PATH_TOKENS = (
        "/watch", "/player", "/embed", "/download", "/stream", "/video", "/clip",
        "/movie", "/episode", "/season", "/view", "/details",
    )

    JUNK_HINTS = (
        "mailto:", "javascript:", "tel:",
        "/login", "/signin", "/signup", "/register", "/account",
        "/privacy", "/terms", "/policy", "/contact", "/about", "/dmca",
        "facebook.com", "twitter.com", "linkedin.com",
    )

    IGNORED_EXTS = (
        ".css", ".js", ".json", ".xml", ".map",
        ".woff", ".woff2", ".ttf", ".eot",
        ".ico",
        ".zip", ".rar", ".7z", ".tar", ".gz", ".bz2", ".xz",
    )

    # --------------------------- DB ---------------------------------

    def _make_store(self, db_path: str) -> LinkContentCrawlerStore:
        cfg = submanagers.DatabaseConfig(path=db_path)
        db = submanagers.DatabaseSubmanager(cfg, logger=DEBUG_LOGGER)
        store = LinkContentCrawlerStore(db=db)
        store.ensure_schema()
        return store

    # --------------------------- URL extraction helpers ------------------------------

    def _flatten_memory_urls(self, raw: Any) -> List[str]:
        out: List[str] = []
        seen = set()

        def push(u: str):
            u = (u or "").strip()
            if not u:
                return
            if u.startswith(("http://", "https://")):
                if u not in seen:
                    seen.add(u)
                    out.append(u)
                return
            for m in self._URL_RE.finditer(u[:250_000]):
                uu = m.group(0)
                if uu and uu not in seen:
                    seen.add(uu)
                    out.append(uu)

        def walk(x: Any):
            if x is None:
                return
            if isinstance(x, str):
                push(x); return
            if isinstance(x, (int, float)):
                push(str(x)); return
            if isinstance(x, list):
                for it in x: walk(it)
                return
            if isinstance(x, dict):
                for k in ("url", "href", "link", "page", "request_url", "final_url", "source_url"):
                    v = x.get(k)
                    if isinstance(v, str) and v.strip():
                        push(v)
                for k in ("text", "html", "body", "snippet"):
                    v = x.get(k)
                    if isinstance(v, str) and v.strip():
                        push(v)
                for v in x.values():
                    if isinstance(v, (list, dict)):
                        walk(v)
                return
            push(str(x))

        walk(raw)
        return out

    def _is_junk(self, u: str) -> bool:
        low = (u or "").lower()
        if not low:
            return True
        if low.startswith(("#", "javascript:", "mailto:", "tel:")):
            return True
        if any(j in low for j in self.JUNK_HINTS):
            return True
        return False

    def _ext(self, u: str) -> str:
        try:
            path = (u.split("?", 1)[0]).split("#", 1)[0]
            leaf = path.rsplit("/", 1)[-1]
            if "." in leaf:
                return "." + leaf.rsplit(".", 1)[-1].lower()
        except Exception:
            pass
        return ""

    # --------------------------- NEW: param rule parsing ------------------------------

    def _split_csv(self, s: Any) -> List[str]:
        raw = str(s or "").strip()
        if not raw:
            return []
        return [x.strip() for x in raw.split(",") if x.strip()]

    def _parse_identity_rules(self, params: Dict[str, Any]) -> List[Dict[str, Any]]:
        """
        identity_rules format (params):
          [
            {"host": "example.com", "path_prefix": "/watch", "keep": ["v"]},
            {"host": "*.examplecdn.com", "path_prefix": "/player", "keep": "id,token"},
          ]
        """
        rules = params.get("identity_rules", None)
        if not rules:
            return []
        if isinstance(rules, dict):
            rules = [rules]
        if not isinstance(rules, list):
            return []

        out: List[Dict[str, Any]] = []
        for r in rules:
            if not isinstance(r, dict):
                continue
            host = str(r.get("host", "") or "").strip().lower()
            path_prefix = str(r.get("path_prefix", "") or "").strip()
            keep = r.get("keep", [])
            if isinstance(keep, str):
                keep = [x.strip() for x in keep.split(",") if x.strip()]
            if not host and not path_prefix:
                continue
            out.append({
                "host": host,  # supports wildcard via fnmatch
                "path_prefix": path_prefix,
                "keep": [str(x).strip() for x in (keep or []) if str(x).strip()],
            })
        return out

    def _match_identity_rule(self, url: str, rules: List[Dict[str, Any]]) -> Optional[Dict[str, Any]]:
        try:
            pu = urlparse(url)
            host = (pu.netloc or "").lower()
            path = pu.path or ""
        except Exception:
            return None

        for r in rules:
            rh = r.get("host", "") or ""
            rp = r.get("path_prefix", "") or ""
            if rh:
                if not fnmatch.fnmatch(host, rh):
                    continue
            if rp:
                if not path.startswith(rp):
                    continue
            return r
        return None

    # --------------------------- NEW: canonicalize + volatile + redaction ------------------------------

    def _is_tracking_param(self, name: str, patterns: List[str]) -> bool:
        n = (name or "").strip().lower()
        if not n:
            return False
        for pat in patterns:
            p = pat.strip().lower()
            if not p:
                continue
            # allow utm_* style
            if "*" in p:
                if fnmatch.fnmatch(n, p):
                    return True
            else:
                if n == p:
                    return True
        return False

    def _canonicalize_url(
        self,
        url: str,
        *,
        drop_query_patterns: List[str],
        volatile_param_names: List[str],
        redact_param_names: List[str],
        redact_mode: str,
        identity_rules: List[Dict[str, Any]],
        sort_query: bool,
    ) -> Tuple[str, str, bool, bool]:
        """
        Returns:
          canonical_url: stable URL used for dedupe
          raw_redacted_url: original URL but with sensitive params masked/dropped
          is_volatile: True if signed/token-ish params were present
          was_redacted: True if we changed raw URL due to redaction
        """
        try:
            pu = urlparse(url)
        except Exception:
            return url, url, False, False

        # normalize scheme/host casing
        scheme = (pu.scheme or "").lower()
        netloc = pu.netloc
        path = pu.path or ""
        fragment = ""  # drop fragments for both raw+canonical
        base = pu._replace(scheme=scheme, fragment=fragment)

        # parse query into list (preserve duplicates)
        q_pairs = parse_qsl(pu.query or "", keep_blank_values=True)

        # determine rule for identity params
        rule = self._match_identity_rule(url, identity_rules)
        keep_only = set((rule.get("keep") or [])) if rule else set()

        volatile_set = {x.lower() for x in volatile_param_names}
        redact_set = {x.lower() for x in redact_param_names}

        # detect volatility from original query
        is_volatile = any((k or "").lower() in volatile_set for (k, _v) in q_pairs)

        # 1) produce a "raw but redacted" version for storage
        raw_pairs: List[Tuple[str, str]] = []
        was_redacted = False
        for k, v in q_pairs:
            kn = (k or "").strip()
            kl = kn.lower()
            if not kn:
                continue

            # tracking params: keep in raw? generally no value; but raw can keep them if you want.
            # We'll keep them unless they are also in redact list; but we will DROP them later in canonical.
            if kl in redact_set:
                was_redacted = True
                if (redact_mode or "mask").lower() == "drop":
                    continue
                raw_pairs.append((kn, "REDACTED"))
                continue

            raw_pairs.append((kn, v if v is not None else ""))

        if sort_query:
            raw_pairs = sorted(raw_pairs, key=lambda kv: (kv[0].lower(), kv[1]))

        raw_redacted = urlunparse(base._replace(query=urlencode(raw_pairs, doseq=True)))

        # 2) produce canonical version used for dedupe:
        #    - drop tracking params
        #    - drop volatile params (signed links) unless identity rule explicitly keeps them
        #    - optionally keep only identity params if rule matched
        canon_pairs: List[Tuple[str, str]] = []
        for k, v in q_pairs:
            kn = (k or "").strip()
            kl = kn.lower()
            if not kn:
                continue

            # identity rules: keep only specified names
            if keep_only:
                if kn not in keep_only and kl not in {x.lower() for x in keep_only}:
                    continue
            else:
                # otherwise: drop tracking patterns by default
                if self._is_tracking_param(kn, drop_query_patterns):
                    continue

            # drop volatile signature params from canonical (unless identity keeps them)
            if (kl in volatile_set) and not keep_only:
                continue

            # redact sensitive params from canonical as well
            if kl in redact_set:
                # safest: drop them from canonical entirely
                continue

            canon_pairs.append((kn, v if v is not None else ""))

        if sort_query:
            canon_pairs = sorted(canon_pairs, key=lambda kv: (kv[0].lower(), kv[1]))

        canonical = urlunparse(base._replace(query=urlencode(canon_pairs, doseq=True)))

        # normalize: remove trailing "?" if empty query
        if canonical.endswith("?"):
            canonical = canonical[:-1]
        if raw_redacted.endswith("?"):
            raw_redacted = raw_redacted[:-1]

        # also normalize double slashes in path? (optional)
        # leaving as-is to avoid altering semantics.

        return canonical, raw_redacted, is_volatile, was_redacted

    # --------------------------- Classification (unchanged; uses canonical URL) ------------------------------

    def _classify(self, u: str) -> Tuple[str, int]:
        if self._is_junk(u):
            return "junk", 0

        low = u.lower()
        ext = self._ext(low)

        if ext and ext in self.IGNORED_EXTS:
            return "junk", 0

        if ext in self.VIDEO_EXTS or any(low.endswith(x) for x in (".m3u8", ".mpd")):
            return "video", 60
        if ext in self.AUDIO_EXTS:
            return "audio", 55
        if ext in self.IMAGE_EXTS:
            return "image", 45
        if ext in self.DOC_EXTS:
            return "doc", 40

        try:
            path = urlparse(u).path.lower() if u else ""
        except Exception:
            path = ""
        if any(tok in path for tok in self.CONTENT_PATH_TOKENS):
            return "page", 25

        return "page", 5

    def _extract_links_from_html(self, html: str, base_url: str) -> List[str]:
        links: List[str] = []
        seen = set()

        for m in self._HREF_RE.finditer(html or ""):
            raw = (m.group(1) or "").strip()
            if not raw:
                continue
            if raw.startswith(("#", "javascript:", "mailto:", "tel:")):
                continue
            try:
                full = urljoin(base_url, raw)
                pu = urlparse(full)
                if pu.scheme not in ("http", "https"):
                    continue
                if "uddg=" in full:
                    try:
                        full = unquote(full.split("uddg=")[1].split("&")[0])
                    except Exception:
                        pass
                if full not in seen:
                    seen.add(full)
                    links.append(full)
            except Exception:
                continue

        return links

    # --------------------------- Store API compatibility helpers ------------------------------

    def _store_has_emitted(self, store: Any, key_url: str) -> bool:
        # Prefer key-based methods if your store supports them, otherwise fallback.
        try:
            if hasattr(store, "has_emitted_key"):
                return bool(store.has_emitted_key(key_url))
            return bool(store.has_emitted(key_url))
        except Exception:
            return False

    def _store_mark_emitted(
        self,
        store: Any,
        *,
        key_url: str,
        raw_url: str,
        now_ts: float,
        source: str,
        seed_url: str,
        final_url: str,
        kind: str,
        score: int,
        is_volatile: bool,
        was_redacted: bool,
    ) -> None:
        # Your existing store.mark_emitted probably keys on URL. We pass key_url (canonical).
        try:
            store.mark_emitted(
                key_url,
                now_ts=now_ts,
                source=source,
                seed_url=seed_url,
                final_url=final_url,
                kind=kind,
                score=score,
            )
        except Exception:
            pass

        # Optional: if you later add methods, we’ll use them without breaking older stores.
        try:
            if hasattr(store, "mark_last_raw_url"):
                store.mark_last_raw_url(key_url=key_url, raw_url=raw_url, now_ts=now_ts, volatile=is_volatile, redacted=was_redacted)
        except Exception:
            pass

    # --------------------------- Execution ------------------------------

    async def _execute_async(self, payload: Any, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        log: List[str] = []

        memory_sources_raw = str(params.get("memory_sources", "") or "").strip()
        memory_sources = [k.strip() for k in memory_sources_raw.split(",") if k.strip()]
        if not memory_sources:
            return "No operation.", {"error": "linkcontentcrawler requires params['memory_sources']"}

        timeout = float(params.get("timeout", 10.0))
        max_seeds = int(params.get("max_seeds", 150))
        max_concurrency = int(params.get("max_concurrency", 12))
        max_links_per_seed = int(params.get("max_links_per_seed", 250))

        min_score = int(params.get("min_score", 20))
        include_pages = bool(params.get("include_pages", True))

        out_key = str(params.get("content_links_key", "content_links")).strip()
        out_urls_key = str(params.get("content_urls_key", "content_urls")).strip()
        stats_key = str(params.get("per_seed_stats_key", "content_seed_stats")).strip()

        use_database = bool(params.get("use_database", False))
        db_path = str(params.get("db_path", "link_corpus.db"))
        seed_ttl_seconds = float(params.get("seed_ttl_seconds", 6 * 3600))

        # --------------------------- NEW: canonicalization + identity + volatile/redaction settings ---------------------------

        canonicalize_urls = bool(params.get("canonicalize_urls", True))
        sort_query_params = bool(params.get("sort_query_params", True))

        drop_query_params = self._split_csv(params.get(
            "drop_query_params",
            # a decent default set
            "utm_*,gclid,fbclid,msclkid,igshid,mc_cid,mc_eid,ref,ref_src,spm,cmpid,vero_conv,vero_id"
        ))

        volatile_params = self._split_csv(params.get(
            "volatile_params",
            "token,access_token,refresh_token,sig,signature,expires,exp,policy,key,cdn_hash,hash,hmac"
        ))

        redact_params = self._split_csv(params.get(
            "redact_params",
            "access_token,refresh_token,authorization,auth,bearer,session,sessionid,sid,token"
        ))

        redact_mode = str(params.get("redact_mode", "mask")).strip().lower()
        if redact_mode not in ("mask", "drop"):
            redact_mode = "mask"

        identity_rules = self._parse_identity_rules(params)

        DEBUG_LOGGER.log_message(
            f"[LinkContentCrawler] start | memory_sources={memory_sources} timeout={timeout} "
            f"max_seeds={max_seeds} max_concurrency={max_concurrency} min_score={min_score} "
            f"use_database={use_database} canonicalize_urls={canonicalize_urls} "
            f"identity_rules={len(identity_rules)}"
        )

        mem = Memory.load()
        seed_urls: List[str] = []
        for k in memory_sources:
            seed_urls.extend(self._flatten_memory_urls(mem.get(k)))

        seed_urls = list(dict.fromkeys(seed_urls))
        if max_seeds and len(seed_urls) > max_seeds:
            seed_urls = seed_urls[:max_seeds]

        if not seed_urls:
            return "No seeds found.", {"seed_count": 0, "memory_sources": memory_sources}

        store: Optional[LinkContentCrawlerStore] = None
        if use_database:
            try:
                store = self._make_store(db_path)
                log.append(f"[LinkContentCrawler][DB] Enabled db_path={db_path} seed_ttl_seconds={seed_ttl_seconds:.0f}")
            except Exception as e:
                store = None
                use_database = False
                log.append(f"[LinkContentCrawler][DB] Init failed: {e} (continuing without DB)")

        now_ts = time.time()
        seeds_to_fetch = seed_urls
        if store:
            seeds_to_fetch = [
                u for u in seed_urls
                if store.seed_should_fetch(u, ttl_seconds=seed_ttl_seconds, now_ts=now_ts)
            ]
            skipped = len(seed_urls) - len(seeds_to_fetch)
            if skipped:
                msg = f"[LinkContentCrawler][DB] Skipping {skipped} seed(s) due to TTL."
                log.append(msg)
                DEBUG_LOGGER.log_message(msg)

        sem = asyncio.Semaphore(max_concurrency)

        found_objs: List[Dict[str, Any]] = []
        found_keys_set = set()  # canonical_url dedupe
        per_seed_stats: Dict[str, Dict[str, Any]] = {}

        async with submanagers.HTTPSSubmanager(timeout=timeout) as http:

            async def crawl_seed(seed: str):
                if not seed:
                    return
                if self._is_junk(seed):
                    per_seed_stats[seed] = {"status": "skipped_junk", "out_links": 0, "kept": 0}
                    return

                async with sem:
                    t0 = time.time()
                    try:
                        DEBUG_LOGGER.log_message(f"[LinkContentCrawler][Seed] fetch={seed}")

                        # HEAD first
                        st, hdrs = await http.head(seed)
                        hdrs = hdrs or {}
                        ctype = (hdrs.get("Content-Type") or hdrs.get("content-type") or "").lower()

                        final_url = seed
                        status = st

                        if store:
                            try:
                                store.seed_mark_fetched(seed, now_ts=time.time(), status=status, final_url=final_url)
                            except Exception:
                                pass

                        # If non-HTML: treat as direct candidate.
                        if ctype and ("text/html" not in ctype):
                            # canonicalize + redaction
                            if canonicalize_urls:
                                key_url, raw_redacted, is_volatile, was_redacted = self._canonicalize_url(
                                    final_url,
                                    drop_query_patterns=drop_query_params,
                                    volatile_param_names=volatile_params,
                                    redact_param_names=redact_params,
                                    redact_mode=redact_mode,
                                    identity_rules=identity_rules,
                                    sort_query=sort_query_params,
                                )
                            else:
                                key_url, raw_redacted, is_volatile, was_redacted = final_url, final_url, False, False

                            kind, score = self._classify(key_url)
                            kept = 0

                            if score >= min_score and (include_pages or kind != "page") and kind != "junk":
                                if (not store) or (not self._store_has_emitted(store, key_url)):
                                    if key_url not in found_keys_set:
                                        found_keys_set.add(key_url)
                                        obj = {
                                            "url": key_url,                 # canonical URL used as primary
                                            "canonical_url": key_url,
                                            "raw_url": raw_redacted,        # redacted raw URL
                                            "source": "linkcontentcrawler_seed_nonhtml",
                                            "seed": seed,
                                            "final_url": final_url,
                                            "kind": kind,
                                            "score": score,
                                            "volatile": bool(is_volatile),
                                            "redacted": bool(was_redacted),
                                            "first_seen": time.time(),
                                        }
                                        found_objs.append(obj)
                                        kept += 1

                                        if store:
                                            self._store_mark_emitted(
                                                store,
                                                key_url=key_url,
                                                raw_url=raw_redacted,
                                                now_ts=time.time(),
                                                source="seed_nonhtml",
                                                seed_url=seed,
                                                final_url=final_url,
                                                kind=kind,
                                                score=score,
                                                is_volatile=is_volatile,
                                                was_redacted=was_redacted,
                                            )

                            per_seed_stats[seed] = {"status": f"non_html({ctype[:40]})", "out_links": 0, "kept": kept}
                            return

                        # HTML path: GET + parse links
                        html = await http.get_text(seed)
                        if not html:
                            per_seed_stats[seed] = {"status": "empty_html_or_error", "out_links": 0, "kept": 0}
                            return

                        out_links = self._extract_links_from_html(html, seed)
                        if max_links_per_seed and len(out_links) > max_links_per_seed:
                            out_links = out_links[:max_links_per_seed]

                        kept = 0
                        for u in out_links:
                            if self._is_junk(u):
                                continue

                            if canonicalize_urls:
                                key_url, raw_redacted, is_volatile, was_redacted = self._canonicalize_url(
                                    u,
                                    drop_query_patterns=drop_query_params,
                                    volatile_param_names=volatile_params,
                                    redact_param_names=redact_params,
                                    redact_mode=redact_mode,
                                    identity_rules=identity_rules,
                                    sort_query=sort_query_params,
                                )
                            else:
                                key_url, raw_redacted, is_volatile, was_redacted = u, u, False, False

                            kind, score = self._classify(key_url)
                            if kind == "junk":
                                continue
                            if score < min_score:
                                continue
                            if (not include_pages) and kind == "page":
                                continue

                            if store and self._store_has_emitted(store, key_url):
                                continue
                            if key_url in found_keys_set:
                                continue

                            found_keys_set.add(key_url)

                            found_objs.append({
                                "url": key_url,             # canonical primary
                                "canonical_url": key_url,
                                "raw_url": raw_redacted,    # redacted raw
                                "source": "linkcontentcrawler",
                                "seed": seed,
                                "final_url": seed,
                                "kind": kind,
                                "score": score,
                                "volatile": bool(is_volatile),
                                "redacted": bool(was_redacted),
                                "first_seen": time.time(),
                            })
                            kept += 1

                            if store:
                                self._store_mark_emitted(
                                    store,
                                    key_url=key_url,
                                    raw_url=raw_redacted,
                                    now_ts=time.time(),
                                    source="crawl",
                                    seed_url=seed,
                                    final_url=seed,
                                    kind=kind,
                                    score=score,
                                    is_volatile=is_volatile,
                                    was_redacted=was_redacted,
                                )

                        per_seed_stats[seed] = {
                            "status": "ok",
                            "final_url": seed,
                            "ms": int((time.time() - t0) * 1000),
                            "out_links": len(out_links),
                            "kept": kept,
                        }

                    except Exception as e:
                        per_seed_stats[seed] = {"status": "error", "error": str(e)[:200], "out_links": 0, "kept": 0}
                        DEBUG_LOGGER.log_message(f"[LinkContentCrawler][Seed] ERROR seed={seed} err={e}")

            await asyncio.gather(*[crawl_seed(s) for s in seeds_to_fetch])

        # Merge into Memory
        mem2 = Memory.load()

        existing = mem2.get(out_key, [])
        if not isinstance(existing, list):
            existing = []

        # dedupe based on canonical_url
        existing_keys = set()
        for x in existing:
            if isinstance(x, dict):
                cu = x.get("canonical_url") or x.get("url")
                if isinstance(cu, str) and cu:
                    existing_keys.add(cu)

        new_added = 0
        for obj in found_objs:
            key_url = obj.get("canonical_url") or obj.get("url")
            if not key_url or key_url in existing_keys:
                continue
            existing.append(obj)
            existing_keys.add(key_url)
            new_added += 1

        max_memory_items = int(params.get("max_memory_items", 4000))
        if len(existing) > max_memory_items:
            existing = existing[-max_memory_items:]

        mem2[out_key] = existing
        mem2[stats_key] = per_seed_stats
        if out_urls_key:
            mem2[out_urls_key] = [
                (x.get("canonical_url") or x.get("url"))
                for x in existing
                if isinstance(x, dict) and (x.get("canonical_url") or x.get("url"))
            ][-max_memory_items:]

        Memory.save(mem2)

        # Report
        volatile_count = sum(1 for o in found_objs if o.get("volatile"))
        redacted_count = sum(1 for o in found_objs if o.get("redacted"))

        lines = [
            "### 🧠 LinkContentCrawler Report (URL Canonicalization + Identity Rules + Volatile Handling)",
            f"_Memory Sources: {', '.join(memory_sources)}_",
            f"_Seeds: {len(seed_urls)} | Fetched: {len(seeds_to_fetch)} | Found: {len(found_objs)} | Added to Memory: {new_added}_",
            "",
            f"**min_score:** {min_score} | **include_pages:** {include_pages}",
            f"**canonicalize_urls:** {canonicalize_urls} | **sort_query_params:** {sort_query_params}",
            f"**identity_rules:** {len(identity_rules)}",
            f"**volatile_found:** {volatile_count} | **redacted_found:** {redacted_count} (mode={redact_mode})",
            f"**DB Cache:** {'ON' if use_database else 'OFF'}",
        ]
        if use_database:
            lines.append(f"**db_path:** {db_path}")
            lines.append(f"**seed_ttl_seconds:** {seed_ttl_seconds:.0f}")

        lines.append("")
        lines.append("**Sample Found Content (canonical_url | raw_url):**")
        for o in found_objs[:12]:
            lines.append(
                f"- [{o.get('kind')}] score={o.get('score')} "
                f"volatile={bool(o.get('volatile'))} redacted={bool(o.get('redacted'))}\n"
                f"  • canon: {o.get('canonical_url')}\n"
                f"  • raw:   {o.get('raw_url')}"
            )

        if log:
            lines.append("\n**Log:**")
            lines.extend(log)

        meta = {
            "seed_count": len(seed_urls),
            "fetched_seed_count": len(seeds_to_fetch),
            "found_count": len(found_objs),
            "new_added": new_added,
            "content_links_key": out_key,
            "content_urls_key": out_urls_key,
            "per_seed_stats_key": stats_key,
            "use_database": use_database,
            "db_path": db_path if use_database else None,
            "seed_ttl_seconds": seed_ttl_seconds,
            "canonicalize_urls": canonicalize_urls,
            "sort_query_params": sort_query_params,
            "identity_rules_count": len(identity_rules),
            "volatile_found": volatile_count,
            "redacted_found": redacted_count,
            "items": found_objs,
            "stats": per_seed_stats,
        }
        return "\n".join(lines), meta

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asyncio.run(self._execute_async(payload, params))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "memory_sources": "scraped_links",
            "timeout": 10.0,
            "max_seeds": 150,
            "max_concurrency": 12,
            "max_links_per_seed": 250,

            "min_score": 20,
            "include_pages": True,

            "content_links_key": "content_links",
            "content_urls_key": "content_urls",
            "per_seed_stats_key": "content_seed_stats",
            "max_memory_items": 4000,

            "use_database": False,
            "db_path": "link_corpus.db",
            "seed_ttl_seconds": 21600,

            # ---------------- NEW ----------------
            "canonicalize_urls": True,
            "sort_query_params": True,

            # Drops “tracking/noise” from canonical URL
            "drop_query_params": "utm_*,gclid,fbclid,msclkid,igshid,mc_cid,mc_eid,ref,ref_src,spm,cmpid",

            # Params that indicate signed/expiring media URLs (removed from canonical URL by default)
            "volatile_params": "token,access_token,refresh_token,sig,signature,expires,exp,policy,key,cdn_hash,hash,hmac",

            # Sensitive params to mask/drop from stored raw_url and remove from canonical_url
            "redact_params": "access_token,refresh_token,authorization,auth,bearer,session,sessionid,sid,token",
            "redact_mode": "mask",  # "mask" or "drop"

            # Host/path-specific identity rules (keep only these params in canonical URL)
            "identity_rules": [
                # {"host": "www.youtube.com", "path_prefix": "/watch", "keep": ["v"]},
                # {"host": "*.example.com", "path_prefix": "/player", "keep": "id"},
            ],
        }


# register
BLOCKS.register("linkcontentcrawler", LinkContentCrawlerBlock)

# ======================= CDNBlock ============================

@dataclass
class CDNBlock(BaseBlock):
    """
    CDNBlock
    --------
    Feeds on input links (from Memory or explicit list) and outputs CDN-like URLs.

    Patch notes:
      ✅ Always writes cdn_links_key / cdn_urls_key / per_seed_stats_key to Memory,
        even when there are no seeds or no matches (prevents "no output" confusion).
      ✅ Adds diagnostics: missing/empty memory_sources keys are logged and included.
      ✅ Still supports seeds override + payload fallback.
    """

    _URL_RE = re.compile(r"https?://[^\s\"'<>\\)\]]+", re.IGNORECASE)
    _HREF_SRC_RE = re.compile(r"""(?:href|src)=["'](.*?)["']""", re.IGNORECASE)

    _CDN_HOST_TOKENS = (
        "cdn", "edge", "edgesuite", "edgekey", "akamai", "akamaized",
        "cloudfront", "fastly", "fastlylb", "stackpathcdn", "netdna-cdn",
        "cloudflare", "r2.dev", "googleusercontent", "googlevideo", "gvt1",
        "hwcdn", "llnwd", "cachefly", "b-cdn", "bunnycdn", "vkuseraudio",
    )

    _CDN_SUFFIXES = (
        ".cloudfront.net",
        ".akamaized.net",
        ".akamaihd.net",
        ".edgesuite.net",
        ".edgekey.net",
        ".fastly.net",
        ".fastlylb.net",
        ".stackpathcdn.com",
        ".cloudflare.net",
        ".r2.dev",
        ".googlevideo.com",
        ".gvt1.com",
        ".llnwd.net",
        ".hwcdn.net",
        ".cachefly.net",
        ".b-cdn.net",
        ".bunnycdn.ru",
        ".bunnycdn.com",
    )

    _HEADER_SIGNAL_KEYS = (
        "cf-ray", "cf-cache-status",
        "x-amz-cf-id", "x-amz-cf-pop",
        "x-cache", "x-cache-hits",
        "via",
        "x-served-by", "x-timer",
        "server",
        "x-cdn", "x-cdn-request-id",
    )

    def _make_store(self, db_path: str):
        cfg = submanagers.DatabaseConfig(path=db_path)
        db = submanagers.DatabaseSubmanager(cfg, logger=DEBUG_LOGGER)
        store = CDNStore(db=db)
        store.ensure_schema()
        return store

    # ------------------ flatten / parse input ------------------

    def _flatten_urls(self, raw: Any) -> List[str]:
        out: List[str] = []
        seen = set()

        def push(u: str):
            u = (u or "").strip()
            if not u:
                return

            # direct url
            if u.startswith(("http://", "https://")):
                if u not in seen:
                    seen.add(u)
                    out.append(u)
                return

            # scan blob for urls
            for m in self._URL_RE.finditer(u[:250_000]):
                uu = m.group(0)
                if uu and uu not in seen:
                    seen.add(uu)
                    out.append(uu)

        def walk(x: Any):
            if x is None:
                return
            if isinstance(x, str):
                push(x)
                return
            if isinstance(x, (int, float)):
                push(str(x))
                return
            if isinstance(x, list):
                for it in x:
                    walk(it)
                return
            if isinstance(x, dict):
                for k in ("url", "href", "link", "page", "request_url", "final_url", "source_url"):
                    v = x.get(k)
                    if isinstance(v, str) and v.strip():
                        push(v)
                for k in ("text", "html", "body", "snippet"):
                    v = x.get(k)
                    if isinstance(v, str) and v.strip():
                        push(v)
                for v in x.values():
                    if isinstance(v, (list, dict)):
                        walk(v)
                return

            push(str(x))

        walk(raw)
        return out

    def _host(self, u: str) -> str:
        try:
            return urlparse(u).netloc.lower()
        except Exception:
            return ""

    def _looks_cdn_host(self, host: str) -> Tuple[bool, int, List[str]]:
        host = (host or "").lower()
        if not host:
            return False, 0, []

        score = 0
        ev: List[str] = []

        for suf in self._CDN_SUFFIXES:
            if host.endswith(suf):
                score += 60
                ev.append(f"host_suffix:{suf}")
                break

        for tok in self._CDN_HOST_TOKENS:
            if tok in host:
                score += 18
                ev.append(f"host_token:{tok}")

        if "cdn" in host and all("host_token:cdn" != e for e in ev):
            score += 10
            ev.append("host_token:cdn")

        return (score >= 30), score, ev

    def _header_signals(self, headers: Dict[str, str]) -> Tuple[int, List[str]]:
        if not headers:
            return 0, []
        score = 0
        ev: List[str] = []

        lower_map = {str(k).lower(): str(v) for k, v in (headers or {}).items()}
        for k in self._HEADER_SIGNAL_KEYS:
            if k in lower_map:
                score += 10
                ev.append(f"hdr:{k}")

        server = lower_map.get("server", "").lower()
        if any(x in server for x in ("cloudflare", "akamai", "fastly", "varnish")):
            score += 15
            ev.append(f"server_hint:{server[:40]}")
        return score, ev

    def _extract_asset_urls_from_html(self, html: str, base_url: str, max_assets: int = 200) -> List[str]:
        if not html:
            return []
        out: List[str] = []
        seen = set()

        for m in self._HREF_SRC_RE.finditer(html[:600_000]):
            raw = (m.group(1) or "").strip()
            if not raw or raw.startswith(("#", "javascript:", "mailto:", "tel:")):
                continue
            try:
                full = urljoin(base_url, raw)
                pu = urlparse(full)
                if pu.scheme not in ("http", "https"):
                    continue
                if full not in seen:
                    seen.add(full)
                    out.append(full)
                    if len(out) >= max_assets:
                        break
            except Exception:
                continue

        if len(out) < max_assets:
            for m in self._URL_RE.finditer(html[:600_000]):
                u = m.group(0)
                if u and u not in seen:
                    seen.add(u)
                    out.append(u)
                    if len(out) >= max_assets:
                        break

        return out

    async def _head_or_get(
        self,
        http: "HTTPSSubmanager",
        url: str,
        *,
        want_html_assets: bool,
        max_html_bytes: int,
    ) -> Tuple[Optional[int], Dict[str, str], str, str]:
        try:
            r = await http._request("HEAD", url, want_body=False, allow_redirects=True)
            status = r.status
            hdrs = r.headers or {}
            final_url = r.final_url or url

            html = ""
            ctype = (hdrs.get("Content-Type") or hdrs.get("content-type") or "").lower()
            if want_html_assets and (("text/html" in ctype) or status in (405, 403, 200)):
                r2 = await http._request("GET", final_url, want_body=True, allow_redirects=True, max_bytes=max_html_bytes)
                hdrs = r2.headers or hdrs
                final_url = r2.final_url or final_url
                if r2.ok and r2.body:
                    try:
                        html = r2.body.decode("utf-8", errors="ignore")
                    except Exception:
                        html = ""
            return status, hdrs, final_url, html
        except Exception:
            return None, {}, url, ""

    # ------------------ Memory output initializer (PATCH) ------------------

    def _ensure_memory_outputs(
        self,
        *,
        out_key: str,
        out_urls_key: str,
        stats_key: str,
        per_seed_stats: Dict[str, Any],
        existing_items: Optional[List[Dict[str, Any]]] = None,
        max_memory_items: int = 5000,
        diagnostics: Optional[Dict[str, Any]] = None,
    ) -> None:
        mem = Memory.load()
        if not isinstance(mem, dict):
            mem = {}

        items = existing_items if isinstance(existing_items, list) else mem.get(out_key, [])
        if not isinstance(items, list):
            items = []

        # cap
        if len(items) > max_memory_items:
            items = items[-max_memory_items:]

        mem[out_key] = items
        mem[stats_key] = per_seed_stats or {}

        if out_urls_key:
            mem[out_urls_key] = [x.get("url") for x in items if isinstance(x, dict) and x.get("url")][-max_memory_items:]

        # Optional extra debug info without breaking schema
        if diagnostics:
            mem.setdefault("cdn_debug", {})
            if isinstance(mem["cdn_debug"], dict):
                mem["cdn_debug"].update(diagnostics)

        Memory.save(mem)

    # ------------------ Execution ------------------

    async def _execute_async(self, payload: Any, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        # Inputs
        memory_sources_raw = str(params.get("memory_sources", "") or "").strip()
        memory_sources = [k.strip() for k in memory_sources_raw.split(",") if k.strip()]
        seeds_override = str(params.get("seeds", "") or "").strip()

        # Perf knobs
        timeout = float(params.get("timeout", 6.0))
        max_seeds = int(params.get("max_seeds", 200))
        max_concurrency = int(params.get("max_concurrency", 12))

        # HTML asset extraction
        extract_assets = bool(params.get("extract_assets", True))
        max_html_bytes = int(params.get("max_html_bytes", 220_000))
        max_assets_per_seed = int(params.get("max_assets_per_seed", 200))

        # Emit knobs
        min_score = int(params.get("min_score", 45))

        # Memory outputs
        out_key = str(params.get("cdn_links_key", "cdn_links")).strip()
        out_urls_key = str(params.get("cdn_urls_key", "cdn_urls")).strip()
        stats_key = str(params.get("per_seed_stats_key", "cdn_seed_stats")).strip()
        max_memory_items = int(params.get("max_memory_items", 5000))

        # DB support
        use_database = bool(params.get("use_database", False))
        db_path = str(params.get("db_path", "link_corpus.db"))
        seed_ttl_seconds = float(params.get("seed_ttl_seconds", 6 * 3600))

        DEBUG_LOGGER.log_message(
            f"[CDNBlock] start | memory_sources={memory_sources} seeds_override={'YES' if bool(seeds_override) else 'NO'} "
            f"timeout={timeout} max_seeds={max_seeds} max_concurrency={max_concurrency} "
            f"extract_assets={extract_assets} min_score={min_score} use_database={use_database}"
        )

        # Build seed list + diagnostics (PATCH)
        seed_urls: List[str] = []
        missing_keys: List[str] = []
        empty_keys: List[str] = []

        if seeds_override:
            seed_urls = [s.strip() for s in seeds_override.split(",") if s.strip()]
        else:
            if not memory_sources:
                seed_urls = self._flatten_urls(payload)
            else:
                mem = Memory.load()
                if not isinstance(mem, dict):
                    mem = {}
                for k in memory_sources:
                    if k not in mem:
                        missing_keys.append(k)
                        continue
                    raw_val = mem.get(k)
                    flattened = self._flatten_urls(raw_val)
                    if not flattened:
                        empty_keys.append(k)
                    seed_urls.extend(flattened)

        # Dedup + cap
        seed_urls = list(dict.fromkeys([u for u in seed_urls if u.startswith(("http://", "https://"))]))
        if max_seeds and len(seed_urls) > max_seeds:
            seed_urls = seed_urls[:max_seeds]

        per_seed_stats: Dict[str, Dict[str, Any]] = {}

        # ✅ PATCH: Always write outputs even if no seeds
        if not seed_urls:
            self._ensure_memory_outputs(
                out_key=out_key,
                out_urls_key=out_urls_key,
                stats_key=stats_key,
                per_seed_stats=per_seed_stats,
                existing_items=[],
                max_memory_items=max_memory_items,
                diagnostics={
                    "last_run": time.time(),
                    "reason": "no_seeds",
                    "memory_sources": memory_sources,
                    "missing_keys": missing_keys,
                    "empty_keys": empty_keys,
                },
            )
            msg = (
                "### 🌐 CDNBlock Report\n"
                "_No seeds found; wrote empty outputs to Memory._\n\n"
                f"- memory_sources={memory_sources}\n"
                f"- missing_keys={missing_keys}\n"
                f"- empty_keys={empty_keys}\n"
            )
            meta = {
                "error": "no seeds",
                "seed_count": 0,
                "missing_keys": missing_keys,
                "empty_keys": empty_keys,
                "cdn_links_key": out_key,
                "cdn_urls_key": out_urls_key,
                "per_seed_stats_key": stats_key,
            }
            return msg, meta

        # Optional DB store
        store: Optional[CDNStore] = None
        if use_database:
            try:
                store = self._make_store(db_path)
                DEBUG_LOGGER.log_message(f"[CDNBlock][DB] init ok | db_path={db_path}")
            except Exception as e:
                store = None
                use_database = False
                DEBUG_LOGGER.log_message(f"[CDNBlock][DB] init FAILED: {e} (DB disabled)")

        # TTL gating
        now_ts = time.time()
        seeds_to_fetch = seed_urls
        if store:
            seeds_to_fetch = [u for u in seed_urls if store.seed_should_fetch(u, ttl_seconds=seed_ttl_seconds, now_ts=now_ts)]

        found: List[Dict[str, Any]] = []
        found_set: set[str] = set()
        sem = asyncio.Semaphore(max_concurrency)

        async with submanagers.HTTPSSubmanager(timeout=timeout, retries=2, max_conn_per_host=8) as http:

            async def process_seed(seed: str):
                async with sem:
                    t0 = time.time()
                    seed_host = self._host(seed)

                    status, hdrs, final_url, html = await self._head_or_get(
                        http,
                        seed,
                        want_html_assets=extract_assets,
                        max_html_bytes=max_html_bytes,
                    )

                    if store:
                        try:
                            store.seed_mark_fetched(seed, now_ts=time.time(), status=int(status or 0))
                        except Exception:
                            pass

                    if status is None:
                        per_seed_stats[seed] = {"status": "error", "ms": int((time.time() - t0) * 1000)}
                        return

                    final_host = self._host(final_url)
                    hdr_score, hdr_ev = self._header_signals(hdrs)
                    host_is_cdn, host_score, host_ev = self._looks_cdn_host(final_host)

                    host_change_score = 0
                    host_change_ev: List[str] = []
                    if seed_host and final_host and seed_host != final_host:
                        host_change_score = 12
                        host_change_ev.append("host_changed")

                    score_a = host_score + hdr_score + host_change_score
                    ev_a = host_ev + hdr_ev + host_change_ev
                    kept_a = 0

                    if score_a >= min_score and final_url and final_url not in found_set:
                        if (not store) or (not store.has_emitted(final_url)):
                            found_set.add(final_url)
                            found.append({
                                "url": final_url,
                                "source": "cdnblock_final_url",
                                "seed": seed,
                                "final_url": final_url,
                                "seed_host": seed_host,
                                "cdn_host": final_host,
                                "status": int(status),
                                "score": int(score_a),
                                "evidence": ev_a[:12],
                                "first_seen": time.time(),
                            })
                            kept_a = 1
                            if store:
                                store.mark_emitted(
                                    final_url, host=final_host, kind="final_url",
                                    source_seed=seed, score=int(score_a), now_ts=time.time()
                                )

                    kept_assets = 0
                    scanned_assets = 0
                    if extract_assets and html:
                        assets = self._extract_asset_urls_from_html(html, final_url, max_assets=max_assets_per_seed)
                        scanned_assets = len(assets)
                        for u in assets:
                            if u in found_set:
                                continue
                            h = self._host(u)
                            is_cdn, hs, hev = self._looks_cdn_host(h)
                            if not is_cdn:
                                continue
                            sc = hs + (hdr_score // 2)
                            if sc < min_score:
                                continue
                            if store and store.has_emitted(u):
                                continue

                            found_set.add(u)
                            found.append({
                                "url": u,
                                "source": "cdnblock_html_asset",
                                "seed": seed,
                                "final_url": final_url,
                                "seed_host": seed_host,
                                "cdn_host": h,
                                "status": int(status),
                                "score": int(sc),
                                "evidence": (hev + hdr_ev)[:12],
                                "first_seen": time.time(),
                            })
                            kept_assets += 1
                            if store:
                                store.mark_emitted(
                                    u, host=h, kind="html_asset",
                                    source_seed=seed, score=int(sc), now_ts=time.time()
                                )

                    per_seed_stats[seed] = {
                        "status": f"http_{int(status)}",
                        "final_url": final_url,
                        "ms": int((time.time() - t0) * 1000),
                        "kept_final": kept_a,
                        "scanned_assets": scanned_assets,
                        "kept_assets": kept_assets,
                        "final_host": final_host,
                        "final_score": int(score_a),
                        "final_evidence": ev_a[:8],
                    }

            await asyncio.gather(*[process_seed(s) for s in seeds_to_fetch])

        # Merge into Memory (always ensures outputs exist)
        mem = Memory.load()
        if not isinstance(mem, dict):
            mem = {}

        existing = mem.get(out_key, [])
        if not isinstance(existing, list):
            existing = []

        existing_urls = {str(x.get("url")) for x in existing if isinstance(x, dict) and x.get("url")}
        new_added = 0
        for obj in found:
            u = obj.get("url")
            if not u or u in existing_urls:
                continue
            existing.append(obj)
            existing_urls.add(u)
            new_added += 1

        # ✅ PATCH: use unified writer (caps + urls list + stats + debug)
        self._ensure_memory_outputs(
            out_key=out_key,
            out_urls_key=out_urls_key,
            stats_key=stats_key,
            per_seed_stats=per_seed_stats,
            existing_items=existing,
            max_memory_items=max_memory_items,
            diagnostics={
                "last_run": time.time(),
                "memory_sources": memory_sources,
                "missing_keys": missing_keys,
                "empty_keys": empty_keys,
                "seed_count": len(seed_urls),
                "fetched_seed_count": len(seeds_to_fetch),
                "found_count": len(found),
                "new_added": new_added,
            },
        )

        lines = [
            "### 🌐 CDNBlock Report",
            f"_Seeds: {len(seed_urls)} | Fetched: {len(seeds_to_fetch)} | Found CDN URLs: {len(found)} | Added to Memory: {new_added}_",
            "",
            f"**extract_assets:** {extract_assets} | **min_score:** {min_score}",
            f"**DB Cache:** {'ON' if use_database else 'OFF'}",
        ]
        if memory_sources:
            lines.append(f"**memory_sources:** {memory_sources}")
        if missing_keys or empty_keys:
            lines.append(f"**missing_keys:** {missing_keys}")
            lines.append(f"**empty_keys:** {empty_keys}")

        lines.append("")
        lines.append("**Sample CDN URLs:**")
        for o in found[:15]:
            lines.append(f"- score={o.get('score')} host={o.get('cdn_host')} {o.get('url')}")

        meta = {
            "seed_count": len(seed_urls),
            "fetched_seed_count": len(seeds_to_fetch),
            "found_count": len(found),
            "new_added": new_added,
            "cdn_links_key": out_key,
            "cdn_urls_key": out_urls_key,
            "per_seed_stats_key": stats_key,
            "missing_keys": missing_keys,
            "empty_keys": empty_keys,
            "items": found,
            "urls": [o["url"] for o in found],
            "stats": per_seed_stats,
        }
        return "\n".join(lines), meta

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asyncio.run(self._execute_async(payload, params))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "memory_sources": "content_links,scraped_links",
            "seeds": "",
            "timeout": 6.0,
            "max_seeds": 200,
            "max_concurrency": 12,
            "extract_assets": True,
            "max_html_bytes": 220000,
            "max_assets_per_seed": 200,
            "min_score": 45,
            "cdn_links_key": "cdn_links",
            "cdn_urls_key": "cdn_urls",
            "per_seed_stats_key": "cdn_seed_stats",
            "max_memory_items": 5000,
            "use_database": False,
            "db_path": "link_corpus.db",
            "seed_ttl_seconds": 21600,
        }

# register
BLOCKS.register("cdn", CDNBlock)


# ======================= HiddenContentTrackerBlock ===========================

@dataclass
class HiddenContentTrackerBlock(BaseBlock):
    IGNORED_EXTENSIONS = {
        ".css", ".js", ".json", ".xml", ".svg", ".png", ".jpg", ".jpeg",
        ".gif", ".ico", ".woff", ".woff2", ".ttf", ".eot", ".map"
    }

    _URL_RE = re.compile(r"https?://[^\s\"'<>\\)]+", re.IGNORECASE)
    _IMAGE_EXT_RE = re.compile(r"\.(jpg|jpeg|png|webp|gif|bmp|tiff|avif)(\?|#|$)", re.I)

    def __post_init__(self):
        self.db: Optional[submanagers.DatabaseSubmanager] = None
        self.store: Optional[PageTrackerStore] = None

        self.js_sniffer = submanagers.JSSniffer(
            submanagers.JSSniffer.Config(enable_auto_scroll=True, max_scroll_steps=20, scroll_step_delay_ms=350)
        )
        self.network_sniffer = submanagers.NetworkSniffer(
            submanagers.NetworkSniffer.Config(enable_auto_scroll=True, max_scroll_steps=20, scroll_step_delay_ms=350)
        )
        self.runtime_sniffer = submanagers.RuntimeSniffer(submanagers.RuntimeSniffer.Config())
        self.react_sniffer = submanagers.ReactSniffer(
            submanagers.ReactSniffer.Config(hook_history_api=True, hook_link_clicks=True, inspect_react_devtools_hook=True)
        )
        self.database_sniffer = submanagers.DatabaseSniffer(
            submanagers.DatabaseSniffer.Config(
                enable_indexeddb_dump=True,
                enable_backend_fingerprint=True,
                enable_html_link_scan=True,
                enable_backend_link_scan=True,
            )
        )
        self.interaction_sniffer = submanagers.InteractionSniffer(
            submanagers.InteractionSniffer.Config(
                enable_cdp_listeners=True,
                enable_overlay_detection=True,
                enable_form_extraction=True,
            )
        )

    # ------------------------------------------------------------------ #
    # Playwright context helpers
    # ------------------------------------------------------------------ #
    async def _open_playwright_context(
        self,
        *,
        ua: str,
        block_resources: bool,
        blocked_resource_types: Set[str],
        block_domains: bool,
        blocked_domains: Set[str],
        log: List[str],
        use_camoufox: bool = False,
        camoufox_options: Optional[Dict[str, Any]] = None,
        headless: bool = True,
    ):
        camoufox_options = camoufox_options or {}

        def _host_blocked(url: str) -> bool:
            try:
                host = urlparse(url).netloc.lower().split(":", 1)[0]
            except Exception:
                return False
            if not host:
                return False
            for d in blocked_domains:
                dd = (d or "").strip().lower()
                if not dd:
                    continue
                if host == dd or host.endswith("." + dd):
                    return True
            return False

        async def _install_route_blocking(context):
            if not (block_resources or block_domains):
                return

            async def route_handler(route, request):
                try:
                    rtype = (request.resource_type or "").lower()
                except Exception:
                    rtype = ""

                if block_domains and _host_blocked(request.url):
                    await route.abort()
                    return

                if block_resources and rtype in blocked_resource_types:
                    await route.abort()
                    return

                await route.continue_()

            await context.route("**/*", route_handler)

        # Camoufox
        if use_camoufox and AsyncCamoufox is not None:
            try:
                opts = dict(camoufox_options or {})
                opts.setdefault("headless", headless)
                opts.setdefault("block_webrtc", True)
                opts.setdefault("geoip", False)
                opts.setdefault("humanize", False)

                cm = AsyncCamoufox(**opts)
                browser = await cm.__aenter__()
                context = await browser.new_context(user_agent=ua)
                await _install_route_blocking(context)
                log.append("[HiddenContentTracker][PW] Camoufox context opened.")
                return cm, browser, context
            except Exception as e:
                log.append(f"[HiddenContentTracker][PW] Camoufox failed ({e}); falling back to Chromium.")

        # Standard Playwright
        try:
            from playwright.async_api import async_playwright
        except Exception as e:
            log.append(f"[HiddenContentTracker][PW] Playwright not available: {e}")
            return None, None, None

        pw = await async_playwright().start()
        browser = await pw.chromium.launch(headless=headless)
        context = await browser.new_context(user_agent=ua)
        await _install_route_blocking(context)

        log.append("[HiddenContentTracker][PW] Chromium context opened.")
        return pw, browser, context

    async def _close_playwright_context(self, pw_handle, browser, context, log: List[str]):
        try:
            if context is not None:
                await context.close()
        except Exception as e:
            log.append(f"[HiddenContentTracker][PW] context.close error: {e}")

        try:
            if browser is not None:
                await browser.close()
        except Exception as e:
            log.append(f"[HiddenContentTracker][PW] browser.close error: {e}")

        try:
            if pw_handle is not None:
                stop = getattr(pw_handle, "stop", None)
                if stop:
                    if asyncio.iscoroutinefunction(stop):
                        await stop()
                    else:
                        stop()
                else:
                    aexit = getattr(pw_handle, "__aexit__", None)
                    if aexit:
                        if asyncio.iscoroutinefunction(aexit):
                            await aexit(None, None, None)
                        else:
                            aexit(None, None, None)
        except Exception as e:
            log.append(f"[HiddenContentTracker][PW] stop/__aexit__ error: {e}")

        log.append("[HiddenContentTracker][PW] context closed.")

    # ------------------------------------------------------------------ #
    # DB lifecycle
    # ------------------------------------------------------------------ #
    def _initialize_database(self, db_path: str, logger=None) -> None:
        if self.db and self.store:
            return
        cfg = submanagers.DatabaseConfig(path=str(db_path or "link_corpus.db"))
        self.db = submanagers.DatabaseSubmanager(cfg, logger=logger)
        self.db.open()
        self.store = PageTrackerStore(db=self.db)
        self.store.ensure_schema()

    # ------------------------------------------------------------------ #
    # Reverse image fingerprinting (optional)
    # ------------------------------------------------------------------ #
    def _sha256_file(self, path: str) -> str:
        h = hashlib.sha256()
        with open(path, "rb") as f:
            for chunk in iter(lambda: f.read(1024 * 1024), b""):
                h.update(chunk)
        return h.hexdigest()

    def _phash(self, img_path: str) -> Optional[str]:
        if Image is None:
            return None
        try:
            img = Image.open(img_path).convert("L").resize((32, 32))
            pixels = list(img.getdata())
            mat = [pixels[i * 32:(i + 1) * 32] for i in range(32)]
            small = []
            for y in range(8):
                for x in range(8):
                    small.append(mat[y][x])
            avg = sum(small) / max(1, len(small))
            bits = ["1" if v > avg else "0" for v in small]
            return hex(int("".join(bits), 2))[2:].rjust(16, "0")
        except Exception:
            return None

    # ------------------------------------------------------------------ #
    # NEW: Reverse-image helpers (NO API KEYS)
    # ------------------------------------------------------------------ #
    async def _search_searxng_json(
        self,
        searxng_url: str,
        query: str,
        limit: int,
        timeout: float,
        log: List[str],
        *,
        engines: str = "",
        safesearch: int = 0,
        language: str = "en",
    ) -> List[str]:
        """
        Minimal SearXNG JSON search. Returns list of result URLs.
        Requires: searxng_url points at your instance, e.g. "http://127.0.0.1:8080"
        """
        searxng_url = (searxng_url or "").rstrip("/")
        if not searxng_url:
            log.append("[HiddenContentTracker][SearXNG] missing searxng_url.")
            return []

        params = {
            "q": query,
            "format": "json",
            "language": language,
            "safesearch": str(int(safesearch)),
        }
        if engines:
            params["engines"] = engines

        out: List[str] = []
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(
                    f"{searxng_url}/search",
                    params=params,
                    timeout=aiohttp.ClientTimeout(total=timeout),
                    headers={"User-Agent": "Mozilla/5.0 PromptChat/HiddenContentTracker"},
                ) as resp:
                    txt = await resp.text()
                    if resp.status != 200:
                        log.append(f"[HiddenContentTracker][SearXNG] HTTP {resp.status}: {txt[:300]}")
                        return []
                    js = json.loads(txt)

            for r in (js.get("results") or []):
                u = (r.get("url") or "").strip()
                if u:
                    out.append(u)
                    if len(out) >= int(limit):
                        break
        except Exception as e:
            log.append(f"[HiddenContentTracker][SearXNG] error: {e}")
            return []

        return out

    async def _coerce_reverse_image_inputs(
        self,
        *,
        image_url: str,
        image_path: str,
        timeout: float,
        log: List[str],
        ffmpeg_bin: str = "ffmpeg",
    ) -> Tuple[str, str, List[str]]:
        """
        (your function verbatim, lightly namespaced for this block)
        """
        import tempfile
        import subprocess
        from urllib.parse import urlparse

        temp_files: List[str] = []

        image_url = (image_url or "").strip()
        image_path = (image_path or "").strip()

        IMG_EXTS = (".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp", ".tiff", ".avif", ".svg")
        VID_EXTS = (".mp4", ".mkv", ".mov", ".avi", ".webm", ".wmv", ".flv", ".m4v", ".gif")

        def _is_http_url(u: str) -> bool:
            try:
                p = urlparse(u)
                return p.scheme in ("http", "https") and bool(p.netloc)
            except Exception:
                return False

        def _looks_like_image_file(path: str) -> bool:
            return (path or "").lower().endswith(IMG_EXTS)

        def _looks_like_video_file(path: str) -> bool:
            low = (path or "").lower()
            return low.endswith(VID_EXTS) or any(x in low for x in (".m3u8", ".mpd"))

        def _looks_like_image_url(u: str) -> bool:
            low = (u or "").lower()
            return low.endswith(IMG_EXTS) or bool(self._IMAGE_EXT_RE.search(low))

        async def _download_to_temp(url: str) -> str:
            parsed = urlparse(url)
            base = os.path.basename(parsed.path or "")
            ext = os.path.splitext(base)[1].lower()
            if not ext or len(ext) > 8:
                ext = ".bin"

            fd, outp = tempfile.mkstemp(prefix="revimg_", suffix=ext)
            os.close(fd)
            temp_files.append(outp)

            try:
                async with aiohttp.ClientSession() as session:
                    async with session.get(
                        url,
                        timeout=aiohttp.ClientTimeout(total=timeout),
                        headers={"User-Agent": "Mozilla/5.0 PromptChat/HiddenContentTracker"},
                    ) as resp:
                        resp.raise_for_status()
                        with open(outp, "wb") as f:
                            while True:
                                chunk = await resp.content.read(1024 * 64)
                                if not chunk:
                                    break
                                f.write(chunk)
            except Exception as e:
                log.append(f"[HiddenContentTracker][RevImg] download failed url={url!r}: {e}")
                return ""

            return outp

        def _ffmpeg_extract_first_frame(src_path: str) -> str:
            fd, outp = tempfile.mkstemp(prefix="revimg_frame_", suffix=".png")
            os.close(fd)
            temp_files.append(outp)

            cmd = [ffmpeg_bin, "-y", "-i", src_path, "-frames:v", "1", outp]
            try:
                p = subprocess.run(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=max(5, int(timeout)),
                    check=False,
                )
                if p.returncode != 0 or not os.path.exists(outp) or os.path.getsize(outp) <= 0:
                    err = (p.stderr or b"")[:800].decode("utf-8", "ignore")
                    log.append(f"[HiddenContentTracker][RevImg] ffmpeg extract failed rc={p.returncode} err={err}")
                    return ""
            except Exception as e:
                log.append(f"[HiddenContentTracker][RevImg] ffmpeg error: {e}")
                return ""

            return outp

        # 1) Prefer local path if valid
        if image_path:
            if not os.path.exists(image_path):
                log.append(f"[HiddenContentTracker][RevImg] image_path does not exist: {image_path}")
                image_path = ""
            else:
                if _looks_like_image_file(image_path):
                    return "", image_path, temp_files
                if _looks_like_video_file(image_path):
                    frame = _ffmpeg_extract_first_frame(image_path)
                    if frame:
                        log.append(f"[HiddenContentTracker][RevImg] extracted frame -> {frame}")
                        return "", frame, temp_files
                return "", image_path, temp_files

        # 2) URL input
        if image_url and _is_http_url(image_url):
            if _looks_like_image_url(image_url):
                return image_url, "", temp_files

            tmp = await _download_to_temp(image_url)
            if not tmp:
                return image_url, "", temp_files

            if _looks_like_image_file(tmp):
                return "", tmp, temp_files

            frame = _ffmpeg_extract_first_frame(tmp)
            if frame:
                return "", frame, temp_files

            return "", tmp, temp_files

        return "", "", temp_files

    async def _reverse_image_search_seeds(
        self,
        *,
        image_url: str,
        image_path: str,
        limit: int,
        timeout: float,
        log: List[str],
        searxng_url: str,
        searxng_engines: str = "",
        catbox_upload: bool = True,
    ) -> List[str]:
        """
        (your function, adjusted to call _search_searxng_json + optional catbox toggle)
        """
        import aiohttp

        limit = max(1, int(limit or 10))

        # 1) Catbox upload (optional)
        if catbox_upload and image_path and os.path.exists(image_path) and not image_url:
            log.append(f"[HiddenContentTracker][RevImg] Uploading {os.path.basename(image_path)} to Catbox...")
            try:
                async with aiohttp.ClientSession() as session:
                    data = aiohttp.FormData()
                    data.add_field("reqtype", "fileupload")
                    with open(image_path, "rb") as f:
                        data.add_field("fileToUpload", f, filename=os.path.basename(image_path))
                        async with session.post(
                            "https://catbox.moe/user/api.php",
                            data=data,
                            timeout=aiohttp.ClientTimeout(total=timeout),
                        ) as resp:
                            if resp.status == 200:
                                image_url = (await resp.text()).strip()
                                log.append(f"[HiddenContentTracker][RevImg] Catbox URL: {image_url}")
                            else:
                                log.append(f"[HiddenContentTracker][RevImg] Catbox upload failed: {resp.status}")
            except Exception as e:
                log.append(f"[HiddenContentTracker][RevImg] Catbox error: {e}")

        queries: List[str] = []

        # 2) Footprint queries
        if image_url:
            queries.append(f'"{image_url}"')
            queries.append(f'"{image_url}" (source OR original OR mirror)')
            # (Optional) mild “visual engine pages” hunting; many instances will just be noise:
            queries.append(f'"{image_url}" site:yandex')
            queries.append(f'"{image_url}" site:bing')
            queries.append(f'"{image_url}" site:google')

        if image_path:
            fn = os.path.basename(image_path)
            if fn:
                queries.append(f'"{fn}"')
            stem = os.path.splitext(fn)[0]
            if stem and len(stem) > 4:
                queries.append(f'"{stem}" source')

        if not queries:
            log.append("[HiddenContentTracker][RevImg] No usable seeds after coercion.")
            return []

        seeds: List[str] = []
        seen: Set[str] = set()
        per_query = max(15, limit * 2)

        for q in queries:
            found = await self._search_searxng_json(
                searxng_url,
                q,
                per_query,
                timeout,
                log,
                engines=searxng_engines,
            )
            for u in found:
                u = (u or "").strip()
                # filter common engine noise
                low = u.lower()
                if (
                    not u
                    or u in seen
                    or "google.com/search" in low
                    or "bing.com/images" in low
                    or "yandex" in low and "/images" in low
                ):
                    continue
                seen.add(u)
                seeds.append(u)
                if len(seeds) >= limit:
                    break
            if len(seeds) >= limit:
                break

        log.append(f"[HiddenContentTracker][RevImg] Seeds discovered: {len(seeds)}")
        return seeds[:limit]

    # ------------------------------------------------------------------ #
    # Search methods (you must have at least one)
    # ------------------------------------------------------------------ #
    async def _search_duckduckgo(self, query: str, *, max_results: int, ua: str, timeout: float, page_limit: int, per_page: int) -> List[str]:
        """
        Placeholder: keep whatever you already have in PageTracker.
        If you prefer SearXNG for *normal* search too, just call _search_searxng_json here.
        """
        return []

    # ------------------------------------------------------------------ #
    # Main execution (key changes: reverse_provider removed)
    # ------------------------------------------------------------------ #
    async def _execute_async(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        query_raw = str(params.get("query", "") or str(payload or "")).strip()

        timeout = float(params.get("timeout", 6.0))
        engine = str(params.get("engine", "duckduckgo")).lower()

        # Reverse-image inputs (NEW)
        reverse_image_path = str(params.get("reverse_image_path", "") or "").strip()
        reverse_image_url = str(params.get("reverse_image_url", "") or "").strip()
        reverse_seed_limit = int(params.get("reverse_seed_limit", 20))
        searxng_url = str(params.get("searxng_url", "") or "").strip()  # e.g. "http://127.0.0.1:8080"
        searxng_engines = str(params.get("searxng_engines", "") or "").strip()  # optional, e.g. "duckduckgo,brave"
        catbox_upload = bool(params.get("catbox_upload", True))
        ffmpeg_bin = str(params.get("ffmpeg_bin", "ffmpeg") or "ffmpeg")

        # Crawl controls
        max_pages_total = int(params.get("max_pages_total", 32))
        max_depth = max(0, int(params.get("max_depth", 0)))
        min_term_overlap = max(1, int(params.get("min_term_overlap", 1)))
        required_sites = [s.strip().lower() for s in str(params.get("site_require", "")).split(",") if s.strip()]

        # sniffers
        use_js = bool(params.get("use_js", False))
        use_network_sniff = bool(params.get("use_network_sniff", False))
        use_runtime_sniff = bool(params.get("use_runtime_sniff", False))
        use_react_sniff = bool(params.get("use_react_sniff", False))
        use_database_sniff = bool(params.get("use_database_sniff", False))
        use_interaction_sniff = bool(params.get("use_interaction_sniff", False))
        return_debug = bool(params.get("return_debug", False))

        # archive
        enable_wayback = bool(params.get("enable_wayback", True))
        wayback_limit = int(params.get("wayback_limit", 30))

        # Keyword extraction
        keywords: List[str] = [w.strip().lower() for w in query_raw.split() if w.strip()]
        keywords.extend([w.strip().lower() for w in str(params.get("url_keywords", "")).split(",") if w.strip()])
        keywords = list(dict.fromkeys([k for k in keywords if k]))

        def _clean_domain(u: str) -> str:
            try:
                return urlparse(u).netloc.lower().split(":")[0]
            except Exception:
                return ""

        def _allowed_by_required_sites(u: str) -> bool:
            if not required_sites:
                return True
            d = _clean_domain(u)
            return any(req in d for req in required_sites)

        def _term_overlap_ok(haystack: str) -> bool:
            if not keywords:
                return True
            h = haystack.lower()
            hits = 0
            for k in keywords:
                if k and k in h:
                    hits += 1
                    if hits >= min_term_overlap:
                        return True
            return False

        def _score(u: str, title: str) -> int:
            s = 0
            low = (u or "").lower()
            for tok, w in [
                ("/watch", 3), ("/view", 3), ("/post", 3), ("/thread", 3),
                ("/gallery", 3), ("/image", 2), ("/video", 2),
                ("/download", 4), (".m3u8", 6), (".mpd", 6),
            ]:
                if tok in low:
                    s += w
            s += sum(2 for k in keywords if k and k in low)
            tl = (title or "").lower()
            s += sum(2 for k in keywords if k and k in tl)
            return s

        log: List[str] = []
        candidate_pages: List[str] = []

        # --- Reverse-image seed discovery (NO reverse_provider, NO keys) ---
        temp_files: List[str] = []
        if reverse_image_path or reverse_image_url:
            coerced_url, coerced_path, temp_files = await self._coerce_reverse_image_inputs(
                image_url=reverse_image_url,
                image_path=reverse_image_path,
                timeout=timeout,
                log=log,
                ffmpeg_bin=ffmpeg_bin,
            )

            if coerced_path:
                sha = self._sha256_file(coerced_path)
                ph = self._phash(coerced_path)
                log.append(f"[HiddenContentTracker] reverse_image sha256={sha[:16]}… phash={ph or 'n/a'}")

            # Only run SearXNG reverse seeds if we have searxng_url
            if searxng_url:
                seeds = await self._reverse_image_search_seeds(
                    image_url=coerced_url,
                    image_path=coerced_path,
                    limit=reverse_seed_limit,
                    timeout=timeout,
                    log=log,
                    searxng_url=searxng_url,
                    searxng_engines=searxng_engines,
                    catbox_upload=catbox_upload,
                )
                for u in seeds:
                    if u and _allowed_by_required_sites(u):
                        candidate_pages.append(u)
            else:
                log.append("[HiddenContentTracker] reverse inputs provided but searxng_url is blank; skipping reverse seed search.")

        # --- Normal query search (keep your existing behavior) ---
        if query_raw:
            if engine == "searxng":
                if not searxng_url:
                    log.append("[HiddenContentTracker] engine=searxng but searxng_url is blank.")
                    urls = []
                else:
                    urls = await self._search_searxng_json(
                        searxng_url,
                        query_raw,
                        limit=max(20, int(params.get("search_per_page", 50))),
                        timeout=timeout,
                        log=log,
                        engines=searxng_engines,
                    )
            else:
                # duckduckgo / etc via your PageTracker methods
                try:
                    urls = await self._search_duckduckgo(
                        query_raw,
                        max_results=256,
                        ua="PromptChat/HiddenContentTracker",
                        timeout=timeout,
                        page_limit=int(params.get("search_page_limit", 1)),
                        per_page=int(params.get("search_per_page", 50)),
                    )
                except Exception as e:
                    log.append(f"[HiddenContentTracker] search error: {e}")
                    urls = []

            for u in urls:
                if u and _allowed_by_required_sites(u):
                    candidate_pages.append(u)

        candidate_pages = list(dict.fromkeys(candidate_pages))[:max_pages_total]

        # ---------------- Playwright shared context ----------------
        pw_needed = (
            use_js or use_network_sniff or use_runtime_sniff or use_react_sniff or
            use_database_sniff or use_interaction_sniff
        )

        pw_p = pw_browser = pw_context = None
        if pw_needed:
            ua_pw = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/HiddenContentTracker"
            pw_p, pw_browser, pw_context = await self._open_playwright_context(
                ua=ua_pw,
                block_resources=bool(params.get("block_resources", False)),
                blocked_resource_types={t.strip().lower() for t in str(params.get("blocked_resource_types", "image,stylesheet,font")).split(",") if t.strip()},
                block_domains=bool(params.get("block_domains", True)),
                blocked_domains={d.strip().lower() for d in str(params.get("blocked_domains", "")).split(",") if d.strip()},
                log=log,
                use_camoufox=bool(params.get("use_camoufox", False)),
                camoufox_options=(params.get("camoufox_options") or {}),
            )

        # ---------------- Crawl ----------------
        found_pages: List[Dict[str, Any]] = []
        visited: Set[str] = set()

        all_debug = {
            "js_links": [],
            "network_links": [],
            "runtime_hits": [],
            "react_hits": [],
            "database_hits": [],
            "interaction_hits": [],
        }

        ua_http = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/HiddenContentTracker"
        async with submanagers.HTTPSSubmanager(user_agent=ua_http, timeout=timeout, retries=2, max_conn_per_host=8) as http:

            async def _process_page(page_url: str, depth: int) -> Tuple[List[Dict[str, Any]], List[str]]:
                local_pages: List[Dict[str, Any]] = []
                next_pages: List[str] = []
                html = ""

                # sniffers
                if pw_context and use_network_sniff:
                    try:
                        sniff_result = await self.network_sniffer.sniff(pw_context, page_url, timeout=timeout, log=log, extensions=None)
                        if isinstance(sniff_result, tuple) and sniff_result:
                            html = sniff_result[0] or html
                            items = sniff_result[1] if len(sniff_result) > 1 else []
                        else:
                            items = []
                        for it in items:
                            u = it.get("url") or ""
                            if u and _allowed_by_required_sites(u):
                                all_debug["network_links"].append({"page": page_url, **it})
                                if depth < max_depth and (not any(urlparse(u).path.lower().endswith(ext) for ext in self.IGNORED_EXTENSIONS)):
                                    next_pages.append(u)
                    except Exception as e:
                        log.append(f"[HiddenContentTracker][Network] {page_url}: {e}")

                if pw_context and use_runtime_sniff:
                    try:
                        rt_html, rt_hits = await self.runtime_sniffer.sniff(pw_context, page_url, timeout=timeout, log=log)
                        if rt_html and not html:
                            html = rt_html
                        for h in (rt_hits or []):
                            all_debug["runtime_hits"].append(h)
                            u = (h.get("url") or "").strip()
                            if depth < max_depth and u and _allowed_by_required_sites(u):
                                next_pages.append(u)
                    except Exception as e:
                        log.append(f"[HiddenContentTracker][Runtime] {page_url}: {e}")

                if pw_context and use_react_sniff:
                    try:
                        r_html, r_hits = await self.react_sniffer.sniff(pw_context, page_url, timeout=timeout, log=log)
                        if r_html and not html:
                            html = r_html
                        for h in (r_hits or []):
                            all_debug["react_hits"].append(h)
                            u = (h.get("url") or "").strip()
                            if depth < max_depth and u and _allowed_by_required_sites(u):
                                next_pages.append(u)
                    except Exception as e:
                        log.append(f"[HiddenContentTracker][React] {page_url}: {e}")

                if pw_context and use_database_sniff:
                    try:
                        d_html, d_hits = await self.database_sniffer.sniff(pw_context, page_url, timeout=timeout, log=log)
                        if d_html and not html:
                            html = d_html
                        for h in (d_hits or []):
                            all_debug["database_hits"].append(h)
                            u = (h.get("url") or "").strip()
                            if depth < max_depth and u and _allowed_by_required_sites(u):
                                next_pages.append(u)
                    except Exception as e:
                        log.append(f"[HiddenContentTracker][DB] {page_url}: {e}")

                if pw_context and use_interaction_sniff:
                    try:
                        i_html, i_hits = await self.interaction_sniffer.sniff(pw_context, page_url, timeout=timeout, log=log)
                        if i_html and not html:
                            html = i_html
                        for h in (i_hits or []):
                            all_debug["interaction_hits"].append(h)
                    except Exception as e:
                        log.append(f"[HiddenContentTracker][Interaction] {page_url}: {e}")

                if pw_context and use_js:
                    try:
                        js_html, js_links = await self.js_sniffer.sniff(pw_context, page_url, timeout=timeout, log=log, extensions=None)
                        if js_html:
                            html = js_html
                        for jl in (js_links or []):
                            all_debug["js_links"].append({"page": page_url, **jl})
                            u = jl.get("url") or ""
                            if depth < max_depth and u and _allowed_by_required_sites(u):
                                next_pages.append(u)
                    except Exception as e:
                        log.append(f"[HiddenContentTracker][JS] {page_url}: {e}")

                # fallback HTTP
                if not html:
                    try:
                        html = await http.get_text(page_url)
                    except Exception as e:
                        log.append(f"[HiddenContentTracker][HTTP] {page_url}: {e}")
                        html = ""

                soup = BeautifulSoup(html or "", "html.parser")

                title = ""
                try:
                    if soup.title and soup.title.string:
                        title = soup.title.string.strip()
                except Exception:
                    title = ""

                hay = f"{title} {page_url}"
                if _allowed_by_required_sites(page_url) and (not keywords or _term_overlap_ok(hay)):
                    local_pages.append({"title": (title or "[no title]")[:200], "url": page_url, "source": None, "depth": depth, "score": _score(page_url, title)})

                for a in soup.select("a[href]"):
                    href = a.get("href")
                    if not href:
                        continue
                    u = urljoin(page_url, href)
                    p = urlparse(u).path.lower()
                    if any(p.endswith(ext) for ext in self.IGNORED_EXTENSIONS):
                        continue
                    if not _allowed_by_required_sites(u):
                        continue
                    txt = a.get_text(strip=True) or ""
                    if keywords and not _term_overlap_ok(f"{txt} {u}"):
                        continue
                    local_pages.append({"title": (txt or "[no title]")[:200], "url": u, "source": page_url, "depth": depth + 1, "score": _score(u, txt)})
                    if depth < max_depth:
                        next_pages.append(u)

                if enable_wayback:
                    try:
                        snaps = await self._wayback_cdx(http, page_url, timeout=timeout, limit=wayback_limit)
                        for s in snaps:
                            if _allowed_by_required_sites(s):
                                local_pages.append({"title": "[Wayback snapshot]", "url": s, "source": page_url, "depth": depth + 1, "score": _score(s, "[wayback]") + 3})
                    except Exception:
                        pass

                return local_pages, list(dict.fromkeys(next_pages))

            # BFS
            frontier = candidate_pages[:]
            depth = 0
            while frontier and depth <= max_depth and len(visited) < max_pages_total:
                batch = []
                for u in frontier:
                    if u in visited:
                        continue
                    visited.add(u)
                    batch.append(u)
                    if len(batch) >= max_pages_total:
                        break

                results = await asyncio.gather(*[_process_page(u, depth) for u in batch], return_exceptions=True)

                next_candidates: List[str] = []
                for r in results:
                    if isinstance(r, Exception):
                        log.append(f"[HiddenContentTracker] page task exception: {r}")
                        continue
                    pages, nxt = r
                    found_pages.extend(pages)
                    next_candidates.extend(nxt)

                frontier = []
                seen_next = set()
                for u in next_candidates:
                    if u not in visited and u not in seen_next:
                        seen_next.add(u)
                        frontier.append(u)
                frontier = frontier[:max_pages_total]
                depth += 1

        if pw_needed:
            await self._close_playwright_context(pw_p, pw_browser, pw_context, log)

        # cleanup temp files from coercion
        for p in temp_files:
            try:
                if p and os.path.exists(p):
                    os.remove(p)
            except Exception:
                pass

        # final dedupe
        final: Dict[str, Dict[str, Any]] = {}
        for p in found_pages:
            u = p.get("url")
            if not u:
                continue
            if u not in final or p.get("score", 0) > final[u].get("score", 0):
                final[u] = p

        final_list = sorted(final.values(), key=lambda x: x.get("score", 0), reverse=True)[:500]

        lines = [f"### HiddenContentTracker Found {len(final_list)} Pages"]
        lines.append(f"_Query: {query_raw or '[none]'} | reverse_image: {bool(reverse_image_path or reverse_image_url)} | engine: {engine} | depth: {max_depth}_\n")
        for p in final_list[:100]:
            title = p.get("title") or "[no title]"
            url = p.get("url")
            host = urlparse(url).netloc
            lines.append(f"- **[{title}]({url})**")
            lines.append(f"  - *Host: {host} | Score: {p.get('score', 0)} | Depth: {p.get('depth', 0)}*")

        result = {
            "found": len(final_list),
            "pages": final_list,
            "visited": len(visited),
            "keywords_used": keywords,
            "required_sites": required_sites,
            "reverse_image_used": bool(reverse_image_path or reverse_image_url),
            "log": log,
        }
        if return_debug:
            result.update(all_debug)

        return "\n".join(lines), result

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        return asyncio.run(self._execute_async(payload, params=params))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "example query",
            "timeout": 6.0,

            # search engine: "duckduckgo" (your old) or "searxng"
            "engine": "searxng",
            "searxng_url": "http://127.0.0.1:8080",
            "searxng_engines": "",  # optional: "duckduckgo,brave,bing"

            "search_page_limit": 1,
            "search_per_page": 50,

            "site_require": "",
            "max_pages_total": 32,
            "max_depth": 1,
            "min_term_overlap": 1,
            "url_keywords": "",

            # sniffers
            "use_js": False,
            "use_network_sniff": True,
            "use_runtime_sniff": True,
            "use_react_sniff": False,
            "use_database_sniff": False,
            "use_interaction_sniff": False,

            # archive boost
            "enable_wayback": True,
            "wayback_limit": 30,

            # reverse image (NO reverse_provider)
            "reverse_image_path": "",
            "reverse_image_url": "",
            "reverse_seed_limit": 20,
            "catbox_upload": True,      # set False if you do NOT want any upload
            "ffmpeg_bin": "ffmpeg",

            # Playwright settings
            "use_camoufox": False,
            "camoufox_options": {},
            "block_resources": False,
            "blocked_resource_types": "image,stylesheet,font",
            "block_domains": True,
            "blocked_domains": "",

            # db (optional)
            "use_database": False,
            "db_path": "link_corpus.db",

            "return_debug": False,
        }

BLOCKS.register("hiddencontenttracker", HiddenContentTrackerBlock)