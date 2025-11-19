# ========================================================
# ================  blocks.py  ===========================
# ========================================================
from __future__ import annotations

import ast
import functools
import html
import json
import math
import os
import re
import sqlite3
import sys
from collections import defaultdict
from dataclasses import dataclass
from typing import Any, Dict, Tuple, List, Optional, Set
import json as _json
import os as _os
import time
from urllib.parse import urlencode, urlparse, urljoin
import feedparser
import numpy as np
import requests
from playwright.sync_api import BrowserContext
from registry import BLOCKS
from models import get_chat_model  # <-- models now live separately
import xml.etree.ElementTree as ET
import re as _re
from dotenv import load_dotenv

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
            parent_params: Dict[str, Any]
    ) -> Any:
        """
        Runs a mini-pipeline of sub-blocks on a value.

        Args:
            initial_value: The starting value (e.g., a query string).
            pipeline_param_name: The key in 'parent_params' that holds the list/string of
                                 sub-blocks (e.g., "subpipeline").
            parent_params: The main block's 'params' dict.

        Returns:
            The final, processed value from the last sub-block.
        """
        from registry import SUB_BLOCKS
        import subblocks

        pipeline_def = parent_params.get(pipeline_param_name, None)

        if pipeline_def is None:
            return initial_value

        if isinstance(pipeline_def, str):
            sub_block_names = [s.strip() for s in pipeline_def.split("|") if s.strip()]
        elif isinstance(pipeline_def, list):
            sub_block_names = [str(s) for s in pipeline_def]
        else:
            sub_block_names = []

        if not sub_block_names:
            return initial_value

        current_value = initial_value

        for sub_block_name in sub_block_names:
            try:
                sub_params = {}
                prefix = f"{sub_block_name}."
                for k, v in parent_params.items():
                    if k.startswith(prefix):
                        sub_params[k[len(prefix):]] = v

                sub_block_inst = SUB_BLOCKS.create(sub_block_name)
                current_value = sub_block_inst.execute(current_value, params=sub_params)

            except Exception as e:
                print(f"[BaseBlock] Sub-pipeline failed at '{sub_block_name}': {e}", file=sys.stderr)
                # Stop the sub-pipeline, but keep the last good value
                return current_value

        return current_value


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


# ---------------- Prompt Builder (Smart & Dissecting) ----------------
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


# ---------------- Corpus (HF with timeout + wiki_api fallback) ----------------
@dataclass
class CorpusBlock(BaseBlock):
    """
    Resilient corpus puller:
      • provider = "wikimedia/wikipedia" (default) with short startup timeout
      • automatic fallback to provider = "wiki_api" (direct Wikipedia REST) on timeout/failure
      • [NEW] Caches results in a local SQLite FTS (Full-Text Search) database.
      • [NEW] Queries FTS database first, falling back to HF/API.
      • BM25-ish re-ranking, sentence extraction, auto-lexicon
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os, re, json, time, threading
        import sqlite3  # [NEW]
        from math import log
        from typing import Iterable, Dict, List
        from itertools import islice

        # ---- Params ----
        provider = str(params.get("provider", "wikimedia/wikipedia"))
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

        # [NEW] DB Params
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

        # ---- [NEW] DB Helpers (with FTS5) ----
        def _get_db_conn():
            conn = sqlite3.connect(db_path)
            # Main table for doc storage
            conn.execute("""
            CREATE TABLE IF NOT EXISTS corpus_docs (
                id INTEGER PRIMARY KEY,
                title TEXT NOT NULL,
                content TEXT NOT NULL,
                config TEXT NOT NULL, -- '20231101.en', 'wiki_api', etc.
                fetched_at DATETIME DEFAULT CURRENT_TIMESTAMP,
                UNIQUE(title, config)
            );
            """)
            # FTS table to search
            conn.execute("""
            CREATE VIRTUAL TABLE IF NOT EXISTS corpus_fts USING fts5(
                content='corpus_docs', -- Link to the table
                content_rowid='id',    -- Link to its rowid
                tokenize='porter unicode61',
                -- Columns to index
                title,
                content
            );
            """)
            # Triggers to keep them in sync
            conn.executescript("""
            CREATE TRIGGER IF NOT EXISTS corpus_docs_ai AFTER INSERT ON corpus_docs BEGIN
              INSERT INTO corpus_fts(rowid, title, content) VALUES (new.id, new.title, new.content);
            END;
            CREATE TRIGGER IF NOT EXISTS corpus_docs_ad AFTER DELETE ON corpus_docs BEGIN
              INSERT INTO corpus_fts(corpus_fts, rowid, title, content) VALUES ('delete', old.id, old.title, old.content);
            END;
            CREATE TRIGGER IF NOT EXISTS corpus_docs_au AFTER UPDATE ON corpus_docs BEGIN
              INSERT INTO corpus_fts(corpus_fts, rowid, title, content) VALUES ('delete', old.id, old.title, old.content);
              INSERT INTO corpus_fts(rowid, title, content) VALUES (new.id, new.title, new.content);
            END;
            """)
            return conn

        def _save_many_to_db(docs: List[Dict[str, str]], config_key: str):
            if not use_db_cache or not docs: return
            try:
                with _get_db_conn() as conn:
                    conn.executemany(
                        "INSERT OR IGNORE INTO corpus_docs (title, content, config) VALUES (?, ?, ?)",
                        [(d['title'], d['text'], config_key) for d in docs]
                    )
            except Exception as e:
                print(f"[CorpusBlock] DB bulk save failed: {e}")

        def _load_from_db(query: str, config_key: str) -> List[Dict[str, str]]:
            if not use_db_cache or not query: return []

            # Sanitize query for FTS
            fts_query = " ".join(re.findall(r'[a-zA-Z0-9]+', query))
            if not fts_query: return []

            docs = []
            try:
                with _get_db_conn() as conn:
                    # FTS query to get relevant rowids, matching *either* the specified config
                    # or the 'wiki_api' fallback config.
                    sql = """
                    SELECT T.title, T.content 
                    FROM corpus_docs AS T
                    JOIN corpus_fts AS F ON T.id = F.rowid
                    WHERE F.corpus_fts MATCH ? 
                      AND (T.config = ? OR T.config = 'wiki_api')
                    ORDER BY F.rank -- FTS rank
                    LIMIT ?;
                    """
                    # Fetch a larger candidate pool from DB to feed into BM25
                    fetch_limit = max(sample * 5, 50)

                    cursor = conn.execute(sql, (fts_query, config_key, fetch_limit))
                    for row in cursor.fetchall():
                        docs.append({"title": row[0], "text": row[1]})
                return docs
            except Exception as e:
                print(f"[CorpusBlock] DB load failed: {e}")
                return []

        # ---- Standard Helpers ----
        def _normalize(v) -> str:
            if v is None: return ""
            if isinstance(v, str): return v
            if isinstance(v, list): return " ".join(_normalize(x) for x in v)
            if isinstance(v, dict): return " ".join(_normalize(x) for x in v.values())
            return str(v)

        def _tokenize(t: str) -> List[str]:
            return re.findall(r"[A-Za-z0-9][A-Za-z0-9_\-]+", t.lower())

        def _contains_whole_word(t: str, q: str) -> bool:
            return re.search(rf"\b{re.escape(q)}\b", t, flags=re.IGNORECASE) is not None

        q_pattern = re.compile(regex_query, re.IGNORECASE) if isinstance(regex_query,
                                                                         str) and regex_query.strip() else None

        def _matches(title: str, text: str) -> bool:
            hay = title if title_only else (title + "\n" + text)
            if len(hay) < min_doc_chars: return False
            # positive
            if q_pattern:
                if not q_pattern.search(hay): return False
            elif query:
                if whole_word:
                    if not _contains_whole_word(hay, query): return False
                else:
                    if query.lower() not in hay.lower(): return False
            # must terms
            for m in must_terms:
                if m and (m not in hay.lower()): return False
            # negatives
            for n in neg:
                if re.search(rf"\b{re.escape(n)}\b", hay, flags=re.IGNORECASE):
                    return False
            return True

        def _split_sents(text: str) -> List[str]:
            bits = re.split(r"(?<=[.!?])\s+|\n+", text.strip())
            return [b.strip() for b in bits if b.strip()]

        # ---- wiki_api provider (no HF, zero “Resolving data files”) ----
        def _fetch_wiki_api_pages(topic: str) -> List[Dict[str, str]]:
            # ... (function unchanged) ...
            import requests
            session = requests.Session()
            session.headers.update({"User-Agent": "promptchat/mini-crawler"})
            titles: List[str] = []

            # Seed titles from the topic if it looks like a name; otherwise use search
            if re.search(r"raf\s+simons", topic, re.I):
                titles = ["Raf_Simons", "Raf_Simons_(brand)", "Prada", "Jil_Sander", "Calvin_Klein", "Dior"]
            elif re.search(r"transport\s+layer\s+security|tls", topic, re.I):
                titles = ["Transport_Layer_Security", "TLS_1.3", "HTTPS", "X.509", "Public_key_certificate",
                          "Forward_secrecy"]
            else:
                # fallback: try a top-5 search
                try:
                    r = session.get("https://en.wikipedia.org/w/api.php", params={
                        "action": "opensearch", "search": topic, "limit": 5, "namespace": 0, "format": "json"
                    }, timeout=8)
                    r.raise_for_status()
                    data = r.json()
                    titles = [re.sub(r"^.*/wiki/", "", u) for u in data[3]]
                    if not titles:
                        titles = [topic.replace(" ", "_")]
                except Exception:
                    titles = [topic.replace(" ", "_")]

            docs: List[Dict[str, str]] = []
            for t in titles:
                try:
                    r = session.get(f"https://en.wikipedia.org/api/rest_v1/page/plain/{t}", timeout=8)
                    if r.status_code != 200:
                        continue
                    text = r.text
                    title = t.replace("_", " ")
                    if _matches(title, text):
                        docs.append({"title": title, "text": text})
                except Exception:
                    continue
                if len(docs) >= max(1, sample):
                    break
            return docs

        # ---- HF provider with startup timeout, then fallback to wiki_api ----
        def _load_hf_docs() -> List[Dict[str, str]]:
            # ... (function unchanged) ...
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
                        # Python-side filter (avoid heavy .filter planning)
                        keep: List[Dict[str, str]] = []
                        # take up to scan_limit rows to keep snappy
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
        db_config_key = config  # This is the config we'll use for DB query/save

        # [NEW] Try DB first
        if use_db_cache:
            docs_raw = _load_from_db(query, db_config_key)
            if docs_raw:
                meta["db_source"] = "fts_cache"

        # [NEW] If DB cache failed or was empty, go to source
        if not docs_raw:
            meta["db_source"] = "fetch"
            if provider == "wiki_api":
                docs_raw = _fetch_wiki_api_pages(query or "Raf Simons")
                db_config_key = "wiki_api"  # Set config key for saving
            else:
                try:
                    docs_raw = _load_hf_docs()
                    if not docs_raw:
                        # timeout / empty → fallback
                        used_provider = "wiki_api"
                        db_config_key = "wiki_api"
                        docs_raw = _fetch_wiki_api_pages(query or "Raf Simons")
                except Exception:
                    used_provider = "wiki_api"
                    db_config_key = "wiki_api"
                    docs_raw = _fetch_wiki_api_pages(query or "Raf Simons")

            # [NEW] Save freshly fetched docs to DB
            _save_many_to_db(docs_raw, db_config_key)

        # ---- no docs? return early (but with metadata explaining why) ----
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
                "scan_limit": scan_limit
            })
            return base, meta

        # ---- ranking (BM25-ish + regex boost) ----
        # This now ranks the candidates from *either* the DB or the fresh fetch
        corpus_tokens = [set(_tokenize((d["title"] + " " + d["text"]).lower())) for d in docs_raw]
        N = len(corpus_tokens)
        q_terms = set(_tokenize(query)) if query else set()
        df: Dict[str, int] = {}
        for terms in corpus_tokens:
            for t in terms:
                df[t] = df.get(t, 0) + 1

        def _bm25ish_score(doc_text: str) -> float:
            words = _tokenize(doc_text);
            L = len(words) or 1
            score = 0.0
            if q_terms:
                for t in q_terms:
                    tf = words.count(t)
                    if tf == 0: continue
                    idf = log((N - df.get(t, 0) + 0.5) / (df.get(t, 0) + 0.5) + 1.0)
                    k1, b, avgdl = 1.2, 0.75, 2000.0
                    score += idf * ((tf * (k1 + 1)) / (tf + k1 * (1 - b + b * (L / avgdl))))
            if q_pattern and q_pattern.search(doc_text):
                score += 2.0
            return score

        ranked = sorted(docs_raw, key=lambda d: _bm25ish_score(d["title"] + " " + d["text"]), reverse=True)[
                 :max(1, top_k_docs)]

        # ---- sentence extraction ----
        # ... (function unchanged) ...
        hit_sents: List[str] = []
        per_doc_quota = max(1, top_k_sents // max(1, len(ranked)))
        for d in ranked:
            title = (d["title"] or "").strip()
            sents = _split_sents(d["text"] or "")
            scored: List[Tuple[float, int, str]] = []
            for idx, s in enumerate(sents):
                tok = set(_tokenize(s))
                overlap = len(tok & q_terms) if q_terms else 0
                if q_pattern and q_pattern.search(s): overlap += 2
                if query and whole_word and _contains_whole_word(s, query): overlap += 1
                if overlap > 0: scored.append((float(overlap), idx, s))
            took = 0
            for _, idx, _ in sorted(scored, key=lambda x: (-x[0], x[1]))[:per_doc_quota]:
                lo = max(0, idx - sent_window);
                hi = min(len(sents), idx + sent_window + 1)
                chunk = " ".join(sents[lo:hi]).strip()
                if chunk and chunk not in hit_sents:
                    if title and (not hit_sents or not hit_sents[-1].startswith("# ")):
                        hit_sents.append(f"# {title}")
                    hit_sents.append(chunk);
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
        # ... (function unchanged) ...
        def _extract_terms_local(text: str, *, top_k: int = 50, min_len: int = 4) -> List[str]:
            counts: Dict[str, int] = {}
            for raw in text.split():
                w = "".join(ch.lower() for ch in raw if ch.isalnum() or ch in "-_")
                if len(w) < min_len or w in _STOPWORDS: continue
                counts[w] = counts.get(w, 0) + 1
            return [t for t, _ in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:top_k]]

        lexicon = _extract_terms_local(context, top_k=lexicon_top_k, min_len=lexicon_min_len) if context else []
        if use_phrases and context:
            phrase_candidates = re.findall(r"\b([A-Za-z0-9][A-Za-z0-9_\-]+(?:\s+[A-Za-z0-9][A-Za-z0-9_\-]+){1,3})\b",
                                           context)
            phrase_counts: Dict[str, int] = {}
            for ph in phrase_candidates:
                ph = ph.lower().strip()
                if any(tok in _STOPWORDS for tok in ph.split()): continue
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
            "db_path": db_path if use_db_cache else None,  # [NEW]
        })
        return out, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "provider": "wikimedia/wikipedia",
            "config": "20231101.en",
            "split": "train",
            "query": "",
            "neg": "",
            "must_terms": "",
            "sample": 50,
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
            "export_lexicon": True,
            "lexicon_key": "corpus_lexicon",
            "inject_lexicon": True,
            "inject_context": True,
            "db_path": "corpus_cache.db",  # [NEW]
            "use_db_cache": True,  # [NEW]
        }


# keep registration
BLOCKS.register("corpus", CorpusBlock)


# ---------------- Chat (no personas/prompts; uses lexicon only) ----------------
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

        # --- [NEW] Apply sub-pipeline to core text ---
        # This allows you to run english_chat.op=fix_grammar, etc.
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


# ---------------- WebCorpus (web search + fetch + summarize) ----------------
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
      • [NEW] Caches and retrieves results from a persistent SQLite DB.
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os, re, time, hashlib, json
        import sqlite3  # [NEW] Import SQLite
        from math import log
        from typing import List, Dict, Tuple
        from urllib.parse import urlparse

        # ---- Params ----
        query_raw = str(params.get("query", "") or str(payload or "")).strip()
        engine = str(params.get("engine", "duckduckgo")).lower()  # duckduckgo | serpapi | google_cse
        num_results = int(params.get("num_results", 10))
        max_fetch = int(params.get("max_fetch", 8))  # how many pages to actually fetch
        timeout_sec = float(params.get("timeout", 8.0))
        read_timeout = float(params.get("read_timeout", 12.0))
        user_agent = str(params.get("user_agent", "promptchat/webcorpus"))
        pause = float(params.get("pause", 0.7))  # polite delay between fetches
        cache_dir = str(params.get("cache_dir", os.path.join(APP_DIR, "webcache")))
        os.makedirs(cache_dir, exist_ok=True)

        # [NEW] DB Params
        db_path = str(params.get("db_path", os.path.join(APP_DIR, "webcorpus.db")))
        use_db_cache = bool(params.get("use_db_cache", True))

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

        # compile regex
        q_pattern = re.compile(regex_query, re.IGNORECASE) if isinstance(regex_query,
                                                                         str) and regex_query.strip() else None

        # ---- Build list of queries to run (subpipeline OR raw) ----
        queries_to_run: Any

        if "subpipeline" in params and str(params["subpipeline"]).strip():
            # Use the configured subpipeline
            queries_to_run = self.run_sub_pipeline(
                initial_value=query_raw,
                pipeline_param_name="subpipeline",
                parent_params=params,
            )
        else:
            # No subpipeline configured: just use the raw query.
            queries_to_run = [query_raw] if query_raw else []

        # Normalize result from subpipeline
        if isinstance(queries_to_run, str):
            queries_to_run = [queries_to_run]
        elif not isinstance(queries_to_run, list):
            queries_to_run = [query_raw] if query_raw else []

        # Strip empties
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

        meta: Dict[str, Any] = {"queries_run": queries_to_run}

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

        # ---- [NEW] DB Helpers ----
        def _get_db_conn():
            conn = sqlite3.connect(db_path)
            conn.execute("""
            CREATE TABLE IF NOT EXISTS corpus (
                url TEXT PRIMARY KEY,
                title TEXT,
                content TEXT,
                fetched_at DATETIME DEFAULT CURRENT_TIMESTAMP
            );
            """)
            return conn

        def _save_to_db(url: str, title: str, content: str):
            if not use_db_cache: return
            try:
                with _get_db_conn() as conn:
                    conn.execute(
                        "INSERT OR REPLACE INTO corpus (url, title, content, fetched_at) VALUES (?, ?, ?, CURRENT_TIMESTAMP)",
                        (url, title, content)
                    )
            except Exception as e:
                print(f"[WebCorpusBlock] DB save failed for {url}: {e}")

        def _load_from_db(url: str) -> Tuple[str, str] | None:
            if not use_db_cache: return None
            try:
                with _get_db_conn() as conn:
                    cursor = conn.execute("SELECT title, content FROM corpus WHERE url = ?", (url,))
                    row = cursor.fetchone()
                    if row:
                        return row[0], row[1]  # title, content
            except Exception as e:
                print(f"[WebCorpusBlock] DB load failed for {url}: {e}")
            return None

        # ---- File Cache (still used by _fetch_html) ----
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

        def _fetch_html(url: str) -> str:
            cached = _load_cache(url)
            if cached:
                return cached
            import requests
            try:
                r = requests.get(url, headers={"User-Agent": user_agent}, timeout=(timeout_sec, read_timeout))
                if r.status_code == 200 and r.text:
                    _save_cache(url, r.text)
                    return r.text
            except Exception:
                return ""
            return ""

        def _extract_text(html: str, url: str) -> str:
            try:
                import trafilatura
                clean_text = trafilatura.extract(
                    html,
                    include_comments=False,
                    include_tables=False,
                    deduplicate=True
                )
                return clean_text or ""
            except ImportError:
                print(
                    "[WebCorpusBlock] ERROR: `trafilatura` not installed. Please `pip install trafilatura`. Falling back to bs4.")
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

            # must terms
            for m in must_terms:
                if m and m not in low:
                    return False

            # neg terms
            for n in neg:
                if n and re.search(rf"\b{re.escape(n)}\b", text, flags=re.IGNORECASE):
                    return False

            # regex
            if q_pattern and not q_pattern.search(text):
                return False

            # token overlap (uses the passed-in query)
            if query and not q_pattern:
                qt = [t for t in _tokenize(query) if t not in _STOPWORDS]
                if qt:
                    overlap = sum(1 for t in qt if t in low)  # This counts *unique* terms found
                    if overlap < min_term_overlap:
                        return False

            return True

        def _matches_any(text: str) -> bool:
            """
            Accept a document if it matches the original query OR any
            of the sub-queries produced by the subpipeline.
            """
            if not queries_to_run:
                return _matches(text, query_raw)
            for q in queries_to_run:
                if q and _matches(text, q):
                    return True
            return False

        # ---- Search backends ----
        def search_duckduckgo(q: str, n: int) -> List[str]:
            # ... (search logic unchanged) ...
            try:
                from ddgs import DDGS  # pip install duckduckgo_search
                with DDGS() as ddgs:
                    out = []
                    for r in ddgs.text(q, max_results=n, safesearch='off'):
                        u = r.get("href") or r.get("url")
                        if u:
                            out.append(u)
                    return out
            except Exception:
                pass

            import requests
            urls = []
            try:
                r = requests.get(
                    "https://duckduckgo.com/html/",
                    params={"q": q},
                    headers={"User-Agent": user_agent},
                    timeout=(timeout_sec, read_timeout)
                )
                if r.status_code == 200:
                    from bs4 import BeautifulSoup
                    soup = BeautifulSoup(r.text, "html.parser")
                    for a in soup.select("a.result__a, a.result__url, a.result__a.js-result-title-link"):
                        href = a.get("href")
                        if href and href.startswith("http"):
                            urls.append(href)
                            if len(urls) >= n:
                                break
            except Exception:
                pass
            return urls

        def search_serpapi(q: str, n: int) -> List[str]:
            # ... (search logic unchanged) ...
            key = os.environ.get("SERPAPI_KEY")
            if not key:
                return []
            import requests
            try:
                r = requests.get(
                    "https://serpapi.com/search",
                    params={"engine": "google", "q": q, "num": n, "api_key": key},
                    timeout=(timeout_sec, read_timeout)
                )
                r.raise_for_status()
                data = r.json()
                out = []
                for item in (data.get("organic_results") or []):
                    u = item.get("link")
                    if u:
                        out.append(u)
                return out[:n]
            except Exception:
                return []

        def search_google_cse(q: str, n: int) -> List[str]:
            # ... (search logic unchanged) ...
            cx = os.environ.get("GOOGLE_CSE_ID")
            key = os.environ.get("GOOGLE_API_KEY")
            if not (cx and key):
                return []
            import requests
            out = []
            try:
                for start in range(1, min(n, 10) + 1, 10):
                    r = requests.get(
                        "https://www.googleapis.com/customsearch/v1",
                        params={"q": q, "cx": cx, "key": key, "num": min(10, n), "start": start},
                        timeout=(timeout_sec, read_timeout)
                    )

                    r.raise_for_status()
                    data = r.json()
                    for item in (data.get("items") or []):
                        u = item.get("link")
                        if u:
                            out.append(u)
                    if len(out) >= n:
                        break
            except Exception:
                return out[:n]
            return out[:n]

        # ---- Run searches for each query ----
        all_urls: List[str] = []
        for q in queries_to_run:
            if not q:
                continue
            if engine == "serpapi":
                urls = search_serpapi(q, num_results)
            elif engine == "google_cse":
                urls = search_google_cse(q, num_results)
            else:
                urls = search_duckduckgo(q, num_results)
            all_urls.extend(urls)

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

        # ---- Fetch pages ----
        docs_raw: List[Dict[str, str]] = []
        for u in urls:
            # [NEW] Check DB first
            if use_db_cache:
                db_entry = _load_from_db(u)
                if db_entry:
                    db_title, db_text = db_entry
                    if _matches_any(db_text):  # Check relevance of cached text
                        docs_raw.append({"title": db_title, "text": db_text, "url": u})
                    continue  # Got it from DB (relevant or not), so skip fetch

            # Not in DB, so fetch
            html = _fetch_html(u)  # _fetch_html still uses file cache
            if not html:
                continue
            text = _extract_text(html, u)

            # Check relevance
            if not _matches_any(text):
                continue

            # Guess title
            title_guess = _clean_domain(u)
            try:
                from bs4 import BeautifulSoup
                soup = BeautifulSoup(html, "html.parser")
                t = (soup.title.string or "").strip() if soup.title else ""
                if t:
                    title_guess = t
            except Exception:
                pass

            # [NEW] Save to DB
            _save_to_db(u, title_guess, text)

            docs_raw.append({"title": title_guess, "text": text, "url": u})
            time.sleep(pause)

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
            })
            return base, meta

        # ---- ranking BM25-ish (+ regex boost) ----
        # ... (ranking logic unchanged) ...
        corpus_tokens = [set(_tokenize(d["title"] + " " + d["text"])) for d in docs_raw]
        N = len(corpus_tokens)

        # Rank relevance based on *original* query
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
            reverse=True
        )[:max(1, top_k_docs)]

        # ---- sentence extraction ----
        # ... (sentence extraction logic unchanged) ...
        hit_sents: List[str] = []
        per_doc_quota = max(1, top_k_sents // max(1, len(ranked)))
        for d in ranked:
            title = (d["title"] or "").strip()
            sents = _split_sents(d["text"] or "")
            scored: List[Tuple[float, int, str]] = []
            for idx, s in enumerate(sents):
                tok = set(_tokenize(s))
                # Use original query terms for overlap
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
        # ... (lexicon logic unchanged) ...
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
                context
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
        # ... (memory store logic unchanged) ...
        export_context = bool(params.get("export_context", True))
        context_key = str(params.get("context_key", "web_context"))
        append_ctx = bool(params.get("append_context", False))

        if export_lexicon and lexicon:
            store = Memory.load()
            store[lexicon_key] = lexicon
            Memory.save(store)

        if export_context and context:
            store = Memory.load()
            if append_ctx and isinstance(store.get(context_key), str) and store[context_key]:
                store[context_key] = store[context_key].rstrip() + "\n\n" + context
            else:
                store[context_key] = context
            Memory.save(store)

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
            "db_path": db_path if use_db_cache else None,  # [NEW]
        })
        return out, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "",
            "subpipeline": "",  # Default: no subpipeline
            "prompt_query.op": "clean_permutate",  # Config for sub-block
            "engine": "duckduckgo, google_cse",
            "num_results": 10,
            "max_fetch": 8,
            "timeout": 8.0,
            "pause": 0.7,
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
            "db_path": "webcorpus.db",  # [NEW]
            "use_db_cache": True,  # [NEW]
        }


BLOCKS.register("webcorpus", WebCorpusBlock)


# ---------------- WebCorpus (Playwright Hybrid) ----------------
@dataclass
class PlaywrightBlock(BaseBlock):
    """
    Playwright-powered corpus builder (Hybrid v7.2) with optional subpipeline:
      • If `subpipeline` is provided, expand the raw query into multiple
        natural queries (e.g. via PromptQuerySubBlock) and search each.
      • If `subpipeline` is NOT provided, behave like before and use the
        raw query as-is.
      • [NEW] Caches and retrieves results from a persistent SQLite DB.
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os, re, json, time, sys
        import sqlite3  # [NEW] Import SQLite
        from math import log
        from typing import List, Dict, Tuple, Set
        from urllib.parse import urlparse
        from collections import defaultdict

        try:
            from playwright.sync_api import sync_playwright
            import trafilatura
            from ddgs import DDGS
            from bs4 import BeautifulSoup
            import requests
        except ImportError:
            print("[PlaywrightBlock] ERROR: Missing dependencies. Please run:", file=sys.stderr)
            print("pip install playwright trafilatura duckduckgo_search beautifulsoup4 requests", file=sys.stderr)
            print("python -m playwright install --with-deps chromium", file=sys.stderr)
            return str(payload), {"error": "Missing dependencies. See console."}

        # ---- Base raw query ----
        query_raw = str(params.get("query", "") or str(payload or "")).strip()

        # ---- Optional subpipeline expansion ----
        # ... (subpipeline logic unchanged) ...
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

        query = query_raw

        # ---- Params ----
        num_results = int(params.get("num_results", 15))
        headless = bool(params.get("headless", True))
        timeout_sec = float(params.get("timeout", 15.0))
        read_timeout = float(params.get("read_timeout", 12.0))
        user_agent = str(params.get(
            "user_agent",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36"
        ))
        verbose = bool(params.get("verbose", False))

        # [NEW] DB Params
        db_path = str(params.get("db_path", os.path.join(APP_DIR, "webcorpus.db")))
        use_db_cache = bool(params.get("use_db_cache", True))

        # Target & Learning
        default_targets = "grailed.com,hypebeast.com,vogue.com,depop.com,poshmark.com"
        target_sites = str(params.get("target_sites", default_targets))
        num_per_site = int(params.get("num_per_site", 2))
        num_general = int(params.get("num_general", 10))

        learn_new_sites = bool(params.get("learn_new_sites", True))
        learned_sites_key = str(params.get("learned_sites_key", "web_learned_sites"))
        learn_min_hits = int(params.get("learn_min_hits", 2))
        default_junk = "pinterest.com,twitter.com,facebook.com,reddit.com,ebay.com,walmart.com,amazon.com,youtube.com,tiktok.com,instagram.com,linkedin.com"
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
            "db_path": db_path if use_db_cache else None,  # [NEW]
        }

        # compile regex
        q_pattern = re.compile(regex_query, re.IGNORECASE) if isinstance(regex_query,
                                                                         str) and regex_query.strip() else None

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

        # ---- [NEW] DB Helpers ----
        def _get_db_conn():
            conn = sqlite3.connect(db_path)
            conn.execute("""
            CREATE TABLE IF NOT EXISTS corpus (
                url TEXT PRIMARY KEY,
                title TEXT,
                content TEXT,
                fetched_at DATETIME DEFAULT CURRENT_TIMESTAMP
            );
            """)
            return conn

        def _save_to_db(url: str, title: str, content: str):
            if not use_db_cache: return
            try:
                with _get_db_conn() as conn:
                    conn.execute(
                        "INSERT OR REPLACE INTO corpus (url, title, content, fetched_at) VALUES (?, ?, ?, CURRENT_TIMESTAMP)",
                        (url, title, content)
                    )
            except Exception as e:
                print(f"[PlaywrightBlock] DB save failed for {url}: {e}")

        def _load_from_db(url: str) -> Tuple[str, str] | None:
            if not use_db_cache: return None
            try:
                with _get_db_conn() as conn:
                    cursor = conn.execute("SELECT title, content FROM corpus WHERE url = ?", (url,))
                    row = cursor.fetchone()
                    if row:
                        return row[0], row[1]  # title, content
            except Exception as e:
                print(f"[PlaywrightBlock] DB load failed for {url}: {e}")
            return None

        def _hybrid_search(q: str, n: int) -> List[Dict[str, str]]:
            # ... (search logic unchanged) ...
            try:
                if verbose:
                    print(f"[PlaywrightBlock] Searching (via DDGS library) for: {q}", file=sys.stderr)
                with DDGS() as ddgs:
                    out = []
                    for r in ddgs.text(q, max_results=n, safesearch='off'):
                        url = r.get("href") or r.get("url")
                        title = r.get("title") or _clean_domain(url)
                        if url:
                            out.append({"title": title, "url": url})
                if out:
                    meta["search_method"] = "ddgs_library"
                    return out
            except Exception as e:
                if verbose:
                    print(f"[PlaywrightBlock] DDGS library failed: {e}", file=sys.stderr)

            # Fallback
            if verbose:
                print(f"[PlaywrightBlock] Searching (via requests fallback) for: {q}", file=sys.stderr)
            urls = []
            try:
                r = requests.get("https://duckduckgo.com/html/",
                                 params={"q": q},
                                 headers={"User-Agent": user_agent},
                                 timeout=(timeout_sec, read_timeout))
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
                    print(f"[PlaywrightBlock] Requests fallback failed: {e}", file=sys.stderr)

            meta["search_method"] = "failed"
            return []

        docs_raw: List[Dict[str, str]] = []

        if not query:
            base = "" if payload is None else str(payload)
            return base, {"rows": 0, "note": "empty query", "engine": "playwright_hybrid"}

        # --- 1. SEARCH (GENETIC LEARNING) ---
        # ... (search/learning logic unchanged) ...
        search_links: List[Dict[str, str]] = []
        seen_urls: Set[str] = set()
        store = Memory.load()
        sites_to_search: Set[str] = set()
        for s in target_sites.split(","):
            if s.strip():
                sites_to_search.add(s.strip())
        if learn_new_sites:
            learned_sites = store.get(learned_sites_key, [])
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
                print(f"[PlaywrightBlock] Running targeted search on {len(sites_to_search)} known sites...",
                      file=sys.stderr)
            for site in sites_to_search:
                targeted_query = f"{query} site:{site}"
                links = _hybrid_search(targeted_query, n=num_per_site)
                for link in links:
                    url = link["url"]
                    if url not in seen_urls:
                        seen_urls.add(url)
                        search_links.append(link)

            if verbose:
                print(f"[PlaywrightBlock] Running general search for discovery...", file=sys.stderr)
            general_links = _hybrid_search(query, n=num_general)
            new_domain_counts: Dict[str, int] = defaultdict(int)
            discovered_links: List[Dict[str, str]] = []
            for link in general_links:
                url = link["url"]
                if url in seen_urls: continue
                domain = _clean_domain(url)
                if not domain: continue
                if any(domain == s or domain.endswith("." + s) for s in junk_list): continue
                if any(domain == s or domain.endswith("." + s) for s in sites_to_search): continue
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
                    current_learned = set(store.get(learned_sites_key, []))
                    current_learned.update(newly_learned_sites)
                    store[learned_sites_key] = list(current_learned)
                    Memory.save(store)
                    meta["newly_learned"] = newly_learned_sites

            search_links.extend(discovered_links)
            search_links = search_links[:num_results]
            meta["search_results"] = search_links

            if verbose:
                print(f"[PlaywrightBlock] Total {len(search_links)} links to scrape.", file=sys.stderr)
            if not search_links:
                print(f"[PlaywrightBlock] ERROR: No search results for query: {query}", file=sys.stderr)

        except Exception as e:
            print(f"[PlaywrightBlock] FATAL ERROR during search step: {e}", file=sys.stderr)
            return str(payload), {"error": f"Search failed: {e}", **meta}

        # --- 2. SCRAPE via Playwright ---
        try:
            with sync_playwright() as p:
                if verbose:
                    print(f"[PlaywrightBlock] Launching browser (headless={headless})...", file=sys.stderr)
                browser = p.chromium.launch(
                    headless=headless,
                    args=["--disable-blink-features=AutomationControlled"]
                )
                b_context = browser.new_context(
                    user_agent=user_agent,
                    java_script_enabled=True
                )
                b_context.set_default_timeout(timeout_ms)
                page = b_context.new_page()

                for link in search_links:
                    # [NEW] Check DB first
                    if use_db_cache:
                        db_entry = _load_from_db(link["url"])
                        if db_entry:
                            db_title, db_text = db_entry
                            # Check length and overlap of cached text
                            if len(db_text) >= min_doc_chars and _term_overlap_ok(db_text):
                                if verbose:
                                    print(f"[PlaywrightBlock] Using DB cache: {link['url']}", file=sys.stderr)
                                docs_raw.append({"title": db_title, "text": db_text, "url": link["url"]})
                                meta["scraped_urls"].append(link["url"])
                            continue  # Got it from DB

                    # Not in DB, so scrape
                    try:
                        if verbose:
                            print(f"[PlaywrightBlock] Scraping: {link['url']}", file=sys.stderr)
                        page.goto(link["url"], timeout=timeout_ms, wait_until="domcontentloaded")
                        page.wait_for_timeout(1000)
                        html = page.content()

                        text = trafilatura.extract(
                            html,
                            include_comments=False,
                            include_tables=False,
                            deduplicate=True
                        )

                        if not text or len(text) < min_doc_chars:
                            if verbose:
                                print(f"[PlaywrightBlock] Text too short for {link['url']}", file=sys.stderr)
                            continue

                        if not _term_overlap_ok(text):
                            if verbose:
                                print(f"[PlaywrightBlock] Overlap too low for {link['url']}", file=sys.stderr)
                            continue

                        # [NEW] Save to DB
                        _save_to_db(link["url"], link["title"], text)

                        docs_raw.append({"title": link["title"], "text": text, "url": link["url"]})
                        meta["scraped_urls"].append(link["url"])

                    except Exception as e:
                        err_msg = f"{link['url']}: {str(e)[:100]}"
                        if verbose:
                            print(f"[PlaywrightBlock] SCRAPE_ERROR: {err_msg}", file=sys.stderr)
                        meta["scrape_errors"].append(err_msg)

                if verbose:
                    print(f"[PlaywrightBlock] Closing browser.", file=sys.stderr)
                browser.close()

        except Exception as e:
            print(f"[PlaywrightBlock] FATAL ERROR during Playwright scrape: {e}", file=sys.stderr)
            return str(payload), {"error": f"Playwright execution failed: {e}", **meta}

        # --- 3. Post-processing ---
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

        # ... (ranking logic unchanged) ...
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
            reverse=True
        )[:max(1, top_k_docs)]

        # ... (sentence extraction logic unchanged) ...
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

        # ... (lexicon logic unchanged) ...
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
            phrases = re.findall(r"\b([A-Za-z0-9][A-Za-z0-9_\-]+(?:\s+[A-Za-z0-9][A-Za-z0-9_\-]+){1,3})\b", context)
            pc: Dict[str, int] = {}
            for ph in phrases:
                ph = ph.lower().strip()
                if any(tok in _STOPWORDS for tok in ph.split()):
                    continue
                pc[ph] = pc.get(ph, 0) + 1
            phrase_top = [p for p, _ in sorted(pc.items(), key=lambda kv: (-kv[1], kv[0]))[:10]]
            lexicon = list(dict.fromkeys(phrase_top + lexicon))[:lexicon_top_k]

        # ... (memory store logic unchanged) ...
        if export_lexicon and lexicon:
            store = Memory.load()
            store[lexicon_key] = lexicon
            Memory.save(store)
            if verbose:
                print(f"[PlaywrightBlock] Exported {len(lexicon)} terms to memory[{lexicon_key}]", file=sys.stderr)

        if export_context and context:
            store = Memory.load()
            if append_ctx and isinstance(store.get(context_key), str) and store[context_key]:
                store[context_key] = store[context_key].rstrip() + "\n\n" + context
            else:
                store[context_key] = context
            Memory.save(store)
            if verbose:
                print(f"[PlaywrightBlock] Exported {len(context)} chars to memory[{context_key}]", file=sys.stderr)

        # compose output
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
            "num_results": 15,
            "headless": True,
            "timeout": 15.0,
            "verbose": False,
            "target_sites": "grailed.com,hypebeast.com,vogue.com",
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
            "db_path": "webcorpus.db",  # [NEW]
            "use_db_cache": True,  # [NEW]
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


# ---------------- Code Generation (Specialized, no-guides/no-fallbacks) ----------------
@dataclass
class CodeBlock(BaseBlock):

    # ---- helpers -------------------------------------------------
    def _trim_to_chars(self, text: str, max_chars: int) -> str:
        # ... (helper unchanged) ...
        if max_chars and len(text) > max_chars:
            return text[:max_chars]
        return text

    def _guess_lang_from_prompt(self, prompt: str, explicit_lang: str) -> str:
        # ... (helper unchanged) ...
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
        # ... (helper unchanged) ...
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
        # ... (helper unchanged) ...
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
        # ... (helper unchanged) ...
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
        # ... (helper unchanged) ...
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
        # ... (helper unchanged) ...
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

        store = Memory.load()
        ctx_key = str(params.get("context_key", "web_context"))
        ctx = (store.get(ctx_key, "") or "").strip()
        context_chars = int(params.get("context_chars", params.get("code.context_chars", 0)))
        if ctx and context_chars > 0:
            ctx = ctx[:context_chars]

        if ctx:
            final_prompt = f"{ctx}\n\n{user_prompt}"
        else:
            final_prompt = user_prompt

        max_input_chars = int(params.get("max_input_chars", 8000))
        final_prompt = self._trim_to_chars(final_prompt, max_input_chars)

        explicit_lang = str(params.get("lang", "python"))
        lang = self._guess_lang_from_prompt(user_prompt, explicit_lang)

        model_name = str(params.get("model", "lexicon-adv")).strip().lower()

        # --- [FIXED] Only pass known/safe params to model constructor ---
        # This prevents the `prompt=` kwarg from crashing the model's __init__
        init_kwargs: Dict[str, Any] = {}
        model_init_keys = [
            "model_name",        # <-- ADD THIS LINE
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
        # --- [END FIX] ---

        # Runtime kwargs for .generate()
        style = str(params.get("style", "plain"))
        try:
            max_chars = int(params.get("max_chars", 0))
        except Exception:
            max_chars = 0

        lexicon = params.get("lexicon", None)

        try:
            # Pass all parent params to generate
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

        # --- [MODIFIED] Use "subpipeline" ---
        subpipeline_name = params.get("subpipeline")  # <-- RENAMED
        if subpipeline_name:
            code_raw = self.run_sub_pipeline(
                initial_value=code_raw,
                pipeline_param_name="subpipeline",  # <-- RENAMED
                parent_params=params,
            )
        # --- [END MODIFIED] ---

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
            "context_chars": len(ctx),
            "prompt_len": len(final_prompt),
            "tokens_generated": len(code_raw),
            "style": style,
            "max_chars": max_chars,
            "max_input_chars": max_input_chars,
            "used_context": bool(ctx),
            "subpipeline": subpipeline_name,  # <-- RENAMED
        }
        return result, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "prompt": "REQUIRED: Write a python function...",
            "context_key": "web_context",
            "context_chars": 0,
            "model": "lexicon-adv",
            "max_input_chars": 8000,
            "wrap": True,
            "inject_tag": "code_solution",
            "lang": "python",

            # --- [MODIFIED] ---
            "subpipeline": "",  # e.g., "code_chat"
            "code_chat.op": "passthrough",  # Example of delegated param
            # --- [END MODIFIED] ---

            # Knobs passed into model.generate(...)
            "style": "plain",
            "max_chars": 0,
            "max_terms": 12,

            # Model-specific params (for hf-llm, etc.)
            "max_new_tokens": 128,
            "temperature": 0.7,
            "top_p": 0.9,
            "top_k": 50,
        }


BLOCKS.register("code", CodeBlock)


# ---------------- CodeCorpus (code docs & API learner) ----------------
@dataclass
class CodeCorpusBlock(BaseBlock):
    """
    Code-focused corpus builder.
      • Inputs: list of urls, sitemap(s), or (query + site_include) search.
      • Extracts: fenced / <pre>/<code> blocks from Markdown/HTML.
      • Saves ONLY code snippets to a local SQLite FTS5 database (kind='code').
      • NEW: Can use Playwright to fall back for JS-heavy sites.
      • NEW: Remembers scraped URLs and skips them unless force_refresh=true.

    Deps:
      - requests, beautifulsoup4
      - trafilatura (optional, preferred for HTML)
      - duckduckgo_search (optional, for query)
      - playwright (optional, for use_playwright_fallback=true)

    Example:
      --block codecorpus --extra codecorpus.urls="https://react.dev/learn"
      --extra codecorpus.use_playwright_fallback=true
    """

    # --- DB Helpers ---

    def _init_db(self, db_path: str):
        """Initialize the FTS5 virtual table."""
        with sqlite3.connect(db_path) as conn:
            conn.execute("""
            CREATE VIRTUAL TABLE IF NOT EXISTS docs USING fts5(
                url UNINDEXED,    -- Don't index the URL itself
                title,            -- Index the title
                content,          -- Index the main content
                kind,             -- 'prose' or 'code'
                tokenize = 'porter unicode61'
            );
            """)

    # --- NEW: URL Tracking DB ---
    def _init_url_tracking_db(self, db_path: str):
        """
        Initializes a separate table to track scraped URLs and times.
        """
        with sqlite3.connect(db_path) as conn:
            conn.execute("""
            CREATE TABLE IF NOT EXISTS indexed_urls (
                url TEXT PRIMARY KEY,
                last_scraped_time REAL NOT NULL
            );
            """)

    def _get_last_scraped_time(self, conn: sqlite3.Connection, url: str) -> float:
        """Check the DB for the last scraped time of a URL."""
        try:
            cur = conn.execute(
                "SELECT last_scraped_time FROM indexed_urls WHERE url = ?", (url,)
            )
            row = cur.fetchone()
            return float(row[0]) if row else 0.0
        except sqlite3.Error as e:
            print(f"Error checking scrape time for {url}: {e}")
            return 0.0

    # --- END NEW ---

    def _clean_domain(self, u: str) -> str:
        """Utility to get the bare domain from a URL."""
        try:
            netloc = urlparse(u).netloc.lower()
            return netloc.split(":")[0]
        except Exception:
            return ""

    def _clear_db_for_urls(self, conn: sqlite3.Connection, urls: List[str]):
        """Clear old entries for domains we are about to re-scrape."""
        domains = set(self._clean_domain(u) for u in urls)
        domains.discard("")
        if not domains:
            return

        patterns = [f"https://{d}%" for d in domains] + [f"http://{d}%" for d in domains]
        placeholders = " OR ".join(["url LIKE ?"] * len(patterns))

        try:
            # Clear from FTS table
            cur = conn.execute(f"DELETE FROM docs WHERE {placeholders};", patterns)
            print(f"Cleared {cur.rowcount} old FTS entries for domains: {', '.join(domains)}")

            # --- NEW: Clear from tracking table ---
            cur_track = conn.execute(f"DELETE FROM indexed_urls WHERE {placeholders};", patterns)
            print(f"Cleared {cur_track.rowcount} old tracking entries.")

        except sqlite3.Error as e:
            print(f"Error clearing old entries: {e}")

    def _looks_like_traceback(self, code: str) -> bool:
        c = code.lower()
        if "traceback (most recent call last)" in c:
            return True
        if "error:" in c or "exception" in c:
            # Very simple heuristic: mostly "File ..." lines, no 'def'/'class'
            lines = [ln.strip() for ln in code.splitlines() if ln.strip()]
            file_like = sum(ln.startswith("file \"") or ln.startswith("file \"") for ln in lines)
            has_def = any("def " in ln or "class " in ln for ln in lines)
            if file_like >= 2 and not has_def:
                return True
        return False

    # --- Identifier & text processing ---
    _STOP = set([
        "the", "a", "an", "and", "or", "if", "on", "in", "to", "for", "from", "of", "at", "by", "with", "as", "is",
        "are", "was", "were", "be", "been", "being", "that", "this", "these", "those", "it", "its", "into", "about",
        "over", "under", "can", "should", "would", "will", "may", "might", "must", "do", "does", "did", "done", "have",
        "has", "had", "having", "not", "no", "yes", "you", "your", "we", "our", "they", "their", "there", "here",
        "also", "such", "via", "etc", "see",
        "code", "example", "examples", "note", "notes", "true", "false", "none", "null", "class", "function", "method",
        "module", "package", "return", "returns", "type", "types", "param", "parameter", "parameters"
    ])

    _IDENT_RE = re.compile(
        r"""
        (?:
          [A-Za-z_][A-Za-z0-9_]* # snake/UPPER/mixed
          (?:\.[A-Za-z_][A-Za-z0-9_]*)* # dotted api.name
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
        re.VERBOSE
    )

    _FENCE_RE = re.compile(
        r"""
        ^```[ \t]*([A-Za-z0-9_\-\+\.]*)[ \t]*\n   # opening fence with optional lang
        (.*?)                                     # code body (non-greedy)
        \n```[ \t]*$                              # closing fence
        """,
        re.MULTILINE | re.DOTALL | re.VERBOSE
    )

    def _extract_identifiers(self, text: str, min_len: int) -> List[str]:
        ids = self._IDENT_RE.findall(text or "")
        out = []
        for s in ids:
            tok = s.strip().strip(".")
            if len(tok) < min_len:
                continue
            low = tok.lower()
            if low in self._STOP:
                continue
            out.append(tok)
        return out

    # --- fetch helpers ---

    def _get_page_static(self, url: str) -> str:
        """Fast static HTML fetch using requests."""
        try:
            import requests
            r = requests.get(
                url,
                headers={"User-Agent": self.user_agent},
                timeout=(self.timeout, self.read_timeout)
            )
            if r.status_code == 200:
                return r.text
        except Exception as e:
            print(f"Static fetch failed for {url}: {e}")
            return ""
        return ""

    def _get_page_dynamic(self, browser: "Browser", url: str) -> str:
        """Rendered HTML fetch using an existing Playwright browser instance."""
        page = None
        try:
            page = browser.new_page(
                user_agent=self.user_agent,
                java_script_enabled=True
            )
            page.goto(url, timeout=int(self.timeout * 1000), wait_until="domcontentloaded")
            page.wait_for_timeout(500)
            return page.content()
        except Exception as e:
            print(f"Playwright fetch error for {url}: {e}")
            return ""
        finally:
            if page:
                page.close()

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
                    html_text, include_comments=False, include_tables=False, deduplicate=True
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

        self.timeout = float(params.get("timeout", 10.0))
        self.read_timeout = float(params.get("read_timeout", 12.0))
        self.user_agent = str(params.get("user_agent", "promptchat/codecorpus"))
        verbose = bool(params.get("verbose", False))

        use_playwright_fallback = bool(params.get("use_playwright_fallback", True))

        # --- NEW: Refresh Param ---
        force_refresh = bool(params.get("force_refresh", False))

        # --- Check dependencies ---
        try:
            import requests
        except Exception:
            return str(payload), {"error": "Install `requests` to use CodeCorpusBlock."}

        try:
            from bs4 import BeautifulSoup
        except Exception:
            return str(payload), {"error": "Install `beautifulsoup4` to use CodeCorpusBlock."}

        try:
            import trafilatura
            _has_traf = True
        except Exception:
            _has_traf = False

        try:
            from ddgs import DDGS
            _has_ddgs = True
        except Exception:
            _has_ddgs = False

        try:
            from playwright.sync_api import sync_playwright, Page, Browser
            _has_playwright = True
        except Exception:
            _has_playwright = False
            if use_playwright_fallback:
                print(
                    "Warning: use_playwright_fallback=true, but 'playwright' is not installed. Skipping JS rendering.")
                use_playwright_fallback = False

        def _allowed(url: str) -> bool:
            d = self._clean_domain(url)
            if not d:
                return False
            if site_include and not any(d.endswith(s) for s in site_include):
                return False
            if any(d.endswith(s) for s in site_exclude):
                return False
            return True

        # --- Initialize DB ---
        try:
            self._init_db(db_path)
            self._init_url_tracking_db(db_path)  # --- NEW ---
        except Exception as e:
            return str(payload), {"error": f"Failed to initialize database at {db_path}: {e}"}

        # --- collect URLs ---
        candidates: List[str] = []
        if urls_raw:
            candidates.extend([u.strip() for u in urls_raw.split(",") if u.strip()])

        if sitemaps_raw:
            for sm in [s.strip() for s in sitemaps_raw.split(",") if s.strip()]:
                try:
                    xml = self._get_page_static(sm)
                    if not xml:
                        continue
                    locs = re.findall(r"<loc>(.*?)</loc>", xml, re.IGNORECASE | re.DOTALL)
                    for loc in locs:
                        u = html.unescape(loc).strip()
                        if _allowed(u):
                            candidates.append(u)
                except Exception:
                    continue

        if query and not (urls_raw or sitemaps_raw) and _has_ddgs:
            from ddgs import DDGS
            with DDGS() as ddgs:
                try:
                    for r in ddgs.text(query, max_results=max_pages * 2, safesearch='off'):
                        u = r.get("href") or r.get("url")
                        if u and _allowed(u):
                            candidates.append(u)
                except Exception as e:
                    print(f"DDGS search failed: {e}")

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

        # --- NEW: Playwright Lifecycle Management ---
        playwright_context = None
        browser = None
        if use_playwright_fallback and _has_playwright:
            try:
                from playwright.sync_api import sync_playwright
                playwright_context = sync_playwright().start()
                browser = playwright_context.chromium.launch(headless=True)
            except Exception as e:
                print(f"Failed to launch Playwright, disabling fallback: {e}")
                use_playwright_fallback = False
                if playwright_context:
                    playwright_context.stop()
                playwright_context = None

        # --- Connect to DB and clear old entries ---
        try:
            conn = sqlite3.connect(db_path)
            # --- NEW: Only clear if refreshing ---
            if force_refresh:
                self._clear_db_for_urls(conn, final_urls)
            # --- END NEW ---
        except Exception as e:
            if browser:
                browser.close()
            if playwright_context:
                playwright_context.stop()
            return str(payload), {"error": f"DB connect/clear failed: {e}"}

        # --- fetch and parse pages ---
        domain_hits: Dict[str, int] = defaultdict(int)
        total_prose = 0
        total_code = 0
        # --- NEW: Counters ---
        total_indexed = 0
        total_updated = 0
        total_skipped = 0
        total_errors = 0
        # --- END NEW ---

        for u in final_urls:
            try:
                # --- NEW: Check if URL should be skipped ---
                current_time = time.time()
                last_scraped_time = self._get_last_scraped_time(conn, u)

                if last_scraped_time > 0.0 and not force_refresh:
                    if verbose:
                        print(f"Skipping (already indexed): {u}")
                    total_skipped += 1
                    continue
                # --- END NEW ---

                html_text = self._get_page_static(u)
                if not html_text:
                    total_errors += 1
                    continue

                if u.lower().endswith(".md") or "/raw/" in u or "raw.githubusercontent.com" in u:
                    prose_body, code_blocks = self._extract_text_md(html_text)
                else:
                    prose_body, code_blocks = self._extract_text_html(html_text, _has_traf)

                code_text = "\n\n".join(code_blocks).strip()

                if len(code_text) < min_doc_chars and use_playwright_fallback and browser and not u.lower().endswith(
                        ".md"):
                    if verbose:
                        print(f"Static scrape for {u} got {len(code_text)} code chars, retrying with Playwright...")
                    html_text_js = self._get_page_dynamic(browser, u)
                    if html_text_js:
                        html_text = html_text_js  # Use JS html for title
                        prose_body, code_blocks = self._extract_text_html(html_text, _has_traf)
                        code_text = "\n\n".join(code_blocks).strip()

                if len(code_text) < min_doc_chars:
                    total_skipped += 1  # Skip if still not enough content
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

                # --- Insert ONLY code snippets into DB ---
                url_had_code = False
                for code in code_blocks:
                    code = (code or "").strip()
                    if len(code) < 20:
                        continue
                    if self._looks_like_traceback(code):
                        continue

                    conn.execute(
                        "INSERT OR REPLACE INTO docs (url, title, content, kind) VALUES (?, ?, ?, ?)",
                        (u, title, code, "code")
                    )
                    total_code += 1
                    url_had_code = True

                # --- NEW: Update tracking DB only if we found content ---
                if url_had_code:
                    conn.execute(
                        "INSERT OR REPLACE INTO indexed_urls (url, last_scraped_time) VALUES (?, ?)",
                        (u, current_time)
                    )
                    if last_scraped_time == 0.0:
                        total_indexed += 1
                    else:
                        total_updated += 1
                # --- END NEW ---

                domain_hits[self._clean_domain(u)] += 1

            except Exception as e:
                total_errors += 1
                if verbose:
                    print(f"Error processing {u}: {e}")

        # --- Close Playwright ---
        if browser: browser.close()
        if playwright_context: playwright_context.stop()

        # --- Commit DB ---
        try:
            conn.commit()
            conn.close()
        except Exception:
            pass

        # --- Learn new domains ---
        newly_learned: List[str] = []
        if learn_new_sites:
            store = Memory.load()
            learned = set(store.get(learned_sites_key, []))
            for dom, c in domain_hits.items():
                if not dom: continue
                if c >= learn_min_hits and dom not in learned and _allowed(f"https://{dom}/"):
                    learned.add(dom)
                    newly_learned.append(dom)
            if newly_learned:
                store[learned_sites_key] = sorted(list(learned))
                Memory.save(store)

        # --- Compose output ---
        base = "" if payload is None else str(payload)
        # --- NEW: Updated report ---
        out_msg = (
            f"Web corpus scan complete. Processed {len(final_urls)} URLs.\n"
            f"  - New Snippets Indexed: {total_indexed}\n"
            f"  - Snippets Updated:     {total_updated}\n"
            f"  - URLs Skipped:         {total_skipped}\n"
            f"  - Total Snippets Added: {total_code}\n"
            f"  - Errors:               {total_errors}"
        )

        meta = {
            "db_path": db_path,
            "urls_scraped": len(final_urls),
            "total_prose_snippets": 0,  # This block only indexes code
            "total_code_snippets": total_code,
            "files_indexed": total_indexed,
            "files_updated": total_updated,
            "files_skipped": total_skipped,
            "errors": total_errors,
            "site_include": site_include,
            "site_exclude": site_exclude,
            "learned_sites_key": learned_sites_key if learn_new_sites else None,
            "newly_learned": newly_learned,
        }
        return f"{base}\n\n[corpus_update]\n{out_msg}", meta

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
            "force_refresh": False  # <-- NEW PARAM
        }


# Register the block
BLOCKS.register("codecorpus", CodeCorpusBlock)



@dataclass
class CodeSearchBlock(BaseBlock):
    """
    "Smarter" Code Retrieval using SQLite FTS + Numpy Vector Reranking.

    Features:
      • Retrieval: Fetches a large pool of candidates (top_k * 5) using SQLite FTS5.
      • Vectorization: Uses Numpy to build a Term-Document Matrix based on query terms.
      • Scoring: Computes Cosine Similarity (Query vs. Candidates).
      • Heuristics: Boosts scores for 'code' vs 'prose', and penalizes 'spaghetti' code.
      • Diversity: Penalizes multiple chunks from the same file to ensure broad context.

    Inputs:
      --extra codesearch.query="how to implement a router in python"

    Requires:
      `pip install numpy` (Falls back to standard python scoring if missing).
    """

    _SEARCH_STOP_WORDS = {
        "a", "an", "and", "are", "as", "at", "be", "by", "for", "from",
        "how", "in", "is", "it", "of", "on", "or", "show", "tell", "that",
        "the", "this", "to", "what", "when", "where", "which", "with",
        "me", "give", "using", "write", "basic", "script", "code", "function"
    }

    # --- 1. Text Processing & Helpers ---

    def _tokenize(self, text: str) -> List[str]:
        """Splits text into lowercase alphanumeric tokens."""
        return re.findall(r"\w+", (text or "").lower())

    def _extract_identifiers(self, text: str) -> Set[str]:
        """Extracts likely variable/function names (snake_case, camelCase)."""
        # (Simplified regex for speed)
        return set(re.findall(r"[a-zA-Z_][a-zA-Z0-9_]*", text))

    def _guess_code_lang(self, code_snippet: str) -> str:
        """Heuristic language detection for code blocks."""
        s = code_snippet.lower()
        if "def " in s and "import " in s: return "python"
        if "function" in s and "{" in s: return "javascript"
        if "public class" in s or "system.out" in s: return "java"
        if "#include" in s and "std::" in s: return "cpp"
        if "using system" in s or "namespace" in s: return "csharp"
        return ""

    def _format_fts_query(self, query: str) -> str:
        """Formats a raw string into a valid SQLite FTS5 query string."""
        tokens = [t for t in self._tokenize(query) if t not in self._SEARCH_STOP_WORDS]
        if not tokens:
            return query.replace('"', '""')  # Fallback

        # Strategy: (term1* AND term2*) OR (term1* OR term2*)
        and_part = " AND ".join(f'"{t}"*' for t in tokens)
        or_part = " OR ".join(f'"{t}"*' for t in tokens)
        return f"({and_part}) OR ({or_part})"

    # --- 2. Numpy Scoring Engine ---

    def _rank_with_numpy(
            self,
            query: str,
            candidates: List[Dict[str, Any]]
    ) -> List[Tuple[float, Dict[str, Any]]]:
        """
        Uses Numpy to perform Cosine Similarity + Heuristic weighting.
        """
        if not candidates:
            return []

        # --- A. Prepare Vocabulary (Query-Centric) ---
        # We only care about dimensions (words) that exist in the query.
        q_tokens = [t for t in self._tokenize(query) if t not in self._SEARCH_STOP_WORDS]
        vocab = sorted(list(set(q_tokens)))

        if not vocab:
            # If query was only stopwords, return SQLite order
            return [(1.0, c) for c in candidates]

        n_docs = len(candidates)
        n_terms = len(vocab)

        # --- B. Build Matrices ---
        # Query Vector (1 x V)
        # Doc Matrix   (N x V)

        # 1. Query Vector (Binary: 1 if term exists)
        Q = np.ones(n_terms, dtype=np.float32)

        # 2. Document Matrix (Term Counts)
        D = np.zeros((n_docs, n_terms), dtype=np.float32)

        # 3. Feature Arrays for Heuristics
        kinds_score = np.zeros(n_docs, dtype=np.float32)
        lengths_score = np.zeros(n_docs, dtype=np.float32)

        vocab_map = {term: i for i, term in enumerate(vocab)}

        for i, doc in enumerate(candidates):
            content = (doc.get("content") or "").lower()
            title = (doc.get("title") or "").lower()
            kind = (doc.get("kind") or "prose").lower()

            # Fill Document Matrix
            # We give 2x weight to matches in the Title
            doc_tokens = self._tokenize(content) + (self._tokenize(title) * 2)

            for t in doc_tokens:
                if t in vocab_map:
                    D[i, vocab_map[t]] += 1.0

            # Fill Heuristic Arrays
            # 1. Kind Boost: Code > Prose
            if "code" in kind:
                kinds_score[i] = 1.2
            else:
                kinds_score[i] = 0.9

            # 2. Length Heuristic (Bell curve preference for medium chunks)
            # Small (<100 chars) = bad. Huge (>3000 chars) = bad.
            ln = len(content)
            if ln < 100:
                lengths_score[i] = 0.5
            elif ln > 3000:
                lengths_score[i] = 0.7
            else:
                lengths_score[i] = 1.0

        # --- C. TF-IDF Weighing (Simplified) ---
        # Calculate Document Frequency (how many docs contain term t)
        df = np.sum(D > 0, axis=0)
        # Avoid divide by zero
        idf = np.log((n_docs + 1) / (df + 1)) + 1

        # Apply IDF to Document Matrix
        D_tfidf = D * idf

        # --- D. Cosine Similarity ---
        # Dot product of Query and Docs
        # Q is all 1s (scaled by IDF effectively in dot product if we weighed Q,
        # but here we map Q against D_tfidf directly)

        # Dot product: sum of weights for matched terms
        dot_products = np.dot(D_tfidf, Q)

        # Norms (magnitude of vectors)
        doc_norms = np.linalg.norm(D_tfidf, axis=1)
        q_norm = np.linalg.norm(Q)

        # Avoid zero division
        doc_norms[doc_norms == 0] = 1.0

        cosine_sim = dot_products / (doc_norms * q_norm)

        # --- E. Final Weighted Score ---
        # Score = CosineSim * KindBoost * LengthBoost
        final_scores = cosine_sim * kinds_score * lengths_score

        # Zip and Sort
        results = []
        for i in range(n_docs):
            results.append((float(final_scores[i]), candidates[i]))

        # Sort Descending
        results.sort(key=lambda x: x[0], reverse=True)
        return results


    # --- 3. Main Execution ---

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        query = str(params.get("query", "")).strip()
        if not query:
            return str(payload), {"error": "CodeSearchBlock: 'query' parameter is required."}

        db_path = str(params.get("db_path", "code_corpus.db"))
        top_k = int(params.get("top_k", 5))
        export_key = str(params.get("export_key", "code_search_context"))
        max_chars = int(params.get("max_chars", 6000))
        inject = bool(params.get("inject", True))

        # 1. Fetch Candidates from SQLite
        # We fetch 4x top_k to give the Numpy reranker a good pool to filter from.
        fetch_limit = top_k * 4
        fts_query = self._format_fts_query(query)

        rows = []
        try:
            with sqlite3.connect(db_path) as conn:
                conn.row_factory = sqlite3.Row
                # Fetch basic matches
                sql = f"""
                    SELECT url, title, content, kind 
                    FROM docs 
                    WHERE docs MATCH ? 
                    LIMIT ?
                """
                cursor = conn.execute(sql, (fts_query, fetch_limit))
                # Convert to list of dicts so we can mutate/score easily
                rows = [dict(row) for row in cursor.fetchall()]
        except sqlite3.Error as e:
            return str(payload), {"error": f"DB Error: {e}", "query": query}

        if not rows:
            return str(payload), {"note": "No results found in SQLite.", "hits": 0}

        # 2. Re-rank (Vector vs Fallback)
        scored_candidates = self._rank_with_numpy(query, rows)
        ranker_used = "numpy_cosine"

        # 3. Apply Diversity Filter & Final Selection
        # We want to avoid filling the context with 5 chunks from the exact same file.
        final_selection = []
        seen_files = {}  # filename -> count

        total_chars = 0

        for score, doc in scored_candidates:
            if len(final_selection) >= top_k:
                break

            # Extract file path/name from URL or Title for grouping
            # Usually URL is "path/to/file::chunk_name"
            origin = doc['url'].split("::")[0]

            # Diversity Penalty: Skip if we already have 2 chunks from this file
            if seen_files.get(origin, 0) >= 2:
                continue

            # Length cap check
            content = doc['content']
            if total_chars + len(content) > max_chars:
                continue

            final_selection.append(doc)
            seen_files[origin] = seen_files.get(origin, 0) + 1
            total_chars += len(content)

        # 4. Format Output
        context_blocks = []
        for doc in final_selection:
            title = doc['title']
            kind = doc['kind']
            content = doc['content']

            # Add nice markdown fencing
            lang = ""
            if "code" in kind:
                lang = kind.split(":")[-1] if ":" in kind else self._guess_code_lang(content)

            header = f"### {kind.upper()} | {title}"
            if lang and "code" in kind:
                block = f"{header}\n```{lang}\n{content}\n```"
            else:
                block = f"{header}\n{content}"

            context_blocks.append(block)

        full_context = "\n\n".join(context_blocks)

        # 5. Save & Return
        store = Memory.load()
        store[export_key] = full_context
        Memory.save(store)

        meta = {
            "query": query,
            "hits_found": len(rows),
            "hits_returned": len(final_selection),
            "ranker": ranker_used,
            "diversity_groups": len(seen_files)
        }

        out_text = str(payload)
        if inject and full_context:
            out_text += f"\n\n[{export_key}]\n{full_context}"

        return out_text, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "REQUIRED. The search string.",
            "db_path": "code_corpus.db",
            "top_k": 5,
            "inject": True,
            "export_key": "code_search_context",
            "max_chars": 6000
        }


BLOCKS.register("codesearch", CodeSearchBlock)


# ---------------- LocalCodeCorpus (scans local files) ----------------
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
            CREATE TABLE IF NOT EXISTS indexed_files (
                path TEXT PRIMARY KEY,
                last_indexed_mtime REAL NOT NULL
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


# ---------------- Intelligence (Code vs. Prose) ----------------
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
    A deep-dive crawler designed to find specific 'hard-to-find' assets.

    It searches for a topic, visits the result pages, and scans their HTML
    (and optionally JS-rendered DOM via Playwright) for specific file
    extensions (.pdf, .mp3, .zip) or regex/keyword patterns.

    Modes:
    - 'media': looks for .mp3, .wav, .flac, .m4a, .ogg
    - 'docs': looks for .pdf, .doc, .docx, .epub, .mobi
    - 'archives': looks for .zip, .rar, .7z, .tar, .gz
    - 'custom': uses 'extensions' param

    Features:
    - Search engines: duckduckgo (default), google_cse
    - Verify: Can perform a HEAD request to ensure the link is alive (200 OK).
    - Dedupe: Removes duplicate links found across multiple pages.
    - Optional site filter via `site_require` (e.g. archive.org only).
    - Optional JS rendering via Playwright: linktracker.use_js=true
    - Optional JS link dump: linktracker.return_all_js_links=true
    - Optional Playwright network sniff:
        • linktracker.use_network_sniff=true
        • linktracker.return_network_sniff_links=true
    - min_term_overlap:
        • linktracker.min_term_overlap=N
        Require at least N distinct keyword tokens (from query + url_keywords)
        to appear in the URL/text haystack. For "lil uzi vert", setting
        min_term_overlap=2 or 3 will bias to links that really mention the artist.

    Advanced:
    - subpipeline:
        • Can be a chain like "prompt_query|sitemap" or "prompt_query|xml".
        • If the final sub-block returns a list of URLs (e.g. from sitemap/xml),
          LinkTracker will:
              1) Harvest direct assets from that list (.mp3, .flac, .pdf, etc.)
              2) Use the remaining URLs as candidate HTML pages for BFS crawling.
    """

    # Obvious static / junk-ish filenames we don't want to prioritize
    JUNK_FILENAME_KEYWORDS = {
        "sprite",
        "icon",
        "favicon",
        "logo",
        "tracking",
        "pixel",
        "blank",
        "placeholder",
    }

    IGNORED_EXTENSIONS = {
        ".css", ".js", ".json", ".xml", ".svg", ".png", ".jpg", ".jpeg",
        ".gif", ".ico", ".woff", ".woff2", ".ttf", ".eot", ".map"
    }

    # ------------------------------------------------------------------ #
    # Network & JS Helpers
    # ------------------------------------------------------------------ #

    def _fetch_page_with_network_sniff(
            self,
            page_url: str,
            timeout: float,
            ua: str,
            log: List[str],
            extensions: set,
    ) -> Tuple[str, List[Dict[str, str]]]:
        try:
            from playwright.sync_api import sync_playwright, TimeoutError as PlaywrightTimeoutError
        except ImportError:
            log.append("Playwright not installed (network sniff unavailable).")
            return "", []

        html = ""
        found_items: List[Dict[str, str]] = []
        seen_network = set()

        try:
            with sync_playwright() as p:
                browser = p.chromium.launch(headless=True)
                context = browser.new_context(user_agent=ua)
                page = context.new_page()

                def handle_response(response):
                    try:
                        url = response.url

                        # 1) Extension-based fast path
                        if any(url.lower().endswith(ext) for ext in extensions):
                            if url not in seen_network:
                                seen_network.add(url)
                                found_items.append(
                                    {
                                        "url": url,
                                        "text": "[Network File]",
                                        "tag": "network_sniff",
                                        "size": response.headers.get("content-length", "?"),
                                    }
                                )
                                return

                        # 2) Content-Type sniff (streams)
                        ctype = response.headers.get("content-type", "").lower()
                        if (
                                "audio" in ctype
                                or "video" in ctype
                                or "application/octet-stream" in ctype
                        ):
                            cl_raw = response.headers.get("content-length", "0")
                            try:
                                cl = int(cl_raw)
                            except Exception:
                                cl = 0

                            # Skip tiny assets (icons / pixels)
                            if cl > 50000 and url not in seen_network:
                                seen_network.add(url)
                                found_items.append(
                                    {
                                        "url": url,
                                        "text": f"[Network Stream] ({ctype})",
                                        "tag": "network_sniff",
                                        "size": str(cl),
                                    }
                                )
                    except Exception:
                        return  # best-effort

                page.on("response", handle_response)

                sniff_goto_timeout = max(15000, int(timeout * 1000))  # >= 15s

                try:
                    page.goto(
                        page_url,
                        wait_until="domcontentloaded",
                        timeout=sniff_goto_timeout,
                    )
                except PlaywrightTimeoutError as e:
                    log.append(
                        f"Network sniff: goto timeout on {page_url} ({e}). "
                        "Proceeding with whatever responses we captured."
                    )

                sniff_window_ms = int(timeout * 1000)
                page.wait_for_timeout(sniff_window_ms)

                html = page.content()
                browser.close()

                log.append(
                    f"Network sniff finished on {page_url}. "
                    f"Found {len(found_items)} network assets."
                )
        except Exception as e:
            log.append(f"Playwright/Network Error on {page_url}: {e}")

        return html, found_items

    def _search_duckduckgo(self, q: str, n: int, ua: str, timeout: float) -> List[str]:
        """Runs a DuckDuckGo search, returns a list of URLs."""
        pages: List[str] = []

        # Phase 1: ddgs.text()
        try:
            from ddgs import DDGS

            with DDGS() as ddgs:
                for r in ddgs.text(q, max_results=n, safesearch="off"):
                    u = r.get("href") or r.get("url")
                    if u:
                        pages.append(u)
            if pages:
                return pages
        except Exception:
            pass

        # Phase 2: HTML fallback (best effort)
        try:
            import requests
            from bs4 import BeautifulSoup
            from urllib.parse import unquote

            r = requests.get(
                "https://html.duckduckgo.com/html/",
                params={"q": q},
                headers={"User-Agent": ua},
                timeout=timeout,
            )
            r.raise_for_status()
            soup = BeautifulSoup(r.text, "html.parser")
            for a in soup.select(".result__a"):
                href = a.get("href")
                if href and "uddg=" in href:
                    href = unquote(href.split("uddg=")[1].split("&")[0])
                    pages.append(href)
        except Exception:
            pass

        return pages

    def _search_google_cse(self, q: str, n: int, timeout: float) -> List[str]:
        """Runs a Google CSE search, returns a list of URLs."""
        import os
        import requests

        cx = os.environ.get("GOOGLE_CSE_ID")
        key = os.environ.get("GOOGLE_API_KEY")
        if not (cx and key):
            # No key or CSE ID -> behave like "no results"
            return []

        out: List[str] = []
        try:
            r = requests.get(
                "https://www.googleapis.com/customsearch/v1",
                params={"q": q, "cx": cx, "key": key, "num": min(10, n)},
                timeout=timeout,
            )
            if r.status_code != 200:
                return []
            data = r.json()
            for item in (data.get("items") or []):
                u = item.get("link")
                if u:
                    out.append(u)
            return out[:n]
        except Exception:
            return out[:n]

    # ------------------------------------------------------------------ #
    # Keyword helpers
    # ------------------------------------------------------------------ #

    def _extract_keywords_from_query(self, query: str) -> List[str]:
        """Get significant query tokens, using _STOPWORDS if present."""
        try:
            stops = _STOPWORDS
        except NameError:
            stops = {"the", "a", "an", "is", "to", "for", "of", "and", "or"}

        tokens = [
            t
            for t in re.findall(r"[A-Za-z0-9][A-Za-z0-9_\-]+", query.lower())
            if t not in stops
        ]
        out: List[str] = []
        for t in tokens:
            if t not in out:
                out.append(t)
        return out

    # ------------------------------------------------------------------ #
    # Fetch helpers
    # ------------------------------------------------------------------ #

    def _fetch_page_html_plain(self, session, page_url: str, timeout: float) -> str:
        """Fetch page HTML via requests only."""
        import requests

        resp = session.get(page_url, timeout=timeout)
        resp.raise_for_status()
        return resp.text

    def _fetch_page_with_js(
            self,
            page_url: str,
            timeout: float,
            ua: str,
            log: List[str],
    ) -> Tuple[str, List[Dict[str, str]]]:
        """
        Use Playwright to:
          • Render the page (domcontentloaded, short timeout).
          • Run JS that collects candidate links:
                a[href], audio[src], video[src], source[src],
                iframe[src], embed[src].

        Returns (html, links) where links is a list of {url,text,tag}.
        """
        try:
            from playwright.sync_api import sync_playwright
        except Exception:
            log.append(
                "Playwright not available, falling back to plain HTML (no JS links)."
            )
            return "", []

        html = ""
        links: List[Dict[str, str]] = []

        try:
            with sync_playwright() as p:
                browser = p.firefox.launch(headless=True)
                page = browser.new_page(user_agent=ua)
                js_timeout_ms = int(max(timeout, 10.0) * 1000)
                page.goto(
                    page_url,
                    wait_until="domcontentloaded",
                    timeout=js_timeout_ms,
                )

                html = page.content()

                raw_links = page.evaluate(
                    """
                    () => {
                      const out = [];
                      const seen = new Set();

                      function push(el, url, tag) {
                        if (!url) return;
                        if (seen.has(url)) return;
                        seen.add(url);
                        const text = (el.innerText || el.textContent || el.title || "").trim();
                        out.push({ url, text, tag });
                      }

                      const selectors = [
                        "a[href]",
                        "audio[src]",
                        "video[src]",
                        "video source[src]",
                        "source[src]",
                        "iframe[src]",
                        "embed[src]"
                      ];

                      for (const sel of selectors) {
                        document.querySelectorAll(sel).forEach(el => {
                          let url = el.href || el.currentSrc || el.src;
                          if (!url && el.getAttribute) {
                            url = el.getAttribute("src") || el.getAttribute("href");
                          }
                          if (!url) return;
                          push(el, url, el.tagName.toLowerCase());
                        });
                      }

                      return out;
                    }
                    """
                ) or []

                for item in raw_links:
                    url = item.get("url")
                    if not url:
                        continue
                    links.append(
                        {
                            "url": url,
                            "text": (item.get("text") or "").strip(),
                            "tag": item.get("tag") or "a",
                        }
                    )

                browser.close()
                log.append(
                    f"Rendered JS DOM + gathered {len(links)} JS links for: {page_url}"
                )
        except Exception as e:
            log.append(f"Playwright error on {page_url}: {e}")

        return html, links

    # ------------------------------------------------------------------ #
    # Main execution
    # ------------------------------------------------------------------ #

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import requests
        from bs4 import BeautifulSoup
        from urllib.parse import urljoin, urlparse

        # --- 1. Input & optional sub-pipeline (sitemap/xml/etc.) ---
        query_raw = str(params.get("query", "") or str(payload or "")).strip()
        subpipe_name = str(params.get("subpipeline", "") or "").strip()

        if subpipe_name:
            pipeline_result: Any = self.run_sub_pipeline(
                initial_value=query_raw,
                pipeline_param_name="subpipeline",
                parent_params=params,
            )
        else:
            pipeline_result = query_raw

        # --- 2. Configuration Parameters ---
        mode = str(params.get("mode", "docs")).lower()
        scan_limit = int(params.get("scan_limit", 5))
        max_pages_total = int(params.get("max_pages_total", scan_limit))
        max_pages_total = max(1, max_pages_total)

        timeout = float(params.get("timeout", 5.0))
        verify_links = bool(params.get("verify", True))
        engine = str(params.get("engine", "duckduckgo")).lower()

        use_js = bool(params.get("use_js", False))
        return_all_js_links = bool(params.get("return_all_js_links", False))
        max_links_per_page = int(params.get("max_links_per_page", 500))
        search_results_cap = int(params.get("search_results_cap", 256))
        use_network_sniff = bool(params.get("use_network_sniff", False))
        return_network_sniff_links = bool(params.get("return_network_sniff_links", False))

        min_term_overlap_raw = int(params.get("min_term_overlap", 1))
        min_term_overlap = max(1, min_term_overlap_raw)

        custom_ext = str(params.get("extensions", "")).split(",")
        keywords_in_url = str(params.get("url_keywords", "")).split(",")
        site_require_raw = str(params.get("site_require", "")).split(",")
        required_sites = [s.strip().lower() for s in site_require_raw if s.strip()]
        max_depth = int(params.get("max_depth", 0))
        max_depth = max(0, max_depth)

        # --- 3. Target Extensions ---
        targets = set()
        if mode == "media":
            targets.update([".mp3", ".wav", ".flac", ".m4a", ".ogg"])
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

        # --- 4. Keyword Extraction (from the *raw* user query) ---
        keywords: List[str] = [k.strip().lower() for k in keywords_in_url if k.strip()]
        strict_keywords = bool(params.get("strict_keywords", False))

        if query_raw:
            if strict_keywords:
                whole = query_raw.lower().strip()
                if whole and whole not in keywords:
                    keywords.append(whole)
            else:
                q_tokens = self._extract_keywords_from_query(query_raw)
                for qt in q_tokens:
                    if qt not in keywords:
                        keywords.append(qt)

        # --- 5. Helper Functions ---
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

        def _augment_search_query(q: str, mode: str, required_sites: list[str]) -> str:
            sq = q.strip()
            site_clauses = []
            for raw in required_sites or []:
                s = (raw or "").strip().lower()
                if not s:
                    continue
                if "://" in s:
                    s = s.split("://", 1)[1]
                s = s.split("/", 1)[0].lstrip(".")
                if not s:
                    continue
                site_clauses.append(f"site:{s}")

            if site_clauses:
                sites_expr = " OR ".join(site_clauses)
                sq = f"({sites_expr}) {sq}" if sq else f"({sites_expr})"

            q_lower = sq.lower()
            if mode == "media":
                media_hint = "(mp3 OR flac OR m4a OR ogg)"
                if not any(x in q_lower for x in ["mp3", "flac", "m4a", "ogg"]):
                    sq = f"{sq} {media_hint}".strip()
            elif mode == "docs":
                if "filetype:pdf" not in q_lower:
                    sq = f"{sq} filetype:pdf".strip()
            return sq

        # --- 6. Search vs URL-list triage (sitemap/xml/etc.) ---
        candidate_pages: List[str] = []
        direct_asset_urls: List[str] = []
        queries_to_run: List[str] = []
        skip_search_engine = False

        # If subpipeline (e.g., sitemap/xml) returned a URL list:
        if isinstance(pipeline_result, list) and pipeline_result:
            first_item = str(pipeline_result[0]).strip()
            if first_item.startswith("http://") or first_item.startswith("https://"):
                skip_search_engine = True
                queries_to_run = ["<URL list>"]

                unique_urls = [
                    str(u).strip() for u in pipeline_result if str(u).strip()
                ]
                unique_urls = list(dict.fromkeys(unique_urls))  # preserve order

                for u in unique_urls:
                    if not _allowed_by_required_sites(u):
                        continue

                    path = _clean_path(u)

                    # 1) Direct asset match (e.g., .mp3/.flac/.pdf/etc.)
                    if any(path.endswith(ext) for ext in targets):
                        if _term_overlap_ok(u):
                            direct_asset_urls.append(u)
                        continue

                    # 2) Junk static assets we never want to crawl
                    if any(path.endswith(ext) for ext in self.IGNORED_EXTENSIONS):
                        continue

                    # 3) HTML-like pages worth scanning
                    if not keywords or _term_overlap_ok(u):
                        candidate_pages.append(u)

                candidate_pages = candidate_pages[:max_pages_total]

        # If we're *not* using a URL-list, fallback to search-engine queries
        if not skip_search_engine:
            if isinstance(pipeline_result, str) and pipeline_result.strip():
                queries_to_run = [pipeline_result.strip()]
            elif isinstance(pipeline_result, list):
                # List of non-URL strings (e.g. from a prompt_query sub-block)
                for qv in pipeline_result:
                    qv_s = str(qv).strip()
                    if qv_s:
                        queries_to_run.append(qv_s)
            else:
                if query_raw:
                    queries_to_run = [query_raw]

            if not queries_to_run and query_raw:
                queries_to_run = [query_raw]

        # Canonical query string (for display only)
        query = queries_to_run[0] if queries_to_run else query_raw

        # --- 7. Search-based discovery (if not URL-list mode) ---
        if not skip_search_engine and queries_to_run:
            ua = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/LinkTracker"
            seen_search_urls: set[str] = set()

            for q in queries_to_run:
                search_q = _augment_search_query(q, mode, required_sites)

                if engine == "google_cse":
                    raw_pages = self._search_google_cse(search_q, search_results_cap, timeout)
                else:
                    raw_pages = self._search_duckduckgo(search_q, search_results_cap, ua, timeout)

                for u in raw_pages:
                    if u in seen_search_urls:
                        continue
                    if _allowed_by_required_sites(u) or not required_sites:
                        candidate_pages.append(u)
                        seen_search_urls.add(u)
                    if len(candidate_pages) >= max_pages_total:
                        break
                if len(candidate_pages) >= max_pages_total:
                    break

        # --- 8. Crawl / Page Scan ---
        from concurrent.futures import ThreadPoolExecutor, as_completed

        found_assets: List[Dict[str, Any]] = []
        seen_asset_urls: set[str] = set()  # dedupe assets
        visited_pages: set[str] = set()  # dedupe pages

        log: List[str] = []
        all_js_links: List[Dict[str, str]] = []
        all_network_links: List[Dict[str, str]] = []

        # 8a. First, harvest direct assets from URL list (sitemap/xml/etc.)
        if direct_asset_urls:
            session_direct = requests.Session()
            session_direct.headers.update(
                {
                    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                                  "PromptChat/LinkTracker"
                }
            )

            for u in direct_asset_urls:
                if u in seen_asset_urls:
                    continue
                seen_asset_urls.add(u)

                status = "unverified"
                size = "?"
                if verify_links:
                    try:
                        h = session_direct.head(u, allow_redirects=True, timeout=3)
                        if h.status_code == 200:
                            status = "200 OK"
                            cl = h.headers.get("Content-Length")
                            if cl:
                                size = f"{int(cl) // 1024} KB"
                        else:
                            status = f"Dead ({h.status_code})"
                    except Exception:
                        status = "Timeout/Error"

                if not verify_links or status == "200 OK":
                    filename = _clean_path(u).rsplit("/", 1)[-1] or "[asset]"
                    filename = filename[:100]
                    found_assets.append(
                        {
                            "text": filename,
                            "url": u,
                            "source": "<urls>",
                            "size": size,
                            "status": status,
                        }
                    )

        # 8b. Page-worker for BFS
        def _process_page(page_url: str, depth: int) -> Dict[str, Any]:
            import requests
            from bs4 import BeautifulSoup

            local_log: List[str] = []
            local_js_links: List[Dict[str, str]] = []
            local_network_links: List[Dict[str, str]] = []
            local_assets: List[Dict[str, Any]] = []
            next_pages: List[str] = []

            session = requests.Session()
            session.headers.update(
                {
                    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                                  "PromptChat/LinkTracker"
                }
            )

            try:
                links_on_page: List[Dict[str, str]] = []
                html = ""

                sniff_items: List[Dict[str, str]] = []
                if use_network_sniff:
                    sniff_html, sniff_items = self._fetch_page_with_network_sniff(
                        page_url,
                        timeout,
                        session.headers["User-Agent"],
                        local_log,
                        targets,
                    )
                    html = sniff_html or html

                    for si in sniff_items:
                        local_network_links.append(
                            {
                                "page": page_url,
                                "url": si.get("url", ""),
                                "text": si.get("text", ""),
                                "tag": si.get("tag", "network_sniff"),
                                "size": si.get("size", "?"),
                            }
                        )

                if use_js:
                    js_html, js_links = self._fetch_page_with_js(
                        page_url,
                        timeout,
                        session.headers["User-Agent"],
                        local_log,
                    )
                    if js_html:
                        html = js_html
                    links_on_page.extend(js_links)

                    for jl in js_links:
                        local_js_links.append(
                            {
                                "page": page_url,
                                "url": jl.get("url", ""),
                                "text": jl.get("text", ""),
                                "tag": jl.get("tag", ""),
                            }
                        )

                    if not html:
                        try:
                            html = self._fetch_page_html_plain(
                                session, page_url, timeout
                            )
                        except Exception as e:
                            local_log.append(
                                f"Error fetching {page_url} (fallback): {e}"
                            )
                            if not links_on_page and not sniff_items:
                                return {
                                    "page": page_url,
                                    "assets": local_assets,
                                    "next_pages": next_pages,
                                    "js_links": local_js_links,
                                    "network_links": local_network_links,
                                    "log": local_log,
                                }
                    soup = BeautifulSoup(html or "", "html.parser")
                else:
                    if not html:
                        try:
                            html = self._fetch_page_html_plain(
                                session, page_url, timeout
                            )
                        except Exception as e:
                            local_log.append(f"Error fetching {page_url}: {e}")
                            return {
                                "page": page_url,
                                "assets": local_assets,
                                "next_pages": next_pages,
                                "js_links": local_js_links,
                                "network_links": local_network_links,
                                "log": local_log,
                            }
                    soup = BeautifulSoup(html or "", "html.parser")

                # Plain HTML <a> links (bounded)
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

                # ---- Scan DOM links for assets ----
                for link in links_on_page:
                    raw_link = link["url"]
                    full_url = urljoin(page_url, raw_link)
                    parsed = urlparse(full_url)
                    path = parsed.path.lower()

                    if not any(path.endswith(ext) for ext in targets):
                        continue

                    if keywords:
                        link_text = (link.get("text") or "").lower()
                        url_text = full_url.lower().replace("%20", " ")
                        haystack = link_text + " " + url_text
                        if not _term_overlap_ok(haystack):
                            continue

                    if not _allowed_by_required_sites(full_url):
                        continue

                    status = "unverified"
                    size = "?"
                    if verify_links:
                        try:
                            h = session.head(
                                full_url, allow_redirects=True, timeout=3
                            )
                            if h.status_code == 200:
                                status = "200 OK"
                                cl = h.headers.get("Content-Length")
                                if cl:
                                    size = f"{int(cl) // 1024} KB"
                            else:
                                status = f"Dead ({h.status_code})"
                        except Exception:
                            status = "Timeout/Error"

                    if not verify_links or status == "200 OK":
                        display_text = link.get("text", "") or path.split("/")[-1]
                        display_text = display_text[:100]
                        local_assets.append(
                            {
                                "text": display_text,
                                "url": full_url,
                                "source": page_url,
                                "size": size,
                                "status": status,
                            }
                        )

                # ---- Network-sniffed assets ----
                if sniff_items:
                    for item in sniff_items:
                        full_url = item.get("url")
                        if not full_url:
                            continue
                        if not _allowed_by_required_sites(full_url):
                            continue

                        if keywords:
                            link_text = (item.get("text") or "").lower()
                            url_text = full_url.lower().replace("%20", " ")
                            haystack = link_text + " " + url_text
                            if not _term_overlap_ok(haystack):
                                continue

                        status = "sniffed"
                        size = item.get("size") or "?"
                        if verify_links:
                            try:
                                h = session.head(
                                    full_url, allow_redirects=True, timeout=3
                                )
                                if h.status_code == 200:
                                    status = "200 OK"
                                    cl = h.headers.get("Content-Length")
                                    if cl:
                                        size = f"{int(cl) // 1024} KB"
                                else:
                                    status = f"Dead ({h.status_code})"
                            except Exception:
                                status = "Timeout/Error"

                        if not verify_links or status == "200 OK":
                            display_text = (
                                    item.get("text")
                                    or full_url.rsplit("/", 1)[-1]
                                    or "[network asset]"
                            )
                            display_text = display_text[:100]
                            local_assets.append(
                                {
                                    "text": display_text,
                                    "url": full_url,
                                    "source": page_url,
                                    "size": size,
                                    "status": status,
                                }
                            )

                # ---- Enqueue next-level pages (HTML-like, not assets) ----
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

                        if keywords:
                            haystack = (link.get("text") or "") + " " + full_url
                            if not _term_overlap_ok(haystack):
                                continue

                        next_pages.append(full_url)

            except Exception as e:
                local_log.append(f"Error scanning {page_url}: {e}")

            return {
                "page": page_url,
                "assets": local_assets,
                "next_pages": next_pages,
                "js_links": local_js_links,
                "network_links": local_network_links,
                "log": local_log,
            }

        # BFS frontier: start from candidate pages at depth 0
        frontier: List[str] = []
        for u in candidate_pages:
            if _allowed_by_required_sites(u):
                frontier.append(u)
            elif not required_sites:
                frontier.append(u)

        frontier = frontier[:max_pages_total]

        current_depth = 0
        while frontier and current_depth <= max_depth and len(visited_pages) < max_pages_total:
            remaining_slots = max_pages_total - len(visited_pages)
            batch = [u for u in frontier if u not in visited_pages][:remaining_slots]
            if not batch:
                break

            next_frontier: List[str] = []
            max_workers = min(8, len(batch))

            with ThreadPoolExecutor(max_workers=max_workers) as ex:
                future_map = {
                    ex.submit(_process_page, url, current_depth): url
                    for url in batch
                }

                for fut in as_completed(future_map):
                    res = fut.result()
                    page_url = res["page"]
                    visited_pages.add(page_url)

                    log.extend(res["log"])
                    all_js_links.extend(res["js_links"])
                    all_network_links.extend(res["network_links"])

                    for asset in res["assets"]:
                        a_url = asset["url"]
                        if not a_url or a_url in seen_asset_urls:
                            continue
                        seen_asset_urls.add(a_url)
                        found_assets.append(asset)

                    for nxt in res["next_pages"]:
                        if nxt not in visited_pages:
                            next_frontier.append(nxt)

            current_depth += 1
            frontier = list(dict.fromkeys(next_frontier))

        # --- 9. Format Output ---
        from urllib.parse import urlparse as _urlparse

        if not found_assets:
            base_text = (
                f"### LinkTracker: No specific assets found.\n"
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
                    lines.append(
                        f"  - *Tag: <{tag}> | From page: {host}*"
                    )

            if return_network_sniff_links and all_network_links:
                lines.append("\n### All Network-Sniffed Assets (debug)\n")
                for nl in all_network_links:
                    host = (
                        _urlparse(nl["page"]).netloc if nl.get("page") else "(unknown)"
                    )
                    url = nl["url"]
                    text = nl["text"] or "(no text)"
                    tag = nl["tag"] or "network_sniff"
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
                f"  - *Size: {asset['size']} | Status: {asset['status']} | "
                f"Source: {_urlparse(asset['source']).netloc}*"
            )

        if return_all_js_links and all_js_links:
            lines.append("\n### All JS-Gathered Links (debug)\n")
            for jl in all_js_links:
                host = _urlparse(jl["page"]).netloc if jl.get("page") else "(unknown)"
                url = jl["url"]
                text = jl["text"] or "(no text)"
                tag = jl["tag"] or "a"
                lines.append(f"- **[{text}]({url})**")
                lines.append(
                    f"  - *Tag: <{tag}> | From page: {host}*"
                )

        if return_network_sniff_links and all_network_links:
            lines.append("\n### All Network-Sniffed Assets (debug)\n")
            for nl in all_network_links:
                host = _urlparse(nl["page"]).netloc if nl.get("page") else "(unknown)"
                url = nl["url"]
                text = nl["text"] or "(no text)"
                tag = nl["tag"] or "network_sniff"
                size = nl.get("size", "?")
                lines.append(f"- **[{text}]({url})**")
                lines.append(
                    f"  - *Tag: <{tag}> | From page: {host} | Size: {size}*"
                )

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
            "log": log,
            "queries_run": queries_to_run,
        }

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "rare aphex twin interview",
            "timeout": 5,
            "mode": "docs",  # media, docs, archives, custom
            "scan_limit": 5,
            "search_results_cap": 256,
            "verify": True,
            "extensions": ".pdf,.txt",  # optional overrides
            "url_keywords": "archive,download",  # optional filter
            "engine": "duckduckgo",  # or: google_cse
            "site_require": "",  # e.g. 'archive.org,ca.archive.org'
            "use_js": False,  # Enable Playwright JS rendering
            "return_all_js_links": False,
            "max_links_per_page": 500,
            "strict_keywords": False,
            "use_network_sniff": False,
            "return_network_sniff_links": False,
            "min_term_overlap": 1,  # require at least N keyword hits in URL/text
            "max_depth": 0,  # 0 = search pages only, 1 = follow their links, etc.
            "max_pages_total": 32,  # global safety cap on pages crawled
            "subpipeline": "",  # e.g. 'prompt_query|sitemap' or 'prompt_query|xml'
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

# ======================= VideoLinkTrackerBlock =============================

@dataclass
class VideoLinkTrackerBlock(BaseBlock):
    """
    Bounded, smarter video crawler.

    Modes via 'source' param:
      • source="search"  (default): run web search to find hub pages.
      • source="payload": parse input payload (e.g., WebCorpus output) for hub URLs.

    Features:
      • DuckDuckGo / Google CSE search with optional site: filters.
      • Optional JS rendering via Playwright (use_js=true).
      • Optional Playwright network sniffing (use_network_sniff=true) to capture
        video URLs seen in real network responses.
      • Ad / tracking filters to skip obvious junk.
      • Optional shallow second-level crawl (controlled by max_depth).
      • Stream-aware detection (.mp4, .m3u8, 'videoplayback', etc.)
      • Optional HEAD-based Content-Type sniffing (smart_sniff).
      • Hard safety limits (max_pages_total, max_assets).
      • NEW: min_term_overlap:
          - videotracker.min_term_overlap=N
          Require at least N distinct keyword tokens (from the query) to appear
          in the URL/text haystack. For "lil uzi vert", setting
          min_term_overlap=2 or 3 biases strongly to pages *about* Lil Uzi Vert.
      • NEW: subpipeline (optional):
          - videotracker.subpipeline="prompt_query"
          - videotracker.subpipeline="prompt_query|sitemap"
          - videotracker.subpipeline="prompt_query|xml"
        If the final sub-block returns:
          • List[str] of URLs → treat as hub pages to crawl (sitemap/xml).
          • List[str] of queries → run search for each (prompt_query).
    """

    # --- Constants --------------------------------------------------------
    VIDEO_EXTENSIONS = {
        ".mp4", ".webm", ".mkv", ".mov", ".avi", ".flv", ".wmv", ".m3u8", ".mpd",
    }
    VIDEO_PLATFORMS = {
        "youtube.com/embed/", "youtube-nocookie.com/embed/",
        "player.vimeo.com/video/", "dailymotion.com/embed/video/",
        "rumble.com/embed/", "v.redd.it", "/player.html", "/player/",
    }
    STREAM_HINT_KEYWORDS = {
        "videoplayback", "hls", "dash", "manifest", "master.m3u8",
        "index.m3u8", "playlist.m3u8",
    }
    VIDEO_CONTENT_PREFIXES = {"video/"}
    HLS_CONTENT_TYPES = {"application/x-mpegurl", "application/vnd.apple.mpegurl"}
    DASH_CONTENT_TYPES = {"application/dash+xml"}
    AD_HOST_SUBSTRINGS = {
        "doubleclick", "googlesyndication", "adservice", "adserver",
        "adsystem", "adnxs", "trk.", "tracking", "analytics",
        "metrics", "scorecardresearch",
    }
    AD_PATH_KEYWORDS = {
        "/ads/", "/adserver/", "/banner/", "/banners/", "/promo/",
        "/promotions/", "/tracking/", "/click/", "/impression", "/pixel",
    }
    JUNK_FILENAME_KEYWORDS = {
        "sprite", "icon", "favicon", "logo", "tracking",
        "pixel", "blank", "placeholder",
    }

    # ------------------------------------------------------------------ #
    # Search helpers
    # ------------------------------------------------------------------ #
    def _search_duckduckgo(self, q: str, n: int, ua: str, timeout: float) -> List[str]:
        pages: List[str] = []
        try:
            from ddgs import DDGS
            with DDGS() as ddgs:
                for r in ddgs.text(q, max_results=n, safesearch="off"):
                    u = r.get("href") or r.get("url")
                    if u:
                        pages.append(u)
            if pages:
                return pages
        except Exception:
            pass

        # HTML fallback
        try:
            import requests
            from bs4 import BeautifulSoup
            from urllib.parse import unquote

            r = requests.get(
                "https://html.duckduckgo.com/html/",
                params={"q": q},
                headers={"User-Agent": ua},
                timeout=timeout,
            )
            r.raise_for_status()
            soup = BeautifulSoup(r.text, "html.parser")
            for a in soup.select(".result__a"):
                href = a.get("href")
                if href and "uddg=" in href:
                    href = unquote(href.split("uddg=")[1].split("&")[0])
                    pages.append(href)
        except Exception:
            pass

        return pages

    def _search_google_cse(self, q: str, n: int, timeout: float) -> List[str]:
        import os
        import requests

        cx = os.environ.get("GOOGLE_CSE_ID")
        key = os.environ.get("GOOGLE_API_KEY")
        if not (cx and key):
            return []

        out: List[str] = []
        try:
            r = requests.get(
                "https://www.googleapis.com/customsearch/v1",
                params={"q": q, "cx": cx, "key": key, "num": min(10, n)},
                timeout=timeout,
            )
            if r.status_code != 200:
                return []
            data = r.json()
            for item in (data.get("items") or []):
                u = item.get("link")
                if u:
                    out.append(u)
            return out[:n]
        except Exception:
            return out[:n]

    # ------------------------------------------------------------------ #
    # Keyword / URL heuristics
    # ------------------------------------------------------------------ #
    def _get_keywords_from_query(self, query: str) -> List[str]:
        try:
            stops = _STOPWORDS
        except NameError:
            stops = {"the", "a", "an", "is", "to", "for", "of"}
        tokens = [
            t
            for t in re.findall(r"[A-Za-z0-9][A-Za-z0-9_\-]+", query.lower())
            if t not in stops and len(t) > 2
        ]
        # preserve order, dedupe
        return list(dict.fromkeys(tokens))

    def _clean_domain(self, u: str) -> str:
        try:
            netloc = urlparse(u).netloc.lower()
            return netloc.split(":")[0]
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

    def _is_probable_video_url(self, full_url: str, path: str, url_lower: str) -> bool:
        if any(path.endswith(ext) for ext in self.VIDEO_EXTENSIONS):
            return True
        if path.endswith(".m3u8") or path.endswith(".mpd"):
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
        content_hints = [
            "/details/", "/video/", "/videos/", "/watch/",
            "/title/", "/entry/", "/post/",
        ]
        return any(h in p for h in content_hints)

    # ------------------------------------------------------------------ #
    # Fetch helpers
    # ------------------------------------------------------------------ #
    def _fetch_page_html_plain(self, session, page_url: str, timeout: float) -> str:
        import requests
        resp = session.get(page_url, timeout=timeout)
        resp.raise_for_status()
        return resp.text

    def _fetch_page_with_js(
        self,
        pw_context,              # BrowserContext (type hinted via __future__ annotations)
        page_url: str,
        timeout: float,
        log: List[str],
        use_network_sniff: bool = False,
        sniff_sink: Optional[List[Dict[str, str]]] = None,
    ) -> Tuple[str, List[Dict[str, str]]]:
        """
        Use Playwright to:
          • Render the page.
          • Optionally sniff network responses for video URLs.
          • Collect DOM links (video, a[href], iframe, embed, etc.).

        Returns (html, links) where links is a list of {url,text,tag}.
        """
        html = ""
        links: List[Dict[str, str]] = []
        page = None
        from urllib.parse import urlparse as _urlparse_local  # avoid shadowing

        try:
            page = pw_context.new_page()

            if use_network_sniff:
                seen_sniff = set()

                def handle_response(response):
                    try:
                        url = response.url
                        if not url or url.startswith("blob:"):
                            return
                        if url in seen_sniff:
                            return

                        parsed = _urlparse_local(url)
                        netloc = parsed.netloc
                        path = parsed.path or "/"
                        url_lower = url.lower()

                        # Skip obvious ad/tracking hosts
                        if self._looks_like_ad(netloc, path):
                            return

                        # Heuristic: is this probably video?
                        is_video = self._is_probable_video_url(url, path.lower(), url_lower)
                        ctype = (response.headers.get("content-type") or "").lower()

                        if not is_video and ctype:
                            if any(ctype.startswith(pfx) for pfx in self.VIDEO_CONTENT_PREFIXES):
                                is_video = True
                            if ctype in self.HLS_CONTENT_TYPES or ctype in self.DASH_CONTENT_TYPES:
                                is_video = True

                        if not is_video:
                            return

                        seen_sniff.add(url)

                        sniff_link = {
                            "url": url,
                            "text": "[Network Video]",
                            "tag": "network_sniff",
                        }
                        links.append(sniff_link)

                        if sniff_sink is not None:
                            sniff_sink.append(
                                {
                                    "page": page_url,
                                    "url": url,
                                    "text": "[Network Video]",
                                    "tag": "network_sniff",
                                    "content_type": ctype,
                                }
                            )
                    except Exception:
                        return

                page.on("response", handle_response)

            js_timeout_ms = int(min(timeout, 10.0) * 1000)
            page.goto(page_url, wait_until="domcontentloaded", timeout=js_timeout_ms)
            html = page.content()

            raw_links = page.evaluate(
                """
                () => {
                  const out = [];
                  const seen = new Set();

                  function push(el, url, tag) {
                    if (!url || url.startsWith('blob:') || seen.has(url)) return;
                    seen.add(url);
                    const text = (el.innerText || el.textContent || el.title || "").trim();
                    out.push({ url, text, tag });
                  }

                  const selectors = [
                    "video[src]",
                    "video source[src]",
                    "source[src]",
                    "a[href]",
                    "iframe[src]",
                    "embed[src]"
                  ];

                  for (const sel of selectors) {
                    document.querySelectorAll(sel).forEach(el => {
                      let url = el.href || el.currentSrc || el.src;
                      if (!url && el.getAttribute) {
                        url = el.getAttribute("src") || el.getAttribute("href");
                      }
                      push(el, url, el.tagName.toLowerCase());
                    });
                  }

                  return out;
                }
                """
            ) or []

            for item in raw_links:
                url = item.get("url")
                if not url:
                    continue
                links.append(
                    {
                        "url": url,
                        "text": (item.get("text") or "").strip(),
                        "tag": item.get("tag") or "a",
                    }
                )

            log.append(
                f"Rendered JS DOM + gathered {len(links)} JS/network links for: {page_url}"
            )
        except Exception as e:
            log.append(f"Playwright error on {page_url}: {e}")
        finally:
            if page and not page.is_closed():
                page.close()

        return html, links

    # ------------------------------------------------------------------ #
    # Main execution
    # ------------------------------------------------------------------ #
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import requests
        from bs4 import BeautifulSoup
        from urllib.parse import urlparse as _urlparse

        # --- Parameters & OPTIONAL subpipeline -----------------------------
        query_raw = str(params.get("query", "") or str(payload or "")).strip()
        source = str(params.get("source", "search")).lower()

        # NEW: optional subpipeline (prompt_query, sitemap, xml, etc.)
        subpipe_name = str(params.get("subpipeline", "") or "").strip()
        pipeline_urls: List[str] = []
        pipeline_queries: List[str] = []

        if subpipe_name:
            # Only run subpipeline if the parameter exists & is non-empty
            pr = self.run_sub_pipeline(
                initial_value=query_raw,
                pipeline_param_name="subpipeline",
                parent_params=params,
            )

            if isinstance(pr, list):
                for item in pr:
                    s = str(item or "").strip()
                    if not s:
                        continue
                    if s.startswith("http://") or s.startswith("https://"):
                        pipeline_urls.append(s)
                    else:
                        pipeline_queries.append(s)
            elif isinstance(pr, str):
                # Allow subpipeline to rewrite the query string if it wants
                s = pr.strip()
                if s:
                    query_raw = s

        sites_raw = str(params.get("sites", "")).split(",")
        sites = [s.strip().lower() for s in sites_raw if s.strip()]
        global_mode = not sites
        if global_mode:
            sites = ["*"]

        scan_limit = int(params.get("scan_limit", 3))
        timeout = float(params.get("timeout", 8.0))
        ua = str(params.get("user_agent", "promptchat/VideoLinkTracker"))
        engine = str(params.get("engine", "duckduckgo")).lower()
        verify_links = bool(params.get("verify", False))
        use_js = bool(params.get("use_js", False))
        smart_sniff = bool(params.get("smart_sniff", False))
        return_all_js_links = bool(params.get("return_all_js_links", False))
        max_depth = int(params.get("max_depth", 0))
        child_page_limit = int(params.get("child_page_limit", 4))
        max_pages_total = int(params.get("max_pages_total", 20))
        max_links_per_page = int(params.get("max_links_per_page", 200))
        max_assets = int(params.get("max_assets", 100))

        # NEW: network-sniff toggles
        use_network_sniff = bool(params.get("use_network_sniff", False))
        return_network_sniff_links = bool(
            params.get("return_network_sniff_links", False)
        )

        # NEW: min_term_overlap
        min_term_overlap_raw = int(params.get("min_term_overlap", 1))
        min_term_overlap = max(1, min_term_overlap_raw)

        # Old behavior: only error if no query AND no subpipeline
        if not query_raw and source == "search" and not subpipe_name:
            return "", {
                "error": "VideoLinkTracker: No query provided for 'search' source."
            }

        # Keywords are always extracted from the *original* query text
        keywords = self._get_keywords_from_query(query_raw)
        log: List[str] = []
        found_assets: List[Dict[str, Any]] = []
        seen_urls: set[str] = set()
        visited_pages: set[str] = set()
        pages_to_crawl_tuples: List[Tuple[str, int]] = []  # (url, depth)
        pages_processed = 0
        all_js_links: List[Dict[str, str]] = []
        all_network_links: List[Dict[str, str]] = []  # network-sniff hits

        session = requests.Session()
        session.headers.update({"User-Agent": ua})

        def _allowed_by_required_sites(u: str) -> bool:
            if global_mode or not sites or sites == ["*"]:
                return True
            d = self._clean_domain(u)
            return any(req in d for req in sites)

        def _term_overlap_ok(haystack: str) -> bool:
            """
            Require at least min_term_overlap distinct keyword hits in haystack.
            ex: query 'lil uzi vert' → tokens: ['lil','uzi','vert'].
            With min_term_overlap=2, any two of those must appear in URL/text.
            """
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

        # --- Core crawl function (per page) ------------------------
        def crawl_page(
            page_url: str,
            depth_left: int,
            pw_context: Optional[Any],  # BrowserContext or None
        ) -> List[str]:
            nonlocal pages_processed

            page_child_candidates: List[str] = []

            if page_url in visited_pages or depth_left < 0:
                return page_child_candidates
            if pages_processed >= max_pages_total or len(found_assets) >= max_assets:
                return page_child_candidates

            visited_pages.add(page_url)
            pages_processed += 1

            links_on_page: List[Dict[str, str]] = []

            try:
                if use_js and pw_context:
                    # Playwright + optional network sniff
                    html, js_links = self._fetch_page_with_js(
                        pw_context,
                        page_url,
                        timeout,
                        log,
                        use_network_sniff=use_network_sniff,
                        sniff_sink=all_network_links,
                    )
                    links_on_page.extend(js_links)
                    for jl in js_links:
                        all_js_links.append({**jl, "page": page_url})

                    if not html:
                        try:
                            html = self._fetch_page_html_plain(session, page_url, timeout)
                        except Exception as e:
                            log.append(f"Error fetching {page_url} (fallback): {e}")
                            if not links_on_page:
                                return page_child_candidates
                    soup = BeautifulSoup(html, "html.parser")
                else:
                    html = self._fetch_page_html_plain(session, page_url, timeout)
                    soup = BeautifulSoup(html, "html.parser")
            except Exception as e:
                log.append(f"Error fetching/parsing {page_url}: {e}")
                return page_child_candidates

            # Add <a> links
            link_count = 0
            for a in soup.find_all("a", href=True):
                links_on_page.append(
                    {"url": a["href"], "text": a.get_text(strip=True), "tag": "a"}
                )
                link_count += 1
                if link_count >= max_links_per_page:
                    break

            # Add <video> / <source> links if room
            if link_count < max_links_per_page:
                for v in soup.find_all("video"):
                    if v.get("src"):
                        links_on_page.append(
                            {
                                "url": v["src"],
                                "text": v.get("title", ""),
                                "tag": "video",
                            }
                        )
                    for s in v.find_all("source", src=True):
                        links_on_page.append(
                            {
                                "url": s["src"],
                                "text": s.get("title", ""),
                                "tag": "source",
                            }
                        )

            # --- Filter / classify links on this page ----------------
            for link in links_on_page:
                if len(found_assets) >= max_assets:
                    break
                try:
                    full_url = urljoin(page_url, link["url"])
                    parsed = urlparse(full_url)
                    netloc = parsed.netloc
                    path = parsed.path or "/"
                    url_lower = full_url.lower()

                    if self._looks_like_ad(netloc, path):
                        continue

                    head_done = False
                    status = "unverified"
                    content_type = None

                    is_video = self._is_probable_video_url(
                        full_url, path.lower(), url_lower
                    )

                    # Child-page candidates for deeper crawl (non-video content pages)
                    if (not is_video) and depth_left > 0:
                        if self._is_content_child_candidate(full_url, netloc, path):
                            if (
                                full_url not in visited_pages
                                and len(page_child_candidates) < child_page_limit
                            ):
                                page_child_candidates.append(full_url)

                    # Optional HEAD-based sniff
                    if (not is_video) and smart_sniff:
                        try:
                            h = session.head(
                                full_url, allow_redirects=True, timeout=3
                            )
                            head_done = True
                            status = (
                                f"{h.status_code} OK"
                                if h.status_code == 200
                                else f"Dead ({h.status_code})"
                            )
                            content_type = (h.headers.get("Content-Type") or "").lower()
                            if any(
                                content_type.startswith(pfx)
                                for pfx in self.VIDEO_CONTENT_PREFIXES
                            ):
                                is_video = True
                            if (
                                content_type in self.HLS_CONTENT_TYPES
                                or content_type in self.DASH_CONTENT_TYPES
                            ):
                                is_video = True
                        except Exception:
                            status = "Timeout/Error"

                    if not is_video:
                        continue
                    if full_url in seen_urls:
                        continue

                    haystack = (
                        (link.get("text", "") or "") + " " + full_url
                    ).lower().replace("%20", " ")

                    # NEW: min_term_overlap-based filtering
                    if keywords and not _term_overlap_ok(haystack):
                        continue

                    if not _allowed_by_required_sites(full_url):
                        continue

                    seen_urls.add(full_url)

                    if verify_links and not head_done:
                        try:
                            h = session.head(
                                full_url, allow_redirects=True, timeout=3
                            )
                            status = (
                                f"{h.status_code} OK"
                                if h.status_code == 200
                                else f"Dead ({h.status_code})"
                            )
                        except Exception:
                            status = "Timeout/Error"

                    if (not verify_links) or "OK" in status:
                        found_assets.append(
                            {
                                "text": (link.get("text", "") or path.split("/")[-1])[
                                    :100
                                ],
                                "url": full_url,
                                "source_page": page_url,
                                "tag": link["tag"],
                                "status": status,
                            }
                        )
                except Exception:
                    continue

            return page_child_candidates

        # ------------------------------------------------------------------
        # Step 1: Discovery (Populate Crawl Queue)
        # ------------------------------------------------------------------

        # NEW: if sitemap/xml subpipeline returned URLs, treat them as hub pages
        if pipeline_urls:
            limited = pipeline_urls[:scan_limit] if scan_limit > 0 else pipeline_urls
            for u in limited:
                if _allowed_by_required_sites(u):
                    pages_to_crawl_tuples.append((u, 0))

        if source == "payload":
            log.append("Reading hub pages from payload...")

            payload_str = str(payload)
            urls_from_payload = re.findall(
                r"#.*?(https?://[^\s<\]]+)", payload_str
            )
            urls_from_payload.extend(
                re.findall(r"\[.*?\]\((https?://[^\s)]+)\)", payload_str)
            )
            if not urls_from_payload:
                urls_from_payload.extend(
                    re.findall(r"\b(https?://[^\s<\]]+)\b", payload_str)
                )

            seen_payload_urls = set()
            candidate_pages: List[str] = []

            for u in urls_from_payload:
                u = u.strip().rstrip(")")
                if u not in seen_payload_urls:
                    if _allowed_by_required_sites(u):
                        candidate_pages.append(u)
                        seen_payload_urls.add(u)

            log.append(f"Found {len(candidate_pages)} unique URLs in payload.")
            if scan_limit > 0:
                candidate_pages = candidate_pages[:scan_limit]

            for url in candidate_pages:
                pages_to_crawl_tuples.append((url, 0))

        else:  # source == "search"
            log.append("Finding hub pages via built-in search...")

            # Queries from prompt_query subpipeline OR fallback to raw query
            search_queries: List[str] = []
            if pipeline_queries:
                search_queries = pipeline_queries
            elif query_raw:
                search_queries = [query_raw]

            if not search_queries and not pipeline_urls:
                log.append("No query or subpipeline-derived search queries; skipping search.")
            else:
                for site_domain in sites:
                    for q in search_queries:
                        if not q:
                            continue
                        search_q = (
                            f"site:{site_domain} {q}"
                            if not global_mode
                            else q
                        )
                        log.append(f"Searching {engine} for: {search_q}")

                        if engine == "google_cse":
                            hub_pages = self._search_google_cse(
                                search_q, scan_limit, timeout
                            )
                        else:
                            hub_pages = self._search_duckduckgo(
                                search_q, scan_limit, ua, timeout
                            )

                        if not hub_pages:
                            log.append(f"No hub pages found for: {search_q}")
                        else:
                            for page_url in hub_pages[:scan_limit]:
                                if page_url not in visited_pages:
                                    pages_to_crawl_tuples.append((page_url, 0))

                        if global_mode:
                            # For global mode, we only need to run once per query
                            break

        # ------------------------------------------------------------------
        # Step 2: Deep Scan (Wrapper around crawl_page)
        # ------------------------------------------------------------------
        try:
            if use_js:
                from playwright.sync_api import sync_playwright

                with sync_playwright() as p:
                    browser = p.firefox.launch(headless=True)
                    pw_context = browser.new_context(user_agent=ua)

                    while (
                        pages_to_crawl_tuples
                        and pages_processed < max_pages_total
                        and len(found_assets) < max_assets
                    ):
                        page_url, depth = pages_to_crawl_tuples.pop(0)
                        if page_url in visited_pages:
                            continue

                        child_candidates = crawl_page(page_url, depth, pw_context)

                        if depth < max_depth:
                            for child_url in child_candidates:
                                if (
                                    child_url not in visited_pages
                                    and len(pages_to_crawl_tuples)
                                    < (max_pages_total - pages_processed)
                                ):
                                    pages_to_crawl_tuples.append(
                                        (child_url, depth + 1)
                                    )

                    browser.close()
            else:
                # Run without Playwright context
                while (
                    pages_to_crawl_tuples
                    and pages_processed < max_pages_total
                    and len(found_assets) < max_assets
                ):
                    page_url, depth = pages_to_crawl_tuples.pop(0)
                    if page_url in visited_pages:
                        continue

                    child_candidates = crawl_page(page_url, depth, None)

                    if depth < max_depth:
                        for child_url in child_candidates:
                            if (
                                child_url not in visited_pages
                                and len(pages_to_crawl_tuples)
                                < (max_pages_total - pages_processed)
                            ):
                                pages_to_crawl_tuples.append(
                                    (child_url, depth + 1)
                                )
        except Exception as e:
            log.append(f"FATAL CRAWL ERROR: {e}")
            if "browser" in locals():
                try:
                    if locals()["browser"].is_connected():
                        locals()["browser"].close()
                except Exception:
                    pass

        # ------------------------------------------------------------------
        # Step 3: Format Output
        # ------------------------------------------------------------------
        display_sites = (
            "[payload]"
            if source == "payload"
            else ("[all]" if global_mode else ", ".join(sites))
        )

        # Display query: prefer raw, otherwise first prompt_query variant
        display_query = query_raw
        if not display_query and pipeline_queries:
            display_query = pipeline_queries[0]

        if not found_assets:
            base_text = (
                f"### VideoTracker: No video assets found.\n"
                f"Source: {source} | Scanned {display_sites} for query: {display_query}\n"
                f"Required keywords: {keywords}\n"
                f"min_term_overlap: {min_term_overlap}\n"
                f"Log: {log}\n"
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
                    lines.append(
                        f"- <{jl.get('tag')}> "
                        f"[{jl.get('text')}]({jl.get('url')}) @ {host}"
                    )

            if return_network_sniff_links and all_network_links:
                lines.append("\n### All Network-Sniffed Video Links (debug)\n")
                for nl in all_network_links:
                    host = (
                        _urlparse(nl.get("page", "")).netloc
                        if nl.get("page")
                        else "(unknown)"
                    )
                    lines.append(
                        f"- <{nl.get('tag','network_sniff')}> "
                        f"[{nl.get('text')}]({nl.get('url')}) @ {host} "
                        f"(ctype={nl.get('content_type','?')})"
                    )

            return "\n".join(lines), {
                "count": 0,
                "keywords_used": keywords,
                "min_term_overlap": min_term_overlap,
                "sites": [] if global_mode else sites,
                "global_mode": global_mode,
                "log": log,
                "js_links": all_js_links,
                "network_sniff_links": all_network_links,
                "source": source,
                "subpipeline": subpipe_name,
            }

        # Sort assets for nicer display (shorter URLs first)
        found_assets.sort(key=lambda a: len(a["url"]))

        lines = [f"### VideoTracker Found {len(found_assets)} Assets"]
        lines.append(
            f"_Source: {source} | Query: {display_query} | Sites: {display_sites} | "
            f"Keywords: {keywords} | min_term_overlap: {min_term_overlap} | "
            f"Pages: {pages_processed}_"
        )
        lines.append("")

        for asset in found_assets:
            lines.append(f"- **[{asset['text']}]({asset['url']})**")
            lines.append(
                f"  - *Tag: <{asset['tag']}> | "
                f"Source: {_urlparse(asset['source_page']).netloc} | "
                f"Status: {asset['status']}*"
            )

        if return_all_js_links and all_js_links:
            lines.append("\n### All JS-Gathered Links (debug)\n")
            for jl in all_js_links:
                host = (
                    _urlparse(jl["page"]).netloc
                    if jl.get("page")
                    else "(unknown)"
                )
                lines.append(
                    f"- <{jl.get('tag')}> "
                    f"[{jl.get('text')}]({jl.get('url')}) @ {host}"
                )

        if return_network_sniff_links and all_network_links:
            lines.append("\n### All Network-Sniffed Video Links (debug)\n")
            for nl in all_network_links:
                host = (
                    _urlparse(nl.get("page", "")).netloc
                    if nl.get("page")
                    else "(unknown)"
                )
                lines.append(
                    f"- <{nl.get('tag','network_sniff')}> "
                    f"[{nl.get('text')}]({nl.get('url')}) @ {host} "
                    f"(ctype={nl.get('content_type','?')})"
                )

        return "\n".join(lines), {
            "found": len(found_assets),
            "scanned_sites": [] if global_mode else sites,
            "global_mode": global_mode,
            "assets": found_assets,
            "keywords_used": keywords,
            "min_term_overlap": min_term_overlap,
            "pages_processed": pages_processed,
            "log": log,
            "js_links": all_js_links,
            "network_sniff_links": all_network_links,
            "source": source,
            "subpipeline": subpipe_name,
        }

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "rare aphex twin interview",
            "mode": "docs",  # media, docs, archives, custom
            "scan_limit": 5,
            "search_results_cap": 256,
            "verify": True,
            "extensions": ".pdf,.txt",  # optional overrides
            "url_keywords": "archive,download",  # optional filter
            "engine": "duckduckgo",  # or: google_cse
            "site_require": "",  # e.g. 'archive.org,ca.archive.org'
            "use_js": False,  # Enable Playwright JS rendering
            "return_all_js_links": False,
            "max_links_per_page": 500,
            "strict_keywords": False,
            "use_network_sniff": False,
            "return_network_sniff_links": False,
            "min_term_overlap": 1,  # require at least N keyword hits in URL/text
            # NEW:
            "max_depth": 0,  # 0 = search pages only, 1 = follow their links, etc.
            "max_pages_total": 32,  # global safety cap on pages crawled
            "subpipeline": "",  # e.g. "prompt_query|sitemap" or "prompt_query|xml"
        }


# Register the block
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
