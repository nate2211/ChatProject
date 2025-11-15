# ========================================================
# ================  blocks.py  ===========================
# ========================================================
from __future__ import annotations

import functools
import html
import json
import re
from dataclasses import dataclass
from typing import Any, Dict, Tuple, List, Optional
import json as _json
import os as _os
import random
import time
from urllib.parse import urlencode

import feedparser
import requests
from datasets import load_dataset

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

def _markdown_list(items: List[Dict[str, Any]], title_key="title", url_key="link", extra_keys: Optional[List[str]] = None, limit: int = 10) -> str:
    out = []
    for row in items[:limit]:
        title = row.get(title_key) or row.get("name") or row.get("headline") or "(no title)"
        link  = row.get(url_key) or row.get("url") or row.get("href") or ""
        extra = []
        if extra_keys:
            for k in extra_keys:
                v = row.get(k)
                if v:
                    if isinstance(v, (dict, list)):
                        v = json.dumps(v, ensure_ascii=False)[:240] + "…" if len(json.dumps(v)) > 240 else json.dumps(v, ensure_ascii=False)
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
        pub  = (e.findtext("atom:updated", default="", namespaces=ns) or "").strip()
        if title or href:
            items.append({"title": title, "link": href, "published": pub})
    # RSS items
    for i in root.findall(".//item"):
        title = (i.findtext("title") or "").strip()
        link  = (i.findtext("link") or "").strip()
        pub   = (i.findtext("pubDate") or "").strip()
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
        print("[_get_hf_pipeline] ERROR: `transformers` or `torch` not installed. Please `pip install transformers torch`")
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
        print(f"[_get_hf_pipeline] Loading pipeline: task={task}, model={model or 'default'}, device={dev_str}... (this may take a moment on first run)")

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
    "the","a","an","and","or","but","if","on","in","to","for","from","of","at","by","with","as","is","are",
    "was","were","be","been","being","that","this","these","those","it","its","into","about","over","under",
    "up","down","out","so","than","then","too","very","can","cannot","could","should","would","will","may",
    "might","must","do","does","did","done","doing","have","has","had","having","not","no","yes","you","your",
    "yours","we","our","ours","they","their","theirs","i","me","my","mine","he","she","him","her","his","hers",
    "them","there","here","also","such","via"
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


# ---------------- Corpus (HF with timeout + wiki_api fallback) ----------------
@dataclass
class CorpusBlock(BaseBlock):
    """
    Resilient corpus puller:
      • provider = "wikimedia/wikipedia" (default) with short startup timeout
      • automatic fallback to provider = "wiki_api" (direct Wikipedia REST) on timeout/failure
      • streaming scan_limit supported for HF; python-side filtering
      • BM25-ish ranking, sentence extraction, auto-lexicon
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os, re, json, time, threading
        from math import log
        from typing import Iterable, Dict, List
        from itertools import islice

        provider    = str(params.get("provider", "wikimedia/wikipedia"))
        config      = str(params.get("config", "20231101.en"))
        split       = str(params.get("split", "train"))
        query       = str(params.get("query", "")).strip()
        neg         = [s.strip().lower() for s in str(params.get("neg", "")).split(",") if s.strip()]
        must_terms  = [s.strip().lower() for s in str(params.get("must_terms", "")).split(",") if s.strip()]
        sample      = int(params.get("sample", 50))
        columns     = params.get("columns", ["title", "text"])
        sep         = str(params.get("sep", "\n\n"))
        max_chars   = int(params.get("max_chars", 2800))
        cache_dir   = params.get("cache_dir")

        # ranking / extraction
        title_only   = bool(params.get("title_only", False))
        whole_word   = bool(params.get("whole_word", True))
        regex_query  = params.get("regex")
        top_k_docs   = int(params.get("top_k_docs", 5))
        top_k_sents  = int(params.get("top_k_sents", 12))
        sent_window  = int(params.get("sent_window", 1))
        min_doc_chars= int(params.get("min_doc_chars", 200))

        # streaming controls (HF only)
        streaming   = bool(params.get("streaming", False))
        scan_limit  = int(params.get("scan_limit", 200_000))
        hf_timeout  = float(params.get("hf_timeout_sec", 10.0))  # startup timeout for HF path
        set_hf_env  = bool(params.get("set_hf_env", True))

        # lexicon
        export_lexicon = bool(params.get("export_lexicon", True))
        lexicon_key    = str(params.get("lexicon_key", "corpus_lexicon"))
        inject_lexicon = bool(params.get("inject_lexicon", True))
        inject_context = bool(params.get("inject_context", True))
        lexicon_top_k  = int(params.get("lexicon_top_k", 40))
        lexicon_min_len= int(params.get("lexicon_min_len", 4))
        use_phrases    = bool(params.get("lexicon_phrases", True))

        # helpers
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

        q_pattern = re.compile(regex_query, re.IGNORECASE) if isinstance(regex_query, str) and regex_query.strip() else None

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
            """
            Minimal Wikipedia REST pull. Uses a small set of relevant titles when possible.
            """
            import requests
            session = requests.Session()
            session.headers.update({"User-Agent": "promptchat/mini-crawler"})
            titles: List[str] = []

            # Seed titles from the topic if it looks like a name; otherwise use search
            if re.search(r"raf\s+simons", topic, re.I):
                titles = ["Raf_Simons", "Raf_Simons_(brand)", "Prada", "Jil_Sander", "Calvin_Klein", "Dior"]
            elif re.search(r"transport\s+layer\s+security|tls", topic, re.I):
                titles = ["Transport_Layer_Security", "TLS_1.3", "HTTPS", "X.509", "Public_key_certificate", "Forward_secrecy"]
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
                            text  = _normalize(rec.get("text") or rec.get("body"))
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
                            text  = _normalize(rec.get("text") or rec.get("body"))
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

        if provider == "wiki_api":
            docs_raw = _fetch_wiki_api_pages(query or "Raf Simons")
        else:
            try:
                docs_raw = _load_hf_docs()
                if not docs_raw:
                    # timeout / empty → fallback
                    used_provider = "wiki_api"
                    docs_raw = _fetch_wiki_api_pages(query or "Raf Simons")
            except Exception:
                used_provider = "wiki_api"
                docs_raw = _fetch_wiki_api_pages(query or "Raf Simons")

        # ---- no docs? return early (but with metadata explaining why) ----
        if not docs_raw:
            base = "" if payload is None else str(payload)
            return base, {
                "rows": 0,
                "note": "no docs matched or provider unavailable",
                "provider": used_provider,
                "query": query,
                "regex": bool(q_pattern),
                "neg": neg,
                "must": must_terms,
                "streaming": streaming,
                "scan_limit": scan_limit
            }

        # ---- ranking (BM25-ish + regex boost) ----
        corpus_tokens = [set(_tokenize((d["title"] + " " + d["text"]).lower())) for d in docs_raw]
        N = len(corpus_tokens)
        q_terms = set(_tokenize(query)) if query else set()
        df: Dict[str, int] = {}
        for terms in corpus_tokens:
            for t in terms:
                df[t] = df.get(t, 0) + 1

        def _bm25ish_score(doc_text: str) -> float:
            words = _tokenize(doc_text); L = len(words) or 1
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

        ranked = sorted(docs_raw, key=lambda d: _bm25ish_score(d["title"] + " " + d["text"]), reverse=True)[:max(1, top_k_docs)]

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
                if q_pattern and q_pattern.search(s): overlap += 2
                if query and whole_word and _contains_whole_word(s, query): overlap += 1
                if overlap > 0: scored.append((float(overlap), idx, s))
            took = 0
            for _, idx, _ in sorted(scored, key=lambda x: (-x[0], x[1]))[:per_doc_quota]:
                lo = max(0, idx - sent_window); hi = min(len(sents), idx + sent_window + 1)
                chunk = " ".join(sents[lo:hi]).strip()
                if chunk and chunk not in hit_sents:
                    if title and (not hit_sents or not hit_sents[-1].startswith("# ")):
                        hit_sents.append(f"# {title}")
                    hit_sents.append(chunk); took += 1
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
                if len(w) < min_len or w in _STOPWORDS: continue
                counts[w] = counts.get(w, 0) + 1
            return [t for t, _ in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:top_k]]

        lexicon = _extract_terms_local(context, top_k=lexicon_top_k, min_len=lexicon_min_len) if context else []
        if use_phrases and context:
            phrase_candidates = re.findall(r"\b([A-Za-z0-9][A-Za-z0-9_\-]+(?:\s+[A-Za-z0-9][A-Za-z0-9_\-]+){1,3})\b", context)
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

        meta = {
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
        }
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
            "inject_context": True
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
            "max_chars": 0
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

    New:
      • min_term_overlap: require at least N query tokens to appear in doc text.
        This helps avoid collisions like "RAF" (air force) when query is "Raf Simons".
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os, re, time, hashlib, json
        from math import log
        from typing import List, Dict, Tuple
        from urllib.parse import urlparse

        # ---- Params ----
        query        = str(params.get("query", "") or str(payload or "")).strip()
        engine       = str(params.get("engine", "duckduckgo")).lower()  # duckduckgo | serpapi | google_cse
        num_results  = int(params.get("num_results", 10))
        max_fetch    = int(params.get("max_fetch", 8))                  # how many pages to actually fetch
        timeout_sec  = float(params.get("timeout", 8.0))
        read_timeout = float(params.get("read_timeout", 12.0))
        user_agent   = str(params.get("user_agent", "promptchat/webcorpus"))
        pause        = float(params.get("pause", 0.7))                  # polite delay between fetches
        cache_dir    = str(params.get("cache_dir", os.path.join(APP_DIR, "webcache")))
        os.makedirs(cache_dir, exist_ok=True)

        # text handling
        regex_query   = params.get("regex")
        neg           = [s.strip() for s in str(params.get("neg", "")).split(",") if s.strip()]
        must_terms    = [s.strip().lower() for s in str(params.get("must_terms", "")).split(",") if s.strip()]
        top_k_docs    = int(params.get("top_k_docs", 6))
        top_k_sents   = int(params.get("top_k_sents", 18))
        sent_window   = int(params.get("sent_window", 1))
        max_chars     = int(params.get("max_chars", 2800))
        min_doc_chars = int(params.get("min_doc_chars", 400))
        site_include  = [s.strip().lower() for s in str(params.get("site_include", "")).split(",") if s.strip()]
        site_exclude  = [s.strip().lower() for s in str(params.get("site_exclude", "")).split(",") if s.strip()]

        # NEW: minimum number of query tokens that must appear in the doc
        min_term_overlap = int(params.get("min_term_overlap", 1))

        # lexicon export
        export_lexicon  = bool(params.get("export_lexicon", True))
        lexicon_key     = str(params.get("lexicon_key", "web_lexicon"))
        inject_lexicon  = bool(params.get("inject_lexicon", True))
        inject_context  = bool(params.get("inject_context", True))
        lexicon_top_k   = int(params.get("lexicon_top_k", 40))
        lexicon_min_len = int(params.get("lexicon_min_len", 4))
        use_phrases     = bool(params.get("lexicon_phrases", True))

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
            # Use trafilatura for much cleaner text extraction
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
                print("[WebCorpusBlock] ERROR: `trafilatura` not installed. Please `pip install trafilatura`. Falling back to bs4.")
            except Exception:
                pass

            # Fallback: raw BeautifulSoup
            try:
                from bs4 import BeautifulSoup
                soup = BeautifulSoup(html or "", "html.parser")
                for t in soup(["script", "style", "noscript"]):
                    t.extract()
                return soup.get_text(" ", strip=True)
            except Exception:
                return ""

        def _matches(text: str) -> bool:
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

            # token overlap
            if query and not q_pattern:
                qt = [t for t in _tokenize(query) if t not in _STOPWORDS]
                if qt:
                    overlap = sum(1 for t in qt if t in low)
                    if overlap < min_term_overlap:
                        return False

            return True

        # ---- Search backends ----
        def search_duckduckgo(q: str, n: int) -> List[str]:
            try:
                from ddgs import DDGS  # pip install duckduckgo_search
                with DDGS() as ddgs:
                    out = []
                    for r in ddgs.text(q, max_results=n):
                        u = r.get("href") or r.get("url")
                        if u:
                            out.append(u)
                    return out
            except Exception:
                pass

            import requests
            urls = []
            try:
                r = requests.get("https://duckduckgo.com/html/",
                                 params={"q": q},
                                 headers={"User-Agent": user_agent},
                                 timeout=(timeout_sec, read_timeout))
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
            key = os.environ.get("SERPAPI_KEY")
            if not key:
                return []
            import requests
            try:
                r = requests.get("https://serpapi.com/search",
                                 params={"engine": "google", "q": q, "num": n, "api_key": key},
                                 timeout=(timeout_sec, read_timeout))
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
            cx  = os.environ.get("GOOGLE_CSE_ID")
            key = os.environ.get("GOOGLE_API_KEY")
            if not (cx and key):
                return []
            import requests
            out = []
            try:
                for start in range(1, min(n, 10) + 1, 10):
                    r = requests.get("https://www.googleapis.com/customsearch/v1",
                                     params={"q": q, "cx": cx, "key": key, "num": min(10, n), "start": start},
                                     timeout=(timeout_sec, read_timeout))

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

        if not query:
            base = "" if payload is None else str(payload)
            return base, {"rows": 0, "note": "empty query", "engine": engine}

        if engine == "serpapi":
            urls = search_serpapi(query, num_results)
        elif engine == "google_cse":
            urls = search_google_cse(query, num_results)
        else:
            urls = search_duckduckgo(query, num_results)

        # Filter by site allow/deny, dedupe domains
        seen = set()
        filtered = []
        for u in urls:
            if not _allow_site(u):
                continue
            d = _clean_domain(u)
            if d in seen:
                continue
            seen.add(d)
            filtered.append(u)
        urls = filtered[:max_fetch] if max_fetch > 0 else filtered

        # Fetch pages
        docs_raw: List[Dict[str, str]] = []
        for u in urls:
            html = _fetch_html(u)
            if not html:
                continue
            text = _extract_text(html, u)
            if not _matches(text):
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
            docs_raw.append({"title": title_guess, "text": text, "url": u})
            time.sleep(pause)

        if not docs_raw:
            base = "" if payload is None else str(payload)
            return base, {
                "rows": 0,
                "note": "no pages matched",
                "engine": engine,
                "query": query,
                "regex": bool(q_pattern),
                "neg": neg,
                "must_terms": must_terms,
                "sites": {"include": site_include, "exclude": site_exclude},
            }

        # ---- ranking BM25-ish (+ regex boost) ----
        corpus_tokens = [set(_tokenize(d["title"] + " " + d["text"])) for d in docs_raw]
        N = len(corpus_tokens)
        q_terms = set(_tokenize(query))
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
                        src = f"# {title} — {d.get('url','')}".strip()
                        hit_sents.append(src)
                    hit_sents.append(chunk)
                    took += 1

            if took == 0 and sents:
                chunk = " ".join(sents[: max(1, sent_window + 1)]).strip()
                if chunk and chunk not in hit_sents:
                    if title and (not hit_sents or not hit_sents[-1].startswith("# ")):
                        src = f"# {title} — {d.get('url','')}".strip()
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
            phrases = re.findall(r"\b([A-Za-z0-9][A-Za-z0-9_\-]+(?:\s+[A-Za-z0-9][A-Za-z0-9_\-]+){1,3})\b", context)
            pc: Dict[str, int] = {}
            for ph in phrases:
                ph = ph.lower().strip()
                if any(tok in _STOPWORDS for tok in ph.split()):
                    continue
                pc[ph] = pc.get(ph, 0) + 1
            phrase_top = [p for p, _ in sorted(pc.items(), key=lambda kv: (-kv[1], kv[0]))[:10]]
            lexicon = list(dict.fromkeys(phrase_top + lexicon))[:lexicon_top_k]

        # ---- store lexicon + context in Memory ----
        export_context = bool(params.get("export_context", True))
        context_key    = str(params.get("context_key", "web_context"))
        append_ctx     = bool(params.get("append_context", False))

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

        meta = {
            "engine": engine,
            "query": query,
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
        }
        return out, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "",
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
        }

BLOCKS.register("webcorpus", WebCorpusBlock)


# ---------------- WebCorpus (Playwright Hybrid) ----------------
@dataclass
class PlaywrightBlock(BaseBlock):
    """
    Playwright-powered corpus builder (Hybrid v7.2):
      • Performs targeted searches on a hardcoded list AND a "learned" list from memory.
      • Runs a general search to "discover" new high-quality domains.
      • Filters out junk domains (pinterest, ebay, etc.).
      • "Learns" new, good domains by saving them to memory.json for future runs.
      • Feeds all high-quality URLs (targeted, learned, discovered) into Playwright.
      • Uses 'trafilatura', BM25 ranking, and sentence extraction as before.

    New:
      • min_term_overlap: require at least N query tokens to appear in text
        (used for learning + keeping scraped docs).
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os, re, json, time, sys
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

        # ---- Params ----
        query        = str(params.get("query", "") or str(payload or "")).strip()
        num_results  = int(params.get("num_results", 15))  # Max *total* links to scrape
        headless     = bool(params.get("headless", True))
        timeout_sec  = float(params.get("timeout", 15.0))
        read_timeout = float(params.get("read_timeout", 12.0))
        user_agent   = str(params.get(
            "user_agent",
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36"
        ))
        verbose      = bool(params.get("verbose", False))

        # Target & Learning
        default_targets = "grailed.com,hypebeast.com,vogue.com,depop.com,poshmark.com"
        target_sites    = str(params.get("target_sites", default_targets))
        num_per_site    = int(params.get("num_per_site", 2))
        num_general     = int(params.get("num_general", 10))

        learn_new_sites   = bool(params.get("learn_new_sites", True))
        learned_sites_key = str(params.get("learned_sites_key", "web_learned_sites"))
        learn_min_hits    = int(params.get("learn_min_hits", 2))
        default_junk      = "pinterest.com,twitter.com,facebook.com,reddit.com,ebay.com,walmart.com,amazon.com,youtube.com,tiktok.com,instagram.com,linkedin.com"
        junk_domains      = str(params.get("junk_domains", default_junk))

        # text handling
        regex_query   = params.get("regex")
        neg           = [s.strip() for s in str(params.get("neg", "")).split(",") if s.strip()]
        must_terms    = [s.strip().lower() for s in str(params.get("must_terms", "")).split(",") if s.strip()]
        top_k_docs    = int(params.get("top_k_docs", 10))
        top_k_sents   = int(params.get("top_k_sents", 25))
        sent_window   = int(params.get("sent_window", 1))
        max_chars     = int(params.get("max_chars", 4000))
        min_doc_chars = int(params.get("min_doc_chars", 250))
        site_exclude  = [s.strip().lower() for s in str(params.get("site_exclude", "")).split(",") if s.strip()]

        # NEW: minimum query-token overlap for learning + docs
        min_term_overlap = int(params.get("min_term_overlap", 1))

        # lexicon export
        export_lexicon  = bool(params.get("export_lexicon", True))
        lexicon_key     = str(params.get("lexicon_key", "web_lexicon"))
        inject_lexicon  = bool(params.get("inject_lexicon", True))
        inject_context  = bool(params.get("inject_context", True))
        lexicon_top_k   = int(params.get("lexicon_top_k", 40))
        lexicon_min_len = int(params.get("lexicon_min_len", 4))
        use_phrases     = bool(params.get("lexicon_phrases", True))
        export_context  = bool(params.get("export_context", True))
        context_key     = str(params.get("context_key", "web_context"))
        append_ctx      = bool(params.get("append_context", False))

        timeout_ms = int(timeout_sec * 1000)
        meta: Dict[str, Any] = {
            "engine": "hybrid_ddgs_playwright",
            "query": query,
            "headless": headless,
            "search_results": [],
            "scrape_errors": [],
            "scraped_urls": [],
            "search_method": "unknown",
            "learned_sites": [],
            "newly_learned": [],
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

        # NEW: basic overlap check for learning/docs
        def _term_overlap_ok(text: str) -> bool:
            if not query or min_term_overlap <= 0:
                return True
            qt = [t for t in _tokenize(query) if t not in _STOPWORDS]
            if not qt:
                return True
            low = text.lower()
            overlap = sum(1 for t in qt if t in low)
            return overlap >= min_term_overlap

        def _hybrid_search(q: str, n: int) -> List[Dict[str, str]]:
            try:
                if verbose:
                    print(f"[PlaywrightBlock] Searching (via DDGS library) for: {q}", file=sys.stderr)
                with DDGS() as ddgs:
                    out = []
                    for r in ddgs.text(q, max_results=n):
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
        search_links: List[Dict[str, str]] = []
        seen_urls: Set[str] = set()

        store = Memory.load()

        # master "good" sites
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

        # master "bad" sites
        junk_list: Set[str] = set()
        for s in junk_domains.split(","):
            if s.strip():
                junk_list.add(s.strip())
        for s in site_exclude:
            if s.strip():
                junk_list.add(s.strip())

        try:
            # 1b. targeted search on known sites
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

            # 1c. general search for discovery
            if verbose:
                print(f"[PlaywrightBlock] Running general search for discovery...", file=sys.stderr)
            general_links = _hybrid_search(query, n=num_general)

            new_domain_counts: Dict[str, int] = defaultdict(int)
            discovered_links: List[Dict[str, str]] = []

            for link in general_links:
                url = link["url"]
                if url in seen_urls:
                    continue

                domain = _clean_domain(url)
                if not domain:
                    continue

                # skip junk or already-known
                if any(domain == s or domain.endswith("." + s) for s in junk_list):
                    continue
                if any(domain == s or domain.endswith("." + s) for s in sites_to_search):
                    continue

                # NEW: only consider this domain "on-topic" enough to learn
                search_text = (link.get("title", "") + " " + url)
                if not _term_overlap_ok(search_text):
                    # still may be scraped if we really want, but won't be "learned"
                    discovered_links.append(link)
                    seen_urls.add(url)
                    continue

                new_domain_counts[domain] += 1
                discovered_links.append(link)
                seen_urls.add(url)

            # 1d. Learn & evolve
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

            # 1e. Final scrape list
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

                        # NEW: Reject off-topic docs based on overlap
                        if not _term_overlap_ok(text):
                            if verbose:
                                print(f"[PlaywrightBlock] Overlap too low for {link['url']}", file=sys.stderr)
                            continue

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

        # sentence extraction
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

        # lexicon
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

        # store lexicon + context
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
        task = str(params.get("task", "zero-shot-classification"))
        model = params.get("model")  # None lets HF pipeline pick default
        model_name = str(model) if model else f"default_for_{task}"
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
            "model": model_name,
        }

        pipe = _get_hf_pipeline(task, model_name if model else None,
                                device=device, verbose=verbose)
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

        elif task == "text2text-generation":
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
    def _trim_to_tokens(self, pipe, text: str, max_input_tokens: int = 480) -> str:
        """Trim prompt by tokenizer length (keep task head + tail)."""
        try:
            tok = pipe.tokenizer

            # Respect model's own maximum if available
            model_max = getattr(tok, "model_max_length", None)
            if isinstance(model_max, int) and model_max > 0:
                limit = min(max_input_tokens, model_max)
            else:
                limit = max_input_tokens

            ids = tok.encode(text, add_special_tokens=False)
            if len(ids) <= limit:
                return text

            # Keep head + tail, biasing towards keeping more tail (typically user prompt)
            keep_head = min(128, limit // 3)
            keep_tail = max(limit - keep_head, 0)

            head_ids = ids[:keep_head]
            tail_ids = ids[-keep_tail:] if keep_tail > 0 else []

            return (
                tok.decode(head_ids, skip_special_tokens=True)
                + "\n...\n"
                + tok.decode(tail_ids, skip_special_tokens=True)
            )
        except Exception:
            # Last-resort hard cut
            return text[:4000]

    def _guess_lang_from_prompt(self, prompt: str, explicit_lang: str) -> str:
        """Heuristically guess language from prompt/fence, fallback to explicit_lang."""
        lang = (explicit_lang or "").strip().lower() or "python"
        p = prompt.lower()

        # Very light-weight guessing — only a few common langs
        if "javascript" in p or " typescript" in p or " ts " in p:
            return "javascript"
        if "typescript" in p:
            return "typescript"
        if "c++" in p or "cpp" in p:
            return "cpp"
        if "c#" in p or "csharp" in p:
            return "csharp"
        if "rust" in p:
            return "rust"
        if "java" in p and "javascript" not in p:
            return "java"

        # If user already uses a fenced code block hint like ```python
        for marker in ("```python", "```js", "```ts", "```cpp", "```csharp", "```rust", "```java"):
            if marker in p:
                # Extract lang from marker
                return marker.strip("`").split()[-1]

        return lang or "python"

    def _extract_code_block(self, s: str, lang: str = "python") -> str:
        """Extract the best fenced code block; if none, return raw generation."""
        s = s.strip()
        if "```" not in s:
            return s

        parts = s.split("```")
        candidates = []

        # Simple set of known language tags to strip from the first line
        LANG_TAGS = {
            "python", "py",
            "javascript", "js",
            "ts", "typescript",
            "cpp", "c++",
            "csharp", "c#",
            "rust", "java", "go", "php", "swift", "kotlin",
        }

        lang = (lang or "python").lower()

        for i in range(1, len(parts), 2):
            block = parts[i]

            # Separate first line (possibly language) from body
            lines = block.splitlines()
            if not lines:
                continue

            first = lines[0].strip().lower()
            stripped = False

            # If first token is a language tag, drop it
            if first in LANG_TAGS:
                lines = lines[1:]
                stripped = True
            elif first.startswith(lang):  # e.g., "python3"
                lines = lines[1:]
                stripped = True

            body = "\n".join(lines).strip()

            if not body:
                continue

            # Score block for "code-likeness"
            score = self._score_code_like(body, lang=lang, lang_stripped=stripped)
            candidates.append((score, body))

        if not candidates:
            return s

        # Pick highest scoring block
        candidates.sort(key=lambda x: x[0], reverse=True)
        best = candidates[0][1].strip()
        return best or s

    def _score_code_like(self, block: str, lang: str, lang_stripped: bool) -> float:
        """
        Heuristic score: more punctuation + keywords + indentation → more code-like.
        """
        lines = block.splitlines()
        if not lines:
            return 0.0

        text = block
        punct = sum(c in "{}[]();:.,+-=*/<>|&^%" for c in text)
        letters = sum(c.isalpha() for c in text)
        digits = sum(c.isdigit() for c in text)
        indented = sum(1 for ln in lines if ln.startswith((" ", "\t")))
        keywords = 0

        if lang == "python":
            PY_KW = ("def ", "class ", "import ", "from ", "async ", "await ", "return ", "with ", "for ", "while ", "if ", "elif ", "else:")
            keywords = sum(1 for ln in lines for kw in PY_KW if kw in ln)
        elif lang in ("javascript", "typescript", "js", "ts"):
            JS_KW = ("function ", "=>", "const ", "let ", "var ", "return ", "if (", "for (", "while (", "class ")
            keywords = sum(1 for ln in lines for kw in JS_KW if kw in ln)

        # Base score from punctuation and structure
        score = (
            punct * 1.0
            + digits * 0.3
            + keywords * 6.0
            + indented * 0.5
        )

        # Slight boost if a language tag was stripped
        if lang_stripped:
            score *= 1.2

        # Prevent extremely long pure-text blocks from dominating
        if letters > 0:
            ratio = punct / max(letters, 1)
            score *= (1.0 + ratio)

        return score

    def _strip_banner_comments(self, code: str) -> str:
        """Remove large banner/license headers if they dominate the top."""
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
                # stop early if banner is obviously long
                if banner_lines >= 12:
                    break
                continue
            break
        if banner_lines >= 10:
            return "\n".join(lines[i:]).lstrip()
        # Also nuke common license keywords at top few lines
        head = "\n".join(lines[:10]).lower()
        if any(k in head for k in ("copyright", "licensed", "apache", "all rights reserved")):
            return "\n".join(lines[i:]).lstrip()
        return code

    def _post_sanitize_code(self, code: str) -> str:
        """Final cleanup: trim stray fences, ensure sane trailing newline."""
        c = code.strip()

        # Strip surrounding fences if somehow still present
        if c.startswith("```") and c.endswith("```"):
            c = c.strip("`").strip()

        # Avoid runaway trailing snippets after '```'
        if "```" in c:
            c = c.split("```", 1)[0].rstrip()

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
        # Context is optional and trimmed hard; no lexicon injection here.
        ctx_key = str(params.get("context_key", "web_context"))
        ctx = (store.get(ctx_key, "") or "").strip()
        context_chars = int(params.get("context_chars", params.get("code.context_chars", 0)))
        if ctx and context_chars > 0:
            ctx = ctx[:context_chars]

        # Final prompt: strictly input content, no guides or instructions.
        # Order: context (if any) then user prompt, separated minimally.
        if ctx:
            final_prompt = f"{ctx}\n\n{user_prompt}"
        else:
            final_prompt = user_prompt

        explicit_lang = str(params.get("lang", "python"))
        lang = self._guess_lang_from_prompt(user_prompt, explicit_lang)

        model_name = str(params.get("model", "Salesforce/codet5p-220m"))
        device = params.get("device", "auto")

        # Decoding: deterministic, advanced constraints
        max_new_tokens = int(params.get("max_new_tokens", 128))
        min_new_tokens = int(params.get("min_new_tokens", 8))
        num_beams = int(params.get("num_beams", 4))
        do_sample = bool(params.get("do_sample", False))
        temperature = float(params.get("temperature", 0.2))
        top_k = int(params.get("top_k", 0))         # disabled when 0
        top_p = float(params.get("top_p", 1.0))     # keep deterministic path
        repetition_penalty = float(params.get("repetition_penalty", 1.12))
        no_repeat_ngram_size = int(params.get("no_repeat_ngram_size", 4))
        early_stopping = bool(params.get("early_stopping", True))
        max_time_sec = float(params.get("max_time_sec", params.get("code.max_time", 12.0)))
        max_input_tokens = int(params.get("max_input_tokens", 480))

        inject_tag = str(params.get("inject_tag", "code_solution"))
        wrap = bool(params.get("wrap", True))

        pipe = _get_hf_pipeline(
            "text2text-generation",
            model_name,
            device=device,
            verbose=params.get("verbose", False),
        )
        if pipe is None:
            return f"{payload}\n\n[{inject_tag}] (Model load failed)", {
                "error": "pipeline_failed"
            }

        # Guard against encoder limit
        final_prompt = self._trim_to_tokens(pipe, final_prompt, max_input_tokens)

        gen_kwargs = dict(
            max_new_tokens=max_new_tokens,
            min_new_tokens=min_new_tokens,
            do_sample=do_sample,
            temperature=temperature,
            top_k=top_k,
            top_p=top_p,
            num_beams=num_beams,
            repetition_penalty=repetition_penalty,
            no_repeat_ngram_size=no_repeat_ngram_size,
            early_stopping=early_stopping,
            max_time=max_time_sec,
        )

        try:
            pred = pipe(final_prompt, **gen_kwargs)
        except Exception as e:
            # No fallback content — just surface the error.
            return f"{payload}\n\n[{inject_tag}] (Error: {e})", {
                "error": "generation_failed",
                "exception": str(e),
            }

        gen_text = ""
        try:
            if isinstance(pred, list) and pred:
                cand = pred[0]
                gen_text = cand.get("generated_text") or cand.get("summary_text") or ""
        except Exception:
            gen_text = ""

        gen_text = gen_text.strip()

        # Post-process ONLY (no fallback synthesis)
        code_raw = self._extract_code_block(gen_text, lang=lang)
        code_raw = self._strip_banner_comments(code_raw)
        code_raw = self._post_sanitize_code(code_raw)

        # Safety: if we somehow got completely empty, keep the raw gen
        if not code_raw:
            code_raw = gen_text

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
            "beams": num_beams,
            "do_sample": do_sample,
            "temperature": temperature,
            "top_k": top_k,
            "top_p": top_p,
            "no_repeat_ngram_size": no_repeat_ngram_size,
            "repetition_penalty": repetition_penalty,
            "max_time_sec": max_time_sec,
            "max_input_tokens": max_input_tokens,
            "used_context": bool(ctx),
        }
        return result, meta

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "prompt": "REQUIRED: Write a python function...",
            "context_key": "web_context",
            "context_chars": 0,
            "model": "Salesforce/codet5p-220m",
            "device": "auto",
            "max_new_tokens": 128,
            "min_new_tokens": 8,
            "num_beams": 4,
            "do_sample": False,
            "temperature": 0.2,
            "top_k": 0,
            "top_p": 1.0,
            "repetition_penalty": 1.12,
            "no_repeat_ngram_size": 4,
            "early_stopping": True,
            "max_time_sec": 12.0,
            "max_input_tokens": 480,
            "inject_tag": "code_solution",
            "wrap": True,
            "lang": "python",
        }


BLOCKS.register("code", CodeBlock)


# ---------------- CodeCorpus (code docs & API learner) ----------------
@dataclass
class CodeCorpusBlock(BaseBlock):
    """
    Code-focused corpus builder (no markdown-it dependency):
      • Inputs: list of urls, sitemap(s), or (query + site_include) search.
      • Extracts: headings/paragraphs + fenced code blocks from Markdown/HTML.
      • Learns: identifiers & API names → exports lexicon (code_lexicon) and context (code_context).
      • Optional: remembers good domains across runs (learned_code_sites).

    Deps (optional fallbacks included):
      - requests, beautifulsoup4
      - trafilatura (preferred HTML text extraction; falls back to bs4)
      - duckduckgo_search (optional) for discovery

    Example:
      --extra codecorpus.urls="https://docs.python.org/3/tutorial/index.html,https://pandas.pydata.org/docs/"
      --extra codecorpus.sitemaps="https://docs.python.org/sitemap.xml"
      --extra codecorpus.query="list comprehension site:docs.python.org"
      --extra codecorpus.site_include="docs.python.org,readthedocs.io"

    Exports into Memory by default:
      - code_lexicon (terms)
      - code_context (snippets + sentences)
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import re, os, json, time, html
        from typing import List, Dict, Tuple, Set
        from urllib.parse import urlparse
        import hashlib

        # ---------- Params ----------
        query          = str(params.get("query", "")).strip()
        urls_raw       = str(params.get("urls", "")).strip()
        sitemaps_raw   = str(params.get("sitemaps", "")).strip()
        site_include   = [s.strip().lower() for s in str(params.get("site_include", "")).split(",") if s.strip()]
        site_exclude   = [s.strip().lower() for s in str(params.get("site_exclude", "github.com,stackoverflow.com,reddit.com")).split(",") if s.strip()]
        max_pages      = int(params.get("max_pages", 12))
        min_doc_chars  = int(params.get("min_doc_chars", 200))
        max_chars      = int(params.get("max_chars", 3800))
        top_k_docs     = int(params.get("top_k_docs", 10))
        top_k_sents    = int(params.get("top_k_sents", 30))
        sent_window    = int(params.get("sent_window", 0))

        # Learning
        learn_new_sites   = bool(params.get("learn_new_sites", True))
        learned_sites_key = str(params.get("learned_sites_key", "learned_code_sites"))
        learn_min_hits    = int(params.get("learn_min_hits", 2))

        # Lexicon/context export
        export_lexicon = bool(params.get("export_lexicon", True))
        export_context = bool(params.get("export_context", True))
        inject_lexicon = bool(params.get("inject_lexicon", True))
        inject_context = bool(params.get("inject_context", True))
        lexicon_key    = str(params.get("lexicon_key", "code_lexicon"))
        context_key    = str(params.get("context_key", "code_context"))
        append_ctx     = bool(params.get("append_context", False))
        lexicon_top_k  = int(params.get("lexicon_top_k", 60))
        lexicon_min_len= int(params.get("lexicon_min_len", 3))  # identifiers can be short
        use_phrases    = bool(params.get("lexicon_phrases", True))

        # Runtime
        timeout        = float(params.get("timeout", 10.0))
        read_timeout   = float(params.get("read_timeout", 12.0))
        user_agent     = str(params.get("user_agent", "promptchat/codecorpus"))
        verbose        = bool(params.get("verbose", False))

        # ---------- Imports & helpers ----------
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

        # Optional discovery
        try:
            from ddgs import DDGS  # pip install duckduckgo_search
            _has_ddgs = True
        except Exception:
            _has_ddgs = False

        def _clean_domain(u: str) -> str:
            try:
                netloc = urlparse(u).netloc.lower()
                return netloc.split(":")[0]
            except Exception:
                return ""

        def _allowed(url: str) -> bool:
            d = _clean_domain(url)
            if site_include and not any(d.endswith(s) for s in site_include):
                return False
            if any(d.endswith(s) for s in site_exclude):
                return False
            return True

        # --- Identifier & text processing ---
        _STOP = set([
            "the","a","an","and","or","if","on","in","to","for","from","of","at","by","with","as","is","are","was",
            "were","be","been","being","that","this","these","those","it","its","into","about","over","under",
            "can","should","would","will","may","might","must","do","does","did","done","have","has","had","having",
            "not","no","yes","you","your","we","our","they","their","there","here","also","such","via","etc","see",
            "code","example","examples","note","notes","true","false","none","null","class","function","method",
            "module","package","return","returns","type","types","param","parameter","parameters"
        ])

        _IDENT_RE = re.compile(
            r"""
            (?:
              [A-Za-z_][A-Za-z0-9_]*           # snake/UPPER/mixed
              (?:\.[A-Za-z_][A-Za-z0-9_]*)*    # dotted api.name
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
            re.VERBOSE
        )

        def _extract_identifiers(text: str) -> List[str]:
            ids = _IDENT_RE.findall(text or "")
            out = []
            for s in ids:
                tok = s.strip().strip(".")
                if len(tok) < lexicon_min_len:
                    continue
                low = tok.lower()
                if low in _STOP:
                    continue
                out.append(tok)
            return out

        def _split_sents(text: str) -> List[str]:
            bits = re.split(r"(?<=[.!?])\s+|\n+", (text or "").strip())
            return [b.strip() for b in bits if b.strip()]

        # --- fetch helpers ---
        def _get(url: str) -> str:
            try:
                r = requests.get(url, headers={"User-Agent": user_agent}, timeout=(timeout, read_timeout))
                if r.status_code == 200:
                    return r.text
            except Exception:
                return ""
            return ""

        def _extract_text_html(html_text: str) -> Tuple[str, List[str]]:
            """Return (clean_text, code_blocks) from HTML."""
            code_blocks: List[str] = []
            clean_text = ""

            if _has_traf:
                try:
                    clean_text = trafilatura.extract(
                        html_text, include_comments=False, include_tables=False, deduplicate=True
                    ) or ""
                except Exception:
                    clean_text = ""

            if not clean_text:
                try:
                    soup = BeautifulSoup(html_text or "", "html.parser")
                    # collect code fences
                    for pre in soup.select("pre, code"):
                        code = pre.get_text("\n", strip=True)
                        if code and len(code) >= 8:
                            code_blocks.append(code)
                    # remove script/style
                    for t in soup(["script", "style", "noscript"]): t.extract()
                    clean_text = soup.get_text(" ", strip=True)
                except Exception:
                    pass

            return clean_text or "", code_blocks

        # --- Markdown extractor: regex-only (no markdown-it) ---
        _FENCE_RE = re.compile(
            r"""
            ^```[ \t]*([A-Za-z0-9_\-\+\.]*)[ \t]*\n   # opening fence with optional lang
            (.*?)                                      # code body (non-greedy)
            \n```[ \t]*$                               # closing fence
            """,
            re.MULTILINE | re.DOTALL | re.VERBOSE
        )

        def _extract_text_md(md_text: str) -> Tuple[str, List[str]]:
            """Return (clean_text, code_blocks) from Markdown using regex fences only."""
            code_blocks: List[str] = []
            text = md_text or ""

            # collect fenced code
            for m in _FENCE_RE.finditer(text):
                code = m.group(2).strip()
                if len(code) >= 8:
                    code_blocks.append(code)

            # remove fenced blocks to leave prose
            text_wo_fences = _FENCE_RE.sub(" ", text)

            # strip inline code ticks (light cleanup)
            text_wo_inline = re.sub(r"`([^`]+)`", r"\1", text_wo_fences)

            # collapse whitespace
            clean = re.sub(r"[ \t]+", " ", text_wo_inline)
            clean = re.sub(r"\n{2,}", "\n", clean).strip()

            return clean, code_blocks

        # --- collect URLs: direct, sitemaps, discovery ---
        candidates: List[str] = []

        if urls_raw:
            candidates.extend([u.strip() for u in urls_raw.split(",") if u.strip()])

        if sitemaps_raw:
            for sm in [s.strip() for s in sitemaps_raw.split(",") if s.strip()]:
                try:
                    xml = _get(sm)
                    if not xml:
                        continue
                    locs = re.findall(r"<loc>(.*?)</loc>", xml, re.IGNORECASE | re.DOTALL)
                    for loc in locs:
                        u = html.unescape(loc).strip()
                        if _allowed(u):
                            candidates.append(u)
                except Exception:
                    continue

        if query and not candidates and _has_ddgs:
            with DDGS() as ddgs:
                for r in ddgs.text(query, max_results=max_pages * 2):
                    u = r.get("href") or r.get("url")
                    if u and _allowed(u):
                        candidates.append(u)

        # Dedup & cap
        seen = set()
        final_urls = []
        for u in candidates:
            if u in seen:
                continue
            seen.add(u)
            if _allowed(u):
                final_urls.append(u)
            if len(final_urls) >= max_pages:
                break

        # --- fetch and parse pages ---
        docs_raw: List[Dict[str, str]] = []
        domain_hits: Dict[str, int] = {}

        for u in final_urls:
            html_text = _get(u)
            if not html_text:
                continue

            if u.lower().endswith(".md") or "/raw/" in u or "raw.githubusercontent.com" in u:
                body, code_blocks = _extract_text_md(html_text)
            else:
                body, code_blocks = _extract_text_html(html_text)

            code_join = "\n\n".join(code_blocks[:5])
            full_text = (body.strip() + ("\n\n" + code_join if code_join else "")).strip()

            if len(full_text) < min_doc_chars:
                continue

            title = _clean_domain(u)
            try:
                if "<title" in html_text.lower():
                    soup = BeautifulSoup(html_text, "html.parser")
                    if soup.title and soup.title.string:
                        title = soup.title.string.strip()
            except Exception:
                pass

            docs_raw.append({"title": title, "text": full_text, "url": u})
            d = _clean_domain(u)
            domain_hits[d] = domain_hits.get(d, 0) + 1

        if not docs_raw:
            base = "" if payload is None else str(payload)
            return base, {
                "rows": 0, "note": "no docs scraped",
                "query": query, "max_pages": max_pages,
                "site_include": site_include, "site_exclude": site_exclude
            }

        # --- rank docs ---
        def _tokenize(t: str) -> List[str]:
            return re.findall(r"[A-Za-z0-9][A-Za-z0-9_\-\.]+", (t or "").lower())

        q_terms = set(_tokenize(query)) if query else set()

        def _score(doc: Dict[str, str]) -> float:
            text = doc["text"]
            ids = set(i.lower() for i in _extract_identifiers(text))
            overlap = len(ids & q_terms) if q_terms else len(ids) * 0.1
            return overlap + min(2.0, len(text) / 4000.0)

        ranked = sorted(docs_raw, key=_score, reverse=True)[:max(1, top_k_docs)]

        # --- sentence extraction (prefer sentences with identifiers) ---
        hit_sents: List[str] = []
        per_doc_quota = max(1, top_k_sents // max(1, len(ranked)))
        for d in ranked:
            title = (d["title"] or "").strip()
            sents = _split_sents(d["text"] or "")
            scored: List[Tuple[float, int, str]] = []
            for idx, s in enumerate(sents):
                s_ids = set(_extract_identifiers(s))
                score = len(s_ids) + (1 if any(t in s.lower() for t in q_terms) else 0)
                if score > 0:
                    scored.append((float(score), idx, s))
            took = 0
            for _, idx, _ in sorted(scored, key=lambda x: (-x[0], x[1]))[:per_doc_quota]:
                lo = max(0, idx - sent_window)
                hi = min(len(sents), idx + sent_window + 1)
                chunk = " ".join(sents[lo:hi]).strip()
                if chunk and chunk not in hit_sents:
                    src = f"# {title} — {d.get('url','')}".strip()
                    if not hit_sents or hit_sents[-1] != src:
                        hit_sents.append(src)
                    hit_sents.append(chunk)
                    took += 1
            if took == 0 and sents:
                chunk = " ".join(sents[:1]).strip()
                if chunk:
                    src = f"# {title} — {d.get('url','')}".strip()
                    if not hit_sents or hit_sents[-1] != src:
                        hit_sents.append(src)
                    hit_sents.append(chunk)

        context = "\n\n".join(hit_sents).strip()
        if max_chars > 0 and len(context) > max_chars:
            context = context[:max_chars] + "…"

        # --- lexicon from identifiers + dotted phrases ---
        def _extract_terms_local(text: str, *, top_k: int, min_len: int) -> List[str]:
            terms = _extract_identifiers(text)
            counts: Dict[str, int] = {}
            for t in terms:
                counts[t] = counts.get(t, 0) + 1
            ranked_terms = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
            return [t for t, _ in ranked_terms[:top_k]]

        lexicon = _extract_terms_local(context or "\n".join(d["text"] for d in ranked),
                                       top_k=lexicon_top_k, min_len=lexicon_min_len)

        if use_phrases and context:
            phrases = re.findall(r"\b([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+)\b", context)
            pc: Dict[str, int] = {}
            for ph in phrases:
                if any(tok.lower() in _STOP for tok in ph.split(".")):
                    continue
                pc[ph] = pc.get(ph, 0) + 1
            phrase_top = [p for p, _ in sorted(pc.items(), key=lambda kv: (-kv[1], kv[0]))[:10]]
            seenp = set()
            merged = []
            for t in phrase_top + lexicon:
                if t not in seenp:
                    merged.append(t); seenp.add(t)
            lexicon = merged[:lexicon_top_k]

        # --- Learn new domains (optional) ---
        newly_learned = []
        if learn_new_sites:
            store = Memory.load()
            learned = set(store.get(learned_sites_key, []))
            for dom, c in domain_hits.items():
                if c >= learn_min_hits and dom not in learned and _allowed(f"https://{dom}/"):
                    learned.add(dom)
                    newly_learned.append(dom)
            if newly_learned:
                store[learned_sites_key] = sorted(learned)
                Memory.save(store)

        # --- Export to Memory ---
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

        # --- Compose output back into pipeline ---
        base = "" if payload is None else str(payload)
        parts: List[str] = [base] if base else []
        if inject_lexicon and lexicon:
            parts.append("[lexicon]\n" + ", ".join(lexicon))
        if inject_context and context:
            parts.append("[context]\n" + context)
        out = "\n\n".join(parts).strip()

        meta = {
            "rows": len(docs_raw),
            "ranked_docs": len(ranked),
            "top_urls": [d.get("url") for d in ranked],
            "lexicon_key": lexicon_key if (export_lexicon and lexicon) else None,
            "lexicon_size": len(lexicon),
            "context_key": context_key if (export_context and context) else None,
            "context_len": len(context),
            "site_include": site_include,
            "site_exclude": site_exclude,
            "learned_sites_key": learned_sites_key if learn_new_sites else None,
            "newly_learned": newly_learned,
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
            "max_chars": 3800,
            "top_k_docs": 10,
            "top_k_sents": 30,
            "learn_new_sites": True,
            "lexicon_key": "code_lexicon",
            "context_key": "code_context",
            "append_ctx": False,
            "lexicon_top_k": 60,
            "lexicon_min_len": 3
        }
# Register the block
BLOCKS.register("codecorpus", CodeCorpusBlock)


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
                link  = data.get("content_urls", {}).get("desktop", {}).get("page") or data.get("extract_url") or ""
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
        "mercari": "mercari.com",          # US/Global Mercari
        "mercari_jp": "jp.mercari.com",    # Japanese Mercari
        "rakuma": "fril.jp",               # Rakuma uses fril.jp domain
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
        backend = str(params.get("backend", "ddg")).lower()        # "ddg" or "playwright"

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
                    for r in ddgs.text(full_query, max_results=limit):
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
    for specific file extensions (.pdf, .mp3, .zip) or regex patterns.

    Modes:
    - 'media': looks for .mp3, .wav, .flac, .m4a
    - 'docs': looks for .pdf, .doc, .docx, .txt, .epub
    - 'archives': looks for .zip, .rar, .7z, .tar
    - 'custom': uses 'target_extensions' param

    Features:
    - Search engines: duckduckgo (default), google_cse
    - Verify: Can perform a HEAD request to ensure the link is alive (200 OK).
    - Dedupe: Removes duplicate links found across multiple pages.
    - Optional site filter via `site_require` (e.g. archive.org only).
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os
        import re
        import requests
        from bs4 import BeautifulSoup
        from urllib.parse import urljoin, urlparse
        from ddgs import DDGS  # DuckDuckGo Search

        # --- Parameters ---
        query = str(params.get("query", "") or str(payload or "")).strip()
        mode = str(params.get("mode", "docs")).lower()
        num_pages_to_scan = int(params.get("scan_limit", 5))  # How many search results to visit
        timeout = float(params.get("timeout", 5.0))
        verify_links = bool(params.get("verify", True))       # Check if 200 OK

        # NEW: search engine selection
        engine = str(params.get("engine", "duckduckgo")).lower()  # duckduckgo | google_cse

        # Custom filters
        custom_ext = str(params.get("extensions", "")).split(",")
        keywords_in_url = str(params.get("url_keywords", "")).split(",")

        # NEW: required sites (domains/substrings)
        # Example: "archive.org,ca.archive.org"
        site_require_raw = str(params.get("site_require", "")).split(",")
        required_sites = [s.strip().lower() for s in site_require_raw if s.strip()]

        # Setup target extensions based on mode
        targets = set()
        if mode == "media":
            targets.update([".mp3", ".wav", ".flac", ".m4a", ".ogg"])
        elif mode == "docs":
            targets.update([".pdf", ".epub", ".mobi", ".doc", ".docx"])
        elif mode == "archives":
            targets.update([".zip", ".rar", ".7z", ".tar", ".gz"])

        # Add custom extensions (remove empty strings)
        for e in custom_ext:
            if e.strip():
                targets.add(e.strip().lower() if e.startswith(".") else f".{e.strip().lower()}")

        # --- [NEW] Smart Keyword Filtering ---
        # 1. Start with user-provided keywords
        keywords = [k.strip().lower() for k in keywords_in_url if k.strip()]

        # 2. Automatically add query tokens as required keywords
        if query:
            try:
                query_tokens = [
                    t for t in re.findall(r"[A-Za-z0-9][A-Za-z0-9_\-]+", query.lower())
                    if t not in _STOPWORDS
                ]
            except NameError:
                query_tokens = [t for t in query.lower().split() if t not in _STOPWORDS]

            for qt in query_tokens:
                if qt not in keywords:
                    keywords.append(qt)
        # --- [END NEW] ---

        if not query:
            return "", {"error": "No query provided for LinkTracker."}

        # --- Small helpers ---
        def _clean_domain(u: str) -> str:
            try:
                netloc = urlparse(u).netloc.lower()
                return netloc.split(":")[0]
            except Exception:
                return ""

        def _allowed_by_required_sites(u: str) -> bool:
            """
            If required_sites is empty -> always True.
            Otherwise, URL's domain must contain at least one of required_sites entries.
            """
            if not required_sites:
                return True
            d = _clean_domain(u)
            return any(req in d for req in required_sites)

        # --- Step 1: Discovery (Find Hub Pages) ---

        # Slightly tuned search query per mode (optional)
        search_q = query
        if mode == "media":
            search_q += " index of mp3"
        elif mode == "docs":
            search_q += " filetype:pdf"

        def _search_duckduckgo(q: str, n: int):
            pages = []
            try:
                with DDGS() as ddgs:
                    for r in ddgs.text(q, max_results=n):
                        u = r.get("href") or r.get("url")
                        if not u:
                            continue
                        pages.append(u)
            except Exception:
                pass
            return pages

        def _search_google_cse(q: str, n: int):
            cx = os.environ.get("GOOGLE_CSE_ID")
            key = os.environ.get("GOOGLE_API_KEY")
            if not (cx and key):
                # No key or CSE ID -> behave like "no results"
                return []
            out = []
            try:
                # For simplicity, single page of results; n is small anyway for LinkTracker
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

        if engine == "google_cse":
            candidate_pages = _search_google_cse(search_q, num_pages_to_scan * 2)
        else:
            candidate_pages = _search_duckduckgo(search_q, num_pages_to_scan * 2)

        # Limit to requested count
        # AND apply required_sites filter at the hub-page level too
        filtered_candidates = []
        for u in candidate_pages:
            if _allowed_by_required_sites(u):
                filtered_candidates.append(u)
            elif not required_sites:
                # If no required_sites, just keep all
                filtered_candidates.append(u)
            if len(filtered_candidates) >= num_pages_to_scan:
                break

        candidate_pages = filtered_candidates

        # --- Step 2: Deep Scan ---
        found_assets = []
        seen_urls = set()

        session = requests.Session()
        session.headers.update({
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) PromptChat/LinkTracker"
        })

        log = []

        for page_url in candidate_pages:
            try:
                resp = session.get(page_url, timeout=timeout)
                if resp.status_code != 200:
                    continue

                soup = BeautifulSoup(resp.text, "html.parser")

                # Scan every single link on the page
                for a in soup.find_all("a", href=True):
                    raw_link = a["href"]
                    full_url = urljoin(page_url, raw_link)
                    parsed = urlparse(full_url)
                    path = parsed.path.lower()

                    if full_url in seen_urls:
                        continue

                    # 1. Check Extension
                    is_hit = False
                    for ext in targets:
                        if path.endswith(ext):
                            is_hit = True
                            break

                    # --- Keyword filtering ---
                    if keywords and is_hit:
                        link_text = (a.get_text(strip=True) or "").lower()
                        url_text = full_url.lower().replace("%20", " ")
                        haystack = link_text + " " + url_text
                        if not any(k in haystack for k in keywords):
                            is_hit = False  # Failed keyword check

                    # --- NEW: required_sites filter at asset level ---
                    if is_hit and not _allowed_by_required_sites(full_url):
                        is_hit = False

                    if is_hit:
                        seen_urls.add(full_url)

                        # 3. Verification
                        status = "unverified"
                        size = "?"
                        if verify_links:
                            try:
                                h = session.head(full_url, allow_redirects=True, timeout=3)
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
                            link_text = (a.get_text(strip=True) or path.split("/")[-1])[:100]
                            found_assets.append({
                                "text": link_text,
                                "url": full_url,
                                "source": page_url,
                                "size": size
                            })

            except Exception as e:
                log.append(f"Error scanning {page_url}: {e}")
                continue

        # --- Step 3: Format Output ---
        if not found_assets:
            return (
                f"### LinkTracker: No specific assets found.\n"
                f"Scanned {len(candidate_pages)} pages for extensions: {list(targets)}.\n"
                f"Required keywords: {keywords}\n"
                f"Required sites: {required_sites or '[none]'}\n"
                f"Engine: {engine}"
            ), {
                "count": 0,
                "keywords_used": keywords,
                "engine": engine,
                "required_sites": required_sites,
            }

        lines = [f"### LinkTracker Found {len(found_assets)} Assets"]
        lines.append(
            f"_Mode: {mode} | Query: {query} | Engine: {engine} | "
            f"Required Keywords: {keywords} | Required Sites: {required_sites or '[none]'}_"
        )
        lines.append("")

        for asset in found_assets:  # Show all links
            lines.append(f"- **[{asset['text']}]({asset['url']})**")
            lines.append(f"  - *Size: {asset['size']} | Source: {urlparse(asset['source']).netloc}*")

        return "\n".join(lines), {
            "found": len(found_assets),
            "scanned_pages": len(candidate_pages),
            "assets": found_assets,
            "keywords_used": keywords,
            "engine": engine,
            "required_sites": required_sites,
        }

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "query": "rare aphex twin interview",
            "mode": "docs",           # media, docs, archives, custom
            "scan_limit": 5,
            "verify": True,
            "extensions": ".pdf,.txt",  # optional overrides
            "url_keywords": "archive,download",  # optional filter
            "engine": "duckduckgo",   # or: google_cse
            "site_require": ""        # e.g. 'archive.org,ca.archive.org'
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
                    "comment_count": int(stats.get("commentCount", 0)) if stats.get("commentCount") is not None else None,
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
            "order": "relevance",        # date | rating | relevance | title | viewCount
            "safe_search": "moderate",   # none | moderate | strict
            "channel_id": "",
            "video_duration": "any",     # any | short | medium | long
            "published_after": "",       # RFC3339, e.g. 2023-01-01T00:00:00Z
            "export_key": "youtube_results",
            "export_to_memory": True,
            "engine_note": "Uses GOOGLE_API_KEY env var (YouTube Data API v3)",
        }


BLOCKS.register("youtube", YouTubeDataBlock)