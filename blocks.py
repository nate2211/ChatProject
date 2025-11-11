# ========================================================
# ================  blocks.py  ===========================
# ========================================================
from __future__ import annotations

import functools
from dataclasses import dataclass
from typing import Any, Dict, Tuple, List
import json as _json
import os as _os
import random
import time

from datasets import load_dataset
from registry import BLOCKS
from models import get_chat_model  # <-- models now live separately

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
# keep registration
BLOCKS.register("corpus", CorpusBlock)

# ---------------- Chat (no personas/prompts; uses lexicon only) ----------------
@dataclass
class ChatBlock(BaseBlock):
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        model_name = str(params.get("model", "toy"))
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
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        import os, re, time, hashlib, json
        from math import log
        from typing import List, Dict, Tuple
        from urllib.parse import urlparse
        import threading

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
        regex_query  = params.get("regex")
        neg          = [s.strip() for s in str(params.get("neg", "")).split(",") if s.strip()]
        must_terms   = [s.strip().lower() for s in str(params.get("must_terms", "")).split(",") if s.strip()]
        top_k_docs   = int(params.get("top_k_docs", 6))
        top_k_sents  = int(params.get("top_k_sents", 18))
        sent_window  = int(params.get("sent_window", 1))
        max_chars    = int(params.get("max_chars", 2800))
        min_doc_chars= int(params.get("min_doc_chars", 400))
        site_include = [s.strip().lower() for s in str(params.get("site_include", "")).split(",") if s.strip()]
        site_exclude = [s.strip().lower() for s in str(params.get("site_exclude", "")).split(",") if s.strip()]

        # lexicon export
        export_lexicon = bool(params.get("export_lexicon", True))
        lexicon_key    = str(params.get("lexicon_key", "web_lexicon"))
        inject_lexicon = bool(params.get("inject_lexicon", True))
        inject_context = bool(params.get("inject_context", True))
        lexicon_top_k  = int(params.get("lexicon_top_k", 40))
        lexicon_min_len= int(params.get("lexicon_min_len", 4))
        use_phrases    = bool(params.get("lexicon_phrases", True))

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
                # include_comments=False and include_tables=False are good defaults
                clean_text = trafilatura.extract(
                    html,
                    include_comments=False,
                    include_tables=False,
                    deduplicate=True
                )
                return clean_text or "" # Return "" if extraction fails
            except ImportError:
                print("[WebCorpusBlock] ERROR: `trafilatura` not installed. Please `pip install trafilatura`. Falling back to bs4.")
            except Exception:
                pass # Fallback on any trafilatura error

            # Fallback: raw BeautifulSoup (your old code)
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
            # if no regex, make sure at least query tokens show up
            if not q_pattern and query:
                qt = [t for t in _tokenize(query) if t not in _STOPWORDS]
                if qt and not any(t in low for t in qt):
                    return False
            return True

        # ---- Search backends ----
        def search_duckduckgo(q: str, n: int) -> List[str]:
            # Prefer python package if available
            try:
                from ddgs import DDGS  # pip install duckduckgo_search
                with DDGS() as ddgs:
                    out = []
                    for r in ddgs.text(q, max_results=n):
                        u = r.get("href") or r.get("url")
                        if u: out.append(u)
                    return out
            except Exception:
                pass
            # HTML-lite fallback (very simple)
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
                    if u: out.append(u)
                return out[:n]
            except Exception:
                return []

        def search_google_cse(q: str, n: int) -> List[str]:
            cx  = os.environ.get("GOOGLE_CSE_ID")
            key = os.environ.get("GOOGLE_API_KEY")
            if not (cx and key):
                return []
            import requests, math
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
                        if u: out.append(u)
                    if len(out) >= n:
                        break
            except Exception:
                return out[:n]
            return out[:n]

        if not query:
            base = "" if payload is None else str(payload)
            return base, {"rows": 0, "note": "empty query", "engine": engine}

        # Get candidate URLs
        if engine == "serpapi":
            urls = search_serpapi(query, num_results)
        elif engine == "google_cse":
            urls = search_google_cse(query, num_results)
        else:
            urls = search_duckduckgo(query, num_results)

        # Filter by site allow/deny, dedupe domains first
        seen = set()
        filtered = []
        for u in urls:
            if not _allow_site(u): continue
            d = _clean_domain(u)
            if d in seen: continue
            seen.add(d)
            filtered.append(u)
        urls = filtered[:max_fetch] if max_fetch > 0 else filtered

        # Fetch pages (sequential with small pause; robust)
        docs_raw: List[Dict[str, str]] = []
        for u in urls:
            html = _fetch_html(u)
            if not html:
                continue
            text = _extract_text(html, u)
            if not _matches(text):
                continue
            title_guess = _clean_domain(u)
            # light title extraction
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
                "rows": 0, "note": "no pages matched",
                "engine": engine, "query": query, "regex": bool(q_pattern),
                "neg": neg, "must": must_terms, "sites": {"include": site_include, "exclude": site_exclude}
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
                if q_pattern and q_pattern.search(s): overlap += 2
                if overlap > 0: scored.append((float(overlap), idx, s))

            took = 0
            for _, idx, _ in sorted(scored, key=lambda x: (-x[0], x[1]))[:per_doc_quota]:
                lo = max(0, idx - sent_window); hi = min(len(sents), idx + sent_window + 1)
                chunk = " ".join(sents[lo:hi]).strip()
                if chunk and chunk not in hit_sents:
                    if title and (not hit_sents or not hit_sents[-1].startswith("# ")):
                        src = f" # {title} — {d.get('url','')}".strip()
                        hit_sents.append(src)
                    hit_sents.append(chunk); took += 1

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
                if len(w) < min_len or w in _STOPWORDS: continue
                counts[w] = counts.get(w, 0) + 1
            return [t for t, _ in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:top_k]]

        lexicon = _extract_terms_local(context, top_k=lexicon_top_k, min_len=lexicon_min_len) if context else []
        if use_phrases and context:
            phrases = re.findall(r"\b([A-Za-z0-9][A-Za-z0-9_\-]+(?:\s+[A-Za-z0-9][A-Za-z0-9_\-]+){1,3})\b", context)
            pc: Dict[str, int] = {}
            for ph in phrases:
                ph = ph.lower().strip()
                if any(tok in _STOPWORDS for tok in ph.split()): continue
                pc[ph] = pc.get(ph, 0) + 1
            phrase_top = [p for p, _ in sorted(pc.items(), key=lambda kv: (-kv[1], kv[0]))[:10]]
            lexicon = list(dict.fromkeys(phrase_top + lexicon))[:lexicon_top_k]

        # ---- store lexicon + context in Memory ----
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

        meta = {
            "engine": engine,
            "query": query,
            "regex": bool(q_pattern),
            "neg": neg,
            "must": must_terms,
            "rows": len(docs_raw),
            "ranked_docs": len(ranked),
            "lexicon_key": lexicon_key if (export_lexicon and lexicon) else None,
            "lexicon_size": len(lexicon),
            "context_key": context_key if (export_context and context) else None,
            "context_len": len(context),
            "top_urls": [d.get("url") for d in ranked],
            "site_include": site_include,
            "site_exclude": site_exclude,
        }
        return out, meta

BLOCKS.register("webcorpus", WebCorpusBlock)


# ---------------- WebCorpus (Playwright Hybrid) ----------------
@dataclass
class PlaywrightBlock(BaseBlock):
    """
    Playwright-powered corpus builder (Hybrid v7.1 - Corrected):
      • Performs targeted searches on a hardcoded list AND a "learned" list from memory.
      • Runs a general search to "discover" new high-quality domains.
      • Filters out junk domains (pinterest, ebay, etc.).
      • "Learns" new, good domains by saving them to memory.json for future runs.
      • Feeds all high-quality URLs (targeted, learned, discovered) into Playwright.
      • Uses 'trafilatura', BM25 ranking, and sentence extraction as before.

    Requires:
      pip install playwright trafilatura duckduckgo_search beautifulsoup4
      python -m playwright install --with-deps chromium
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        # --- Imports (must be inside execute for modularity) ---
        import os, re, json, time, sys
        from math import log
        from typing import List, Dict, Tuple, Set
        from urllib.parse import urlparse
        import threading
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
        query = str(params.get("query", "") or str(payload or "")).strip()
        num_results = int(params.get("num_results", 15))  # Max *total* links to scrape
        headless = bool(params.get("headless", True))
        timeout_sec = float(params.get("timeout", 15.0))  # Page load timeout
        read_timeout = float(params.get("read_timeout", 12.0))  # For requests fallback
        user_agent = str(params.get("user_agent",
                                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36"))
        verbose = bool(params.get("verbose", False))

        # --- Target & Learning Params ---
        default_targets = "grailed.com,hypebeast.com,vogue.com,depop.com,poshmark.com"
        target_sites = str(params.get("target_sites", default_targets))
        num_per_site = int(params.get("num_per_site", 2))  # Links to grab from *each* target site
        num_general = int(params.get("num_general", 10))  # Links to grab from general search for discovery

        # --- Genetic Learning Params ---
        learn_new_sites = bool(params.get("learn_new_sites", True))
        learned_sites_key = str(params.get("learned_sites_key", "web_learned_sites"))
        learn_min_hits = int(params.get("learn_min_hits", 2))  # Hits needed to learn a new site
        default_junk = "pinterest.com,twitter.com,facebook.com,reddit.com,ebay.com,walmart.com,amazon.com,youtube.com,tiktok.com,instagram.com,linkedin.com"
        junk_domains = str(params.get("junk_domains", default_junk))

        # --- text handling ---
        # [FIX] Re-added missing parameter definitions
        regex_query = params.get("regex")
        neg = [s.strip() for s in str(params.get("neg", "")).split(",") if s.strip()]
        must_terms = [s.strip().lower() for s in str(params.get("must_terms", "")).split(",") if s.strip()]
        # ---
        top_k_docs = int(params.get("top_k_docs", 10))
        top_k_sents = int(params.get("top_k_sents", 25))
        sent_window = int(params.get("sent_window", 1))
        max_chars = int(params.get("max_chars", 4000))
        min_doc_chars = int(params.get("min_doc_chars", 250))  # Lower for item pages
        site_exclude = [s.strip().lower() for s in str(params.get("site_exclude", "")).split(",") if s.strip()]

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
            "engine": "hybrid_ddgs_playwright", "query": query, "headless": headless,
            "search_results": [], "scrape_errors": [], "scraped_urls": [], "search_method": "unknown",
            "learned_sites": [], "newly_learned": []
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
                # Remove 'www.' and other common subdomains
                parts = netloc.split('.')
                if len(parts) > 2 and parts[0] in ('www', 'm', 'blog', 'shop'):
                    return ".".join(parts[1:])
                return netloc.split(":")[0]
            except Exception:
                return ""

        def _hybrid_search(q: str, n: int) -> List[Dict[str, str]]:
            # 1. Prefer python package
            try:
                if verbose: print(f"[PlaywrightBlock] Searching (via DDGS library) for: {q}", file=sys.stderr)
                with DDGS() as ddgs:
                    out = []
                    for r in ddgs.text(q, max_results=n):
                        url = r.get("href") or r.get("url")
                        title = r.get("title") or _clean_domain(url)
                        if url: out.append({"title": title, "url": url})
                if out:
                    meta["search_method"] = "ddgs_library"
                    return out
            except Exception as e:
                if verbose: print(f"[PlaywrightBlock] DDGS library failed: {e}", file=sys.stderr)
                pass  # Fallback

            # 2. HTML-lite fallback
            if verbose: print(f"[PlaywrightBlock] Searching (via requests fallback) for: {q}", file=sys.stderr)
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
                if verbose: print(f"[PlaywrightBlock] Requests fallback failed: {e}", file=sys.stderr)
                pass

            meta["search_method"] = "failed"
            return []

        # ---- Playwright Search + Scrape ----
        docs_raw: List[Dict[str, str]] = []

        if not query:
            base = "" if payload is None else str(payload)
            return base, {"rows": 0, "note": "empty query", "engine": "playwright_hybrid"}

        # --- 1. SEARCH (GENETIC LEARNING) ---
        search_links = []
        seen_urls = set()

        # 1a. Build domain lists
        store = Memory.load()

        # Build master list of "good" sites
        sites_to_search: Set[str] = set()
        for s in target_sites.split(","):
            if s.strip(): sites_to_search.add(s.strip())

        if learn_new_sites:
            learned_sites = store.get(learned_sites_key, [])
            if isinstance(learned_sites, list):
                for s in learned_sites:
                    sites_to_search.add(str(s))
        meta["learned_sites"] = list(sites_to_search)

        # Build master list of "bad" sites
        junk_list: Set[str] = set()
        for s in junk_domains.split(","):
            if s.strip(): junk_list.add(s.strip())
        for s in site_exclude:
            if s.strip(): junk_list.add(s.strip())

        try:
            # 1b. Run TARGETED queries on all "good" sites
            if verbose: print(f"[PlaywrightBlock] Running targeted search on {len(sites_to_search)} known sites...",
                              file=sys.stderr)
            for site in sites_to_search:
                targeted_query = f'{query} site:{site}'
                links = _hybrid_search(targeted_query, n=num_per_site)
                for link in links:
                    url = link["url"]
                    if url not in seen_urls:
                        seen_urls.add(url)
                        search_links.append(link)

            # 1c. Run GENERAL query for discovery
            if verbose: print(f"[PlaywrightBlock] Running general search for discovery...", file=sys.stderr)
            general_links = _hybrid_search(query, n=num_general)

            new_domain_counts: Dict[str, int] = defaultdict(int)
            discovered_links: List[Dict] = []

            for link in general_links:
                url = link["url"]
                if url in seen_urls:
                    continue

                domain = _clean_domain(url)
                if not domain:
                    continue

                # Check if junk or already known
                if any(domain == s or domain.endswith("." + s) for s in junk_list):
                    continue
                if any(domain == s or domain.endswith("." + s) for s in sites_to_search):
                    continue

                # This is a new, non-junk, non-target domain
                new_domain_counts[domain] += 1
                discovered_links.append(link)  # Add it to scrape
                seen_urls.add(url)

            # 1d. Learn & Evolve
            newly_learned_sites: List[str] = []
            if learn_new_sites:
                for domain, count in new_domain_counts.items():
                    if count >= learn_min_hits:
                        newly_learned_sites.append(domain)

                if newly_learned_sites:
                    if verbose: print(
                        f"[PlaywrightBlock] Learning {len(newly_learned_sites)} new domains: {newly_learned_sites}",
                        file=sys.stderr)
                    # Add to master list and save
                    current_learned = set(store.get(learned_sites_key, []))
                    current_learned.update(newly_learned_sites)
                    store[learned_sites_key] = list(current_learned)
                    Memory.save(store)
                    meta["newly_learned"] = newly_learned_sites

            # 1e. Finalize scrape list
            search_links.extend(discovered_links)
            search_links = search_links[:num_results]  # Limit *total* scrapes

            if verbose: print(f"[PlaywrightBlock] Total {len(search_links)} links to scrape.", file=sys.stderr)
            meta["search_results"] = search_links
            if not search_links:
                print(f"[PlaywrightBlock] ERROR: No search results found for query: {query}", file=sys.stderr)

        except Exception as e:
            print(f"[PlaywrightBlock] FATAL ERROR during search step: {e}", file=sys.stderr)
            return str(payload), {"error": f"Search failed: {e}", **meta}

        # 2. SCRAPE (using Playwright)
        try:
            with sync_playwright() as p:
                if verbose: print(f"[PlaywrightBlock] Launching browser (headless={headless})...", file=sys.stderr)
                browser = p.chromium.launch(headless=headless, args=["--disable-blink-features=AutomationControlled"])
                b_context = browser.new_context(user_agent=user_agent, java_script_enabled=True)
                b_context.set_default_timeout(timeout_ms)
                page = b_context.new_page()

                for link in search_links:
                    try:
                        if verbose: print(f"[PlaywrightBlock] Scraping: {link['url']}", file=sys.stderr)
                        page.goto(link["url"], timeout=timeout_ms, wait_until="domcontentloaded")
                        page.wait_for_timeout(1000)  # Give JS time to render
                        html = page.content()

                        text = trafilatura.extract(
                            html,
                            include_comments=False,
                            include_tables=False,
                            deduplicate=True
                        )
                        if text and len(text) >= min_doc_chars:
                            docs_raw.append({"title": link["title"], "text": text, "url": link["url"]})
                            meta["scraped_urls"].append(link["url"])
                        elif verbose:
                            print(f"[PlaywrihtBlock] INFO: Scraped text too short or empty for {link['url']}",
                                  file=sys.stderr)
                    except Exception as e:
                        err_msg = f"{link['url']}: {str(e)[:100]}"
                        if verbose: print(f"[PlaywrightBlock] SCRAPE_ERROR: {err_msg}", file=sys.stderr)
                        meta["scrape_errors"].append(err_msg)

                if verbose: print(f"[PlaywrightBlock] Closing browser.", file=sys.stderr)
                browser.close()

        except Exception as e:
            print(f"[PlayWwrightBlock] FATAL ERROR during Playwright scrape: {e}", file=sys.stderr)
            return str(payload), {"error": f"Playwright execution failed: {e}", **meta}

        # ---- 3. Post-Processing ----
        if verbose: print(f"[PlaywrightBlock] Post-processing {len(docs_raw)} scraped documents...", file=sys.stderr)

        if not docs_raw:
            base = "" if payload is None else str(payload)
            print(f"[PlaywrightBlock] ERROR: No pages were successfully scraped.", file=sys.stderr)
            return base, {
                "rows": 0, "note": "no pages matched or scraped",
                "engine": "playwright_hybrid", "query": query, "regex": bool(q_pattern),
                "neg": neg, "must": must_terms, **meta
            }

        # ---- ranking BM25-ish (+ regex boost) ----
        corpus_tokens = [set(_tokenize(d["title"] + " " + d["text"])) for d in docs_raw]
        N = len(corpus_tokens)
        q_terms = set(_tokenize(query))
        df: Dict[str, int] = {}
        for terms in corpus_tokens:
            for t in terms:
                df[t] = df.get(t, 0) + 1

        def _bm25ish_score(doc_text: str, doc_url: str) -> float:
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

            # Boost scores for all "good" sites (targeted + learned)
            doc_domain = _clean_domain(doc_url)
            if any(doc_domain == s or doc_domain.endswith("." + s) for s in sites_to_search):
                score += 1.0
            return score

        ranked = sorted(
            docs_raw,
            key=lambda d: _bm25ish_score(d["title"] + " " + d["text"], d["url"]),
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
                if q_pattern and q_pattern.search(s): overlap += 2
                if overlap > 0: scored.append((float(overlap), idx, s))

            took = 0
            for _, idx, _ in sorted(scored, key=lambda x: (-x[0], x[1]))[:per_doc_quota]:
                lo = max(0, idx - sent_window);
                hi = min(len(sents), idx + sent_window + 1)
                chunk = " ".join(sents[lo:hi]).strip()
                if chunk and chunk not in hit_sents:
                    src = f"# {title} — {d.get('url', '')}".strip()
                    if src not in hit_sents:  # Avoid repeating title
                        hit_sents.append(src)
                    hit_sents.append(chunk);
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

        # ---- lexicon (from context) ----
        def _extract_terms_local(text: str, *, top_k: int = 50, min_len: int = 4) -> List[str]:
            counts: Dict[str, int] = {}
            for raw in text.split():
                w = "".join(ch.lower() for ch in raw if ch.isalnum() or ch in "-_")
                if len(w) < min_len or w in _STOPWORDS: continue
                counts[w] = counts.get(w, 0) + 1
            return [t for t, _ in sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:top_k]]

        lexicon = _extract_terms_local(context, top_k=lexicon_top_k, min_len=lexicon_min_len) if context else []
        if use_phrases and context:
            phrases = re.findall(r"\b([A-Za-z0-9][A-Za-z0-9_\-]+(?:\s+[A-Za-z0-9][A-Za-z0-9_\-]+){1,3})\b", context)
            pc: Dict[str, int] = {}
            for ph in phrases:
                ph = ph.lower().strip()
                if any(tok in _STOPWORDS for tok in ph.split()): continue
                pc[ph] = pc.get(ph, 0) + 1
            phrase_top = [p for p, _ in sorted(pc.items(), key=lambda kv: (-kv[1], kv[0]))[:10]]
            lexicon = list(dict.fromkeys(phrase_top + lexicon))[:lexicon_top_k]

        # ---- store lexicon + context in Memory ----
        if export_lexicon and lexicon:
            store = Memory.load()
            store[lexicon_key] = lexicon
            Memory.save(store)
            if verbose: print(f"[PlaywrightBlock] Exported {len(lexicon)} terms to memory[{lexicon_key}]",
                              file=sys.stderr)

        if export_context and context:
            store = Memory.load()
            if append_ctx and isinstance(store.get(context_key), str) and store[context_key]:
                store[context_key] = store[context_key].rstrip() + "\n\n" + context
            else:
                store[context_key] = context
            Memory.save(store)
            if verbose: print(f"[PlaywrightBlock] Exported {len(context)} chars to memory[{context_key}]",
                              file=sys.stderr)

        # ---- compose output ----
        base = "" if payload is None else str(payload)
        parts: List[str] = [base] if base else []
        if inject_lexicon and lexicon:
            parts.append("[lexicon]\n" + ", ".join(lexicon))
        if inject_context and context:
            parts.append("[context]\n" + context)
        out = "\n\n".join(parts).strip()

        if verbose: print(f"[PlaywrightBlock] Execution complete. Outputting {len(out)} chars.", file=sys.stderr)

        # ---- final metadata ----
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
        })
        return out, meta

BLOCKS.register("playwright", PlaywrightBlock)
@dataclass
class TensorBlock(BaseBlock):
    """
    Runs a local Hugging Face transformers model for tasks like
    classification, NER, text-generation, etc. to add "intelligence"
    to the payload and pipeline.

    NEW Features:
    - `text2text-generation` and `summarization` tasks.
    - `device="auto"` for GPU support.
    - `auto_keywords_key="mem_key"`: Automatically extracts keywords/entities
      from NER or generation and saves them to a memory key for other
      blocks (like WebCorpus) to use.
    - `generation_prompt="task: {payload}"`: Template for generation tasks.
    - `verbose=true` for quieter logging by default.

    Requires: `pip install transformers torch`
    (And for some tasks: `pip install sentencepiece`)
    """

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        text = str(payload or "")
        if not text:
            return "", {"error": "TensorBlock received empty payload."}

        # --- Get parameters ---
        task = str(params.get("task", "zero-shot-classification"))
        model = params.get("model")  # None lets pipeline pick default
        model_name = str(model) if model else f"default_for_{task}"

        # New device/logging params
        device = params.get("device", "auto")  # "auto", "cpu", 0, 1, etc.
        verbose = bool(params.get("verbose", False))

        # New integration params
        auto_keywords_key = params.get("auto_keywords_key")  # e.g., "tensor_keywords"
        generation_prompt = str(params.get("generation_prompt", "{payload}"))

        # Output/injection params
        output_key = params.get("output_key")  # Save full JSON result to memory
        inject_format = str(params.get("inject_format", "simple")).lower()
        inject_tag = str(params.get("inject_tag", task))
        sep = str(params.get("sep", "\n\n"))

        meta = {"task": task, "model": model_name}

        # --- Get cached pipeline ---
        pipe = _get_hf_pipeline(task, model_name if model else None, device=device, verbose=verbose)
        if pipe is None:
            return text, {"error": "Failed to load HF pipeline. See console logs."}
        meta["device"] = str(pipe.device)

        # --- Task-specific arguments ---
        kwargs = {}
        run_text = text
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
            run_text = generation_prompt.format(payload=text)
            kwargs["max_new_tokens"] = int(params.get("max_new_tokens", 50))
            kwargs["do_sample"] = bool(params.get("do_sample", False))
        elif task == "summarization":
            kwargs["min_length"] = int(params.get("min_length", 10))
            kwargs["max_length"] = int(params.get("max_length", 100))

        # --- Run Prediction ---
        try:
            prediction = pipe(run_text, **kwargs)
            meta["prediction_raw"] = prediction
        except Exception as e:
            return text, {"error": f"Prediction failed: {e}", "meta": meta}

        # --- Store in Memory (if requested) ---
        if output_key:
            try:
                store = Memory.load()
                store[output_key] = prediction
                Memory.save(store)
                meta["output_key"] = output_key
            except Exception as e:
                meta["memory_error"] = str(e)

        # --- [NEW] Auto-Keyword Saving ---
        keywords_to_save = []
        if auto_keywords_key:
            try:
                if task == "ner" and prediction:
                    keywords_to_save = [e['word'] for e in prediction if 'word' in e]
                elif task == "text2text-generation" and prediction:
                    # Assumes model was prompted to return comma-separated terms
                    gen_text = prediction[0]['generated_text']
                    keywords_to_save = [k.strip() for k in gen_text.split(",") if k.strip()]

                if keywords_to_save:
                    store = Memory.load()
                    # Append to existing list if one is there
                    existing = store.get(auto_keywords_key, [])
                    if isinstance(existing, list):
                        keywords_to_save = list(dict.fromkeys(existing + keywords_to_save))

                    store[auto_keywords_key] = keywords_to_save
                    Memory.save(store)
                    meta["auto_keywords_key"] = auto_keywords_key
                    meta["auto_keywords_saved"] = len(keywords_to_save)

            except Exception as e:
                meta["auto_keywords_error"] = str(e)

        # --- Inject into Payload (if requested) ---
        injection = ""
        if inject_format == "simple":
            try:
                if task == "zero-shot-classification" and prediction:
                    top_label = prediction['labels'][0]
                    top_score = prediction['scores'][0]
                    injection = f"[{inject_tag}]\nlabel: {top_label}, score: {top_score:.4f}"
                elif task == "ner" and prediction:
                    entities = [f"{e['word']} ({e['entity_group']})" for e in prediction]
                    if entities:
                        injection = f"[{inject_tag}]\n" + ", ".join(entities)
                elif task == "sentiment-analysis" and prediction:
                    p = prediction[0]
                    injection = f"[{inject_tag}]\nlabel: {p['label']}, score: {p['score']:.4f}"
                elif (task == "text2text-generation" or task == "summarization") and prediction:
                    injection = f"[{inject_tag}]\n{prediction[0]['generated_text']}"
            except Exception as e:
                meta["inject_error"] = f"Failed to create simple injection: {e}"

        elif inject_format == "json" and prediction:
            try:
                injection = f"[{inject_tag}]\n{_json.dumps(prediction)}"
            except Exception as e:
                meta["inject_error"] = f"Failed to create JSON injection: {e}"

        # --- Assemble final payload ---
        parts = [text]
        if injection:
            parts.append(injection)

        out = sep.join(parts)
        return out, meta

BLOCKS.register("tensor", TensorBlock)


# ---------------- Code Generation (Specialized, no-guides/no-fallbacks) ----------------
@dataclass
class CodeBlock(BaseBlock):

    # ---- helpers -------------------------------------------------
    def _trim_to_tokens(self, pipe, text: str, max_input_tokens: int = 480) -> str:
        """Trim prompt by tokenizer length (keep task head + tail)."""
        try:
            tok = pipe.tokenizer
            ids = tok.encode(text, add_special_tokens=False)
            if len(ids) <= max_input_tokens:
                return text
            keep_head = min(128, max_input_tokens // 3)
            keep_tail = max_input_tokens - keep_head
            head_ids = ids[:keep_head]
            tail_ids = ids[-keep_tail:]
            return tok.decode(head_ids, skip_special_tokens=True) + "\n...\n" + tok.decode(tail_ids, skip_special_tokens=True)
        except Exception:
            return text[:4000]

    def _extract_code_block(self, s: str, lang: str = "python") -> str:
        """Extract the largest fenced code block; if none, return raw generation."""
        s = s.strip()
        if "```" not in s:
            return s
        parts = s.split("```")
        best = ""
        for i in range(1, len(parts), 2):
            block = parts[i]
            if block.startswith(lang):
                block = block[len(lang):].lstrip()
            if len(block) > len(best):
                best = block
        return best.strip() or s

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

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        # Inputs
        user_prompt = str(params.get("prompt", "")).strip()
        if not user_prompt:
            return str(payload), {"error": "CodeBlock requires 'prompt' param (e.g., --extra code.prompt=...)"}

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
        lang = str(params.get("lang", "python"))

        pipe = _get_hf_pipeline("text2text-generation", model_name, device=device, verbose=params.get("verbose", False))
        if pipe is None:
            return f"{payload}\n\n[{inject_tag}] (Model load failed)", {"error": "pipeline_failed"}

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
            return f"{payload}\n\n[{inject_tag}] (Error: {e})", {"error": "generation_failed", "exception": str(e)}

        gen_text = ""
        try:
            if isinstance(pred, list) and pred:
                cand = pred[0]
                gen_text = cand.get("generated_text") or cand.get("summary_text") or ""
        except Exception:
            gen_text = ""

        # Post-process ONLY (no fallback synthesis)
        code_raw = self._extract_code_block(gen_text, lang="python").strip()
        code_raw = self._strip_banner_comments(code_raw)

        if wrap:
            code_out = f"```{lang}\n{code_raw}\n```"
        else:
            code_out = code_raw

        result = f"{payload}\n\n[{inject_tag}]\n{code_out}"
        meta = {
            "model": model_name,
            "context_chars": len(ctx),
            "prompt_len": len(final_prompt),
            "tokens_generated": len(code_raw),
            "beams": num_beams,
            "do_sample": do_sample,
            "temperature": temperature,
            "no_repeat_ngram_size": no_repeat_ngram_size,
            "repetition_penalty": repetition_penalty,
            "max_time_sec": max_time_sec,
            "max_input_tokens": max_input_tokens,
        }
        return result, meta


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

# Register the block
BLOCKS.register("codecorpus", CodeCorpusBlock)