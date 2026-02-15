# ========================================================
# ================  pipeline.py  =========================
# ========================================================
from __future__ import annotations

import json
import math
import re
from dataclasses import dataclass, field
from typing import Any, Dict, Tuple, List
import sys as _sys
import time

from registry import BLOCKS
import blocks  # for parse_extras


@dataclass
class ChatPipelineBlock(blocks.BaseBlock):
    """
    Orchestrates a sequence of registered blocks.

    - Stages are defined as a '|' separated string: "guard|tools|chat".
    - Per-stage params come from:
        1) global 'all' extras (all.*)
        2) stage-specific extras (e.g., pipeline.webcorpus.query=...)
    - Pipeline-level options (from 'pipeline' extras or direct params):
        * stages / pipeline / pipe : the stage string
        * stop_on_error (bool)    : stop when a stage raises or reports error
        * debug (bool)            : record in/out snippets in meta_chain
    """

    _meta_chain: List[Dict[str, Any]] = field(default_factory=list)

    # ---- extras helpers -------------------------------------------------

    def _get_all_extras(self, params: Dict[str, Any]) -> Dict[str, Dict[str, Any]]:
        """
        Gets the 'all_extras' dict.
        In GUI mode, it's passed via '_gui_extras_passthrough'.
        In CLI mode (fallback), it re-parses sys.argv.
        """
        if "_gui_extras_passthrough" in params:
            # GUI mode: The worker passed us the full extras dict
            return params["_gui_extras_passthrough"]

        # Fallback for CLI execution
        extras_raw: List[str] = []
        argv = _sys.argv[1:]
        i = 0
        while i < len(argv):
            tok = argv[i]
            if tok == "--extra" and i + 1 < len(argv):
                extras_raw.append(argv[i + 1])
                i += 2
            else:
                i += 1
        return blocks.parse_extras(extras_raw)

    def _pipeline_params(self, global_extras: Dict[str, Dict[str, Any]], params: Dict[str, Any]) -> Dict[str, Any]:
        """
        Pipeline-level params are taken from:
        1) extras['pipeline'] (if present)
        2) direct params (override extras)
        """
        merged: Dict[str, Any] = {}
        # This will grab 'pipeline.stages', 'pipeline.debug',
        # AND 'pipeline.webcorpus.query', 'pipeline.chat.style' etc.
        merged.update(global_extras.get("pipeline", {}))
        merged.update(params or {})
        return merged

    def _resolve_stages(self, params: Dict[str, Any], global_extras: Dict[str, Dict[str, Any]]) -> List[str]:
        """
        Determine the pipeline stage string from:
        - params["stages"] / params["pipeline"] / params["pipe"]
        - OR extras["pipeline"]["stages"] / ["pipe"] as a fallback
        """
        # 1) explicit params take precedence
        stages_str = params.get("stages") or params.get("pipeline") or params.get("pipe")

        # 2) fallback to extras if not provided in params
        if not stages_str:
            pipe_extras = global_extras.get("pipeline", {})
            stages_str = pipe_extras.get("stages") or pipe_extras.get("pipeline") or pipe_extras.get("pipe")

        if not isinstance(stages_str, str) or not stages_str.strip():
            raise ValueError(
                "Missing pipeline.stages. Example: "
                "--extra pipeline.stages='corpus|chat'"
            )

        stages = [s.strip() for s in stages_str.split("|") if s.strip()]
        if not stages:
            raise ValueError("Empty pipeline.stages.")
        return stages

    def _stage_params(self, stage: str, global_extras: Dict[str, Dict[str, Any]], pipe_params: Dict[str, Any]) -> Dict[
        str, Any]:
        """
        Merge parameters for a stage.

        Order (lowest → highest precedence):
          1) extras['all'].* (applies to every block)
          2) extras[stage].* (legacy, non-namespaced params, e.g., webcorpus.query)
          3) pipeline-delegated params (e.g., pipeline.webcorpus.query)
        """
        merged: Dict[str, Any] = {}

        # 1. Apply global 'all' defaults first
        merged.update(global_extras.get("all", {}))

        # 2. [NEW] Apply legacy, non-pipeline-prefixed params
        #    (e.g., --extra webcorpus.query=...)
        merged.update(global_extras.get(stage.lower(), {}))

        # 3. Extract and apply pipeline-delegated params
        #    (e.g., --extra pipeline.webcorpus.query=...)
        #    This will OVERWRITE legacy params if they conflict.
        prefix = f"{stage}."
        for k, v in pipe_params.items():
            if k.startswith(prefix):
                # 'pipeline.webcorpus.query' becomes 'query'
                sub_key = k[len(prefix):]
                merged[sub_key] = v

        return merged

    # ---- main execute ---------------------------------------------------
    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        # Get all extras, either from GUI or CLI
        all_extras = self._get_all_extras(params or {})

        # Get all parameters prefixed with 'pipeline.'
        pipe_params = self._pipeline_params(all_extras, params or {})

        # Find the 'stages' list
        stages = self._resolve_stages(pipe_params, all_extras)

        stop_on_error = bool(pipe_params.get("stop_on_error", True))
        debug = bool(pipe_params.get("debug", False))

        current = payload
        self._meta_chain.clear()

        for s in stages:
            blk = BLOCKS.create(s)

            # Get params for this specific stage (e.g., 'webcorpus')
            # This will merge 'all.*' with 'pipeline.webcorpus.*'
            stage_params = self._stage_params(s, all_extras, pipe_params)

            stage_meta: Dict[str, Any] = {"stage": s}
            start = time.time()

            if debug:
                text = current if isinstance(current, str) else str(current)
                stage_meta["in_len"] = len(text)
                stage_meta["in_preview"] = text[:160]

            try:
                out, meta = blk.execute(current, params=stage_params)
                elapsed = time.time() - start
                stage_meta.update(meta or {})
                stage_meta["elapsed_sec"] = round(elapsed, 6)

                if debug:
                    out_text = out if isinstance(out, str) else str(out)
                    stage_meta["out_len"] = len(out_text)
                    stage_meta["out_preview"] = out_text[:200]

                self._meta_chain.append(stage_meta)

                if stop_on_error and stage_meta.get("error"):
                    current = out
                    break

                current = out

            except Exception as e:
                elapsed = time.time() - start
                stage_meta.update({
                    "error": "stage_failed",
                    "exception": repr(e),
                    "elapsed_sec": round(elapsed, 6),
                })
                self._meta_chain.append(stage_meta)

                if stop_on_error:
                    break

        out = current if isinstance(current, str) else str(current)
        return out, {
            "type": "chat-pipeline",
            "stages": stages,
            "chain": self._meta_chain,
            "stop_on_error": stop_on_error,
            "debug": debug,
        }

    def get_params_info(self) -> Dict[str, Any]:
        """Returns a dictionary of default parameters for the GUI."""
        return {
            "stages": "block1|block2",
            "pipe": "block1|block2",
            # Pipeline-level options (documented defaults)
            "stop_on_error": True,
            "debug": False,
            # Example of delegated params
            "block1.param_name": "value",
            "block2.foo": 123
        }


BLOCKS.register("pipeline", ChatPipelineBlock)


# ======================= ConcatBlock =======================================
@dataclass
class ConcatBlock(blocks.BaseBlock):  # Make sure to import blocks
    """
    Joins data from the current pipeline payload and Memory into a single string.
    Useful for pipelines where an intermediate block (like Chat) 'consumes'
    context you want to see in the final output.

    NEW: Now supports `clean_artifacts=True` to remove pipeline tags
    (e.g., [lexicon], [context]) before joining.

    Params:
    - parts: Comma-separated list of sources.
        - 'payload': The input text from the previous block.
        - 'memory:key': Data stored in memory.json (e.g., 'shopping_results').
        - 'text:string': Hardcoded text literals.
    - sep: Separator between parts (default: two newlines).
    - json_indent: If a memory item is a list/dict, indent level (default 2).
    - clean_artifacts: (bool) Strip [lexicon], [context], etc., from all inputs.
    """

    def _clean_artifacts(self, text: str) -> str:
        """Removes known pipeline artifact blocks from a string."""
        known_artifacts = [
            "[lexicon]\n", "[context]\n", "[tensor]\n",
            "[zero-shot-classification]\n", "[intel_analysis]\n",
            "[code_solution]\n", "[summary]\n"
        ]
        clean_text = str(text)

        # We rsplit to remove the *last* instance of each tag block,
        # which is the most common pattern of artifact accumulation.
        for artifact in known_artifacts:
            if artifact in clean_text:
                clean_text = clean_text.rsplit(artifact, 1)[0]

        # Also clean any *stray* tags that might be on their own
        clean_text = re.sub(r"^\s*\[[a-z0-9_\-]+\]\s*$", "", clean_text, flags=re.MULTILINE)

        return clean_text.strip()

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        parts_def = str(params.get("parts", "payload"))
        sep = str(params.get("sep", "\n\n"))
        indent = int(params.get("json_indent", 2))
        clean_artifacts = bool(params.get("clean_artifacts", True))  # Default to ON

        sep = sep.replace("\\n", "\n").replace("\\t", "\t")

        store = blocks.Memory.load()
        output_segments = []
        sources_used = []

        definitions = [x.strip() for x in parts_def.split(",")]

        for d in definitions:
            content = ""

            if d == "payload":
                content = str(payload)
                if clean_artifacts:
                    content = self._clean_artifacts(content)
                sources_used.append("payload")

            elif d.lower().startswith("memory:"):
                key = d.split(":", 1)[1].strip()
                data = store.get(key)

                if data is None:
                    content = f"_(Memory key '{key}' is empty)_"
                elif isinstance(data, (dict, list)):
                    # We don't clean JSON, as it's structured data
                    content = json.dumps(data, indent=indent, ensure_ascii=False)
                else:
                    content = str(data)
                    if clean_artifacts:
                        content = self._clean_artifacts(content)

                sources_used.append(f"memory:{key}")

            elif d.lower().startswith("text:"):
                content = d.split(":", 1)[1]
                sources_used.append("text")

            if content:
                output_segments.append(content)

        final_output = sep.join(output_segments)

        return final_output, {
            "parts_count": len(output_segments),
            "sources": sources_used,
            "length": len(final_output),
            "cleaned_artifacts": clean_artifacts
        }

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "parts": "payload, text:--- ANALYSIS ---, memory:web_context",
            "sep": "\\n\\n",
            "json_indent": 2,
            "clean_artifacts": True
        }


BLOCKS.register("concat", ConcatBlock)

# ======================= QA Orchestrator (qa.* namespace) ====================
@dataclass
class QAPipelineBlock(blocks.BaseBlock):
    """
    QA wrapper pipeline that ALSO mines an extractive answer (no models).

    Configure:
      qa.stages=history|memory|playwright|news|intelligence|...

    Per-stage params:
      qa.playwright.query=...
      qa.news.preset=...
      qa.memory.op=...

    Mining params (inside qa.*):
      qa.answer_mode=auto|mine|passthrough|off
      qa.mine.max_snippets=6
      qa.mine.answer_snippets=3
      qa.mine.capture_outputs=true
      qa.mine.capture_max_chars=20000
      qa.mine.context_keys=web_context,corpus_context,code_context
      qa.mine.lexicon_keys=web_lexicon,corpus_lexicon,code_lexicon
      qa.mine.keep_history=true
      qa.mine.save_to_memory=true
      qa.mine.answer_key=qa_last_answer
      qa.mine.sources_key=qa_last_sources
      qa.mine.show_evidence=true
    """

    _meta_chain: List[Dict[str, Any]] = field(default_factory=list)

    # --- mining helpers ---------------------------------------------------
    _TAG_BLOCK_RE = re.compile(
        r"\[(?P<tag>[a-zA-Z0-9_\-]+)\]\n(?P<body>.*?)(?=\n\[[a-zA-Z0-9_\-]+\]\n|\Z)",
        re.S
    )
    _WORD_RE = re.compile(r"[a-zA-Z0-9_]+")
    _URL_RE = re.compile(r"https?://[^\s\]\)<>\"']+", re.I)
    _ISO_DATE_RE = re.compile(r"\b(20\d{2})[-/](\d{1,2})[-/](\d{1,2})\b")
    _MONTH_DATE_RE = re.compile(
        r"\b(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Sept|Oct|Nov|Dec)[a-z]*\s+\d{1,2},\s+(20\d{2})\b",
        re.I
    )

    _STOP = {
        "the","a","an","and","or","but","if","then","else","to","of","in","on","for","from","with","as",
        "is","are","was","were","be","been","being","it","its","this","that","these","those","i","you",
        "we","they","he","she","them","his","her","our","your","my","me","us",
        "do","does","did","can","could","should","would","may","might","will","just",
        "what","why","how","when","where","who","which"
    }

    def _csv(self, v: Any) -> List[str]:
        return [x.strip() for x in str(v or "").split(",") if x.strip()]

    def _extract_tag_blocks(self, text: str, tag: str) -> List[str]:
        out: List[str] = []
        for m in self._TAG_BLOCK_RE.finditer(text or ""):
            if (m.group("tag") or "").strip().lower() == tag.lower():
                body = (m.group("body") or "").strip()
                if body:
                    out.append(body)
        return out

    def _strip_trailing_blocks(self, text: str) -> str:
        t = str(text or "")
        idx = t.find("\n[")
        return (t[:idx] if idx != -1 else t).strip()

    def _tokens(self, s: str) -> List[str]:
        return [w.lower() for w in self._WORD_RE.findall(s or "")]

    def _query_terms(self, question: str, lexicon: List[str]) -> List[str]:
        q = [t for t in self._tokens(question) if t and t not in self._STOP and len(t) > 1]
        lx: List[str] = []
        for item in (lexicon or []):
            lx.extend([t for t in self._tokens(str(item)) if t and t not in self._STOP and len(t) > 1])

        seen = set()
        out: List[str] = []
        for t in q + lx:
            if t not in seen:
                seen.add(t)
                out.append(t)
        return out

    def _idf(self, candidates: List[Dict[str, Any]], terms: List[str]) -> Dict[str, float]:
        N = max(1, len(candidates))
        df = {t: 0 for t in terms}
        for c in candidates:
            toks = c["tokens"]
            for t in terms:
                if t in toks:
                    df[t] += 1
        return {t: (math.log((N + 1) / (df[t] + 1)) + 1.0) for t in terms}

    def _length_penalty(self, s: str) -> float:
        n = len(s)
        if n < 40:
            return 0.75
        if n > 600:
            return 0.70
        if n > 420:
            return 0.85
        return 1.0

    def _jaccard(self, a: set, b: set) -> float:
        if not a or not b:
            return 0.0
        inter = len(a & b)
        union = len(a | b)
        return inter / max(1, union)

    def _question_bonus(self, question: str, cand: str) -> float:
        q = (question or "").strip().lower()
        bonus = 0.0

        if q.startswith("when") or " date " in f" {q} ":
            if self._ISO_DATE_RE.search(cand) or self._MONTH_DATE_RE.search(cand):
                bonus += 0.8

        if q.startswith("who"):
            if re.search(r"\b[A-Z][a-z]+(?:\s+[A-Z][a-z]+){0,3}\b", cand):
                bonus += 0.4

        if q.startswith("how") or q.startswith("why"):
            if re.search(r"\b(because|therefore|thus|so that|in order to)\b", cand, re.I):
                bonus += 0.3

        if q.startswith(("is ", "are ", "do ", "does ", "can ", "should ")):
            if re.search(r"\b(must|cannot|can't|won't|should|recommended|not)\b", cand, re.I):
                bonus += 0.2

        return bonus

    def _split_candidates(self, sources: List[Dict[str, str]]) -> List[Dict[str, Any]]:
        """
        sources: [{"source": "...", "text": "..."}]
        returns candidates: [{"source","text","tokens","has_date"}]
        """
        out: List[Dict[str, Any]] = []
        for src in sources:
            source = src.get("source") or "unknown"
            text = (src.get("text") or "").strip()
            if not text:
                continue

            paras = [p.strip() for p in text.split("\n\n") if p.strip()]
            for p in paras:
                urls = self._URL_RE.findall(p)
                src_label = urls[0] if urls else source

                lines = [ln.strip() for ln in p.splitlines() if ln.strip()]
                for ln in lines:
                    if len(ln) < 30:
                        continue
                    if self._URL_RE.fullmatch(ln):
                        continue

                    # split mega-lines into sentence-ish chunks
                    parts = re.split(r"(?<=[\.\?\!])\s+", ln) if len(ln) > 520 else [ln]
                    for part in parts:
                        s = part.strip()
                        if len(s) < 30:
                            continue
                        out.append({
                            "source": src_label,
                            "text": s,
                            "tokens": set(self._tokens(s)),
                            "has_date": bool(self._ISO_DATE_RE.search(s) or self._MONTH_DATE_RE.search(s)),
                        })
        return out

    def _mine_answer(
        self,
        *,
        question: str,
        current_text: str,
        captured_outputs: List[Dict[str, str]],
        qa_params: Dict[str, Any],
    ) -> Tuple[str, Dict[str, Any]]:
        # mining config
        max_snippets     = int(qa_params.get("mine.max_snippets", 6))
        answer_snippets  = int(qa_params.get("mine.answer_snippets", 3))
        prefer_recency   = bool(qa_params.get("mine.prefer_recency", True))
        show_evidence    = bool(qa_params.get("mine.show_evidence", True))
        keep_history     = bool(qa_params.get("mine.keep_history", True))

        context_keys = self._csv(qa_params.get("mine.context_keys", "web_context,corpus_context,code_context"))
        lexicon_keys = self._csv(qa_params.get("mine.lexicon_keys", "web_lexicon,corpus_lexicon,code_lexicon"))

        save_to_memory = bool(qa_params.get("mine.save_to_memory", True))
        answer_key = str(qa_params.get("mine.answer_key", "qa_last_answer"))
        sources_key = str(qa_params.get("mine.sources_key", "qa_last_sources"))

        store = blocks.Memory.load()

        # lexicon gather (inline + memory)
        inline_lex: List[str] = []
        for b in self._extract_tag_blocks(current_text, "lexicon"):
            inline_lex.extend([w.strip() for w in b.split(",") if w.strip()])

        mem_lex: List[str] = []
        for k in lexicon_keys:
            v = store.get(k)
            if isinstance(v, list):
                mem_lex.extend([str(x).strip() for x in v if str(x).strip()])

        lexicon = list(dict.fromkeys([*inline_lex, *mem_lex]))

        # build source list for candidates
        sources: List[Dict[str, str]] = []

        # 1) inline [context] in current output
        for c in self._extract_tag_blocks(current_text, "context"):
            sources.append({"source": "inline:context", "text": c})

        # 2) captured stage outputs (prefer their [context] if present; else use output text)
        for item in captured_outputs:
            stage = item.get("stage") or "stage"
            txt = (item.get("text") or "").strip()
            if not txt:
                continue

            ctxs = self._extract_tag_blocks(txt, "context")
            if ctxs:
                for c in ctxs:
                    sources.append({"source": f"stage:{stage}", "text": c})
            else:
                # use the raw output as context (common for news/playwright/intelligence)
                sources.append({"source": f"stage:{stage}", "text": self._strip_trailing_blocks(txt)})

        # 3) memory contexts
        for k in context_keys:
            v = store.get(k)
            if isinstance(v, str) and v.strip():
                sources.append({"source": f"memory:{k}", "text": v.strip()})

        # dedupe sources by (source,text) rough
        seen = set()
        deduped: List[Dict[str, str]] = []
        for s in sources:
            key = (s.get("source") or "", (s.get("text") or "")[:2000])
            if key in seen:
                continue
            seen.add(key)
            deduped.append(s)
        sources = deduped

        if not sources:
            return (
                "No mined context available to answer from. "
                "Add retrieval stages that produce text/context before relying on mining."
            ), {"type": "qa-mine", "error": "no_sources"}

        # candidates
        candidates = self._split_candidates(sources)
        if not candidates:
            return "No usable snippets found to mine an answer.", {"type": "qa-mine", "error": "no_candidates"}

        # scoring
        terms = self._query_terms(question, lexicon)
        if not terms:
            terms = [t for t in self._tokens(question) if t]

        idf = self._idf(candidates, terms)

        scored: List[Dict[str, Any]] = []
        for c in candidates:
            overlap = [t for t in terms if t in c["tokens"]]
            base = sum(idf.get(t, 0.0) for t in overlap)
            bonus = self._question_bonus(question, c["text"])

            if prefer_recency and c.get("has_date"):
                bonus += 0.15

            score = (base + bonus) * self._length_penalty(c["text"])
            if score <= 0:
                continue

            scored.append({
                "score": score,
                "text": c["text"],
                "source": c["source"],
                "tokens": c["tokens"],
            })

        if not scored:
            preview = "\n".join([c["text"] for c in candidates[:8]])
            return (
                "I couldn't find strong matches to your question in the mined context.\n\n"
                f"Context preview:\n{preview}"
            ), {"type": "qa-mine", "matched": 0}

        scored.sort(key=lambda x: x["score"], reverse=True)

        # diversify (avoid near-duplicate lines)
        picked: List[Dict[str, Any]] = []
        for item in scored:
            if len(picked) >= max_snippets:
                break
            if any(self._jaccard(item["tokens"], p["tokens"]) >= 0.70 for p in picked):
                continue
            picked.append(item)

        answer_parts = [p["text"] for p in picked[:max(1, answer_snippets)]]
        answer_text = " ".join(answer_parts).strip()

        if show_evidence:
            ev = []
            for i, p in enumerate(picked, 1):
                ev.append(f"{i}. {p['text']}\n   source: {p['source']}  (score={p['score']:.3f})")
            out = f"Best-effort answer (extractive):\n{answer_text}\n\nEvidence:\n" + "\n".join(ev)
        else:
            out = f"Best-effort answer (extractive):\n{answer_text}"

        if keep_history:
            blocks.HistoryStore.append({"role": "user", "content": question})
            blocks.HistoryStore.append({"role": "assistant", "content": out})

        if save_to_memory:
            store = blocks.Memory.load()
            store[answer_key] = out
            store[sources_key] = [
                {"source": p["source"], "text": p["text"], "score": round(p["score"], 6)}
                for p in picked
            ]
            blocks.Memory.save(store)

        return out, {
            "type": "qa-mine",
            "picked": len(picked),
            "terms_used": terms[:50],
            "answer_len": len(out),
        }

    # ---- extras helpers -------------------------------------------------

    def _get_all_extras(self, params: Dict[str, Any]) -> Dict[str, Dict[str, Any]]:
        if "_gui_extras_passthrough" in (params or {}):
            return params["_gui_extras_passthrough"]

        extras_raw: List[str] = []
        argv = _sys.argv[1:]
        i = 0
        while i < len(argv):
            tok = argv[i]
            if tok == "--extra" and i + 1 < len(argv):
                extras_raw.append(argv[i + 1])
                i += 2
            else:
                i += 1
        return blocks.parse_extras(extras_raw)

    def _qa_params(self, all_extras: Dict[str, Dict[str, Any]], params: Dict[str, Any]) -> Dict[str, Any]:
        merged: Dict[str, Any] = {}
        merged.update(all_extras.get("qa", {}))   # group 'qa' (keys like 'news.limit', 'mine.max_snippets', etc.)
        merged.update(params or {})               # direct params override
        return merged

    def _resolve_stages(self, qa_params: Dict[str, Any], all_extras: Dict[str, Dict[str, Any]]) -> List[str]:
        stages_str = qa_params.get("stages") or qa_params.get("pipe") or qa_params.get("pipeline")
        if not isinstance(stages_str, str) or not stages_str.strip():
            raise ValueError("Missing qa.stages. Example: qa.stages='news|intelligence'")
        stages = [s.strip() for s in stages_str.split("|") if s.strip()]
        if not stages:
            raise ValueError("Empty qa.stages.")
        if "qa" in [s.lower() for s in stages]:
            raise ValueError("qa.stages cannot include 'qa' (would recurse).")
        return stages

    def _stage_params(self, stage: str, all_extras: Dict[str, Dict[str, Any]], qa_params: Dict[str, Any]) -> Dict[str, Any]:
        merged: Dict[str, Any] = {}

        # qa.all.* lives as keys "all.xxx" inside qa_params (because parse_extras splits on first dot only)
        for k, v in (qa_params or {}).items():
            if isinstance(k, str) and k.startswith("all."):
                merged[k[len("all."):]] = v

        # qa.<stage>.* delegated params live as "<stage>.<param>" inside qa_params
        prefix = f"{stage}."
        for k, v in (qa_params or {}).items():
            if isinstance(k, str) and k.startswith(prefix):
                merged[k[len(prefix):]] = v

        return merged

    # ---- main execute ---------------------------------------------------

    def execute(self, payload: Any, *, params: Dict[str, Any]) -> Tuple[str, Dict[str, Any]]:
        all_extras = self._get_all_extras(params or {})
        qa_params = self._qa_params(all_extras, params or {})
        stages = self._resolve_stages(qa_params, all_extras)

        stop_on_error = bool(qa_params.get("stop_on_error", True))
        debug = bool(qa_params.get("debug", False))

        # mining behavior
        answer_mode = str(qa_params.get("answer_mode", "auto")).strip().lower()
        capture_outputs = bool(qa_params.get("mine.capture_outputs", True))
        capture_max_chars = int(qa_params.get("mine.capture_max_chars", 20000))

        # the original user question should be the ORIGINAL payload (not stage-mutated)
        original_text = payload if isinstance(payload, str) else str(payload)
        question = self._strip_trailing_blocks(original_text)

        current = payload
        self._meta_chain.clear()

        captured: List[Dict[str, str]] = []

        for s in stages:
            blk = BLOCKS.create(s)
            stage_params = self._stage_params(s, all_extras, qa_params)

            stage_meta: Dict[str, Any] = {"stage": s}
            start = time.time()

            if debug:
                t = current if isinstance(current, str) else str(current)
                stage_meta["in_len"] = len(t)
                stage_meta["in_preview"] = t[:160]

            try:
                out, meta = blk.execute(current, params=stage_params)
                stage_meta.update(meta or {})
                stage_meta["elapsed_sec"] = round(time.time() - start, 6)

                if debug:
                    ot = out if isinstance(out, str) else str(out)
                    stage_meta["out_len"] = len(ot)
                    stage_meta["out_preview"] = ot[:200]

                self._meta_chain.append(stage_meta)

                # capture outputs for mining
                if capture_outputs:
                    ot = out if isinstance(out, str) else str(out)
                    if ot and ot.strip():
                        if len(ot) > capture_max_chars:
                            ot = ot[:capture_max_chars]
                        captured.append({"stage": s, "text": ot})

                if stop_on_error and stage_meta.get("error"):
                    current = out
                    break

                current = out

            except Exception as e:
                stage_meta.update({
                    "error": "stage_failed",
                    "exception": repr(e),
                    "elapsed_sec": round(time.time() - start, 6),
                })
                self._meta_chain.append(stage_meta)
                if stop_on_error:
                    break

        # passthrough/off modes
        out_text = current if isinstance(current, str) else str(current)
        if answer_mode in ("off", "passthrough"):
            return out_text, {
                "type": "qa-pipeline",
                "stages": stages,
                "chain": self._meta_chain,
                "stop_on_error": stop_on_error,
                "debug": debug,
                "answer_mode": answer_mode,
            }

        # auto/mine -> mine an answer now
        do_mine = (answer_mode == "mine") or (answer_mode == "auto")
        if do_mine:
            mined, mine_meta = self._mine_answer(
                question=question,
                current_text=out_text,
                captured_outputs=captured,
                qa_params=qa_params,
            )

            # append mining meta as a synthetic stage
            self._meta_chain.append({
                "stage": "qa_mine",
                **(mine_meta or {}),
            })

            return mined, {
                "type": "qa-pipeline",
                "stages": stages + ["qa_mine"],
                "chain": self._meta_chain,
                "stop_on_error": stop_on_error,
                "debug": debug,
                "answer_mode": answer_mode,
            }

        # fallback
        return out_text, {
            "type": "qa-pipeline",
            "stages": stages,
            "chain": self._meta_chain,
            "stop_on_error": stop_on_error,
            "debug": debug,
            "answer_mode": answer_mode,
        }

    def get_params_info(self) -> Dict[str, Any]:
        """
        Default params for GUI.
        Note: internal stage params are set via qa.<stage>.<param>=...
        and global defaults via qa.all.<param>=...
        """
        return {
            # --- Orchestrator ---
            "stages": "history|memory|playwright|news|intelligence|textminer|promptminer|displaytextminer",
            "pipe": "history|memory|playwright|news|intelligence|textminer|promptminer|displaytextminer",
            "pipeline": "history|memory|playwright|news|intelligence|textminer|promptminer|displaytextminer",
            "stop_on_error": True,
            "debug": False,

            # Answer behavior:
            #   auto  -> run mining after stages
            #   mine  -> same as auto but explicit
            #   passthrough/off -> return last stage output
            "answer_mode": "auto",

            # --- Mining strategy defaults (qa.mine.*) ---
            "mine.max_snippets": 6,  # how many evidence items to keep
            "mine.answer_snippets": 3,  # how many to stitch into the answer
            "mine.prefer_recency": True,  # small bonus for date-bearing lines
            "mine.show_evidence": True,  # include evidence list in output

            # Capture stage outputs as candidate context
            "mine.capture_outputs": True,
            "mine.capture_max_chars": 20000,

            # Where to mine context/lexicon from (Memory keys)
            "mine.context_keys": "web_context,corpus_context,code_context",
            "mine.lexicon_keys": "web_lexicon,corpus_lexicon,code_lexicon",

            # History + Memory output
            "mine.keep_history": True,
            "mine.save_to_memory": True,
            "mine.answer_key": "qa_last_answer",
            "mine.sources_key": "qa_last_sources",

            # --- Examples of delegated stage params (placeholders) ---
            # These are not applied unless you set them in extras as qa.<stage>.<param>
            "news.preset": "bbc_world",
            "news.limit": 40,
            "playwright.query": "",
            "promptminer.prompt": "{payload}",
            "memory.op": "clear",
            "memory.key": "*",
            "history.op": "clear",
        }


BLOCKS.register("qa", QAPipelineBlock)