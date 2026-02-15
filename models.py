# ========================================================
# ================  models.py  ===========================
# ========================================================
from __future__ import annotations

import math
from datetime import timezone, datetime
from typing import Dict, List, Tuple, Any, Optional
import re


class BaseChatModel:
    """Minimal interface: generate purely from user text + lexicon words."""
    def generate(self, user_text: str, *, lexicon: List[str] | None = None, **kwargs) -> str:
        raise NotImplementedError

    def get_params_info(self) -> Dict[str, Any]:
        """Returns a dictionary of default parameters for the GUI."""
        return {}


class SmartMiningChatModel(BaseChatModel):
    """
    SmartMiningChatModel: a lightweight, deterministic “mining” chat model.

    Goal:
      - Use (context + lexicon + user prompt) to write its OWN natural language answer.
      - No dependence on TextMiner/PromptMiner formatting.
      - Designed so its output can be fed through miners later.

    How it stays “smart” without an LLM:
      - Parses the provided context into candidate “units” (news-like items, link items, paragraphs).
      - Builds dynamic stopwords from the context itself (no big static lists).
      - Scores units using TF-IDF cosine similarity to the prompt (and a smaller lexicon bias).
      - Chooses ONE dominant topic cluster based on the prompt (news vs. links vs. prose vs. code),
        so it doesn’t mix unrelated stuff (e.g., news + Raf Simons) unless the prompt asks for both.
      - Generates a short coherent answer with optional “Sources” links.

    generate() supports:
      - user_text: str
      - context: str | None
      - lexicon: list[str] | None
      - kwargs:
          max_chars: clamp final output length (0 disables)
          max_items: how many mined units to use (default 6)
          min_sim: similarity threshold (default 0.08)
          include_sources: include Sources section (default True)
          prefer_recency: for news items with timestamps (default True)
    """

    _WORD_RE = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_\-]{2,}")
    _URL_RE = re.compile(r"https?://[^\s\"'<>\\)\]]+", re.I)

    _PUBLISHED_RE = re.compile(r"\(Published:\s*([^)]+)\)", re.I)
    _DASH_SPLIT_RE = re.compile(r"\s+[—-]\s+")  # title — summary, title — url
    _CODE_FENCE_RE = re.compile(r"```", re.M)

    def __init__(self, max_items_default: int = 6, **_: object) -> None:
        self.max_items_default = int(max_items_default)

    # ------------------------- token utils -------------------------
    def _tokens(self, s: str) -> List[str]:
        return [m.group(0).lower() for m in self._WORD_RE.finditer(s or "")]

    def _dedupe(self, xs: List[str]) -> List[str]:
        return list(dict.fromkeys([x for x in xs if x]))

    # ------------------------- context parsing -------------------------
    def _strip_tags(self, text: str) -> str:
        t = (text or "").strip()
        if "[context]" in t:
            try:
                t = t.split("[context]\n", 1)[1]
            except Exception:
                pass
        if "[lexicon]" in t:
            t = t.split("[lexicon]", 1)[0].strip()
        return t

    def _split_units(self, context: str) -> List[Dict[str, Any]]:
        """
        Produces “units” with fields:
          - kind: news | link | code | prose | short
          - text: full original unit text
          - title/summary/url/published (when detected)
        """
        t = self._strip_tags(context)
        if not t:
            return []

        # If code fences exist, split around them so code doesn't pollute prose/news scoring
        if "```" in t:
            parts = t.split("```")
            units: List[Dict[str, Any]] = []
            for i, p in enumerate(parts):
                p = p.strip("\n").strip()
                if not p:
                    continue
                if i % 2 == 1:
                    # code block (may start with lang)
                    units.append({"kind": "code", "text": p})
                else:
                    units.extend(self._split_textish_units(p))
            return units[:800]

        return self._split_textish_units(t)[:800]

    def _split_textish_units(self, t: str) -> List[Dict[str, Any]]:
        # Prefer paragraph blocks
        paras = [p.strip() for p in re.split(r"\n{2,}", t) if p.strip()]
        if len(paras) >= 4:
            blocks = paras
        else:
            # Fall back to meaningful lines
            lines = [ln.strip() for ln in t.splitlines() if ln.strip()]
            blocks = [ln for ln in lines if len(ln) >= 25] or paras or lines

        out: List[Dict[str, Any]] = []
        for b in blocks:
            unit = self._classify_unit(b)
            out.append(unit)
        return out

    def _classify_unit(self, b: str) -> Dict[str, Any]:
        text = (b or "").strip()

        # Quick URL detection
        urls = self._URL_RE.findall(text)
        has_url = bool(urls)

        # Try parse “Published: …”
        published = ""
        m_pub = self._PUBLISHED_RE.search(text)
        if m_pub:
            published = (m_pub.group(1) or "").strip()

        # Try split “title — rest”
        title = ""
        summary = ""
        url = ""
        parts = self._DASH_SPLIT_RE.split(text, maxsplit=1)
        if len(parts) == 2:
            title = parts[0].strip()
            rest = parts[1].strip()
            if rest.lower().startswith("http://") or rest.lower().startswith("https://"):
                url = rest
            else:
                summary = rest

        # Determine kind
        kind = "prose"
        if self._CODE_FENCE_RE.search(text):
            kind = "code"
        elif published:
            kind = "news"
        elif has_url and (url or any(re.search(r"\b(poshmark|grailed|hypebeast|shop|store)\b", text, re.I) for _ in [0])):
            # keep this as "link" (shopping-like)
            kind = "link"
        elif has_url:
            kind = "link"
        elif len(text) < 140:
            kind = "short"

        unit = {
            "kind": kind,
            "text": text,
            "title": title,
            "summary": summary,
            "url": url,
            "published": published,
            "urls": urls,
        }
        return unit

    # ------------------------- scoring -------------------------
    def _build_dynamic_stopwords(self, units: List[Dict[str, Any]], top_k: int = 18) -> set:
        freq: Dict[str, int] = {}
        for u in units:
            for t in self._tokens(u.get("text", "")):
                if len(t) < 3 or t.isdigit():
                    continue
                freq[t] = freq.get(t, 0) + 1
        ranked = sorted(freq.items(), key=lambda kv: (-kv[1], kv[0]))
        return set([t for t, _ in ranked[:max(0, int(top_k))]])

    def _tfidf_prepare(self, docs_tokens: List[List[str]], stop: set) -> Tuple[List[Dict[str, float]], Dict[str, float]]:
        """
        Returns:
          - doc_tfidf: list[dict[token]=weight]
          - idf: dict[token]=idf
        """
        N = max(1, len(docs_tokens))
        df: Dict[str, int] = {}

        filtered_docs: List[List[str]] = []
        for toks in docs_tokens:
            ft = [t for t in toks if t not in stop and len(t) >= 3 and not t.isdigit()]
            filtered_docs.append(ft)
            for t in set(ft):
                df[t] = df.get(t, 0) + 1

        idf: Dict[str, float] = {}
        for t, d in df.items():
            # smooth
            idf[t] = math.log((N + 1.0) / (d + 1.0)) + 1.0

        doc_vecs: List[Dict[str, float]] = []
        for ft in filtered_docs:
            tf: Dict[str, int] = {}
            for t in ft:
                tf[t] = tf.get(t, 0) + 1
            vec: Dict[str, float] = {}
            for t, c in tf.items():
                vec[t] = (1.0 + math.log(c)) * idf.get(t, 0.0)
            doc_vecs.append(vec)

        return doc_vecs, idf

    def _cosine(self, a: Dict[str, float], b: Dict[str, float]) -> float:
        if not a or not b:
            return 0.0
        # dot
        dot = 0.0
        for k, va in a.items():
            vb = b.get(k)
            if vb is not None:
                dot += va * vb
        # norms
        na = math.sqrt(sum(v * v for v in a.values()))
        nb = math.sqrt(sum(v * v for v in b.values()))
        if na <= 0 or nb <= 0:
            return 0.0
        return float(dot / (na * nb))

    def _parse_datetime_best_effort(self, s: str) -> Optional[datetime]:
        # We don't assume formats; we just try a few conservative parses.
        ss = (s or "").strip()
        if not ss:
            return None
        # Common RSS style: "Sun, 15 Feb 2026 02:04:02 GMT"
        try:
            dt = datetime.strptime(ss, "%a, %d %b %Y %H:%M:%S %Z")
            return dt.replace(tzinfo=timezone.utc)
        except Exception:
            pass
        try:
            # ISO-ish
            dt = datetime.fromisoformat(ss.replace("Z", "+00:00"))
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=timezone.utc)
            return dt
        except Exception:
            return None

    def _recency_bonus(self, unit: Dict[str, Any]) -> float:
        if unit.get("kind") != "news":
            return 0.0
        dt = self._parse_datetime_best_effort(unit.get("published", ""))
        if not dt:
            return 0.0
        now = datetime.now(timezone.utc)
        age_days = max(0.0, (now - dt).total_seconds() / 86400.0)
        if age_days <= 1.0:
            return 0.08
        if age_days <= 3.0:
            return 0.05
        if age_days <= 7.0:
            return 0.03
        return 0.0

    def _choose_dominant_kind(self, user_text: str, units: List[Dict[str, Any]], sims: List[float]) -> str:
        """
        Pick ONE dominant kind based on the prompt + similarity mass,
        to avoid mixing unrelated content.
        """
        q = (user_text or "").lower()
        want_code = any(w in q for w in ("code", "bug", "fix", "error", "stack", "trace", "python", "c#", "c++", "js", "typescript", "regex"))
        want_news = any(w in q for w in ("news", "headline", "headlines", "world", "breaking", "latest", "politics", "war", "election"))
        want_links = any(w in q for w in ("links", "sources", "url", "website", "shop", "buy", "price", "grailed", "poshmark"))

        # soft preference when the query is tiny/empty: prefer time-sensitive news if present
        q_tokens = self._tokens(user_text)
        weak_query = len(q_tokens) < 3

        mass: Dict[str, float] = {}
        for u, sim in zip(units, sims):
            mass[u["kind"]] = mass.get(u["kind"], 0.0) + max(0.0, sim)

        # hard-ish intent hints
        if want_code and mass.get("code", 0.0) > 0:
            return "code"
        if want_news and mass.get("news", 0.0) > 0:
            return "news"
        if want_links and mass.get("link", 0.0) > 0:
            return "link"

        if weak_query and mass.get("news", 0.0) > 0:
            return "news"

        # otherwise choose by mass
        if not mass:
            return "prose"
        return max(mass.items(), key=lambda kv: kv[1])[0]

    # ------------------------- generation -------------------------
    def generate(
        self,
        user_text: str,
        *,
        context: Optional[str] = None,
        lexicon: Optional[List[str]] = None,
        **kwargs: Any,
    ) -> str:
        query = (user_text or "").strip()
        max_chars = int(kwargs.get("max_chars", 0))
        max_items = int(kwargs.get("max_items", self.max_items_default))
        max_items = max(1, min(max_items, 20))
        min_sim = float(kwargs.get("min_sim", 0.08))
        include_sources = bool(kwargs.get("include_sources", True))
        prefer_recency = bool(kwargs.get("prefer_recency", True))

        ctx = (context or "").strip()
        units = self._split_units(ctx)

        # If there is no context, we can only echo the prompt safely.
        if not units:
            out = f"{query}" if query else "No context provided."
            return (out[:max_chars] + "...") if (max_chars > 0 and len(out) > max_chars) else out

        stop = self._build_dynamic_stopwords(units, top_k=18)

        docs_tokens = [self._tokens(u.get("text", "")) for u in units]
        doc_vecs, idf = self._tfidf_prepare(docs_tokens, stop)

        # query vector
        q_tokens = [t for t in self._tokens(query) if t not in stop and len(t) >= 3 and not t.isdigit()]
        q_tf: Dict[str, int] = {}
        for t in q_tokens:
            q_tf[t] = q_tf.get(t, 0) + 1
        q_vec: Dict[str, float] = {}
        for t, c in q_tf.items():
            q_vec[t] = (1.0 + math.log(c)) * idf.get(t, 0.0)

        # lexicon bias vector (smaller weight)
        lex_toks = []
        for s in (lexicon or [])[:2500]:
            if isinstance(s, str) and s.strip():
                lex_toks.extend(self._tokens(s))
        lex_toks = [t for t in lex_toks if t not in stop and len(t) >= 3 and not t.isdigit()]
        lex_tf: Dict[str, int] = {}
        for t in lex_toks:
            lex_tf[t] = lex_tf.get(t, 0) + 1
        lex_vec: Dict[str, float] = {}
        for t, c in lex_tf.items():
            # lighter than query
            lex_vec[t] = 0.35 * (1.0 + math.log(c)) * idf.get(t, 0.0)

        # similarity per unit
        sims: List[float] = []
        for dv, u in zip(doc_vecs, units):
            sim_q = self._cosine(dv, q_vec)
            sim_l = self._cosine(dv, lex_vec) if lex_vec else 0.0
            sim = (1.00 * sim_q) + (0.35 * sim_l)
            if prefer_recency:
                sim += self._recency_bonus(u)
            sims.append(sim)

        dominant_kind = self._choose_dominant_kind(query, units, sims)

        # pick top items from that kind only
        ranked = sorted(
            [(s, i) for i, s in enumerate(sims) if units[i]["kind"] == dominant_kind],
            key=lambda x: x[0],
            reverse=True,
        )

        picked: List[Dict[str, Any]] = []
        for s, i in ranked:
            if len(picked) >= max_items:
                break
            if s < min_sim and len(picked) > 0:
                break
            picked.append(units[i])

        # fallback: if nothing meets threshold in dominant kind, take global top few
        if not picked:
            ranked_all = sorted([(s, i) for i, s in enumerate(sims)], key=lambda x: x[0], reverse=True)
            for s, i in ranked_all[:max_items]:
                picked.append(units[i])

        # write an actual “chat answer”
        out_lines: List[str] = []

        if dominant_kind == "news":
            out_lines.append("Here’s what the context indicates (news-focused):")
            out_lines.append("")
            for u in picked:
                title = (u.get("title") or "").strip()
                summary = (u.get("summary") or "").strip()
                published = (u.get("published") or "").strip()

                # If our parser didn’t split title/summary well, just use the raw text
                if not title:
                    raw = u.get("text", "")
                    out_lines.append(f"• {raw}")
                    continue

                line = f"• {title}"
                if summary:
                    line += f" — {summary}"
                if published:
                    line += f" ({published})"
                out_lines.append(line)

        elif dominant_kind == "link":
            out_lines.append("Here are the most relevant links from the context:")
            out_lines.append("")
            for u in picked:
                title = (u.get("title") or "").strip()
                url = (u.get("url") or "").strip()
                if not url:
                    # fall back to any URL in text
                    urls = u.get("urls") or []
                    url = urls[0] if urls else ""
                if title and url:
                    out_lines.append(f"• {title} — {url}")
                else:
                    out_lines.append(f"• {u.get('text','')}")
        elif dominant_kind == "code":
            out_lines.append("From the provided context, here’s the most relevant code/info:")
            out_lines.append("")
            for u in picked:
                txt = (u.get("text") or "").strip()
                # keep compact
                if len(txt) > 1200:
                    txt = txt[:1200].rstrip() + "…"
                out_lines.append(txt)
                out_lines.append("")
        else:
            out_lines.append("Based on the provided context:")
            out_lines.append("")
            # concise synthesis: first 1–2 sentences from top blocks
            for u in picked:
                raw = (u.get("text") or "").strip()
                if not raw:
                    continue
                # sentence-ish split
                sents = re.split(r"(?<=[.!?])\s+", raw)
                snippet = " ".join(sents[:2]).strip()
                if snippet:
                    out_lines.append(f"- {snippet}")

        # optional sources section (URLs only, dedup)
        if include_sources:
            urls: List[str] = []
            for u in picked:
                if u.get("url"):
                    urls.append(u["url"])
                for x in (u.get("urls") or []):
                    urls.append(x)
            urls = self._dedupe([x for x in urls if isinstance(x, str) and x.strip()])
            urls = urls[:12]
            if urls:
                out_lines.append("")
                out_lines.append("Sources:")
                for u in urls:
                    out_lines.append(f"- {u}")

        out = "\n".join(out_lines).strip()

        if max_chars > 0 and len(out) > max_chars:
            out = out[:max_chars].rstrip() + "..."

        return out

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "max_items_default": self.max_items_default,
            "generate_kwargs": {
                "context": "context string to mine",
                "lexicon": "list[str] (optional bias)",
                "max_items": 6,
                "min_sim": 0.08,
                "include_sources": True,
                "prefer_recency": True,
                "max_chars": 0,
            },
        }
class LexiconFirstToyModel(BaseChatModel):
    """
    A tiny, deterministic model that tries to use lexicon terms in the reply.
    - Selects up to N lexicon terms and weaves them into a concise paragraph.
    - No personas, no guidelines, no system prompts.
    """
    # [MODIFIED] Added **_: object to ignore extra kwargs like 'max_new_tokens'
    def __init__(self, max_terms: int = 10, **_: object) -> None:
        self.max_terms = int(max_terms)

    def generate(self, user_text: str, *, lexicon: List[str] | None = None, **kwargs) -> str:
        terms = list(dict.fromkeys((lexicon or [])[: self.max_terms]))
        body = f"{(user_text or '').strip()}"
        max_chars = int(kwargs.get("max_chars", 0))
        if max_chars > 0 and len(body) > max_chars:
            body = body[:max_chars] + "..."
        if terms:
            return f"Answer (lexicon-informed):\n\n{body}\n\n[using terms] {', '.join(terms)}"
        return f"Answer (lexicon-informed):\n\n{body}"

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "max_terms": 10
        }


# ===================== NEW ADVANCED MODEL =====================

class LexiconAdvanceModel(BaseChatModel):
    """
    A deterministic, dependency-free writer that prioritizes lexicon terms.
    Features:
      • Styles: plain | bullets | outline  (default: plain)
      • Scores sentences by lexicon overlap; keeps the top K
      • De-duplicates near-identical sentences
      • Optional bold highlighting of matched terms
      • Respects max_terms (constructor) and max_chars (generate kwargs)

    Tuning kwargs accepted by generate():
      - max_chars: int     → clamp final text length (0 = unlimited)
      - style: str         → 'plain' | 'bullets' | 'outline'
      - max_bullets: int   → when non-plain styles are used (default 8)
      - highlight: bool    → bold matched terms (default True)
      - min_sent_len: int  → drop super short sentences (default 24)
      - max_sent_len: int  → drop overly long sentences (default 260)
    """

    # [MODIFIED] Added **_: object to ignore extra kwargs
    def __init__(self, max_terms: int = 12, **_: object) -> None:
        self.max_terms = int(max_terms)

    # ---------- helpers ----------
    @staticmethod
    def _normalize_whitespace(text: str) -> str:
        return re.sub(r"\s+", " ", text or "").strip()

    @staticmethod
    def _split_sentences(text: str) -> List[str]:
        # Split on sentence boundaries and newlines; keep it simple & fast.
        parts = re.split(r"(?<=[.!?])\s+|\n+", (text or "").strip())
        return [p.strip() for p in parts if p and not p.strip().startswith("#")]

    @staticmethod
    def _dedupe_keep_order(items: List[str]) -> List[str]:
        seen = set()
        out = []
        for it in items:
            key = it.lower()
            if key in seen:
                continue
            seen.add(key)
            out.append(it)
        return out

    @staticmethod
    def _score_sentence(sent: str, lex: List[str]) -> int:
        # Score by how many lexicon terms appear (word or dotted API substrings)
        s = sent.lower()
        score = 0
        for term in lex:
            t = term.lower().strip()
            if not t:
                continue
            if "." in t:
                # dotted APIs: substring match
                if t in s:
                    score += 2
            else:
                # whole-word-ish match
                if re.search(rf"\b{re.escape(t)}\b", s):
                    score += 1
        # small preference for moderately long technical lines
        if 40 <= len(sent) <= 160:
            score += 1
        return score

    @staticmethod
    def _highlight(sent: str, lex: List[str]) -> str:
        # Bold lexicon terms (basic, case-insensitive)
        out = sent
        for term in sorted(set(lex), key=lambda x: -len(x)):  # longer first to avoid nested overlaps
            if not term.strip():
                continue
            pat = re.compile(re.escape(term), re.IGNORECASE)
            out = pat.sub(lambda m: f"**{m.group(0)}**", out)
        return out

    # ---------- main ----------
    def generate(self, user_text: str, *, lexicon: List[str] | None = None, **kwargs) -> str:
        style = (kwargs.get("style") or "plain").strip().lower()
        max_bullets = int(kwargs.get("max_bullets", kwargs.get("max_terms", 8)))
        highlight = bool(kwargs.get("highlight", True))
        min_sent_len = int(kwargs.get("min_sent_len", 24))
        max_sent_len = int(kwargs.get("max_sent_len", 260))
        max_chars = int(kwargs.get("max_chars", 0))

        # Clamp lexicon to constructor-provided max_terms
        lex = list(dict.fromkeys((lexicon or [])[: self.max_terms]))

        # Extract and score candidate sentences from the provided user text
        raw_text = self._normalize_whitespace(user_text)
        candidates = self._split_sentences(raw_text)

        # Filter by length to avoid boilerplate/junk
        candidates = [s for s in candidates if min_sent_len <= len(s) <= max_sent_len]
        if not candidates:
            # Fall back: synthesize a compact response from lexicon
            summary = ", ".join(lex[:max_bullets]) if lex else "No context available."
            out = summary if style != "outline" else f"1. {summary}"
            return self._finalize(out, max_chars)

        # Score
        scored: List[Tuple[int, int, str]] = []
        for idx, s in enumerate(candidates):
            scored.append((self._score_sentence(s, lex), idx, s))

        # Take top-N sentences (stable by original order within same score)
        scored.sort(key=lambda x: (-x[0], x[1]))
        top = [s for (sc, _, s) in scored if sc > 0][:max(1, max_bullets)]
        if not top:
            # If nothing matched, keep first few filtered sentences
            top = candidates[:max(1, max_bullets)]

        # De-duplicate
        top = self._dedupe_keep_order(top)

        # Highlight (optional)
        if highlight and lex:
            top = [self._highlight(s, lex) for s in top]

        # Render by style
        if style == "bullets":
            body = "- " + "\n- ".join(top)
        elif style == "outline":
            body = "\n".join(f"{i+1}. {s}" for i, s in enumerate(top))
        else:
            # plain: make a compact paragraph
            body = " ".join(top)

        return self._finalize(body, max_chars)

    @staticmethod
    def _finalize(text: str, max_chars: int) -> str:
        text = text.strip()
        if max_chars and len(text) > max_chars:
            return text[:max_chars].rstrip() + "…"
        return text

    def get_params_info(self) -> Dict[str, Any]:
        # These are all the **kwargs
        return {
            "max_terms": 12,
            "style": "plain",
            "max_bullets": 8,
            "highlight": True,
            "min_sent_len": 24,
            "max_sent_len": 260
        }


class HFLocalLLMModel(BaseChatModel):
    """
    Local LLM wrapper using Hugging Face + transformers + torch.

    This is a generic wrapper that can be used as:

      model = HFLocalLLMModel(
          model_name="google/flan-t5-small",
          mode="seq2seq",
          max_new_tokens=256,
          temperature=0.7,
          top_p=0.9,
          top_k=50,
          device=None,
          max_chars=0,
      )

    generate(user_text, lexicon=None, style="plain", max_chars=..., max_new_tokens=..., ...)

    Notes:
      • Constructor arguments set *defaults*.
      • Per-call kwargs override those defaults.
      • Unknown kwargs are ignored.
    """

    def __init__(
        self,
        model_name: str | None = None,
        mode: str = "seq2seq",
        max_new_tokens: int = 256,
        temperature: float = 0.7,
        top_p: float = 0.9,
        top_k: int = 50,
        device: int | str | None = None,
        max_chars: int = 0,
        **_: object,  # swallow extra kwargs like max_terms, etc.
    ) -> None:
        from transformers import pipeline
        import torch

        # Mode selection: seq2seq vs causal
        self.mode = (mode or "seq2seq").lower()
        if self.mode not in {"seq2seq", "causal"}:
            self.mode = "seq2seq"

        if model_name is None:
            if self.mode == "seq2seq":
                model_name = "google/flan-t5-small"
            else:
                model_name = "gpt2"

        self.model_name = model_name

        # Store defaults (used when call doesn't override)
        self.default_max_new_tokens = int(max_new_tokens)
        self.default_temperature = float(temperature)
        self.default_top_p = float(top_p)
        self.default_top_k = int(top_k)
        self.default_max_chars = int(max_chars)

        # Device selection
        if device is None:
            if torch.cuda.is_available():
                device = 0
            else:
                device = -1
        self.device = device

        task = "text2text-generation" if self.mode == "seq2seq" else "text-generation"

        self._pipe = pipeline(
            task=task,
            model=self.model_name,
            tokenizer=self.model_name,
            device=self.device,
        )

    # ---------- helpers ----------

    def _build_prompt(
        self,
        user_text: str,
        lexicon: List[str] | None,
        style: str = "plain",
    ) -> str:
        """
        Build a simple instruction-style prompt, with optional style and lexicon hints.
        """
        user_text = (user_text or "").strip()
        lexicon = lexicon or []
        style = (style or "plain").strip().lower()

        style_hint = ""
        if style == "bullets":
            style_hint = " Respond in concise bullet points."
        elif style == "outline":
            style_hint = " Respond as a short numbered outline."

        lex_hint = ""
        if lexicon:
            uniq = list(dict.fromkeys(lexicon))
            lex_hint = " When relevant, include or address these terms: " + ", ".join(uniq) + "."

        if self.mode == "seq2seq":
            prompt = (
                "You are a concise assistant. Read the following text and respond helpfully."
                f"{style_hint}{lex_hint}\n\n"
                f"Text:\n{user_text}\n\nAnswer:"
            )
        elif self.mode == "coding":
            # We inject the "lexicon" (context) as comments at the top of the file
            context_str = ""
            if lexicon:
                # Assuming 'lexicon' here actually contains the full RAG context string
                # passed via the pipeline, not just keywords.
                lines = [f"# {line}" for line in lexicon if line.strip()]
                context_str = "\n".join(lines[:20])  # Limit context to top 20 lines to save tokens
                prompt = (
                    f"{context_str}\n\n"
                    f"# TASK: {user_text}\n"
                    f"# SOLUTION:\n"
                    f"```python\n"
                )
        else:
            prompt = (
                "User:\n"
                f"{user_text}\n\n"
                "Assistant (helpful, concise):"
                f"{style_hint}{lex_hint}\n\n"
            )
        return prompt.strip()

    # ---------- main ----------

    def generate(
        self,
        user_text: str,
        *,
        lexicon: List[str] | None = None,
        **kwargs: Any,
    ) -> str:
        # Per-call char clamp; default from constructor
        max_chars = int(kwargs.get("max_chars", self.default_max_chars))
        style = (kwargs.get("style") or "plain").strip().lower()

        prompt = self._build_prompt(user_text, lexicon, style=style)

        # Hard safety guard on prompt length
        if len(prompt) > 8000:
            prompt = prompt[-8000:]

        # Read generation parameters (per-call override > defaults)
        gen_max_new_tokens = int(kwargs.get("max_new_tokens", self.default_max_new_tokens))
        gen_temperature = float(kwargs.get("temperature", self.default_temperature))
        gen_top_p = float(kwargs.get("top_p", self.default_top_p))
        gen_top_k = int(kwargs.get("top_k", self.default_top_k))

        outputs = self._pipe(
            prompt,
            max_new_tokens=gen_max_new_tokens,
            do_sample=True,
            temperature=gen_temperature,
            top_p=gen_top_p,
            top_k=gen_top_k,
        )

        if not outputs:
            return ""

        generated = outputs[0].get("generated_text", "") or ""

        if self.mode == "causal" and generated.startswith(prompt):
            text = generated[len(prompt):].strip()
        else:
            text = generated.strip()

        if max_chars > 0 and len(text) > max_chars:
            text = text[:max_chars].rstrip() + "…"

        return text

    def get_params_info(self) -> Dict[str, Any]:
        # Report constructor defaults so GUI can surface them
        return {
            "model_name": self.model_name,
            "mode": self.mode,
            "max_new_tokens": self.default_max_new_tokens,
            "temperature": self.default_temperature,
            "top_p": self.default_top_p,
            "top_k": self.default_top_k,
            "device": self.device,
            "max_chars": self.default_max_chars,
        }


class LexiconFinalizeModel(BaseChatModel):
    """
    A "model" that doesn't generate text, but instead consolidates a messy
    pipeline payload (with context, lexicons, etc.) into a single, clean output.

    It searches for the *last* [tag] (like [summary] or [code_solution])
    and returns *only* the content that follows that tag.

    If no tags are found, it returns the original text.
    """

    # A simple regex to find any [tag] followed by a newline
    LAST_TAG_RE = re.compile(r"\[[a-zA-Z0-9_]+\]\n")

    def generate(self, user_text: str, *, lexicon: List[str] | None = None, **kwargs) -> str:
        text = user_text or ""

        # Find all matches for [tag]\n
        matches = list(self.LAST_TAG_RE.finditer(text))

        if matches:
            # Get the very last match
            last_match = matches[-1]

            # The content is everything *after* this last tag's newline
            content_start_index = last_match.end()
            content = text[content_start_index:].strip()
            return content

        # Fallback: No tags found, just return the text as-is
        return text

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "info": "This model finalizes output. It has no parameters."
        }



# --- simple factory ---
_MODELS: Dict[str, type[BaseChatModel]] = {
    "lexicon":      LexiconFirstToyModel,
    "lexicon-adv":  LexiconAdvanceModel,
    "lexicon-finalize": LexiconFinalizeModel,
    "hf-llm":       HFLocalLLMModel,
    "smart-miningchatmodel": SmartMiningChatModel
}

def get_chat_model(name: str = "toy", **kwargs) -> BaseChatModel:
    key = (name or "toy").lower()
    if key not in _MODELS:
        raise ValueError(f"Unknown chat model '{name}'. Available: {', '.join(sorted(_MODELS))}")
    return _MODELS[key](**kwargs)