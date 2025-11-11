# ========================================================
# ================  models.py  ===========================
# ========================================================
from __future__ import annotations
from typing import Dict, List, Tuple
import re


class BaseChatModel:
    """Minimal interface: generate purely from user text + lexicon words."""
    def generate(self, user_text: str, *, lexicon: List[str] | None = None, **kwargs) -> str:
        raise NotImplementedError


class LexiconFirstToyModel(BaseChatModel):
    """
    A tiny, deterministic model that tries to use lexicon terms in the reply.
    - Selects up to N lexicon terms and weaves them into a concise paragraph.
    - No personas, no guidelines, no system prompts.
    """
    def __init__(self, max_terms: int = 10) -> None:
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

    def __init__(self, max_terms: int = 12) -> None:
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


# --- simple factory ---
_MODELS: Dict[str, type[BaseChatModel]] = {
    "toy": LexiconFirstToyModel,
    "lexicon": LexiconFirstToyModel,
    # New registrations:
    "lexicon-adv": LexiconAdvanceModel,
    "adv": LexiconAdvanceModel,
}

def get_chat_model(name: str = "toy", **kwargs) -> BaseChatModel:
    key = (name or "toy").lower()
    if key not in _MODELS:
        raise ValueError(f"Unknown chat model '{name}'. Available: {', '.join(sorted(_MODELS))}")
    return _MODELS[key](**kwargs)