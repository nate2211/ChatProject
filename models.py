# ========================================================
# ================  models.py  ===========================
# ========================================================
from __future__ import annotations
from typing import Dict, List, Tuple, Any
import re


class BaseChatModel:
    """Minimal interface: generate purely from user text + lexicon words."""
    def generate(self, user_text: str, *, lexicon: List[str] | None = None, **kwargs) -> str:
        raise NotImplementedError

    def get_params_info(self) -> Dict[str, Any]:
        """Returns a dictionary of default parameters for the GUI."""
        return {}


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
    "hf-llm":       HFLocalLLMModel,   # <-- NEW key
}

def get_chat_model(name: str = "toy", **kwargs) -> BaseChatModel:
    key = (name or "toy").lower()
    if key not in _MODELS:
        raise ValueError(f"Unknown chat model '{name}'. Available: {', '.join(sorted(_MODELS))}")
    return _MODELS[key](**kwargs)