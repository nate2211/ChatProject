# ========================================================
# ================  models.py  ===========================
# ========================================================
from __future__ import annotations
from typing import Dict, List


class BaseChatModel:
    """Minimal interface: generate purely from user text + lexicon words."""
    def generate(self, user_text: str, *, lexicon: List[str] | None = None) -> str:
        raise NotImplementedError


class LexiconFirstToyModel(BaseChatModel):
    """
    A tiny, deterministic model that tries to use lexicon terms in the reply.
    - Selects up to N lexicon terms and weaves them into a concise paragraph.
    - No personas, no guidelines, no system prompts.
    """
    def __init__(self, max_terms: int = 10) -> None:
        self.max_terms = int(max_terms)

    def generate(self, user_text: str, *, lexicon: List[str] | None = None) -> str:
        terms = list(dict.fromkeys((lexicon or [])[: self.max_terms]))  # stable unique slice
        terms_line = (", ".join(terms)) if terms else ""
        # super-simple synthesis that “leans” on the terms:
        head = "Answer (lexicon-informed):"
        body = f"{user_text}".strip()
        if terms_line:
            return f"{head}\n\n{body}\n\n[using terms] {terms_line}"
        return f"{head}\n\n{body}"


# --- simple factory ---
_MODELS: Dict[str, type[BaseChatModel]] = {
    "toy": LexiconFirstToyModel,
    "lexicon": LexiconFirstToyModel,
}

def get_chat_model(name: str = "toy", **kwargs) -> BaseChatModel:
    key = (name or "toy").lower()
    if key not in _MODELS:
        raise ValueError(f"Unknown chat model '{name}'. Available: {', '.join(sorted(_MODELS))}")
    return _MODELS[key](**kwargs)