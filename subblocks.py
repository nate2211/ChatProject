from dataclasses import dataclass
from typing import Dict, Any, List

from registry import SUB_BLOCKS
from blocks import _STOPWORDS

def _tokenize_text(text: str) -> List[str]:
    """
    Light tokenization: lowercased, alnum + internal -/' preserved.
    """
    tokens: List[str] = []
    for raw in (text or "").split():
        # Basic normalization
        w = "".join(ch.lower() for ch in raw if ch.isalnum() or ch in "'-")
        w = w.strip("'-")
        if w:
            tokens.append(w)
    return tokens

@dataclass
class BaseSubBlock:
    """Base class for sub-blocks that are called by main blocks."""
    def execute(self, value: Any, *, params: Dict[str, Any]) -> Any:
        """Sub-blocks transform a value, not a whole payload."""
        raise NotImplementedError

    def get_params_info(self) -> Dict[str, Any]:
        return {}

@dataclass
class PromptQuerySubBlock(BaseSubBlock):
    def _clean_tokens(self, tokens: List[str]) -> List[str]:
        return [t for t in tokens if t not in _STOPWORDS]

    def _segment_query(
        self,
        query: str,
        tokens: List[str],
        clean_tokens: List[str]
    ) -> List[str]:
        """
        Heuristic splitter for queries like:
          'raf simons ss15 ss16 ss17 sterling ruby his work at prada'

        Produces anchored, natural queries like:
          'raf simons ss15'
          'raf simons ss16'
          'raf simons ss17'
          'raf simons sterling ruby'
          'raf simons his work at prada'
          'raf simons prada'
        """
        import re

        if len(tokens) < 3:
            return []

        lower_tokens = [t.lower() for t in tokens]

        # Anchor: usually a name/brand at the front (first 1–2 tokens)
        anchor_tokens = tokens[:2] if len(tokens) >= 2 else tokens[:1]
        anchor = " ".join(anchor_tokens).strip()
        if not anchor:
            return []

        segments: List[str] = []

        # --- Seasons: ss15 / fw14 / aw13 / ss2015 etc. ---
        season_re = re.compile(r"^(ss\d{2,4}|fw\d{2,4}|aw\d{2,4})$", re.IGNORECASE)
        for i, tok in enumerate(lower_tokens):
            if season_re.match(tok):
                seg = f"{anchor} {tokens[i]}"
                segments.append(seg.strip())

        # --- Collab: 'sterling ruby' ---
        for i in range(len(lower_tokens) - 1):
            if lower_tokens[i] == "sterling" and lower_tokens[i + 1] == "ruby":
                seg = f"{anchor} sterling ruby"
                segments.append(seg.strip())
                break

        # --- Work at/with brand: '* work at prada' / '* work with prada' / '* prada' ---
        if "prada" in lower_tokens:
            idx = lower_tokens.index("prada")
            start = max(0, idx - 3)
            phrase = " ".join(tokens[start:idx + 1]).strip()  # e.g. 'his work at prada'
            if phrase:
                seg = f"{anchor} {phrase}"
                segments.append(seg.strip())

            # Also a simpler 'anchor prada' query
            seg2 = f"{anchor} prada"
            segments.append(seg2.strip())

        # Dedup while preserving order
        out: List[str] = []
        seen = set()
        for s in segments:
            if s and s not in seen:
                seen.add(s)
                out.append(s)
        return out

    def _post_filter_queries(self, queries: List[str], original_tokens: List[str]) -> List[str]:
        """
        Drop weird fragments and anything that is basically the whole prompt.

        Rules:
          - Hard cap on max length (e.g. 6 tokens).
          - If a candidate has length >= original_len - 1 (for long prompts),
            drop it as "too close" to the original.
          - Keep only queries with enough non-stopword content.
        """
        out: List[str] = []
        seen = set()

        orig_len = len(original_tokens)
        max_tokens = 6  # global max length for any query

        for q in queries:
            q = q.strip()
            if not q or q in seen:
                continue

            toks = _tokenize_text(q)
            if not toks:
                continue

            # Drop very long queries
            if len(toks) > max_tokens:
                continue

            # If original prompt is long (>=5 tokens), drop queries that are
            # almost as long as the original (e.g. len >= orig_len - 1)
            if orig_len >= 5 and len(toks) >= max(orig_len - 1, 4):
                continue

            lower = [t.lower() for t in toks]
            non_stop = [t for t in lower if t not in _STOPWORDS]

            # Allow important single-term queries like 'prada'
            if len(toks) == 1:
                if lower[0] not in {"raf", "simons", "sterling", "ruby", "prada"}:
                    continue

            # For 2-token queries, require at least 1 non-stopword
            if len(toks) == 2 and len(non_stop) == 0:
                continue

            # For longer queries, require at least 2 non-stopwords
            if len(toks) > 2 and len(non_stop) < 2:
                continue

            seen.add(q)
            out.append(q)

        return out

    def execute(self, value: Any, *, params: Dict[str, Any]) -> List[str]:
        query = str(value or "")
        if not query:
            return []

        op = str(params.get("op", "clean_permutate")).lower()

        tokens = _tokenize_text(query)
        clean_tokens = self._clean_tokens(tokens)
        if not clean_tokens:
            clean_tokens = tokens  # fallback

        if op == "clean":
            q = " ".join(clean_tokens).strip()
            return [q] if q else []

        if op == "clean_permutate":
            queries: List[str] = []

            # NOTE: we DO NOT append the full original query anymore.
            # NOTE: we DO NOT append a full cleaned version either if it's long.

            # 1. First 2–3 terms as core topic (usually 'raf simons' / 'raf simons ss15')
            if len(clean_tokens) > 1:
                q2 = " ".join(clean_tokens[:2]).strip()
                if q2:
                    queries.append(q2)
            if len(clean_tokens) > 2:
                q3 = " ".join(clean_tokens[:3]).strip()
                if q3:
                    queries.append(q3)

            # 2. Heuristic segments (seasons, collabs, work-at-brand)
            segments = self._segment_query(query, tokens, clean_tokens)
            queries.extend(segments)

            # 3. Dedup + natural-language filter + "no-whole-prompt" filter
            return self._post_filter_queries(queries, clean_tokens)

        # Default/passthrough
        q = query.strip()
        return [q] if q else []

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "op": "clean_permutate"
        }


# Register in the SUB_BLOCKS registry
SUB_BLOCKS.register("prompt_query", PromptQuerySubBlock)