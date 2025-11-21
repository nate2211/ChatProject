import requests
import html
import re
from dataclasses import dataclass
from typing import Dict, Any, List, Tuple
from urllib.parse import urljoin, urlparse
import xml.etree.ElementTree as ET
from transformers.generation.continuous_batching import requests

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
        stops = globals().get("_STOPWORDS", set())
        return [t for t in tokens if t not in stops]

    def _segment_query(self, query: str, tokens: List[str], clean_tokens: List[str]) -> List[str]:
        """
        Advanced heuristic splitter.
        Segments by:
        1. Generic Entity Chunking (Capitalized phrases)
        2. Seasonal/Time codes
        3. Prepositional phrases
        4. Sliding Window N-Grams (Fallback for lists of names)
        """
        import re
        if len(tokens) < 2:
            return []

        segments: List[str] = []

        # Anchor: First 2 clean tokens (e.g. "Yung Bans")
        anchor = " ".join(clean_tokens[:2]).strip()

        # --- 1. Entity Chunking (Consecutive Capitalized Groups) ---
        # Ideal for: "Yung Bans Playboi Carti Lil Uzi Vert" -> ["Yung Bans", "Playboi Carti", "Lil Uzi Vert"]
        current_chunk = []
        entities = []

        for tok in tokens:
            if tok[0].isupper() and tok.isalpha():
                current_chunk.append(tok)
            else:
                if current_chunk:
                    entities.append(" ".join(current_chunk))
                current_chunk = []

        # Catch tail
        if current_chunk:
            entities.append(" ".join(current_chunk))

        # If we found multiple distinct entities, add them as queries
        # Strategy: Anchor + Entity (if Entity is not Anchor)
        if len(entities) > 1:
            for ent in entities:
                if ent.lower() not in anchor.lower():
                    segments.append(f"{anchor} {ent}")
                # Also add the entity standalone if it's long enough (e.g. "Lil Uzi Vert")
                if len(ent.split()) >= 2:
                    segments.append(ent)

        # --- 2. Time & Season Codes ---
        time_re = re.compile(r"\b((?:ss|fw|aw|sp|su|fa|wi|q[1-4])\s?'?\d{2,4}|\d{4})\b", re.IGNORECASE)
        for match in time_re.finditer(query):
            matched_text = match.group(0)
            if matched_text.lower() not in anchor.lower():
                segments.append(f"{anchor} {matched_text}")

        # --- 3. Prepositional Relations ---
        prepositions = {"at", "with", "for", "in", "by", "x", "feat", "ft", "versus", "vs"}
        lower_tokens = [t.lower() for t in tokens]

        for i, tok in enumerate(lower_tokens):
            if tok in prepositions and i < len(tokens) - 1:
                # Grab context after preposition
                start = i + 1  # Skip the preposition itself for cleaner search sometimes
                end = min(len(tokens), i + 4)
                phrase = " ".join(tokens[start:end]).strip()

                if phrase and phrase not in anchor.lower():
                    segments.append(f"{anchor} {phrase}")
                    # Also try with the preposition (e.g. "x Playboi Carti")
                    segments.append(f"{anchor} {tokens[i]} {phrase}")

        # --- 4. Sliding Window (Fallback for unstructured lists) ---
        # If we haven't generated much, walk through the query in chunks of 2-3 words
        if len(segments) < 2 and len(clean_tokens) > 3:
            # Overlapping windows of 2 and 3 tokens
            for n in [2, 3]:
                for i in range(len(clean_tokens) - n + 1):
                    window = clean_tokens[i: i + n]
                    phrase = " ".join(window)
                    # Don't just add the anchor again
                    if phrase.lower() != anchor.lower():
                        # If the window is at the start, it's just a subset of anchor, ignore
                        if i > 0:
                            segments.append(f"{anchor} {phrase}")

        return list(dict.fromkeys(segments))

    def _post_filter_queries(self, queries: List[str], original_tokens: List[str]) -> List[str]:
        out: List[str] = []
        seen = set()

        # Recalculate stops locally to avoid globals issues
        stops = globals().get("_STOPWORDS", {
            "the", "and", "or", "is", "at", "which", "on", "in", "a", "an"
        })

        for q in queries:
            q = q.strip()
            if not q or q in seen:
                continue

            toks = _tokenize_text(q)
            if not toks:
                continue

            # Filter: Too long
            if len(toks) > 8:
                continue

            # Filter: Single Stopword
            if len(toks) == 1 and toks[0].lower() in stops:
                continue

            seen.add(q)
            out.append(q)
        return out

    def _hf_rewrite_queries(self, queries: List[str], params: Dict[str, Any]) -> List[str]:
        if not queries or not params.get("hf_model"):
            return queries
        # ... (Keep existing HF logic) ...
        return queries

    def _build_bar_syntax_queries(self, query: str) -> List[str]:
        """
        Special handling for queries like:
          "Lil Uzi Vert | Playboi Carti | Juice Wrld"

        We treat each '|' separated chunk as an atomic phrase and build
        permutations without breaking those phrases apart.
        """
        # Split on '|' and strip whitespace
        groups = [g.strip() for g in query.split("|") if g.strip()]
        if not groups:
            return []

        # Anchor = first phrase (e.g. "Lil Uzi Vert")
        anchor = groups[0]

        queries: List[str] = []

        # 1) Full combo: all phrases together
        full_combo = " ".join(groups)
        if full_combo:
            queries.append(full_combo)

        # 2) Anchor alone
        if anchor:
            queries.append(anchor)

        # 3) Anchor + each other phrase, and standalone phrases
        for g in groups[1:]:
            if not g:
                continue
            # Anchor + other phrase (e.g. "Lil Uzi Vert Playboi Carti")
            queries.append(f"{anchor} {g}")
            # Standalone phrase if it has at least 2 words
            if len(g.split()) >= 2:
                queries.append(g)

        # Optional: you could also add combos of non-anchor groups, e.g.
        # "Playboi Carti Juice Wrld". If you want that, uncomment:
        #
        # if len(groups) > 2:
        #     for i in range(1, len(groups)):
        #         for j in range(i + 1, len(groups)):
        #             pair = f"{groups[i]} {groups[j]}"
        #             queries.append(pair)

        # Dedupe while preserving order
        return list(dict.fromkeys(queries))

    def execute(self, value: Any, *, params: Dict[str, Any]) -> List[str]:
        query = str(value or "")
        if not query:
            return []

        op = str(params.get("op", "clean_permutate")).lower()

        # ---------- SPECIAL "A | B | C" SYNTAX ----------
        if "|" in query and op == "clean_permutate":
            # Use bar-syntax-aware grouping instead of normal segmentation
            base_queries = self._build_bar_syntax_queries(query)

            # We still want to run them through the usual filter + optional HF rewrite
            original_tokens = _tokenize_text(query)
            filtered = self._post_filter_queries(base_queries, original_tokens)
            final = self._hf_rewrite_queries(filtered, params)

            if not final:
                return [query.strip()]

            return final
        # -------------------------------------------------

        # Normal path (no '|' syntax or different op)
        tokens = _tokenize_text(query)
        clean_tokens = self._clean_tokens(tokens)
        if not clean_tokens:
            clean_tokens = tokens

        if op == "clean":
            return [" ".join(clean_tokens).strip()]

        if op == "clean_permutate":
            queries: List[str] = []

            # 1. Always include the full original query (sanitized)
            # This ensures we don't lose the user's specific intent
            full_clean = " ".join(clean_tokens)
            if full_clean:
                queries.append(full_clean)

            # 2. Anchor (First 2 words)
            if len(clean_tokens) >= 2:
                queries.append(" ".join(clean_tokens[:2]).strip())

            # 3. Segmentation Logic
            queries.extend(self._segment_query(query, tokens, clean_tokens))

            # 4. Filter
            final = self._post_filter_queries(queries, clean_tokens)

            # 5. Rewrite (optional)
            final = self._hf_rewrite_queries(final, params)

            if not final:
                return [query.strip()]

            return final

        return [query.strip()]


SUB_BLOCKS.register("prompt_query", PromptQuerySubBlock)

# ======================= NEW ENGLISH SUB-BLOCK ==========================
@dataclass
class EnglishChatSubBlock(BaseSubBlock):
    """
    A sub-block that uses an HF model to rewrite text.
    Designed to be called via `run_sub_pipeline` from a parent block.

    Operations (op=):
    - "fix_grammar": Corrects spelling and grammar.
    - "simplify": Rewrites text to be simple and easy to understand.
    - "professional": Rewrites text in a more formal, professional tone.
    - "casual": Rewrites text in a casual, friendly tone.
    - "passthrough": Returns the text unchanged (default).

    Extra handling for marketplace-style ads / listings:
    - ad_mode = "skip"    → detect listing-like blobs and return as-is (no HF).
    - ad_mode = "shorten" → detect listing-like blobs and return a short title only.
    - ad_mode = "rewrite" → detect listing-like blobs, shorten them, then send
                             that cleaned string through the HF model.
    """

    # --------- Heuristics to detect listing / ad blobs ---------
    @staticmethod
    def _is_listing_snippet(text: str) -> bool:
        """
        Very lightweight check to see if this looks like a resale / marketplace
        listing blob, e.g. Depop / Grailed / eBay style text or generic
        catalog/filter UI like "Sort By: - Size: Various".

        Heuristics:
          - Contains known marketplace keywords (depop, grailed, ebay, poshmark, etc.).
          - Contains "other shirts you may like" / "you may also like".
          - Contains multiple prices or explicit currency with symbols.
          - Lots of hyphen / ' - - ' style separators.
          - Filter UI phrases like "Sort By:" + "Size:".
        """
        import re

        t = (text or "").lower()
        if not t:
            return False

        # --- 1) Marketplace / shop / catalog phrases ---
        marketplace_keywords = [
            "depop", "grailed", "poshmark", "ebay", "vinted",
            "etsy", "stockx", "farfetch", "ssense",
            "add to bundle", "add to cart", "add to bag",
            "other shirts you may like",
            "you may also like",
            "shop now",
            "view all",
        ]
        if any(k in t for k in marketplace_keywords):
            return True

        # Filter / catalog UI patterns like your example:
        # "Raf Simons Women Sort By: - Size: Various Raf Simons $479 ..."
        if "sort by" in t and "size" in t:
            return True

        # Generic "Size: S M L" pattern (size filter)
        if "size:" in t or "sizes:" in t:
            # If we see size plus at least one price, it's almost certainly a listing
            if "$" in t or "£" in t or "€" in t:
                return True

        # --- 2) Currency + multiple prices ---
        if "$" in t or "£" in t or "€" in t:
            price_hits = re.findall(r"[$£€]\s?\d+", t)
            if len(price_hits) >= 2:
                return True

        # --- 3) Hyphen-heavy, scraped layout ---
        if t.count(" - ") >= 3 or " - - " in t:
            return True

        # --- 4) Extreme repetition (same tokens over and over) ---
        tokens = [tok for tok in re.split(r"\s+", t) if tok]
        if len(tokens) > 30:
            uniq = set(tokens)
            if len(uniq) < len(tokens) * 0.5:  # >50% repetition
                return True

        return False

    @staticmethod
    def _shorten_listing(text: str) -> str:
        """
        Try to compress a messy listing blob down to a concise product title.

        Strategy:
          - Take the first line or chunk before obvious site markers (e.g. ' - Depop').
          - Remove trailing site names / boilerplate fragments.
          - Collapse repeated whitespace and hyphens.
        """
        import re

        if not text:
            return ""

        # First, break on newlines to get the first non-empty line.
        lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
        if lines:
            text = lines[0]

        # Then, cut off at obvious site markers.
        cut_markers = [" - depop", " | depop", "| grailed", "- grailed", "| ebay", " - ebay"]
        lower = text.lower()
        cut_idx = None
        for m in cut_markers:
            idx = lower.find(m)
            if idx != -1:
                cut_idx = idx
                break
        if cut_idx is not None:
            text = text[:cut_idx]

        # Remove repeated marketplace boilerplate phrases that survive
        boilerplate_patterns = [
            r"other shirts you may like.*",
            r"you may also like.*",
            r"add to bundle.*",
        ]
        for pat in boilerplate_patterns:
            text = re.sub(pat, "", text, flags=re.IGNORECASE)

        # Collapse repeated spaces and hyphens
        text = re.sub(r"\s*-\s*", " - ", text)
        text = re.sub(r"\s+", " ", text)

        return text.strip()

    def execute(self, value: Any, *, params: Dict[str, Any]) -> Any:
        # --- Local import to avoid circular dependency ---
        try:
            # This import happens at runtime, not module load time
            from blocks import _get_hf_pipeline
        except ImportError:
            print("[EnglishChatSubBlock] CRITICAL: Failed to import _get_hf_pipeline.")
            return value
        # --- End local import ---

        text = str(value or "")
        op = str(params.get("op", "passthrough")).lower()

        # If no operation, just pass the value through
        if op == "passthrough" or not text:
            return text

        # --------- NEW: pre-process listing-like blobs ---------
        ad_mode = str(params.get("ad_mode", "skip")).lower()  # skip | shorten | rewrite

        is_listing = self._is_listing_snippet(text)
        if is_listing:
            if ad_mode == "skip":
                # Detected as a marketplace ad; do not send to HF at all.
                # Caller can decide to ignore these upstream.
                return text

            cleaned = self._shorten_listing(text)

            if ad_mode == "shorten":
                # Return the cleaned product title only, no HF.
                return cleaned or text

            if ad_mode == "rewrite":
                # Use cleaned title (if any) as the basis for the HF rewrite
                if cleaned:
                    text = cleaned

        # --------- Normal HF rewrite path ---------
        model = str(params.get("model", "google/flan-t5-small"))

        pipe = _get_hf_pipeline(
            "text2text-generation",
            model,
            device=params.get("device", "auto"),
            verbose=params.get("verbose", False)
        )
        if pipe is None:
            print(f"[EnglishChatSubBlock] Failed to load model '{model}', returning original text.")
            return text  # Failed to load, return original

        # Define the instruction-prompt for the model
        templates = {
            "fix_grammar": f"Correct the spelling and grammar of the following text: {text}",
            "simplify": f"Rewrite the following text to be simple and easy to understand: {text}",
            "professional": f"Rewrite the following text in a formal, professional business tone: {text}",
            "casual": f"Rewrite the following text in a casual, friendly, and informal tone: {text}"
        }

        prompt = templates.get(op)
        if not prompt:
            print(f"[EnglishChatSubBlock] Unknown op '{op}', returning original text.")
            return text  # Unknown op

        try:
            # Set reasonable generation parameters
            gen_kwargs = {
                "max_new_tokens": int(params.get("max_new_tokens", len(text.split()) + 50)),
                "min_length": int(params.get("min_length", 5)),
                "temperature": float(params.get("temperature", 0.7)),
                "top_p": float(params.get("top_p", 0.95)),
                "do_sample": True
            }

            pred = pipe(prompt, **gen_kwargs)
            generated_text = pred[0]["generated_text"].strip()

            return generated_text if generated_text else text

        except Exception as e:
            print(f"[EnglishChatSubBlock] Error during generation: {e}")
            return text  # Return original on failure

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "op": "passthrough",          # fix_grammar | simplify | professional | casual
            "model": "google/flan-t5-small",
            "max_new_tokens": 128,
            "temperature": 0.7,
            "top_p": 0.95,
            # New ad-handling knob
            "ad_mode": "skip",           # skip | shorten | rewrite
        }

# Register the new sub-block
SUB_BLOCKS.register("english_chat", EnglishChatSubBlock)

# ======================= NEW CODE SUB-BLOCK ==========================
@dataclass
class CodeChatSubBlock(BaseSubBlock):
    """
    A sub-block that uses an HF model to rewrite or explain code.
    Designed to be called via `run_sub_pipeline` from a parent block.

    Operations (op=):
      - "refactor"     : Refactor code for clarity & maintainability.
      - "add_comments" : Add concise, helpful comments without changing logic.
      - "docstring"    : Add or improve docstrings for functions/classes.
      - "fix"          : Fix syntax/logic errors and return valid code.
      - "explain"      : Explain what the code does in natural language.
      - "passthrough"  : Return the code unchanged (default).
    """

    def execute(self, value: Any, *, params: Dict[str, Any]) -> Any:
        # --- Local import to avoid circular dependency ---
        try:
            from blocks import _get_hf_pipeline
        except ImportError:
            print("[CodeChatSubBlock] CRITICAL: Failed to import _get_hf_pipeline.")
            return value
        # --- End local import ---

        code = str(value or "")
        if not code.strip():
            return code

        op = str(params.get("op", "passthrough")).lower()
        if op == "passthrough":
            return code

        model = str(params.get("model", "google/flan-t5-small"))
        lang = str(params.get("lang", "python")).strip().lower() or "python"

        pipe = _get_hf_pipeline(
            "text2text-generation",
            model,
            device=params.get("device", "auto"),
            verbose=params.get("verbose", False),
        )
        if pipe is None:
            print(f"[CodeChatSubBlock] Failed to load model '{model}', returning original code.")
            return code

        # Instruction-style prompts for different operations
        base_intro = f"The following is {lang} code.\n\n"
        templates = {
            "refactor": (
                base_intro
                + "Refactor this code to improve readability and maintainability, "
                  "while preserving its behavior. Return only the refactored code.\n\n"
                  "Code:\n"
                + code
            ),
            "add_comments": (
                base_intro
                + "Add concise, helpful comments to this code without changing its behavior. "
                  "Return only the commented code.\n\n"
                  "Code:\n"
                + code
            ),
            "docstring": (
                base_intro
                + "Add or improve docstrings for all public functions, methods, and classes. "
                  "Return only the updated code with docstrings.\n\n"
                  "Code:\n"
                + code
            ),
            "fix": (
                base_intro
                + "Fix any syntax or obvious logic errors in this code and return valid, "
                  "runnable code. Preserve the original intent as much as possible.\n\n"
                  "Code:\n"
                + code
            ),
            "explain": (
                base_intro
                + "Explain clearly and concisely what this code does, step by step. "
                  "Return only the explanation in English.\n\n"
                  "Code:\n"
                + code
            ),
        }

        prompt = templates.get(op)
        if not prompt:
            print(f"[CodeChatSubBlock] Unknown op '{op}', returning original code.")
            return code

        try:
            gen_kwargs = {
                "max_new_tokens": int(params.get("max_new_tokens", max(64, len(code.split()) + 50))),
                "min_length": int(params.get("min_length", 5)),
                "temperature": float(params.get("temperature", 0.3 if op != "explain" else 0.7)),
                "top_p": float(params.get("top_p", 0.95)),
                "do_sample": bool(params.get("do_sample", op == "explain")),
            }

            pred = pipe(prompt, **gen_kwargs)
            generated_text = (pred[0].get("generated_text") or "").strip()

            # If the op returns code, fall back to the original on empty
            if not generated_text:
                return code

            return generated_text

        except Exception as e:
            print(f"[CodeChatSubBlock] Error during generation: {e}")
            return code  # Return original on failure

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "op": "passthrough",        # refactor | add_comments | docstring | fix | explain | passthrough
            "model": "google/flan-t5-small",
            "lang": "python",
            "max_new_tokens": 256,
            "min_length": 5,
            "temperature": 0.3,
            "top_p": 0.95,
            "do_sample": False,
        }


# Register the new sub-block
SUB_BLOCKS.register("code_chat", CodeChatSubBlock)

# ======================= NEW SITEMAP SUB-BLOCK ==========================
@dataclass
class SitemapSubBlock(BaseSubBlock):
    """
    A sub-block that finds, downloads, and parses sitemaps.
    Can use explicitly provided sitemaps, OR discover them from
    a provided input URL/Domain, OR from 'site_require' parameters.
    """

    DEFAULT_SITEMAP_PATHS = ["/sitemap.xml", "/sitemap_index.xml", "/sitemap/sitemap.xml"]

    def _get_sitemap_urls(self, session: "requests.Session", url: str, timeout: float) -> List[str]:
        import requests
        urls: List[str] = []
        try:
            if url.count("/sitemap") > 5: return []
            if not url.startswith("http"): return []  # Sanity check

            r = session.get(url, timeout=timeout)
            r.raise_for_status()
            content = r.text
        except Exception:
            return []

        try:
            root = ET.fromstring(content)
        except ET.ParseError:
            locs = re.findall(r"(https?://[^\s<>]+)", content)
            return [loc.strip() for loc in locs if len(loc.strip()) > 10]
        except Exception:
            return []

        if root.tag.endswith('sitemapindex'):
            for sitemap_tag in root.findall('.//{*}sitemap'):
                loc_tag = sitemap_tag.find('{*}loc')
                if loc_tag is not None:
                    s = html.unescape(loc_tag.text).strip()
                    urls.extend(self._get_sitemap_urls(session, s, timeout))
        elif root.tag.endswith('urlset'):
            for url_tag in root.findall('.//{*}url'):
                loc_tag = url_tag.find('{*}loc')
                if loc_tag is not None:
                    u = html.unescape(loc_tag.text).strip()
                    if u: urls.append(u)
        return urls

    def _find_sitemap_index(self, session: "requests.Session", base_url: str, timeout: float) -> Tuple[str, List[str]]:
        parsed = urlparse(base_url)
        domain = f"{parsed.scheme}://{parsed.netloc}".rstrip('/')
        sitemap_urls: List[str] = []

        # 1. Robots.txt
        try:
            robots_url = urljoin(domain, '/robots.txt')
            r = session.get(robots_url, timeout=timeout)
            if r.status_code == 200:
                for line in r.text.splitlines():
                    if line.lower().startswith('sitemap:'):
                        s = line.split(':', 1)[1].strip()
                        if s: sitemap_urls.append(s)
                if sitemap_urls: return domain, sitemap_urls
        except Exception:
            pass

        # 2. Defaults
        for path in self.DEFAULT_SITEMAP_PATHS:
            full = urljoin(domain, path)
            try:
                r = session.head(full, timeout=timeout)
                if 200 <= r.status_code < 400:
                    sitemap_urls.append(full)
                    return domain, sitemap_urls
            except Exception:
                continue

        return domain, sitemap_urls

    def execute(self, value: Any, *, params: Dict[str, Any]) -> List[str]:
        import requests

        # 1. Sanitization
        query_or_domain = str(value or "").strip().strip("'").strip('"')

        op = str(params.get("op", "get_urls")).lower()
        timeout = float(params.get("timeout", 10.0))

        # explicit sitemaps
        explicit_sitemaps_raw = params.get("sitemaps", [])
        if isinstance(explicit_sitemaps_raw, str):
            explicit_sitemaps = [s.strip() for s in explicit_sitemaps_raw.split(',') if s.strip()]
        else:
            explicit_sitemaps = [str(s).strip() for s in explicit_sitemaps_raw if str(s).strip()]

        # [NEW] site_require (passed from LinkTracker)
        site_require_raw = params.get("site_require", [])
        if isinstance(site_require_raw, str):
            site_require_list = [s.strip() for s in site_require_raw.split(',') if s.strip()]
        else:
            site_require_list = []
        # Early exit: If nothing provided to work with, and input is just a keyword
        if not explicit_sitemaps and not site_require_list:
            if not query_or_domain or "." not in query_or_domain:
                return []

        session = requests.Session()
        session.headers.update({"User-Agent": "PromptChat/SitemapSubBlock"})

        final_sitemap_index_urls: List[str] = []

        # A. explicit sitemaps
        final_sitemap_index_urls.extend([s for s in explicit_sitemaps if s.startswith('http')])

        # B. site_require domains (Auto-discovery)
        for d in site_require_list:
            if not d: continue
            target = d if d.startswith("http") else f"https://{d}"
            try:
                _, found = self._find_sitemap_index(session, target, timeout)
                final_sitemap_index_urls.extend(found)
            except:
                pass

        # C. input domain (Auto-discovery)
        if query_or_domain and "." in query_or_domain:
            target = query_or_domain if query_or_domain.startswith("http") else f"https://{query_or_domain}"
            try:
                _, found = self._find_sitemap_index(session, target, timeout)
                final_sitemap_index_urls.extend(found)
            except:
                pass

        # Dedupe indices
        final_sitemap_index_urls = list(set(final_sitemap_index_urls))

        if op == "get_index":
            return final_sitemap_index_urls

        # Recursive Fetch
        all_content_urls: List[str] = []
        for sitemap_url in final_sitemap_index_urls:
            try:
                all_content_urls.extend(self._get_sitemap_urls(session, sitemap_url, timeout))
            except:
                continue

        return list(set(all_content_urls))

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "op": "get_urls",
            "sitemaps": "",
            "site_require": "",  # Implicitly used, but good to document
            "timeout": 10.0,
        }

# Register the new sub-block
SUB_BLOCKS.register("sitemap", SitemapSubBlock)


# ======================= NEW XML SUB-BLOCK ==========================
@dataclass
class XmlSubBlock(BaseSubBlock):
    """
    A sub-block that fetches and parses XML (RSS, Atom, or generic).
    Extracts links or specific attribute values to be used as crawl targets.

    Params:
    - op: "extract_links" (default) | "xpath"
    - xpath: (Optional) Custom path to find elements, e.g., ".//enclosure"
    - attr: (Optional) Attribute to extract from found elements.
            If empty, extracts element text.
    """

    def _strip_namespaces(self, el: ET.Element) -> ET.Element:
        """
        Recursively removes {http://...} namespaces from tags to make
        parsing RSS/Atom feeds much easier without strict schema definitions.
        """
        if el.tag.startswith("{"):
            el.tag = el.tag.split("}", 1)[1]
        for child in el:
            self._strip_namespaces(child)
        return el

    def execute(self, value: Any, *, params: Dict[str, Any]) -> List[str]:
        # Local import to avoid collisions
        import requests

        url_or_xml = str(value or "").strip()
        if not url_or_xml:
            return []

        op = str(params.get("op", "extract_links")).lower()
        custom_xpath = str(params.get("xpath", "")).strip()
        target_attr = str(params.get("attr", "")).strip()
        timeout = float(params.get("timeout", 10.0))

        content = ""

        # 1. Fetch if it's a URL
        if url_or_xml.startswith("http://") or url_or_xml.startswith("https://"):
            try:
                with requests.Session() as session:
                    session.headers.update({"User-Agent": "PromptChat/XmlSubBlock"})
                    r = session.get(url_or_xml, timeout=timeout)
                    r.raise_for_status()
                    content = r.text
            except Exception as e:
                print(f"[XmlSubBlock] Fetch error: {e}")
                return []
        else:
            # Assume it's raw XML string
            content = url_or_xml

        if not content:
            return []

        # 2. Parse XML
        extracted_values: List[str] = []
        try:
            # Basic string cleanup to avoid encoding issues
            content = content.strip()
            root = ET.fromstring(content)

            # Strip namespaces to standardize RSS vs Atom parsing
            root = self._strip_namespaces(root)
        except ET.ParseError as e:
            print(f"[XmlSubBlock] Parse error: {e}")
            return []
        except Exception:
            return []

        # 3. Extraction Logic

        # MODE A: Custom XPath
        if op == "xpath" and custom_xpath:
            try:
                elements = root.findall(custom_xpath)
                for el in elements:
                    if target_attr:
                        val = el.get(target_attr)
                    else:
                        val = el.text

                    if val:
                        extracted_values.append(val.strip())
            except Exception as e:
                print(f"[XmlSubBlock] XPath error: {e}")

        # MODE B: Smart Link Extraction (RSS/Atom/Media default)
        else:
            # 1. Standard RSS <link> (text content)
            for link in root.findall(".//link"):
                # Atom uses href attribute, RSS uses text
                if link.text and "http" in link.text:
                    extracted_values.append(link.text.strip())
                elif link.get("href"):
                    extracted_values.append(link.get("href").strip())

            # 2. Enclosures (Podcasts/Media)
            for enc in root.findall(".//enclosure"):
                u = enc.get("url")
                if u: extracted_values.append(u.strip())

            # 3. Media Content (Yahoo Media namespace style)
            for media in root.findall(".//content"):
                u = media.get("url")
                if u: extracted_values.append(u.strip())

        # Dedupe and basic validation
        valid_urls = []
        seen = set()
        for v in extracted_values:
            if v and v not in seen and v.startswith("http"):
                seen.add(v)
                valid_urls.append(v)

        return valid_urls

    def get_params_info(self) -> Dict[str, Any]:
        return {
            "op": "extract_links",  # extract_links | xpath
            "xpath": "",  # e.g. ".//enclosure"
            "attr": "",  # e.g. "url"
            "timeout": 10.0
        }


# Register the new sub-block
SUB_BLOCKS.register("xml", XmlSubBlock)