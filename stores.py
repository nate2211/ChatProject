# ======================= stores.py =======================
from __future__ import annotations

import collections
import random
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple, Set, Callable
from urllib.parse import urlparse

from submanagers import DatabaseSubmanager


@dataclass
class BaseStore:
    """
    Thin base class for typed stores.
    """
    db: DatabaseSubmanager


class LinkTrackerStore(BaseStore):
    """
    Store for LinkTrackerBlock.

    Owns schema + all LinkTracker-specific queries.
    """

    ASSETS_DDL = """
    CREATE TABLE IF NOT EXISTS assets
    (
        url TEXT PRIMARY KEY,
        text TEXT,
        source TEXT,
        size TEXT,
        status TEXT,
        first_seen TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        last_checked TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
    """

    PAGES_DDL = """
    CREATE TABLE IF NOT EXISTS pages
    (
        url TEXT PRIMARY KEY,
        last_scanned TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
    """

    INDEXES_DDL = [
        "CREATE INDEX IF NOT EXISTS idx_assets_source ON assets (source)",
        "CREATE INDEX IF NOT EXISTS idx_assets_last_checked ON assets (last_checked)",
        "CREATE INDEX IF NOT EXISTS idx_pages_last_scanned ON pages (last_scanned)",
    ]

    def ensure_schema(self) -> None:
        self.db.ensure_schema([self.ASSETS_DDL, self.PAGES_DDL, *self.INDEXES_DDL])

        # Example micro-migrations you might add later:
        # self.db.ensure_columns("assets", {"tag": "TEXT DEFAULT ''"})
        # self.db.ensure_columns("pages", {"seed_ok": "INTEGER DEFAULT 0"})

    # -------------------- Assets -------------------- #
    def asset_exists(self, url: str) -> bool:
        r = self.db.fetchone("SELECT 1 FROM assets WHERE url = ?", (url,))
        return r is not None

    def upsert_asset(self, asset: Dict[str, Any]) -> None:
        """
        Preserves first_seen on existing rows.
        """
        url = asset.get("url", "")
        if not url:
            return

        exists = self.asset_exists(url)
        if exists:
            self.db.execute(
                """
                UPDATE assets
                SET status = ?, last_checked = CURRENT_TIMESTAMP, size = ?, source = ?, text = ?
                WHERE url = ?
                """,
                (
                    asset.get("status", ""),
                    asset.get("size", ""),
                    asset.get("source", ""),
                    asset.get("text", ""),
                    url,
                ),
            )
        else:
            self.db.execute(
                """
                INSERT INTO assets (url, text, source, size, status, last_checked)
                VALUES (?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
                """,
                (
                    url,
                    asset.get("text", ""),
                    asset.get("source", ""),
                    asset.get("size", ""),
                    asset.get("status", ""),
                ),
            )

    def fetch_db_seed_assets(
        self,
        limit: int = 200,
        require_keywords: Optional[List[str]] = None,
        required_sites: Optional[List[str]] = None,
        max_age_days: Optional[int] = None,
    ) -> List[Dict[str, Any]]:
        require_keywords = [k.lower() for k in (require_keywords or []) if k]
        required_sites = [s.lower() for s in (required_sites or []) if s]

        where = []
        args: list[Any] = []

        if max_age_days is not None:
            where.append("last_checked >= datetime('now', ?)")
            args.append(f"-{int(max_age_days)} days")

        if require_keywords:
            kw = []
            for k in require_keywords:
                like = f"%{k}%"
                kw.append("(url LIKE ? OR text LIKE ? OR source LIKE ?)")
                args.extend([like, like, like])
            where.append("(" + " OR ".join(kw) + ")")

        if required_sites:
            sc = []
            for s in required_sites:
                sc.append("url LIKE ?")
                args.append(f"%{s}%")
            where.append("(" + " OR ".join(sc) + ")")

        where_sql = ("WHERE " + " AND ".join(where)) if where else ""
        q = f"""
            SELECT url, text, source, last_checked
            FROM assets
            {where_sql}
            ORDER BY last_checked DESC
            LIMIT ?
        """
        args.append(int(limit))

        rows = self.db.fetchall(q, args)
        out = []
        for r in rows:
            out.append({
                "url": r["url"],
                "text": r["text"] or "",
                "source": r["source"] or "",
                "last_checked": r["last_checked"],
            })
        return out

    def fetch_proven_hubs(self, required_sites: List[str], min_hits: int = 1) -> List[str]:
        site_clause = ""
        args: list[Any] = []

        if required_sites:
            clauses = []
            for s in required_sites:
                clauses.append("source LIKE ?")
                args.append(f"%{s}%")
            site_clause = "AND (" + " OR ".join(clauses) + ")"

        q = f"""
            SELECT source, COUNT(*) as hit_count
            FROM assets
            WHERE status = '200 OK'
            AND source LIKE 'http%'
            {site_clause}
            GROUP BY source
            HAVING hit_count >= ?
            ORDER BY hit_count DESC
            LIMIT 50
        """
        args.append(min_hits)

        rows = self.db.fetchall(q, args)
        return [r["source"] for r in rows if r["source"]]

    def seed_pages_from_database(
            self,
            db_assets: List[Dict[str, Any]],
            targets: set[str],
            max_pages_total: int,
            required_sites: List[str],
            keywords: List[str],
            min_term_overlap: int,
    ) -> Tuple[List[str], List[str]]:
        candidate_pages: List[str] = []
        direct_asset_urls: List[str] = []

        def _allowed(u: str) -> bool:
            if not required_sites:
                return True
            try:
                d = urlparse(u).netloc.lower().split(":")[0]
            except Exception:
                return False
            return any(req in d for req in required_sites)

        def _term_ok(h: str) -> bool:
            if not keywords:
                return True
            hlow = h.lower()
            hits = sum(1 for k in keywords if k and k in hlow)
            return hits >= min_term_overlap

        for row in db_assets:
            u = (row.get("url") or "").strip()
            src = (row.get("source") or "").strip()

            if not u:
                continue

            upath = urlparse(u).path.lower()
            if any(upath.endswith(ext) for ext in targets):
                if _allowed(u) and _term_ok(u + " " + (row.get("text") or "")):
                    direct_asset_urls.append(u)

            if src.startswith("http") and _allowed(src) and _term_ok(src):
                candidate_pages.append(src)

            try:
                parsed = urlparse(u)
                parent_path = (parsed.path or "/").rsplit("/", 1)[0] + "/"
                parent_url = f"{parsed.scheme}://{parsed.netloc}{parent_path}"
                if _allowed(parent_url) and _term_ok(parent_url):
                    candidate_pages.append(parent_url)
            except Exception:
                pass

            try:
                host = urlparse(u).netloc.lower()
                if "archive.org" in host:
                    parts = urlparse(u).path.split("/")
                    if len(parts) >= 3:
                        ident = parts[2]
                        for au in self._archive_ident_to_downloads(ident):
                            if _allowed(au) and _term_ok(au):
                                candidate_pages.append(au)
            except Exception:
                pass

        def _dedupe(seq: List[str]) -> List[str]:
            seen = set()
            out = []
            for s in seq:
                if s and s not in seen:
                    seen.add(s)
                    out.append(s)
            return out

        candidate_pages = _dedupe(candidate_pages)[:max_pages_total]
        direct_asset_urls = _dedupe(direct_asset_urls)
        return candidate_pages, direct_asset_urls
    # -------------------- Pages -------------------- #
    def page_scanned(self, url: str) -> bool:
        r = self.db.fetchone("SELECT 1 FROM pages WHERE url = ?", (url,))
        return r is not None

    def mark_page_scanned(self, url: str) -> None:
        if not url:
            return
        self.db.execute(
            """
            INSERT OR REPLACE INTO pages (url, last_scanned)
            VALUES (?, CURRENT_TIMESTAMP)
            """,
            (url,),
        )



class VideoTrackerStore(BaseStore):
    """
    Store for VideoLinkTrackerBlock.
    Owns schema + all SQL + DB seeding/expansion + cooldown ops.

    Block should not touch sqlite directly.
    """

    # -------------------- schema -------------------- #

    ASSETS_DDL = """
    CREATE TABLE IF NOT EXISTS assets
    (
        url TEXT PRIMARY KEY,
        canonical_url TEXT,
        content_id TEXT,
        text TEXT,
        source TEXT,
        size TEXT,
        status TEXT,
        first_seen TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        last_checked TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        seed_ok INTEGER DEFAULT 1,
        synthetic INTEGER DEFAULT 0
    )
    """

    PAGES_DDL = """
    CREATE TABLE IF NOT EXISTS pages
    (
        url TEXT PRIMARY KEY,
        last_scanned TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
    """

    RECENT_RETURNS_DDL = """
    CREATE TABLE IF NOT EXISTS recent_returns
    (
        identifier TEXT PRIMARY KEY,
        returned_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    )
    """

    INDEXES_DDL = [
        "CREATE INDEX IF NOT EXISTS idx_assets_source ON assets (source)",
        "CREATE INDEX IF NOT EXISTS idx_assets_seed_ok ON assets (seed_ok)",
        "CREATE INDEX IF NOT EXISTS idx_assets_last_checked ON assets (last_checked)",
        "CREATE INDEX IF NOT EXISTS idx_assets_canonical ON assets (canonical_url)",
        "CREATE INDEX IF NOT EXISTS idx_assets_content_id ON assets (content_id)",
        "CREATE INDEX IF NOT EXISTS idx_pages_last_scanned ON pages (last_scanned)",
        "CREATE INDEX IF NOT EXISTS idx_recent_returns_at ON recent_returns(returned_at)",
    ]

    def ensure_schema(self) -> None:
        self.db.ensure_schema([self.ASSETS_DDL, self.PAGES_DDL, self.RECENT_RETURNS_DDL, *self.INDEXES_DDL])

        # light migrations if older DBs exist
        self.db.ensure_columns("assets", {
            "seed_ok": "INTEGER DEFAULT 1",
            "synthetic": "INTEGER DEFAULT 0",
            "canonical_url": "TEXT",
            "content_id": "TEXT",
        })

    # -------------------- assets -------------------- #

    def asset_exists_by_canon_or_cid(self, canonical_url: str, content_id: str) -> bool:
        r = self.db.fetchone(
            """
            SELECT status
            FROM assets
            WHERE canonical_url = ? OR content_id = ?
            ORDER BY last_checked DESC
            LIMIT 1
            """,
            (canonical_url, content_id),
        )
        if not r:
            return False
        status = (r["status"] or "").lower()
        # suppress only if previously good-ish
        if "200 ok" in status or "sniffed" in status or "mega" in status:
            return True
        return False

    def upsert_asset(
        self,
        asset: Dict[str, Any],
        *,
        canonical_url: str,
        content_id: str,
        synthetic_tags: Set[str],
    ) -> None:
        """
        Inserts or replaces, preserving first_seen.
        synthetic_tags decides synthetic and seed_ok fields.
        """
        raw_url = asset.get("url") or ""
        if not raw_url:
            return

        tag = (asset.get("tag") or "").lower()
        synthetic = 1 if tag in synthetic_tags else 0
        seed_ok = 0 if synthetic else 1

        exists = self.db.fetchone("SELECT 1 FROM assets WHERE url = ?", (raw_url,)) is not None
        if exists:
            self.db.execute(
                """
                UPDATE assets
                SET canonical_url=?, content_id=?, text=?, source=?, size=?, status=?,
                    last_checked=CURRENT_TIMESTAMP, seed_ok=?, synthetic=?
                WHERE url=?
                """,
                (
                    canonical_url,
                    content_id,
                    asset.get("text", ""),
                    asset.get("source_page", "") or asset.get("source", ""),
                    asset.get("size", ""),
                    asset.get("status", ""),
                    seed_ok,
                    synthetic,
                    raw_url,
                ),
            )
        else:
            self.db.execute(
                """
                INSERT INTO assets
                    (url, canonical_url, content_id, text, source, size, status,
                     last_checked, seed_ok, synthetic)
                VALUES (?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP, ?, ?)
                """,
                (
                    raw_url,
                    canonical_url,
                    content_id,
                    asset.get("text", ""),
                    asset.get("source_page", "") or asset.get("source", ""),
                    asset.get("size", ""),
                    asset.get("status", ""),
                    seed_ok,
                    synthetic,
                ),
            )

    def fetch_recent_good_asset_urls(self, limit: int = 100) -> List[str]:
        rows = self.db.fetchall(
            """
            SELECT url FROM assets
            WHERE status LIKE '%OK%'
            ORDER BY last_checked DESC
            LIMIT ?
            """,
            (int(limit),),
        )
        return [r["url"] for r in rows if r["url"]]

    # -------------------- pages -------------------- #

    def page_scanned(self, url: str) -> bool:
        r = self.db.fetchone("SELECT 1 FROM pages WHERE url = ?", (url,))
        return r is not None

    def mark_page_scanned(self, url: str) -> None:
        if not url:
            return
        self.db.execute(
            """
            INSERT OR REPLACE INTO pages (url, last_scanned)
            VALUES (?, CURRENT_TIMESTAMP)
            """,
            (url,),
        )

    # ---------------- cooldown ---------------- #

    def get_recently_returned(self, cooldown_hours: int) -> Set[str]:
        rows = self.db.fetchall(
            """
            SELECT identifier
            FROM recent_returns
            WHERE returned_at >= datetime('now', ?)
            """,
            (f"-{int(cooldown_hours)} hours",),
        )
        return {r["identifier"] for r in rows if r["identifier"]}

    def mark_returned_identifier(self, ident: str) -> None:
        if not ident:
            return
        self.db.execute(
            """
            INSERT OR REPLACE INTO recent_returns(identifier, returned_at)
            VALUES (?, CURRENT_TIMESTAMP)
            """,
            (ident,),
        )

    # ---------------- advanced db intelligence ---------------- #

    def fetch_proven_hubs(self, required_sites: List[str], min_hits: int = 1) -> List[str]:
        site_clause = ""
        args: list[Any] = []

        if required_sites and required_sites != ["*"]:
            clauses = []
            for s in required_sites:
                clauses.append("source LIKE ?")
                args.append(f"%{s}%")
            site_clause = "AND (" + " OR ".join(clauses) + ")"

        q = f"""
            SELECT source, COUNT(*) as hit_count
            FROM assets
            WHERE (status LIKE '%200 OK%' OR status = 'sniffed' OR status LIKE 'MEGA%')
              AND source LIKE 'http%'
              {site_clause}
            GROUP BY source
            HAVING hit_count >= ?
            ORDER BY hit_count DESC
            LIMIT 50
        """
        args.append(int(min_hits))

        rows = self.db.fetchall(q, args)
        return [r["source"] for r in rows if r["source"]]

    def load_database_seeds(
        self,
        *,
        sources: str = "pages",
        limit: int = 400,
        max_age_days: int = 14,
        include_synthetic: bool = False,
        per_domain_cap: int = 8,
    ) -> List[Dict[str, Any]]:
        sources = (sources or "pages").lower().strip()
        limit = max(1, min(int(limit), 10_000))
        max_age_days = max(1, min(int(max_age_days), 3650))

        out: List[Dict[str, Any]] = []

        age_clause_assets = "last_checked >= datetime('now', ?)"
        age_clause_pages  = "last_scanned >= datetime('now', ?)"

        if sources in ("assets", "both"):
            if include_synthetic:
                rows = self.db.fetchall(
                    f"""
                    SELECT url, source
                    FROM assets
                    WHERE {age_clause_assets}
                    ORDER BY last_checked DESC
                    LIMIT ?
                    """,
                    (f"-{max_age_days} days", limit),
                )
            else:
                rows = self.db.fetchall(
                    f"""
                    SELECT url, source
                    FROM assets
                    WHERE seed_ok=1 AND synthetic=0 AND {age_clause_assets}
                    ORDER BY last_checked DESC
                    LIMIT ?
                    """,
                    (f"-{max_age_days} days", limit),
                )
            for r in rows:
                u = r["url"]
                if u:
                    out.append({"url": u, "kind": "asset", "source": r["source"] or "", "tag": "db_seed"})

        if sources in ("pages", "both"):
            rows = self.db.fetchall(
                f"""
                SELECT url
                FROM pages
                WHERE {age_clause_pages}
                ORDER BY last_scanned DESC
                LIMIT ?
                """,
                (f"-{max_age_days} days", limit),
            )
            for r in rows:
                u = r["url"]
                if u:
                    out.append({"url": u, "kind": "page", "source": "", "tag": "db_seed"})

        # dedupe
        seen = set()
        deduped = []
        for s in out:
            u = s["url"]
            if u in seen:
                continue
            seen.add(u)
            deduped.append(s)

        # diversify domains
        by_domain = collections.defaultdict(list)
        for s in deduped:
            d = (urlparse(s["url"]).netloc or "").lower().split(":")[0]
            by_domain[d].append(s)

        domains = list(by_domain.keys())
        random.shuffle(domains)

        diverse: List[Dict[str, Any]] = []
        for d in domains:
            diverse.extend(by_domain[d][:per_domain_cap])

        return diverse[:limit]

    def expand_db_seed_urls(
        self,
        seeds: List[Dict[str, Any]],
        *,
        max_per_seed: int,
        ladder_depth: int,
        per_domain_cap: int,
        max_pages_out: int,
        max_assets_out: int,
        known_url_fn: Callable[[str], bool],
        clean_domain_fn: Callable[[str], str],
        clean_path_fn: Callable[[str], str],
        is_probable_video_url_fn: Callable[[str, str, str], bool],
        archive_ident_to_downloads_fn: Callable[[str], List[str]],
    ) -> Tuple[List[str], List[str]]:
        """
        Store-owned expansion. Block supplies URL heuristics as callables.
        """
        candidate_pages: List[str] = []
        direct_assets: List[str] = []

        domain_counts_pages = collections.Counter()
        domain_counts_assets = collections.Counter()

        def add_page(u: str):
            if not u or u in candidate_pages:
                return
            if known_url_fn(u):
                return
            d = clean_domain_fn(u)
            if d and domain_counts_pages[d] >= per_domain_cap:
                return
            domain_counts_pages[d] += 1
            candidate_pages.append(u)

        def add_asset(u: str):
            if not u or u in direct_assets:
                return
            if known_url_fn(u):
                return
            d = clean_domain_fn(u)
            if d and domain_counts_assets[d] >= per_domain_cap:
                return
            domain_counts_assets[d] += 1
            direct_assets.append(u)

        if not seeds:
            return [], []

        from urllib.parse import urlparse

        def ladder_up(u: str, depth: int) -> List[str]:
            out = []
            try:
                pu = urlparse(u)
                base = f"{pu.scheme}://{pu.netloc}"
                path = pu.path or "/"
                if not path.endswith("/"):
                    path = path.rsplit("/", 1)[0] + "/"
                parts = [p for p in path.split("/") if p]
                for k in range(min(depth, len(parts)), 0, -1):
                    parent = base + "/" + "/".join(parts[:k]) + "/"
                    out.append(parent)
                out.append(base + "/")
            except Exception:
                return []
            return list(dict.fromkeys(out))

        def archive_expansions(u: str) -> List[str]:
            out = []
            try:
                pu = urlparse(u)
                host = pu.netloc.lower()
                if "archive.org" not in host:
                    return []
                path = pu.path.strip("/")
                ident = ""
                parts = path.split("/")
                if parts:
                    if parts[0] in ("details", "download") and len(parts) >= 2:
                        ident = parts[1]
                    elif len(parts) == 1:
                        ident = parts[0]
                if ident:
                    out.extend(archive_ident_to_downloads_fn(ident))
            except Exception:
                return []
            return list(dict.fromkeys(out))

        for s in seeds:
            if len(candidate_pages) >= max_pages_out and len(direct_assets) >= max_assets_out:
                break

            seed_url = (s.get("url") or "").strip()
            if not seed_url:
                continue

            added_for_seed = 0

            spath = clean_path_fn(seed_url)
            if is_probable_video_url_fn(seed_url, spath, seed_url.lower()):
                add_asset(seed_url)
                added_for_seed += 1
                if added_for_seed >= max_per_seed:
                    continue

            for au in archive_expansions(seed_url):
                if added_for_seed >= max_per_seed:
                    break
                apath = clean_path_fn(au)
                if is_probable_video_url_fn(au, apath, au.lower()):
                    add_asset(au)
                else:
                    add_page(au)
                added_for_seed += 1

            for pu in ladder_up(seed_url, ladder_depth):
                if added_for_seed >= max_per_seed:
                    break
                add_page(pu)
                added_for_seed += 1

        return (
            list(dict.fromkeys(candidate_pages))[:max_pages_out],
            list(dict.fromkeys(direct_assets))[:max_assets_out],
        )

    def extract_urls_from_db_text(
        self,
        *,
        limit_rows: int,
        max_urls: int,
        include_synthetic: bool,
        url_regex,
    ) -> List[str]:
        where = "text IS NOT NULL"
        if not include_synthetic:
            where += " AND seed_ok=1 AND synthetic=0"

        rows = self.db.fetchall(
            f"""
            SELECT text FROM assets
            WHERE {where}
            ORDER BY last_checked DESC
            LIMIT ?
            """,
            (int(limit_rows),),
        )

        out: List[str] = []
        for r in rows:
            txt = r["text"]
            if not txt:
                continue

            tl = txt.lstrip().lower()
            looks_manifest = "#extm3u" in tl or "m3u8" in tl or "dash" in tl
            looks_json = tl.startswith("{") or tl.startswith("[")
            if not (looks_manifest or looks_json):
                continue

            for m in url_regex.finditer(txt):
                u = m.group(0)
                if u:
                    out.append(u)
                    if len(out) >= max_urls:
                        break
            if len(out) >= max_urls:
                break

        return list(dict.fromkeys(out))