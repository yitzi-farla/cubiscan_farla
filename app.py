#!/usr/bin/env python3
# -*- coding: utf-8 -*-
#
# Dimension Capture – Minimal, Beautiful, Resilient Kiosk
# - Dark Spotify-ish UI
# - JSON event logging
# - Offline pool with guaranteed delivery (remove only on confirmed DB insert)
# - TradePeg lookup on barcode (Title + SKU shown and stored)
#
import os, json, math, queue, threading, time, traceback, csv, re, sqlite3
from datetime import datetime, timezone
from pathlib import Path
import tkinter as tk
from tkinter import ttk

import serial
import psycopg2
import psycopg2.extras
import requests

# ----------------------------
# Configuration
# Only real secrets / credentials come from .env.
# Operational constants stay in code so the Pi is harder to misconfigure.
# ----------------------------
PORT = "/dev/cubiscan"
BAUD = 9600
DB_URL = os.getenv("DATABASE_URL", "")
TABLE_NAME = "measurements"

# Command barcodes
SUBMIT_TO_DB_CODE = "SUBMIT"
CLEAR_CODE        = "CLEARFROMSCREEN"
UOM_UNIT_CODE     = "UNIT"
UOM_PACK_CODE     = "PACK"
UOM_CASE_CODE     = "CASE"

# TradePeg / Farla API
TRADEPEG_API_BASE = os.getenv("TRADEPEG_API_BASE", "https://farlatradepegapi-production.up.railway.app").rstrip("/")
TRADEPEG_API_KEY  = os.getenv("TRADEPEG_API_KEY", "")
TRADEPEG_EXPORT_UOM_URL = f"{TRADEPEG_API_BASE}/export/uom"
TRADEPEG_UOM_UPDATE_URL = f"{TRADEPEG_API_BASE}/update/uom"
TRADEPEG_UOM_UPDATE_METHOD = "POST"

# Files
SCRIPT_DIR = Path(__file__).resolve().parent
APP_DIR  = SCRIPT_DIR
LOG_DIR  = APP_DIR / "logs"
LOG_DIR.mkdir(exist_ok=True)
EVT_LOG  = LOG_DIR / "events.jsonl"          # append-only JSONL
RAW_LOG  = LOG_DIR / "raw_device.jsonl"      # raw device frames (optional)
POOL_PATH= LOG_DIR / "pending_pool.json"     # offline queue
UOM_CACHE_PATH = APP_DIR / "tradepeg_uom.csv"
CACHE_DB_PATH = APP_DIR / "tradepeg_cache.sqlite"

# ----------------------------
# Theming
# ----------------------------
DARK_BG   = "#0f1115"
CARD_BG   = "#151923"
SOFT_TXT  = "#b9c0d0"
BRIGHT    = "#e7ecf6"
ACCENT    = "#1db954"
WARN      = "#f59e0b"
ERROR     = "#ef4444"
MUTED     = "#8b93a7"

# ----------------------------
# Utilities: logging & time
# ----------------------------
_lock_log = threading.Lock()

def now_utc():
    return datetime.now(timezone.utc).isoformat()

def log_event(kind: str, **data):
    evt = {"ts": now_utc(), "kind": kind, **data}
    with _lock_log:
        with EVT_LOG.open("a", encoding="utf-8") as f:
            f.write(json.dumps(evt, ensure_ascii=False) + "\n")

def log_raw(line: str):
    with _lock_log:
        with RAW_LOG.open("a", encoding="utf-8") as f:
            f.write(line.rstrip() + "\n")


def cache_progress(message: str):
    """Visible cache/download progress for the kiosk console and JSON log."""
    msg = f"[CACHE] {message}"
    print(msg, flush=True)
    try:
        log_event("cache.progress", message=message)
    except Exception:
        pass


# ----------------------------
# TradePeg UOM cache + barcode/SKU matching
# ----------------------------
GS1_GROUP_SEP = "\x1d"
UOM_CHOICES = ("Unit", "Pack", "Case")


def clean_cell(v):
    return "" if v is None else str(v).strip()


def normalize_uom_name(v):
    s = clean_cell(v).lower()
    if s in ("unit", "each", "ea", "single"):
        return "Unit"
    if s in ("pack", "pk") or "pack" in s:
        return "Pack"
    if s in ("case", "carton", "ctn") or "case" in s:
        return "Case"
    return clean_cell(v).title() if v else ""


def normalize_gtin(gtin):
    digits = re.sub(r"\D+", "", clean_cell(gtin))
    if len(digits) in (8, 12, 13, 14):
        return digits.lstrip("0") or digits
    return digits


def _gs1_gtin(raw):
    original = clean_cell(raw)
    compact = original.replace(" ", "").replace("(", "").replace(")", "")
    compact = compact.replace("]d2", "").replace("]D2", "").replace("]C1", "")
    m = re.search(r"(?:^|[^0-9])01(\d{14})", compact)
    return m.group(1) if m else ""


def barcode_candidates(raw):
    """Return possible lookup keys, preferring the 1D barcode for GS1/2D scans."""
    if not raw:
        return []
    original = clean_cell(raw)
    candidates = []

    def add(x):
        x = clean_cell(x)
        if x and x not in candidates:
            candidates.append(x)
        digits = re.sub(r"\D+", "", x)
        if digits and digits not in candidates:
            candidates.append(digits)
        if digits:
            stripped = digits.lstrip("0") or digits
            if stripped not in candidates:
                candidates.append(stripped)

    # GS1 DataMatrix / 2D scanners often send ]d2, ]C1, parentheses, or FNC1 separators.
    gtin14 = _gs1_gtin(original)
    if gtin14:
        add(gtin14)
        add(normalize_gtin(gtin14))

    add(original)
    return candidates


def canonical_1d_barcode(raw):
    gtin14 = _gs1_gtin(raw)
    if gtin14:
        return normalize_gtin(gtin14)
    for c in barcode_candidates(raw):
        if c.isdigit():
            return c
    return clean_cell(raw)


class UomCache:
    """SQLite-backed TradePeg UOM cache for fast Raspberry Pi barcode/SKU lookup."""
    def __init__(self, path, db_path=CACHE_DB_PATH):
        self.path = Path(path)
        self.db_path = Path(db_path)
        self.loaded_at = None
        self.rows = []  # kept for compatibility; lookups are SQLite-backed
        self._db_lock = threading.Lock()
        self._ready = False

    def _connect(self):
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        conn = sqlite3.connect(str(self.db_path), timeout=30, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        try:
            conn.execute("PRAGMA journal_mode=WAL")
            conn.execute("PRAGMA synchronous=NORMAL")
            conn.execute("PRAGMA temp_store=MEMORY")
        except Exception:
            pass
        return conn

    def _init_db(self, conn):
        conn.executescript("""
        CREATE TABLE IF NOT EXISTS cache_meta (
            name TEXT PRIMARY KEY,
            value TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS uom_rows (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            product TEXT,
            uom_name TEXT,
            uom_sku TEXT,
            uom_ean TEXT,
            canonical_barcode TEXT,
            weight_uom TEXT,
            dimensions_uom TEXT,
            uom_qty TEXT,
            uom_asin TEXT,
            norm_product TEXT,
            norm_uom_sku TEXT,
            raw_json TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS uom_barcode_keys (
            key TEXT PRIMARY KEY,
            row_id INTEGER NOT NULL REFERENCES uom_rows(id) ON DELETE CASCADE
        );
        CREATE INDEX IF NOT EXISTS idx_uom_rows_product ON uom_rows(product);
        CREATE INDEX IF NOT EXISTS idx_uom_rows_norm_product ON uom_rows(norm_product);
        CREATE INDEX IF NOT EXISTS idx_uom_rows_uom_sku ON uom_rows(uom_sku);
        CREATE INDEX IF NOT EXISTS idx_uom_rows_norm_uom_sku ON uom_rows(norm_uom_sku);
        CREATE INDEX IF NOT EXISTS idx_uom_rows_canonical_barcode ON uom_rows(canonical_barcode);
        CREATE INDEX IF NOT EXISTS idx_uom_barcode_keys_row_id ON uom_barcode_keys(row_id);
        """)
        conn.commit()

    def _meta_get(self, conn, name):
        row = conn.execute("SELECT value FROM cache_meta WHERE name=?", (name,)).fetchone()
        return row["value"] if row else None

    def _meta_set(self, conn, name, value):
        conn.execute(
            "INSERT INTO cache_meta(name, value) VALUES(?, ?) ON CONFLICT(name) DO UPDATE SET value=excluded.value",
            (name, str(value)),
        )

    def ensure_downloaded(self, force=False):
        if not force and self.path.exists() and self.path.stat().st_size > 0:
            cache_progress(f"Using UOM cache: {self.path}")
            return
        if not TRADEPEG_API_KEY:
            cache_progress("UOM cache missing/failed, but TRADEPEG_API_KEY is not set; cannot download /export/uom")
            if self.path.exists() and self.path.stat().st_size > 0:
                return
            raise RuntimeError("TRADEPEG_API_KEY not set and no usable UOM cache exists")
        cache_progress(f"Downloading UOM export from {TRADEPEG_EXPORT_UOM_URL}")
        headers = {"x-api-key": TRADEPEG_API_KEY}
        r = requests.get(TRADEPEG_EXPORT_UOM_URL, headers=headers, timeout=90)
        r.raise_for_status()
        if not r.content:
            raise RuntimeError("Downloaded UOM export was empty")
        tmp = self.path.with_suffix(self.path.suffix + ".tmp")
        tmp.write_bytes(r.content)
        tmp.replace(self.path)
        cache_progress(f"Downloaded UOM export: {len(r.content):,} bytes")
        log_event("uom.cache.downloaded", bytes=len(r.content), path=str(self.path))

    def _row_from_sql(self, row):
        if not row:
            return None
        try:
            data = json.loads(row["raw_json"] or "{}")
        except Exception:
            data = {}
        data.update({
            "Product": row["product"] or data.get("Product", ""),
            "UOM Name": row["uom_name"] or data.get("UOM Name", ""),
            "UOM SKU": row["uom_sku"] or data.get("UOM SKU", ""),
            "UOM EAN": row["uom_ean"] or data.get("UOM EAN", ""),
            "Weight UOM": row["weight_uom"] or data.get("Weight UOM", ""),
            "Dimensions UOM": row["dimensions_uom"] or data.get("Dimensions UOM", ""),
            "_canonical_barcode": row["canonical_barcode"] or "",
        })
        if row["uom_qty"]:
            data.setdefault("UOM Qty", row["uom_qty"])
        if row["uom_asin"]:
            data.setdefault("UOM ASIN", row["uom_asin"])
        return data

    def _import_csv_to_sqlite(self, force=False):
        if not self.path.exists() or self.path.stat().st_size <= 0:
            raise FileNotFoundError(f"UOM cache not found: {self.path}")
        with self._db_lock:
            with self._connect() as conn:
                self._init_db(conn)
                csv_mtime = str(self.path.stat().st_mtime_ns)
                db_mtime = self._meta_get(conn, "uom_csv_mtime_ns")
                if not force and db_mtime == csv_mtime:
                    count = conn.execute("SELECT COUNT(*) AS c FROM uom_rows").fetchone()["c"]
                    if count > 0:
                        cache_progress(f"UOM SQLite cache ready: {count:,} rows")
                        self.loaded_at = now_utc()
                        self._ready = True
                        return

                cache_progress(f"Importing UOM CSV into SQLite: {self.db_path}")
                conn.execute("BEGIN")
                conn.execute("DELETE FROM uom_barcode_keys")
                conn.execute("DELETE FROM uom_rows")
                rows_count = 0
                barcode_keys = 0
                with self.path.open("r", encoding="utf-8-sig", newline="") as f:
                    reader = csv.DictReader(f)
                    if not reader.fieldnames or "Product" not in reader.fieldnames:
                        raise RuntimeError(f"UOM CSV has unexpected columns: {reader.fieldnames}")
                    for source_row in reader:
                        row = dict(source_row)
                        product = clean_cell(row.get("Product"))
                        uom = normalize_uom_name(row.get("UOM Name"))
                        row["Product"] = product
                        row["UOM Name"] = uom
                        row["_canonical_barcode"] = canonical_1d_barcode(row.get("UOM EAN"))
                        uom_sku = clean_cell(row.get("UOM SKU"))
                        uom_ean = clean_cell(row.get("UOM EAN"))
                        weight_uom = clean_cell(row.get("Weight UOM")) or "kg"
                        dimensions_uom = clean_cell(row.get("Dimensions UOM")) or "mm"
                        uom_qty = get_uom_qty(row, uom)
                        uom_asin = clean_cell(row.get("UOM ASIN") or row.get("ASIN") or row.get("uomAsin"))
                        cur = conn.execute(
                            """
                            INSERT INTO uom_rows(
                                product, uom_name, uom_sku, uom_ean, canonical_barcode,
                                weight_uom, dimensions_uom, uom_qty, uom_asin,
                                norm_product, norm_uom_sku, raw_json
                            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                            """,
                            (
                                product, uom, uom_sku, uom_ean, row["_canonical_barcode"],
                                weight_uom, dimensions_uom, uom_qty, uom_asin,
                                norm_key(product), norm_key(uom_sku),
                                json.dumps(row, ensure_ascii=False),
                            ),
                        )
                        row_id = cur.lastrowid
                        seen_keys = set()
                        for key in barcode_candidates(uom_ean):
                            k = clean_cell(key).upper()
                            if not k or k in seen_keys:
                                continue
                            seen_keys.add(k)
                            conn.execute(
                                "INSERT OR IGNORE INTO uom_barcode_keys(key, row_id) VALUES(?, ?)",
                                (k, row_id),
                            )
                            barcode_keys += 1
                        rows_count += 1
                if rows_count <= 0:
                    raise RuntimeError("UOM CSV loaded zero rows")
                self._meta_set(conn, "uom_csv_mtime_ns", csv_mtime)
                self._meta_set(conn, "uom_imported_at", now_utc())
                conn.commit()
                cache_progress(f"UOM SQLite cache ready: {rows_count:,} rows, {barcode_keys:,} barcode keys")
                log_event("uom.cache.loaded", rows=rows_count, barcodes=barcode_keys, db=str(self.db_path))
                self.loaded_at = now_utc()
                self._ready = True

    def load(self, force_download=False):
        last_error = None
        for attempt in range(2):
            try:
                self.ensure_downloaded(force=(force_download or attempt == 1))
                self._import_csv_to_sqlite(force=(force_download or attempt == 1))
                return
            except Exception as e:
                last_error = e
                cache_progress(f"UOM cache load failed: {e}")
                log_event("uom.cache.load_failed", error=str(e), attempt=attempt + 1)
                if attempt == 0:
                    cache_progress("Redownloading UOM export because cache load failed")
                    continue
                raise last_error

    def refresh(self, force=False):
        if force:
            cache_progress("Refreshing UOM cache now")
        self.load(force_download=force)

    def ensure_loaded(self):
        if not self._ready:
            self.load(force_download=False)

    def lookup_barcode(self, code):
        self.ensure_loaded()
        with self._db_lock:
            with self._connect() as conn:
                self._init_db(conn)
                for key in barcode_candidates(code):
                    row = conn.execute(
                        """
                        SELECT ur.*
                        FROM uom_barcode_keys bk
                        JOIN uom_rows ur ON ur.id = bk.row_id
                        WHERE bk.key = ?
                        LIMIT 1
                        """,
                        (clean_cell(key).upper(),),
                    ).fetchone()
                    if row:
                        return self._row_from_sql(row), canonical_1d_barcode(code)
        return None, canonical_1d_barcode(code)

    def lookup_sku(self, sku):
        self.ensure_loaded()
        key = clean_cell(sku)
        nk = norm_key(key)
        with self._db_lock:
            with self._connect() as conn:
                rows = conn.execute(
                    """
                    SELECT * FROM uom_rows
                    WHERE UPPER(product)=UPPER(?) OR UPPER(uom_sku)=UPPER(?)
                       OR norm_product=? OR norm_uom_sku=?
                    ORDER BY product, uom_name
                    """,
                    (key, key, nk, nk),
                ).fetchall()
        return [self._row_from_sql(r) for r in rows]

    def product_rows(self, product):
        self.ensure_loaded()
        p = clean_cell(product)
        with self._db_lock:
            with self._connect() as conn:
                rows = conn.execute(
                    "SELECT * FROM uom_rows WHERE UPPER(product)=UPPER(?) OR norm_product=? ORDER BY uom_name",
                    (p, norm_key(p)),
                ).fetchall()
        return [self._row_from_sql(r) for r in rows]

    def rows_by_uom(self, rows):
        out = {}
        for row in rows or []:
            uom = normalize_uom_name(row.get("UOM Name"))
            if uom in UOM_CHOICES and uom not in out:
                out[uom] = row
        return out

    def search_product_matches(self, query, limit=5):
        """Use SQLite to narrow SKU candidates, then score in Python for current fuzzy behavior."""
        self.ensure_loaded()
        q = clean_cell(query)
        qn = norm_key(q)
        if not qn:
            return []
        candidates = {}
        with self._db_lock:
            with self._connect() as conn:
                # Exact and LIKE matches use indexed/normalized columns where possible.
                sql_rows = conn.execute(
                    """
                    SELECT product, MIN(norm_product) AS norm_product
                    FROM uom_rows
                    WHERE norm_product = ?
                       OR norm_product LIKE ?
                       OR UPPER(product) LIKE UPPER(?)
                    GROUP BY product
                    LIMIT 80
                    """,
                    (qn, f"%{qn}%", f"%{q}%"),
                ).fetchall()
                for r in sql_rows:
                    product = clean_cell(r["product"])
                    if product:
                        candidates[product.upper()] = product

                # If the query is very short or LIKE missed a suffix-style SKU, use a small fallback scan of products only.
                if len(candidates) < limit:
                    fallback = conn.execute("SELECT DISTINCT product FROM uom_rows LIMIT 5000").fetchall()
                    for r in fallback:
                        product = clean_cell(r["product"])
                        if product and score_reference(q, product) >= 55:
                            candidates.setdefault(product.upper(), product)
                            if len(candidates) >= 100:
                                break

        matches = []
        for product in candidates.values():
            s = score_reference(q, product)
            if s > 0:
                matches.append({"product": product, "rows": self.product_rows(product), "score": s, "source": "uom_sqlite"})
        matches.sort(key=lambda m: (-m["score"], len(clean_cell(m["product"]))))
        return matches[:limit]

def payload_number(v):
    try:
        if v is None or v == "":
            return None
        f = float(v)
        return f if math.isfinite(f) else None
    except Exception:
        return None


def fmt_num(v, decimals=0):
    """Return endpoint-friendly string numbers, or empty string for missing values."""
    try:
        if v is None or v == "":
            return ""
        f = float(v)
        if not math.isfinite(f):
            return ""
        if decimals == 0:
            return str(int(round(f)))
        return f"{f:.{decimals}f}"
    except Exception:
        return ""


def get_uom_qty(row, uom_name):
    """Return UOM quantity from the export when present, otherwise default to 1."""
    for key in ("UOM Qty", "UOM Quantity", "UOM QTY", "Qty", "Quantity", "UOMQty"):
        val = clean_cell(row.get(key))
        if val:
            return val
    return "1"


def tradepeg_row_summary(payload):
    try:
        rows = payload.get("rows") or []
        return rows[0] if rows else {}
    except Exception:
        return {}


def tradepeg_push_uom(payload):
    """POST the endpoint-compatible {rows:[...]} payload to Farla's TradePeg UOM updater."""
    if not TRADEPEG_API_KEY:
        raise RuntimeError("TRADEPEG_API_KEY not set")
    headers = {"x-api-key": TRADEPEG_API_KEY, "Accept": "application/json", "Content-Type": "application/json"}
    method = TRADEPEG_UOM_UPDATE_METHOD or "POST"
    r = requests.request(method, TRADEPEG_UOM_UPDATE_URL, headers=headers, json=payload, timeout=30)
    if not (200 <= r.status_code < 300):
        raise RuntimeError(f"TradePeg UOM update failed: {r.status_code} {r.text[:500]}")
    first = tradepeg_row_summary(payload)
    log_event(
        "tradepeg.uom_update.ok",
        status_code=r.status_code,
        response=r.text[:500],
        rows=len(payload.get("rows", [])),
        identifier=first.get("identifier"),
        uomName=first.get("uomName"),
        uomEAN=first.get("uomEAN"),
    )
    return True

# ----------------------------
# Offline pool (guaranteed delivery)
# ----------------------------
_pool_lock = threading.Lock()

def _pool_load():
    if not POOL_PATH.exists(): return []
    try:
        return json.loads(POOL_PATH.read_text(encoding="utf-8") or "[]")
    except Exception:
        try:
            POOL_PATH.rename(POOL_PATH.with_suffix(".bad.json"))
        except Exception:
            pass
        return []

def _pool_save(items):
    tmp = POOL_PATH.with_suffix(".tmp")
    tmp.write_text(json.dumps(items, ensure_ascii=False, indent=2), encoding="utf-8")
    tmp.replace(POOL_PATH)

def pool_enqueue(item):
    with _pool_lock:
        items = _pool_load()
        items.append(item)
        _pool_save(items)
        size = len(items)
    log_event("pool.enqueue", size=size)

def pool_peek():
    with _pool_lock:
        items = _pool_load()
        if not items: return None, 0
        return items[0], len(items)

def pool_drop_first():
    with _pool_lock:
        items = _pool_load()
        if items:
            items.pop(0)
            _pool_save(items)
        return len(items)

# ----------------------------
# DB: schema & insert
# ----------------------------
DDL_CREATE = f"""
CREATE TABLE IF NOT EXISTS {TABLE_NAME} (
    id               BIGSERIAL PRIMARY KEY,
    ts_ingested      TIMESTAMPTZ NOT NULL DEFAULT now(),
    product_barcode  TEXT NOT NULL,
    product_title    TEXT,
    product_sku      TEXT,
    product_uom      TEXT,
    product_uom_sku  TEXT,
    normalized_barcode TEXT,
    machine_id       TEXT,
    package_count    INTEGER,
    length_mm        NUMERIC,
    width_mm         NUMERIC,
    height_mm        NUMERIC,
    weight_kg        NUMERIC,
    volume_cm3       NUMERIC,
    dimweight_kg     NUMERIC,
    factor           NUMERIC,
    density_kg_per_l NUMERIC,
    device_datetime  TIMESTAMPTZ,
    raw_json         JSONB
);
"""

DDL_ALTERS = [
    f"ALTER TABLE {TABLE_NAME} ADD COLUMN IF NOT EXISTS product_title TEXT;",
    f"ALTER TABLE {TABLE_NAME} ADD COLUMN IF NOT EXISTS product_sku   TEXT;",
    f"ALTER TABLE {TABLE_NAME} ADD COLUMN IF NOT EXISTS product_uom   TEXT;",
    f"ALTER TABLE {TABLE_NAME} ADD COLUMN IF NOT EXISTS product_uom_sku TEXT;",
    f"ALTER TABLE {TABLE_NAME} ADD COLUMN IF NOT EXISTS normalized_barcode TEXT;",
    f"ALTER TABLE {TABLE_NAME} ADD COLUMN IF NOT EXISTS volume_cm3 NUMERIC;",
    f"ALTER TABLE {TABLE_NAME} ADD COLUMN IF NOT EXISTS dimweight_kg NUMERIC;",
    f"ALTER TABLE {TABLE_NAME} ADD COLUMN IF NOT EXISTS factor NUMERIC;",
    f"ALTER TABLE {TABLE_NAME} ADD COLUMN IF NOT EXISTS density_kg_per_l NUMERIC;",
]

INSERT_SQL = f"""
INSERT INTO {TABLE_NAME} (
    product_barcode, product_title, product_sku,
    product_uom, product_uom_sku, normalized_barcode,
    machine_id, package_count,
    length_mm, width_mm, height_mm, weight_kg,
    volume_cm3, dimweight_kg, factor, density_kg_per_l,
    device_datetime, raw_json
) VALUES (
    %(product_barcode)s, %(product_title)s, %(product_sku)s,
    %(product_uom)s, %(product_uom_sku)s, %(normalized_barcode)s,
    %(machine_id)s, %(package_count)s,
    %(length_mm)s, %(width_mm)s, %(height_mm)s, %(weight_kg)s,
    %(volume_cm3)s, %(dimweight_kg)s, %(factor)s, %(density_kg_per_l)s,
    %(device_datetime)s, %(raw_json)s
) RETURNING id;
"""

def validate_table_name(name):
    if not re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", name or ""):
        raise RuntimeError(f"Invalid TABLE_NAME: {name!r}")


def db_connect_and_init():
    validate_table_name(TABLE_NAME)
    if not DB_URL:
        raise RuntimeError("DATABASE_URL not set")
    conn = psycopg2.connect(DB_URL)
    conn.autocommit = True
    with conn.cursor() as cur:
        cur.execute(DDL_CREATE)
        for stmt in DDL_ALTERS:
            cur.execute(stmt)
    log_event("db.connected")
    return conn

# ----------------------------
# Serial parsing / helpers
# ----------------------------
def to_float(x):
    try:
        if x is None: return math.nan
        if isinstance(x, (int, float)): return float(x)
        s = str(x).strip().replace(",", ".")
        return float(s)
    except Exception:
        return math.nan

def status_ok(code: str) -> bool:
    return (code or "").strip() == "00"

def parse_dev_time(s: str):
    try:
        dt = datetime.strptime(s, "%Y%m%d%H%M%S").replace(tzinfo=timezone.utc)
        return None if dt.year == 1970 else dt
    except Exception:
        return None

def sanitize_bytes(buf: bytes) -> str:
    """
    Accept either:
      1) Plain JSON line ending in CR/LF
      2) STX(0x02) + JSON + ETX(0x03) [+ CRLF]
    Return the JSON substring as utf-8 text, or '' if none.
    """
    s = buf.replace(b"\x00", b"").strip()
    stx = s.find(b"\x02")
    etx = s.rfind(b"\x03")
    if stx != -1 and etx != -1 and etx > stx:
        s = s[stx+1:etx]
    l = s.find(b"{")
    r = s.rfind(b"}")
    if l != -1 and r != -1 and r > l:
        s = s[l:r+1]
    try:
        return s.decode("utf-8", errors="ignore").strip()
    except Exception:
        return ""

def derive(cs: dict):
    L = to_float(cs.get("Length_Value"))
    W = to_float(cs.get("Width_Value"))
    H = to_float(cs.get("Height_Value"))
    m = to_float(cs.get("Weight_Value"))
    fac = to_float(cs.get("Factor_Value"))
    if not math.isfinite(fac) or fac == 0:
        fac = 6000.0

    vol_cm3 = (L * W * H) / 1000.0 if all(map(math.isfinite, [L, W, H])) else math.nan
    dim_kg_calc = (vol_cm3 / fac) if math.isfinite(vol_cm3) else math.nan
    dim_kg = to_float(cs.get("DimWeight_Value"))
    if not math.isfinite(dim_kg):
        dim_kg = dim_kg_calc
    density = (m / (vol_cm3 / 1000.0)) if (math.isfinite(m) and math.isfinite(vol_cm3) and vol_cm3 > 0) else math.nan
    dev_dt = parse_dev_time(cs.get("Date_Time", ""))

    return {
        "L": L if math.isfinite(L) else None,
        "W": W if math.isfinite(W) else None,
        "H": H if math.isfinite(H) else None,
        "m": m if math.isfinite(m) else None,
        "vol_cm3": vol_cm3 if math.isfinite(vol_cm3) else None,
        "dim_kg": dim_kg if math.isfinite(dim_kg) else None,
        "fac": fac if math.isfinite(fac) else None,
        "density": density if math.isfinite(density) else None,
        "dev_dt": dev_dt,
        "machine_id": cs.get("Machine_ID"),
        "package_count": int(cs.get("Package_Count")) if cs.get("Package_Count") else None,
        "ok": all([
            status_ok(cs.get("Status")),
            status_ok(cs.get("Length_Status")),
            status_ok(cs.get("Width_Status")),
            status_ok(cs.get("Height_Status")),
            status_ok(cs.get("Weight_Status")),
        ])
    }

class SerialReader(threading.Thread):
    def __init__(self, port, baud, out_q):
        super().__init__(daemon=True)
        self.port, self.baud, self.out_q = port, baud, out_q
        self._stop = threading.Event()

    def open_serial(self):
        while not self._stop.is_set():
            try:
                ser = serial.Serial(
                    self.port, self.baud,
                    timeout=1,
                    write_timeout=1,
                    bytesize=serial.EIGHTBITS,
                    parity=serial.PARITY_NONE,
                    stopbits=serial.STOPBITS_ONE,
                    xonxoff=False, rtscts=False, dsrdtr=False,
                )
                log_event("serial.opened", port=self.port, baud=self.baud)
                return ser
            except Exception as e:
                log_event("serial.error", error=str(e))
                time.sleep(1.0)
        return None

    def run(self):
        while not self._stop.is_set():
            ser = self.open_serial()
            if ser is None:
                break
            try:
                with ser:
                    while not self._stop.is_set():
                        raw = ser.readline()   # bytes until '\n' or timeout
                        if not raw:
                            continue
                        jtxt = sanitize_bytes(raw)
                        if not jtxt:
                            log_event("serial.debug", sample=raw[:32].hex())
                            continue
                        log_raw(jtxt)
                        try:
                            msg = json.loads(jtxt)
                            cs = msg.get("csMeasureData", msg)
                            d = derive(cs)
                            self.out_q.put({"raw": msg, "derived": d})
                            log_event("serial.frame",
                                      length=d.get("L"), width=d.get("W"),
                                      height=d.get("H"), weight=d.get("m"),
                                      ok=d.get("ok"))
                        except json.JSONDecodeError:
                            log_event("serial.invalid_json", sample=jtxt[:120])
            except Exception as e:
                log_event("serial.loop_error", error=str(e))
                time.sleep(0.5)

    def stop(self):
        self._stop.set()

# ----------------------------
# TradePeg lookup
# ----------------------------
# Direct TradePeg API access is intentionally disabled.
# This kiosk only talks to the Farla Railway API endpoints configured above.

# ----------------------------
# Barcode buffer (keyboard scanner)
# ----------------------------
class BarcodeBuffer:
    def __init__(self): self.buf = ""
    def feed(self, ch):
        if ch in ("\r", "\n"):
            code = self.buf.strip(); self.buf = ""; return code
        if len(ch) == 1 and ch.isprintable(): self.buf += ch
        return None

# ----------------------------
# Background uploader
# ----------------------------
class Uploader(threading.Thread):
    def __init__(self):
        super().__init__(daemon=True)
        self._stop = threading.Event()
        self.conn = None

    def run(self):
        while not self._stop.is_set():
            item, remaining = pool_peek()
            if not item:
                time.sleep(1)
                continue

            try:
                # First update TradePeg, then record locally. The item is removed only after both configured sinks succeed.
                if item.get("tradepeg_payload"):
                    tradepeg_push_uom(item["tradepeg_payload"])

                db_payload = item.get("db_payload", item)
                inserted_id = None
                if DB_URL:
                    if self.conn is None:
                        self.conn = db_connect_and_init()
                    with self.conn.cursor(cursor_factory=psycopg2.extras.RealDictCursor) as cur:
                        params = dict(db_payload)
                        params["raw_json"] = psycopg2.extras.Json(db_payload["raw_json"])
                        cur.execute(INSERT_SQL, params)
                        row = cur.fetchone()
                        inserted_id = row["id"]
                    log_event("db.insert.ok", id=inserted_id)
                remaining = pool_drop_first()
                log_event("upload.complete", db_id=inserted_id, remaining=remaining)
            except Exception as e:
                log_event("upload.fail", error=str(e))
                try:
                    if self.conn: self.conn.close()
                except Exception:
                    pass
                self.conn = None
                time.sleep(3)

    def stop(self):
        self._stop.set()
        try:
            if self.conn: self.conn.close()
        except Exception:
            pass


# ----------------------------
# Fast CSV product catalogue + search helpers
# ----------------------------
TRADEPEG_EXPORT_PRODUCTS_URL = f"{TRADEPEG_API_BASE}/export/products"
PRODUCT_CACHE_PATH = APP_DIR / "tradepeg_products.csv"
PRODUCT_CACHE_REFRESH_SECONDS = 21600
NEON = "#b6ff00"
CARD_BG_2 = "#242424"
CARD_BG_3 = "#303030"


def likely_numeric_barcode(value):
    raw = clean_cell(value)
    if _gs1_gtin(raw):
        return True
    digits = re.sub(r"\D+", "", raw)
    return bool(digits) and len(digits) >= 8 and not re.search(r"[A-Za-z\-/]", raw)


def norm_key(value):
    return re.sub(r"[^A-Z0-9]+", "", clean_cell(value).upper())


def display_product(value):
    return clean_cell(value).upper()


def score_reference(query, reference):
    q_raw = clean_cell(query).upper()
    r_raw = clean_cell(reference).upper()
    q = norm_key(query)
    r = norm_key(reference)
    if not q or not r:
        return 0
    if q == r or q_raw == r_raw:
        return 100
    score = 0
    if q in r:
        score = max(score, 88 - max(0, len(r) - len(q)))
    if r.endswith(q):
        score = max(score, 92 - max(0, len(r) - len(q)))
    if r.startswith(q):
        score = max(score, 86 - max(0, len(r) - len(q)))
    parts = [p for p in re.split(r"[^A-Z0-9]+", q_raw) if p]
    if parts and all(p in r_raw for p in parts):
        score = max(score, 72 + min(15, len("".join(parts))))
    # Small subsequence fallback for cases like NPFL -> FM-NPFL.
    pos = -1
    hits = 0
    for ch in q:
        nxt = r.find(ch, pos + 1)
        if nxt < 0:
            break
        hits += 1
        pos = nxt
    if q and hits == len(q):
        score = max(score, 55 + min(20, hits * 2))
    return min(100, score)


class ProductCatalogCache:
    """SQLite-backed product reference/title/brand cache."""
    def __init__(self, path=PRODUCT_CACHE_PATH, db_path=CACHE_DB_PATH):
        self.path = Path(path)
        self.db_path = Path(db_path)
        self.loaded_at = 0
        self.rows = []  # compatibility only; SQLite is the source of truth
        self._db_lock = threading.Lock()
        self._ready = False

    def _connect(self):
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        conn = sqlite3.connect(str(self.db_path), timeout=30, check_same_thread=False)
        conn.row_factory = sqlite3.Row
        try:
            conn.execute("PRAGMA journal_mode=WAL")
            conn.execute("PRAGMA synchronous=NORMAL")
            conn.execute("PRAGMA temp_store=MEMORY")
        except Exception:
            pass
        return conn

    def _init_db(self, conn):
        conn.executescript("""
        CREATE TABLE IF NOT EXISTS cache_meta (
            name TEXT PRIMARY KEY,
            value TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS product_rows (
            reference TEXT PRIMARY KEY,
            title TEXT,
            brand TEXT,
            norm_reference TEXT,
            raw_json TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_product_rows_reference ON product_rows(reference);
        CREATE INDEX IF NOT EXISTS idx_product_rows_norm_reference ON product_rows(norm_reference);
        """)
        conn.commit()

    def _meta_get(self, conn, name):
        row = conn.execute("SELECT value FROM cache_meta WHERE name=?", (name,)).fetchone()
        return row["value"] if row else None

    def _meta_set(self, conn, name, value):
        conn.execute(
            "INSERT INTO cache_meta(name, value) VALUES(?, ?) ON CONFLICT(name) DO UPDATE SET value=excluded.value",
            (name, str(value)),
        )

    def _candidate_paths(self):
        paths = [
            self.path,
            APP_DIR / "tradepeg_products.csv",
            APP_DIR / "tradepeg_products(2).csv",
            SCRIPT_DIR / "tradepeg_products.csv",
            SCRIPT_DIR / "tradepeg_products(2).csv",
        ]
        seen = set()
        for p in paths:
            p = Path(p)
            if p not in seen:
                seen.add(p)
                yield p

    def _best_existing_csv(self):
        existing = [p for p in self._candidate_paths() if p.exists() and p.stat().st_size > 0]
        if not existing:
            return None
        return max(existing, key=lambda p: p.stat().st_mtime)

    def ensure_downloaded(self, force=False):
        chosen = self._best_existing_csv()
        stale = False
        if chosen and chosen.exists():
            stale = (time.time() - chosen.stat().st_mtime) > PRODUCT_CACHE_REFRESH_SECONDS
        if force or not chosen or stale:
            if not TRADEPEG_API_KEY:
                cache_progress("Product cache missing/stale/failed, but TRADEPEG_API_KEY is not set; cannot download /export/products")
                if chosen and chosen.exists() and chosen.stat().st_size > 0:
                    return chosen
                raise RuntimeError("TRADEPEG_API_KEY not set and no usable product cache exists")
            cache_progress(f"Downloading product export from {TRADEPEG_EXPORT_PRODUCTS_URL}")
            headers = {"x-api-key": TRADEPEG_API_KEY}
            r = requests.get(TRADEPEG_EXPORT_PRODUCTS_URL, headers=headers, timeout=120)
            r.raise_for_status()
            if not r.content:
                raise RuntimeError("Downloaded product export was empty")
            tmp = self.path.with_suffix(self.path.suffix + ".tmp")
            tmp.write_bytes(r.content)
            tmp.replace(self.path)
            chosen = self.path
            cache_progress(f"Downloaded product export: {len(r.content):,} bytes")
            log_event("product.cache.downloaded", bytes=len(r.content), path=str(self.path))
        if chosen and chosen != self.path:
            try:
                if not self.path.exists() or chosen.stat().st_mtime >= self.path.stat().st_mtime:
                    self.path.write_bytes(chosen.read_bytes())
                    chosen = self.path
            except Exception as e:
                log_event("product.cache.copy_error", error=str(e), source=str(chosen), dest=str(self.path))
        cache_progress(f"Using product cache: {chosen or self.path}")
        return chosen or self.path

    def _import_csv_to_sqlite(self, path, force=False):
        if not path.exists() or path.stat().st_size <= 0:
            raise FileNotFoundError(f"Product cache not found: {path}")
        with self._db_lock:
            with self._connect() as conn:
                self._init_db(conn)
                csv_mtime = str(path.stat().st_mtime_ns)
                db_mtime = self._meta_get(conn, "product_csv_mtime_ns")
                if not force and db_mtime == csv_mtime:
                    count = conn.execute("SELECT COUNT(*) AS c FROM product_rows").fetchone()["c"]
                    if count > 0:
                        cache_progress(f"Product SQLite cache ready: {count:,} rows")
                        self.loaded_at = time.time()
                        self._ready = True
                        return

                cache_progress(f"Importing product CSV into SQLite: {self.db_path}")
                conn.execute("BEGIN")
                conn.execute("DELETE FROM product_rows")
                rows_count = 0
                with path.open("r", encoding="utf-8-sig", newline="") as f:
                    reader = csv.DictReader(f)
                    if not reader.fieldnames or "Reference" not in reader.fieldnames:
                        raise RuntimeError(f"Product CSV has unexpected columns: {reader.fieldnames}")
                    for row in reader:
                        ref = clean_cell(row.get("Reference") or row.get("Product") or row.get("SKU") or row.get("Sku"))
                        if not ref:
                            continue
                        title = clean_cell(row.get("Title") or row.get("Name") or row.get("Product Name"))
                        brand = clean_cell(row.get("Brand") or row.get("Manufacturer"))
                        conn.execute(
                            """
                            INSERT OR REPLACE INTO product_rows(reference, title, brand, norm_reference, raw_json)
                            VALUES(?, ?, ?, ?, ?)
                            """,
                            (ref, title, brand, norm_key(ref), json.dumps(row, ensure_ascii=False)),
                        )
                        rows_count += 1
                if rows_count <= 0:
                    raise RuntimeError("Product CSV loaded zero rows")
                self._meta_set(conn, "product_csv_mtime_ns", csv_mtime)
                self._meta_set(conn, "product_imported_at", now_utc())
                conn.commit()
                cache_progress(f"Product SQLite cache ready: {rows_count:,} rows")
                log_event("product.cache.loaded", rows=rows_count, path=str(path), db=str(self.db_path))
                self.loaded_at = time.time()
                self._ready = True

    def load(self, force=False):
        last_error = None
        for attempt in range(2):
            try:
                path = self.ensure_downloaded(force=(force or attempt == 1))
                self._import_csv_to_sqlite(path, force=(force or attempt == 1))
                return
            except Exception as e:
                last_error = e
                cache_progress(f"Product cache load failed: {e}")
                log_event("product.cache.load_failed", error=str(e), attempt=attempt + 1)
                if attempt == 0:
                    cache_progress("Redownloading product export because cache load failed")
                    continue
                raise last_error

    def ensure_loaded(self):
        if not self._ready:
            self.load(force=False)

    def get(self, reference):
        self.ensure_loaded()
        key = clean_cell(reference)
        nk = norm_key(key)
        with self._db_lock:
            with self._connect() as conn:
                row = conn.execute(
                    "SELECT * FROM product_rows WHERE UPPER(reference)=UPPER(?) OR norm_reference=? LIMIT 1",
                    (key, nk),
                ).fetchone()
        if not row:
            return {}
        return {"reference": row["reference"], "title": row["title"] or "", "brand": row["brand"] or "", "_norm": row["norm_reference"] or ""}

    def enrich(self, product):
        info = self.get(product)
        return {
            "product": clean_cell(product),
            "brand": clean_cell(info.get("brand")),
            "title": clean_cell(info.get("title")),
        }

    def enrich_matches(self, matches):
        self.ensure_loaded()
        out = []
        for m in matches:
            info = self.get(m.get("product"))
            mm = dict(m)
            mm["brand"] = clean_cell(info.get("brand"))
            mm["title"] = clean_cell(info.get("title"))
            out.append(mm)
        return out

    def search_reference(self, query, limit=5):
        self.ensure_loaded()
        q = clean_cell(query)
        qn = norm_key(q)
        if not qn:
            return []
        candidates = {}
        with self._db_lock:
            with self._connect() as conn:
                rows = conn.execute(
                    """
                    SELECT * FROM product_rows
                    WHERE norm_reference = ?
                       OR norm_reference LIKE ?
                       OR UPPER(reference) LIKE UPPER(?)
                    LIMIT 100
                    """,
                    (qn, f"%{qn}%", f"%{q}%"),
                ).fetchall()
                for row in rows:
                    ref = clean_cell(row["reference"])
                    if ref:
                        candidates[ref.upper()] = row

                if len(candidates) < limit:
                    fallback = conn.execute("SELECT * FROM product_rows LIMIT 10000").fetchall()
                    for row in fallback:
                        ref = clean_cell(row["reference"])
                        if ref and score_reference(q, ref) >= 55:
                            candidates.setdefault(ref.upper(), row)
                            if len(candidates) >= 100:
                                break

        matches = []
        for row in candidates.values():
            ref = clean_cell(row["reference"])
            s = score_reference(q, ref)
            if s > 0:
                matches.append({
                    "product": ref,
                    "rows": [],
                    "score": s,
                    "source": "product_sqlite",
                    "brand": clean_cell(row["brand"]),
                    "title": clean_cell(row["title"]),
                })
        matches.sort(key=lambda m: (-m["score"], len(clean_cell(m["product"]))))
        return matches[:limit]

def make_synthetic_uom_row(product, uom_name, base_rows=None):
    base_rows = base_rows or []
    template = base_rows[0] if base_rows else {}
    product = clean_cell(product)
    uom = normalize_uom_name(uom_name)
    return {
        "Product": product,
        "UOM Name": uom,
        "UOM SKU": clean_cell(template.get("UOM SKU")) if False else f"{product}-{uom.upper()}",
        "UOM EAN": "",
        "Weight UOM": clean_cell(template.get("Weight UOM")) or "kg",
        "Dimensions UOM": clean_cell(template.get("Dimensions UOM")) or "mm",
        "_synthetic": True,
        "_canonical_barcode": "",
    }


def payload_barcode_for(row, scanned_barcode):
    existing = canonical_1d_barcode(row.get("UOM EAN"))
    if existing and existing.isdigit():
        return existing
    scanned = canonical_1d_barcode(scanned_barcode)
    return scanned if likely_numeric_barcode(scanned_barcode) and scanned.isdigit() else ""


def build_tradepeg_uom_payload(row, barcode, dims):
    """
    Build the endpoint contract required by /update/uom:
    {"rows": [{identifier, uomName, uomQty, uomReference, uomEAN, ...}]}
    """
    product = clean_cell(row.get("Product")) or clean_cell(row.get("UOM SKU"))
    uom_name = normalize_uom_name(row.get("UOM Name"))
    uom_reference = clean_cell(row.get("UOM SKU")) or f"{product}-{uom_name.upper()}"
    uom_ean = payload_barcode_for(row, barcode)

    # The kiosk stores/displays Cubiscan weight as kg. TradePeg endpoint expects grams in the current contract.
    weight_kg = payload_number(dims.get("m"))
    weight_g = None if weight_kg is None else weight_kg * 1000

    uom_asin = (
        clean_cell(row.get("UOM ASIN"))
        or clean_cell(row.get("ASIN"))
        or clean_cell(row.get("uomAsin"))
    )

    return {
        "rows": [
            {
                "identifier": product,
                "uomName": uom_name,
                "uomQty": get_uom_qty(row, uom_name),
                "uomReference": uom_reference,
                "uomEAN": uom_ean,
                "uomWeightUom": "g",
                "uomWeight": fmt_num(weight_g, 0),
                "uomHeight": fmt_num(dims.get("H"), 0),
                "uomWidth": fmt_num(dims.get("W"), 0),
                "uomLength": fmt_num(dims.get("L"), 0),
                "dimensionsUom": "mm",
                "uomAsin": uom_asin,
            }
        ]
    }

# ----------------------------
# UI – warehouse kiosk cards
# ----------------------------
class MetricCard(tk.Frame):
    def __init__(self, master, label, unit):
        super().__init__(master, bg="#202020", highlightthickness=1, highlightbackground="#363636")
        self.grid_columnconfigure(0, weight=1)
        tk.Label(self, text=label.upper(), bg="#202020", fg=MUTED, font=("Inter", 10, "bold"), anchor="w").grid(row=0, column=0, sticky="ew", padx=16, pady=(12, 0))
        line = tk.Frame(self, bg="#202020")
        line.grid(row=1, column=0, sticky="ew", padx=16, pady=(6, 14))
        self.value = tk.Label(line, text="--", bg="#202020", fg=BRIGHT, font=("Inter", 30, "bold"))
        self.value.pack(side="left")
        tk.Label(line, text=unit, bg="#202020", fg=NEON, font=("Inter", 14, "bold")).pack(side="left", padx=(8,0), pady=(10,0))

    def set_value(self, val):
        self.value.configure(text=val if val else "--")


class Toast(ttk.Frame):
    def __init__(self, master):
        super().__init__(master, style="Toast.TFrame", padding=(18, 12))
        self.label = ttk.Label(self, text="", style="Toast.TLabel")
        self.label.pack()
        self.place(relx=.5, rely=1.08, anchor="s")
        self.animating = False

    def show(self, msg, color=NEON):
        self.label.configure(text=msg, foreground=color)
        if not self.animating:
            self.animating = True
            self._slide_in()
            self.after(1800, self._slide_out)

    def _slide_in(self):
        y = getattr(self, "_y", 1.08)
        y = max(0.94, y - 0.025)
        self._y = y
        self.place(relx=.5, rely=y, anchor="s")
        if y > 0.94:
            self.after(8, self._slide_in)

    def _slide_out(self):
        y = getattr(self, "_y", 0.94)
        y = min(1.10, y + 0.025)
        self._y = y
        self.place(relx=.5, rely=y, anchor="s")
        if y < 1.10:
            self.after(8, self._slide_out)
        else:
            self.animating = False


class ProductCard(tk.Frame):
    def __init__(self, master, index, product, brand, title, focused=False, submit_ready=False, subline=""):
        bg = NEON if focused else "#282828"
        fg = "#101010" if focused else BRIGHT
        subfg = "#1e1e1e" if focused else SOFT_TXT
        border = "#dfff74" if focused else "#3f3f3f"
        super().__init__(master, bg=bg, highlightthickness=2 if focused else 1, highlightbackground=border)
        self.grid_columnconfigure(0, weight=1)
        if submit_ready:
            tk.Label(self, text="SELECTED • WILL SUBMIT", bg="#101010", fg=NEON, font=("Inter", 12, "bold"), pady=6).grid(row=0, column=0, sticky="ew")
        elif focused:
            tk.Label(self, text="SELECTED PRODUCT", bg="#101010", fg=NEON, font=("Inter", 12, "bold"), pady=6).grid(row=0, column=0, sticky="ew")
        body = tk.Frame(self, bg=bg)
        body.grid(row=1, column=0, sticky="nsew", padx=18, pady=16)
        body.grid_columnconfigure(1, weight=1)
        tk.Label(body, text=str(index) if index else "", bg="#101010" if focused else NEON, fg=NEON if focused else "#101010", font=("Inter", 20, "bold"), width=3).grid(row=0, column=0, sticky="nw", padx=(0, 14))
        tk.Label(body, text=product or "Unknown", bg=bg, fg=fg, font=("Inter", 26, "bold"), anchor="w").grid(row=0, column=1, sticky="ew")
        tk.Label(body, text=brand or "No brand in product export", bg=bg, fg=fg if focused else NEON, font=("Inter", 15, "bold"), anchor="w").grid(row=1, column=0, columnspan=2, sticky="ew", pady=(18, 0))
        tk.Label(body, text=title or "No title in product export", bg=bg, fg=subfg, font=("Inter", 14), wraplength=420, justify="left", anchor="w").grid(row=2, column=0, columnspan=2, sticky="ew", pady=(6,0))
        if subline:
            tk.Label(body, text=subline, bg="#101010" if focused else "#1e1e1e", fg=NEON if focused else SOFT_TXT, font=("Inter", 12, "bold"), padx=10, pady=8, anchor="w", justify="left").grid(row=3, column=0, columnspan=2, sticky="ew", pady=(18,0))


class UomCard(tk.Frame):
    def __init__(self, master, index, uom_name, product, brand, title, row, focused=False, submit_ready=False):
        bg = NEON if focused else "#282828"
        fg = "#101010" if focused else BRIGHT
        subfg = "#202020" if focused else SOFT_TXT
        border = "#dfff74" if focused else "#3f3f3f"
        exists = not bool(row.get("_synthetic"))
        super().__init__(master, bg=bg, highlightthickness=3 if focused else 1, highlightbackground=border)
        self.grid_columnconfigure(0, weight=1)
        if submit_ready:
            tk.Label(self, text="SELECTED • WILL SUBMIT", bg="#101010", fg=NEON, font=("Inter", 12, "bold"), pady=6).grid(row=0, column=0, sticky="ew")
        elif focused:
            tk.Label(self, text="CHOOSE THIS UOM", bg="#101010", fg=NEON, font=("Inter", 12, "bold"), pady=6).grid(row=0, column=0, sticky="ew")
        body = tk.Frame(self, bg=bg)
        body.grid(row=1, column=0, sticky="nsew", padx=22, pady=18)
        body.grid_columnconfigure(1, weight=1)
        tk.Label(body, text=str(index), bg="#101010" if focused else NEON, fg=NEON if focused else "#101010", font=("Inter", 20, "bold"), width=3).grid(row=0, column=0, sticky="nw", padx=(0, 14))
        tk.Label(body, text=uom_name, bg=bg, fg=fg, font=("Inter", 42, "bold"), anchor="w").grid(row=0, column=1, sticky="ew")
        tk.Label(body, text=product, bg=bg, fg=fg if focused else NEON, font=("Inter", 16, "bold"), anchor="w").grid(row=1, column=0, columnspan=2, sticky="ew", pady=(18, 0))
        tk.Label(body, text=" • ".join([x for x in (brand, title) if x]) or "No title/brand in product export", bg=bg, fg=subfg, font=("Inter", 13), wraplength=420, justify="left", anchor="w").grid(row=2, column=0, columnspan=2, sticky="ew", pady=(6,0))
        state = "Existing UOM" if exists else "New UOM will be created"
        tk.Label(body, text=state, bg="#101010" if focused else ("#1e1e1e" if exists else "#3a2d12"), fg=NEON if focused else (SOFT_TXT if exists else WARN), font=("Inter", 12, "bold"), padx=10, pady=8, anchor="w").grid(row=3, column=0, columnspan=2, sticky="ew", pady=(16,0))
        details = f"UOM SKU: {clean_cell(row.get('UOM SKU')) or '-'}\nBarcode in TradePeg: {canonical_1d_barcode(row.get('UOM EAN')) or '-'}"
        tk.Label(body, text=details, bg=bg, fg=subfg, font=("Inter", 12, "bold"), justify="left", anchor="w").grid(row=4, column=0, columnspan=2, sticky="ew", pady=(10,0))


class App:
    def __init__(self, root):
        self.root = root
        root.title("")
        root.configure(bg=DARK_BG)
        root.attributes("-fullscreen", True)
        root.bind("<Escape>", lambda e: root.attributes("-fullscreen", False))
        style = ttk.Style(root)
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure("Toast.TFrame", background="#141414")
        style.configure("Toast.TLabel", font=("Inter", 16, "bold"), background="#141414")

        self.outer = tk.Frame(root, bg=DARK_BG, padx=26, pady=22)
        self.outer.pack(fill="both", expand=True)
        header = tk.Frame(self.outer, bg=DARK_BG)
        header.pack(fill="x")
        tk.Label(header, text="Farla", bg=DARK_BG, fg=BRIGHT, font=("Inter", 30, "bold")).pack(side="left")
        tk.Label(header, text="  Dimension Capture", bg=DARK_BG, fg=NEON, font=("Inter", 30, "bold")).pack(side="left")

        self.search_wrap = tk.Frame(self.outer, bg="#121212", highlightthickness=2, highlightbackground=NEON, padx=16, pady=10)
        self.search_wrap.pack(fill="x", pady=(22, 14))
        tk.Label(self.search_wrap, text="SCAN / SEARCH", bg="#121212", fg=MUTED, font=("Inter", 11, "bold")).pack(side="left", padx=(0, 14))
        self.search_val = tk.Text(self.search_wrap, height=1, bg="#121212", fg=NEON, insertbackground=NEON, relief="flat", font=("Inter", 27, "bold"), wrap="none")
        self.search_val.tag_configure("fluff", foreground=ERROR)
        self.search_val.tag_configure("barcode", foreground=NEON)
        self.search_val.tag_configure("plain", foreground=NEON)
        self.search_val.configure(state="disabled")
        self.search_val.pack(side="left", fill="x", expand=True)

        self.step_title = tk.Label(self.outer, text="Scan a barcode or SKU", bg=DARK_BG, fg=BRIGHT, font=("Inter", 24, "bold"), anchor="w")
        self.step_title.pack(fill="x", pady=(0, 8))

        self.cards_area = tk.Frame(self.outer, bg=DARK_BG)
        self.cards_area.pack(fill="both", expand=True)

        bottom = tk.Frame(self.outer, bg=DARK_BG)
        bottom.pack(fill="x", pady=(18,0))
        bottom.columnconfigure((0,1,2,3), weight=1, uniform="metrics")
        self.card_h = MetricCard(bottom, "Height", "mm")
        self.card_w = MetricCard(bottom, "Width", "mm")
        self.card_l = MetricCard(bottom, "Length", "mm")
        self.card_m = MetricCard(bottom, "Weight", "kg")
        for i, card in enumerate([self.card_h, self.card_w, self.card_l, self.card_m]):
            card.grid(row=0, column=i, sticky="nsew", padx=8)

        self.toast = Toast(root)
        self.q = queue.Queue()
        self.latest = None
        self.product_barcode = ""
        self.product_title = ""
        self.product_sku = ""
        self.normalized_barcode = ""
        self.selected_row = None
        self.selected_info = {}
        self.selected_product = ""
        self.sku_match_options = []
        self.uom_rows = []
        self.uom_choices = []
        self.focus_index = 0
        self.mode = "idle"  # idle, product, uom, ready
        self.raw_scan_for_submit = ""
        self.uom_cache = UomCache(UOM_CACHE_PATH)
        self.product_cache = ProductCatalogCache()
        threading.Thread(target=self._load_caches, daemon=True).start()
        self.uploader = Uploader(); self.uploader.start()
        self.reader = SerialReader(PORT, BAUD, self.q); self.reader.start()
        self.bb = BarcodeBuffer(); root.bind("<Key>", self.on_key)
        root.after(70, self.poll_serial)
        self._set_search_text("")
        log_event("ui.start", port=PORT, baud=BAUD, submit=SUBMIT_TO_DB_CODE, clear=CLEAR_CODE)

    def _fmt(self, v, n=0):
        return f"{v:.{n}f}" if (v is not None and isinstance(v, (int, float))) else None

    def set_metrics(self, d):
        self.card_h.set_value(self._fmt(d.get("H"), 0))
        self.card_w.set_value(self._fmt(d.get("W"), 0))
        self.card_l.set_value(self._fmt(d.get("L"), 0))
        self.card_m.set_value(self._fmt(d.get("m"), 3))

    def _load_caches(self):
        try:
            cache_progress("Starting cache load")
            self.root.after(0, lambda: self.toast.show("Loading TradePeg data...", color=NEON))
            self.uom_cache.load(force_download=False)
            self.product_cache.load(force=False)
            cache_progress("All caches ready")
            self.root.after(0, lambda: self.toast.show("TradePeg data ready", color=NEON))
        except Exception as e:
            cache_progress(f"Initial cache load failed: {e}")
            log_event("cache.load_error", error=str(e), traceback=traceback.format_exc())
            try:
                self.root.after(0, lambda: self.toast.show("Cache failed - redownloading TradePeg data...", color=WARN))
                cache_progress("Forcing full redownload of UOM and product exports")
                self.uom_cache.load(force_download=True)
                self.product_cache.load(force=True)
                cache_progress("Full cache redownload succeeded")
                self.root.after(0, lambda: self.toast.show("TradePeg data redownloaded", color=NEON))
            except Exception as e2:
                cache_progress(f"Full cache redownload failed: {e2}")
                log_event("cache.redownload_error", error=str(e2), traceback=traceback.format_exc())
                self.root.after(0, lambda: self.toast.show("TradePeg data download failed - check API key/network", color=ERROR))

    def _set_search_text(self, text):
        raw = clean_cell(text)
        self.search_val.configure(state="normal")
        self.search_val.delete("1.0", "end")
        if not raw:
            self.search_wrap.configure(highlightbackground="#3f3f3f")
            self.search_val.insert("end", "Scan barcode or SKU", "plain")
        else:
            gtin = _gs1_gtin(raw)
            if gtin:
                self.search_wrap.configure(highlightbackground=ERROR)
                marker = "01" + gtin
                idx = raw.find(marker)
                if idx >= 0:
                    self.search_val.insert("end", raw[:idx], "fluff")
                    self.search_val.insert("end", normalize_gtin(gtin), "barcode")
                    self.search_val.insert("end", raw[idx+len(marker):], "fluff")
                else:
                    self.search_val.insert("end", raw, "fluff")
                    self.search_val.insert("end", "  →  " + normalize_gtin(gtin), "barcode")
            else:
                self.search_wrap.configure(highlightbackground=NEON)
                self.search_val.insert("end", raw, "plain")
        self.search_val.configure(state="disabled")

    def _clear_cards(self):
        for child in self.cards_area.winfo_children():
            child.destroy()
        for i in range(5):
            self.cards_area.columnconfigure(i, weight=0)
        for r in range(2):
            self.cards_area.rowconfigure(r, weight=0)

    def _render_product_cards(self):
        self._clear_cards()
        self.step_title.configure(text="Select the product")
        count = max(1, len(self.sku_match_options))
        for i in range(count):
            self.cards_area.columnconfigure(i, weight=1, uniform="productcards")
        self.cards_area.rowconfigure(0, weight=1)
        for i, m in enumerate(self.sku_match_options, 1):
            card = ProductCard(self.cards_area, i, clean_cell(m.get("product")), clean_cell(m.get("brand")), clean_cell(m.get("title")), focused=(i-1 == self.focus_index), submit_ready=False)
            card.grid(row=0, column=i-1, sticky="nsew", padx=9, pady=10)

    def _render_uom_cards(self, submit_ready=False):
        self._clear_cards()
        self.step_title.configure(text="Is this a Unit, Pack, or Case?")
        for i in range(3):
            self.cards_area.columnconfigure(i, weight=1, uniform="uomcards")
        self.cards_area.rowconfigure(0, weight=1)
        product = self.selected_product
        brand = clean_cell(self.selected_info.get("brand"))
        title = clean_cell(self.selected_info.get("title"))
        for i, (uom_name, row) in enumerate(self.uom_choices, 1):
            focused = (i-1 == self.focus_index)
            ready = submit_ready and self.selected_row is row
            card = UomCard(self.cards_area, i, uom_name, product, brand, title, row, focused=focused or ready, submit_ready=ready)
            card.grid(row=0, column=i-1, sticky="nsew", padx=12, pady=10)

    def _build_uom_choices(self, product, rows):
        by = self.uom_cache.rows_by_uom(rows)
        choices = []
        for uom in UOM_CHOICES:
            choices.append((uom, by.get(uom) or make_synthetic_uom_row(product, uom, rows)))
        return choices

    def _select_barcode_row(self, row, raw_code, message="Barcode matched"):
        self.selected_row = row
        self.selected_product = clean_cell(row.get("Product")) or clean_cell(row.get("UOM SKU"))
        self.selected_info = self.product_cache.enrich(self.selected_product)
        self.product_sku = self.selected_product
        self.product_title = " - ".join([x for x in (self.selected_info.get("brand"), self.selected_info.get("title")) if x]) or self.selected_product
        self.normalized_barcode = canonical_1d_barcode(raw_code or row.get("UOM EAN"))
        self.product_barcode = self.normalized_barcode
        self.raw_scan_for_submit = raw_code
        self.mode = "ready"
        self.focus_index = 0
        self._set_search_text(raw_code or self.normalized_barcode)
        uom = normalize_uom_name(row.get("UOM Name"))
        self._clear_cards()
        self.step_title.configure(text=message)
        self.cards_area.columnconfigure(0, weight=1)
        self.cards_area.rowconfigure(0, weight=1)
        subline = f"Matched UOM: {uom}\nUOM SKU: {clean_cell(row.get('UOM SKU')) or '-'}\nBarcode: {self.normalized_barcode or '-'}"
        card = ProductCard(self.cards_area, None, self.selected_product, self.selected_info.get("brand"), self.selected_info.get("title"), focused=True, submit_ready=True, subline=subline)
        card.grid(row=0, column=0, sticky="nsew", padx=10, pady=10)
        log_event("uom.selected", sku=self.product_sku, uom=uom, barcode=self.normalized_barcode)

    def _show_product_matches(self, matches, raw_code):
        self.raw_scan_for_submit = raw_code
        self.sku_match_options = matches
        self.focus_index = 0
        self.mode = "product"
        self.selected_row = None
        self._render_product_cards()

    def _choose_product(self, index):
        if index < 0 or index >= len(self.sku_match_options):
            self.toast.show("No product at that number", color=WARN)
            return False
        m = self.sku_match_options[index]
        product = clean_cell(m.get("product"))
        rows = m.get("rows") or self.uom_cache.product_rows(product)
        self.selected_product = product
        self.selected_info = {"product": product, "brand": clean_cell(m.get("brand")), "title": clean_cell(m.get("title"))}
        self.product_sku = product
        self.product_title = " - ".join([x for x in (self.selected_info.get("brand"), self.selected_info.get("title")) if x]) or product
        self.uom_choices = self._build_uom_choices(product, rows)
        self.focus_index = 0
        self.mode = "uom"
        self.selected_row = None
        self.product_barcode = canonical_1d_barcode(self.raw_scan_for_submit) if likely_numeric_barcode(self.raw_scan_for_submit) else ""
        self._render_uom_cards(submit_ready=False)
        return True

    def _choose_uom(self, index_or_name):
        if isinstance(index_or_name, str):
            name = normalize_uom_name(index_or_name)
            idx = next((i for i, (u, _) in enumerate(self.uom_choices) if u == name), -1)
        else:
            idx = int(index_or_name)
        if idx < 0 or idx >= len(self.uom_choices):
            self.toast.show("Choose Unit, Pack, or Case", color=WARN)
            return False
        self.focus_index = idx
        uom, row = self.uom_choices[idx]
        self.selected_row = row
        self.mode = "ready"
        self.normalized_barcode = payload_barcode_for(row, self.raw_scan_for_submit)
        self.product_barcode = self.normalized_barcode or self.selected_product
        self._render_uom_cards(submit_ready=True)
        log_event("uom.selected", sku=self.selected_product, uom=uom, barcode=self.normalized_barcode)
        return True

    def _search_products_thread(self, code, refresh_uom_first=False):
        try:
            if refresh_uom_first:
                self.uom_cache.refresh(force=True)
                row, one_d = self.uom_cache.lookup_barcode(code)
                if row:
                    self.root.after(0, lambda: self._select_barcode_row(row, code, "Barcode matched after refresh"))
                    return
            matches = self.uom_cache.search_product_matches(code, limit=5)
            matches = self.product_cache.enrich_matches(matches)
            if len(matches) < 5:
                seen = {clean_cell(m.get("product")).upper() for m in matches}
                for m in self.product_cache.search_reference(code, limit=5):
                    if clean_cell(m.get("product")).upper() not in seen:
                        m["rows"] = self.uom_cache.product_rows(m.get("product"))
                        matches.append(m)
                        seen.add(clean_cell(m.get("product")).upper())
                    if len(matches) >= 5:
                        break
            if matches:
                self.root.after(0, lambda: self._show_product_matches(matches[:5], code))
            else:
                self.root.after(0, lambda: self._no_match(code))
        except Exception as e:
            log_event("product.search.error", query=code, error=str(e))
            self.root.after(0, lambda: self._no_match(code))

    def _no_match(self, code):
        self.mode = "idle"
        self.selected_row = None
        self._clear_cards()
        self.step_title.configure(text="No match found")
        self.toast.show("No product found", color=WARN)

    def clear_screen(self):
        self.product_barcode = ""
        self.product_title = ""
        self.product_sku = ""
        self.normalized_barcode = ""
        self.selected_row = None
        self.selected_info = {}
        self.selected_product = ""
        self.sku_match_options = []
        self.uom_choices = []
        self.focus_index = 0
        self.mode = "idle"
        self.raw_scan_for_submit = ""
        self._set_search_text("")
        self.step_title.configure(text="Scan a barcode or SKU")
        self._clear_cards()
        # Keep the latest Qubiscan measurement on screen; clear is for product selection.
        log_event("ui.cleared")
        self.toast.show("Cleared", color=NEON)

    def _move_selection(self, delta):
        if self.mode == "product" and self.sku_match_options:
            self.focus_index = (self.focus_index + delta) % len(self.sku_match_options)
            self._render_product_cards()
            return True
        if self.mode in ("uom", "ready") and self.uom_choices:
            self.focus_index = (self.focus_index + delta) % len(self.uom_choices)
            if self.mode == "ready":
                # Moving away from confirmed UOM means it is no longer selected enough to submit.
                self.selected_row = None
                self.mode = "uom"
            self._render_uom_cards(submit_ready=False)
            return True
        return False

    def _confirm_selection(self):
        if self.mode == "product":
            return self._choose_product(self.focus_index)
        if self.mode == "uom":
            return self._choose_uom(self.focus_index)
        return False

    def on_key(self, event):
        if event.keysym in ("Up", "Left"):
            self._move_selection(-1); return
        if event.keysym in ("Down", "Right"):
            self._move_selection(1); return
        if event.keysym in ("Return", "KP_Enter") and not self.bb.buf:
            self._confirm_selection(); return

        code = self.bb.feed(event.char)
        if code is None or not code:
            return
        u = code.upper()
        if u == CLEAR_CODE:
            self.clear_screen(); return
        if u == SUBMIT_TO_DB_CODE:
            self.handle_submit(); return
        if self.mode == "product" and u in ("1", "2", "3", "4", "5"):
            self.focus_index = int(u) - 1
            self._choose_product(self.focus_index); return
        if self.mode in ("uom", "ready") and u in ("1", "2", "3"):
            self._choose_uom(int(u) - 1); return
        if self.mode in ("uom", "ready") and u in (UOM_UNIT_CODE, UOM_PACK_CODE, UOM_CASE_CODE):
            self._choose_uom({UOM_UNIT_CODE: "Unit", UOM_PACK_CODE: "Pack", UOM_CASE_CODE: "Case"}[u]); return

        self._set_search_text(code)
        log_event("barcode.scanned", barcode=code)
        row, one_d = self.uom_cache.lookup_barcode(code)
        if row:
            self._select_barcode_row(row, code, "Barcode matched this product and UOM")
            return
        self._clear_cards()
        self.step_title.configure(text="Searching products")
        if likely_numeric_barcode(code):
            threading.Thread(target=self._search_products_thread, args=(code, True), daemon=True).start()
        else:
            threading.Thread(target=self._search_products_thread, args=(code, False), daemon=True).start()

    def handle_submit(self):
        if not self.latest:
            self.toast.show("No measurement", color=WARN); log_event("submit.blocked", reason="no_measure"); return
        if not self.selected_row:
            self.toast.show("Choose Unit, Pack, or Case first", color=WARN); log_event("submit.blocked", reason="no_uom"); return
        d = self.latest["derived"]
        db_barcode = self.normalized_barcode or self.selected_product
        db_payload = {
            "product_barcode": db_barcode,
            "product_title": self.product_title or None,
            "product_sku": self.selected_product or self.product_sku or None,
            "product_uom": normalize_uom_name(self.selected_row.get("UOM Name")),
            "product_uom_sku": clean_cell(self.selected_row.get("UOM SKU")) or None,
            "normalized_barcode": self.normalized_barcode or None,
            "machine_id": d["machine_id"],
            "package_count": d["package_count"],
            "length_mm": d["L"] if d.get("L") is not None else None,
            "width_mm":  d["W"] if d.get("W") is not None else None,
            "height_mm": d["H"] if d.get("H") is not None else None,
            "weight_kg": d["m"] if d.get("m") is not None else None,
            "volume_cm3": d.get("vol_cm3"),
            "dimweight_kg": d.get("dim_kg"),
            "factor": d.get("fac"),
            "density_kg_per_l": d.get("density"),
            "device_datetime": d["dev_dt"],
            "raw_json": self.latest["raw"],
        }
        tradepeg_payload = build_tradepeg_uom_payload(self.selected_row, self.raw_scan_for_submit, d)
        pool_enqueue({"db_payload": db_payload, "tradepeg_payload": tradepeg_payload})
        self.toast.show("Queued TradePeg update", color=NEON)
        first_row = tradepeg_row_summary(tradepeg_payload)
        log_event(
            "submit.enqueued",
            barcode=first_row.get("uomEAN"),
            sku=first_row.get("identifier"),
            uom=first_row.get("uomName"),
        )

    def poll_serial(self):
        try:
            while True:
                payload = self.q.get_nowait()
                self.latest = payload
                self.set_metrics(payload["derived"])
        except queue.Empty:
            pass
        self.root.after(70, self.poll_serial)

    def shutdown(self):
        try: self.reader.stop()
        except Exception: pass
        try: self.uploader.stop()
        except Exception: pass
        log_event("ui.exit")


def main():
    root = tk.Tk()
    app = App(root)
    def on_close():
        app.shutdown(); root.destroy()
    root.protocol("WM_DELETE_WINDOW", on_close)
    root.mainloop()

if __name__ == "__main__":
    main()
