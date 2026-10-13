#!/usr/bin/env python3
"""Collect India domestic economy fares for wait-vs-buy tracking.

Tracks two sampling slots per day:

    0900 = morning slot
    2100 = evening slot

Flight matching is based EXACTLY on:

    flight_number
    departure date
    departure airport
    arrival airport
    number of stops
    duration

Each API search returns many flights. The collector stores:

1. Flight level:
   - RANDOM_FLIGHTS_PER_NEW_ROUTE randomly selected flights are watched.
   - Those specific flight identities are re-quoted on later samples.
   - Matching uses the exact composite flight key above.

2. Route level:
   - Cheapest and 2nd-cheapest qualifying offers are stored every sample.

Airlines kept:
    IndiGo (6E)
    Air India (AI)
    Air India Express (IX)
    Akasa Air (QP)

Usage:

    # Automatic slot based on current IST time
    python3 collect_fares.py once

    # Manually force a slot
    python3 collect_fares.py once --slot 0900
    python3 collect_fares.py once --slot 2100

    # Limit searches for a run
    python3 collect_fares.py once --slot 0900 --max-searches 20

    # Long-running daemon
    python3 collect_fares.py daemon

    # Export
    python3 collect_fares.py export

    # Status
    python3 collect_fares.py status

The flight_quotes table contains:

    entry_type = FIRST_ENTRY
        The flight identity was first inserted into flight_watches.

    entry_type = MATCHED_ENTRY
        The exact same flight key was already being watched and was
        matched again on a later search.

Flight key:

    flight_number
    departure date
    departure airport
    arrival airport
    stops
    duration

Example:

    6E123|2026-11-15|DEL|BOM|0|02:10

If ANY of these fields changes, it is treated as a different flight identity.

Source:
    FareEagle public search API.

API limit:
    60 searches/hour/IP.

The collector intentionally uses API_LIMIT_PER_HOUR - 10 as a safety margin.
"""

from __future__ import annotations

import argparse
import base64
import csv
import json
import random
import sqlite3
import sys
import time
from datetime import date, datetime, timedelta
from pathlib import Path
from typing import Any
from zoneinfo import ZoneInfo

import requests


# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

IST = ZoneInfo("Asia/Kolkata")

BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = BASE_DIR / "data"
EXPORT_DIR = DATA_DIR / "exports"
DB_PATH = DATA_DIR / "fares.sqlite"

API_URL = "https://www.fareeagle.com/api/v1/flights/search"

# The two logical sampling slots.
SAMPLE_HOURS_IST = (9, 21)

# Used by daemon mode.
#
# With SPREAD_HOURS = 1:
#
#   09 slot -> 09:00-09:59
#   21 slot -> 21:00-21:59
#
# Because the entire run can take several minutes, the daemon starts
# at the beginning of each sampling hour and processes its searches.
SPREAD_HOURS = 1

API_LIMIT_PER_HOUR = 80

# Safety margin below FareEagle's stated 60/hour limit.
API_SAFETY_MARGIN = 10

MAX_STOPS = 1
ADULTS = 1
CABIN = "Economy"

ALLOWED_AIRLINE_CODES = {
    "6E",  # IndiGo
    "AI",  # Air India
    "IX",  # Air India Express
    "QP",  # Akasa Air
}

DAYS_AHEAD_MIN = 1
DAYS_AHEAD_MAX = 60

# Number of route/date watches maintained.
MAX_ROUTE_DATE_WATCHES = 45

# Number of random flights selected from each NEW route/date search.
#
# IMPORTANT:
# This does NOT mean 5 additional API searches.
# One API search returns many flights, from which we randomly select 5.
RANDOM_FLIGHTS_PER_NEW_ROUTE = 10

# One API search returns many flights.
# Therefore API usage scales with route-dates, not individual flights.
SEARCHES_PER_HOUR = min(
    API_LIMIT_PER_HOUR - API_SAFETY_MARGIN,
    max(
        1,
        (
            MAX_ROUTE_DATE_WATCHES
            + SPREAD_HOURS
            - 1
        )
        // SPREAD_HOURS,
    ),
)

NEW_ROUTE_DATES_PER_HOUR = SEARCHES_PER_HOUR

REQUEST_PAUSE_SEC = 2.0
HTTP_TIMEOUT = 45

# Failure handling.
#
# A failed search writes NO flight_quotes rows (it is not the same as
# "flight not found"). Every attempt is logged in search_attempts instead.
SEARCH_MAX_ATTEMPTS = 3          # per route/date search, within one run
SEARCH_ATTEMPTS_BY_KIND = {      # kinds that deserve fewer attempts
    "http_404": 2,
}
RETRYABLE_KINDS = {
    "rate_limited",
    "http_5xx",
    "http_404",      # unknown meaning so far: retry, log body, never write found=0
    "timeout",
    "connection",
    "api_failure",
    "bad_json",
}
API_BUDGET_GUARD = 3             # stop calling when this close to the hourly limit
RETRY_BACKOFF_SEC = 20           # attempt n waits n * this (or Retry-After, capped)
RETRY_MAX_WAIT_SEC = 120

# After a run with failures, the daemon re-runs only what is still due
# for this slot (route/dates that have no row yet), up to this many passes.
DAEMON_MAX_PASSES = 3
DAEMON_PASS_WAIT_SEC = 600


class SearchError(RuntimeError):
    """A search that did not produce a usable result.

    kind: rate_limited | http_5xx | http_<code> | timeout | connection |
          api_failure | bad_json | budget_exhausted
    """

    def __init__(
        self,
        kind: str,
        code: int | None = None,
        retry_after: int | None = None,
        detail: str = "",
    ) -> None:

        self.kind = kind
        self.code = code
        self.retry_after = retry_after
        self.detail = (detail or "")[:500]

        super().__init__(
            f"{kind}"
            + (f" {code}" if code else "")
            + (f": {self.detail[:200]}" if self.detail else "")
        )


# ---------------------------------------------------------------------------
# Airport configuration
# ---------------------------------------------------------------------------

AIRPORTS: dict[str, str] = {
    "AMD": "Ahmedabad",
    "BDQ": "Vadodara",
    "DEL": "Delhi",
    "BLR": "Bengaluru",
    "HYD": "Hyderabad",
    "BOM": "Mumbai",
    "GOI": "Goa Dabolim",
    "GOX": "Goa Mopa",
    "NMI": "Navi Mumbai",
}


# ---------------------------------------------------------------------------
# Airline classification
# ---------------------------------------------------------------------------

AIRLINE_TYPE: dict[str, str] = {
    "6E": "LCC",
    "SG": "LCC",
    "QP": "LCC",
    "IX": "LCC",
    "I5": "LCC",
    "G8": "LCC",
    "AI": "FSC",
    "UK": "FSC",
    "S5": "regional",
    "9I": "regional",
}


SEAT_KEYS = (
    "seats_remaining",
    "seats_left",
    "available_seats",
    "remaining_seats",
    "seats",
    "last_seats",
    "availability",
)


# ---------------------------------------------------------------------------
# Time / slot helpers
# ---------------------------------------------------------------------------

def now_ist() -> datetime:
    return datetime.now(IST)


def validate_slot(slot: str) -> str:
    """Validate and normalize a manually supplied slot."""
    slot = str(slot).strip()

    allowed = {
        "0900": "0900",
        "09": "0900",
        "9": "0900",
        "2100": "2100",
        "21": "2100",
    }

    if slot not in allowed:
        raise ValueError(
            f"Invalid slot '{slot}'. Use 0900 or 2100."
        )

    return allowed[slot]


def slot_name(
    ts: datetime,
    forced_slot: str | None = None,
) -> str:
    """Return the logical sampling slot.

    If forced_slot is supplied, it always wins.

    Example:
        Current time = 23:00
        forced_slot = "0900"

        Result = "0900"
    """
    if forced_slot is not None:
        return validate_slot(forced_slot)

    hour = ts.hour

    nearest = min(
        SAMPLE_HOURS_IST,
        key=lambda h: min(
            abs(hour - h),
            24 - abs(hour - h),
        ),
    )

    return f"{nearest:02d}00"


def sample_window_hours() -> set[int]:
    """Hours during which daemon mode is allowed to run."""
    hours: set[int] = set()

    for start in SAMPLE_HOURS_IST:
        for offset in range(SPREAD_HOURS):
            hours.add((start + offset) % 24)

    return hours


# ---------------------------------------------------------------------------
# Database queries
# ---------------------------------------------------------------------------

def due_route_dates(
    conn: sqlite3.Connection,
    today: str,
    slot: str,
    limit: int,
) -> list[tuple[str, str, str]]:
    """Find route/date watches that have not yet been sampled for this
    calendar date + logical slot.
    """

    rows = conn.execute(
        """
        SELECT
            rw.origin,
            rw.dest,
            rw.dep_date

        FROM route_watches rw

        WHERE rw.active = 1

          AND NOT EXISTS (
              SELECT 1
              FROM route_best_quotes q

              WHERE q.origin = rw.origin
                AND q.dest = rw.dest
                AND q.dep_date = rw.dep_date
                AND q.slot = ?
                AND substr(q.sampled_at, 1, 10) = ?
          )

        ORDER BY (
            SELECT MAX(q.sampled_at)
            FROM route_best_quotes q
            WHERE q.origin = rw.origin
              AND q.dest = rw.dest
              AND q.dep_date = rw.dep_date
        ) ASC

        LIMIT ?
        """,
        (
            slot,
            today,
            limit,
        ),
    ).fetchall()

    return [
        (
            r["origin"],
            r["dest"],
            r["dep_date"],
        )
        for r in rows
    ]


def days_to_dep(
    dep_date: str,
    ts: datetime,
) -> int:

    d = date.fromisoformat(dep_date)

    return (d - ts.date()).days


def airline_type(
    code: str | None,
) -> str:

    if not code:
        return "unknown"

    return AIRLINE_TYPE.get(
        code.upper(),
        "unknown",
    )


def directed_routes() -> list[tuple[str, str]]:

    codes = list(AIRPORTS)

    return [
        (a, b)
        for a in codes
        for b in codes
        if a != b
    ]


# ---------------------------------------------------------------------------
# Offer parsing
# ---------------------------------------------------------------------------

def parse_price(
    offer: dict[str, Any],
) -> float | None:

    price = offer.get("price")

    if isinstance(price, dict):
        amount = price.get("amount")

        if amount is not None:
            return float(amount)

    if isinstance(price, (int, float)):
        return float(price)

    return None


def parse_seats(
    offer: dict[str, Any],
) -> int | None:

    for key in SEAT_KEYS:

        val = offer.get(key)

        if val is None:
            continue

        if isinstance(val, bool):
            continue

        if isinstance(val, (int, float)):
            return int(val)

        if isinstance(val, str):

            digits = "".join(
                ch
                for ch in val
                if ch.isdigit()
            )

            if digits:
                return int(digits)

    return None


def parse_kg(
    text: Any,
) -> int | None:

    if text is None:
        return None

    digits = "".join(
        ch
        for ch in str(text)
        if ch.isdigit()
    )

    return int(digits) if digits else None


def loc_field(
    block: Any,
    *keys: str,
) -> str:

    if not isinstance(block, dict):
        return ""

    for key in keys:

        val = block.get(key)

        if val:
            return str(val).strip()

    return ""


# ---------------------------------------------------------------------------
# IMPORTANT:
# Exact flight matching key
# ---------------------------------------------------------------------------

def normalize_duration(
    offer: dict[str, Any],
) -> str:
    """Return a stable duration string for flight matching.

    Preference:

        1. duration_minutes
        2. duration

    Examples:

        duration_minutes = 130
            -> "130"

        duration = "02:10"
            -> "02:10"

    The value is deliberately included in flight_key.
    """

    duration_minutes = offer.get(
        "duration_minutes"
    )

    if duration_minutes is not None:

        try:
            return str(
                int(float(duration_minutes))
            )

        except (
            ValueError,
            TypeError,
        ):
            pass

    duration = offer.get("duration")

    if duration is None:
        return ""

    return str(duration).strip()


def flight_key(
    offer: dict[str, Any],
) -> str:
    """Build the exact identity used for flight matching.

    MATCHING PARAMETERS:

        flight number
        departure date
        departure airport
        arrival airport
        number of stops
        duration

    Example:

        6E123|2026-11-15|DEL|BOM|0|130

    Any change in one of these values produces a different key.
    """

    dep = offer.get("departure") or {}
    arr = offer.get("arrival") or {}

    flight_number = str(
        offer.get("flight_number")
        or ""
    ).strip().upper()

    dep_date = loc_field(
        dep,
        "date",
    )

    dep_airport = loc_field(
        dep,
        "airport",
    ).strip().upper()

    arr_airport = loc_field(
        arr,
        "airport",
    ).strip().upper()

    stops = str(
        int(
            offer.get("stops") or 0
        )
    )

    duration = normalize_duration(
        offer
    )

    return "|".join(
        [
            flight_number,
            dep_date,
            dep_airport,
            arr_airport,
            stops,
            duration,
        ]
    )


# ---------------------------------------------------------------------------
# Supplier metadata
# ---------------------------------------------------------------------------

def _decode_token_payload(
    token: Any,
) -> dict[str, Any] | None:
    """Best-effort decode of JSON/JWT/base64 token payloads."""

    if not token:
        return None

    try:

        if isinstance(token, dict):
            return token

        raw = str(token).strip()

        # Plain JSON.
        if raw.startswith("{"):

            obj = json.loads(raw)

            return (
                obj
                if isinstance(obj, dict)
                else None
            )

        # JWT.
        parts = raw.split(".")

        candidates = (
            [parts[1]]
            if len(parts) >= 2
            else [raw]
        )

        for candidate in candidates:

            padded = (
                candidate
                + "=" * (-len(candidate) % 4)
            )

            try:

                decoded = (
                    base64.urlsafe_b64decode(
                        padded
                    )
                    .decode("utf-8")
                )

                obj = json.loads(decoded)

                if isinstance(obj, dict):
                    return obj

            except (
                ValueError,
                UnicodeDecodeError,
                json.JSONDecodeError,
            ):
                continue

    except Exception:
        return None

    return None


def extract_token_metadata(
    offer: dict[str, Any],
) -> dict[str, str | None]:

    token = offer.get("booking_token")

    payload = _decode_token_payload(token)

    searched_at = None
    supplier_tag = None

    for key in (
        "searched_at",
        "search_time",
        "search_timestamp",
    ):

        if offer.get(key):

            searched_at = str(
                offer[key]
            )

            break

    for key in (
        "supplier_tag",
        "supplier",
        "supplier_code",
        "provider",
        "provider_code",
    ):

        if offer.get(key):

            supplier_tag = str(
                offer[key]
            )

            break

    if payload:

        for key in (
            "searched_at",
            "search_time",
            "search_timestamp",
        ):

            if payload.get(key):

                searched_at = str(
                    payload[key]
                )

                break

        for key in (
            "supplier_tag",
            "supplier",
            "supplier_code",
            "provider",
            "provider_code",
        ):

            if payload.get(key):

                supplier_tag = str(
                    payload[key]
                )

                break

        for container_key in (
            "search",
            "metadata",
            "meta",
            "fare",
        ):

            nested = payload.get(
                container_key
            )

            if not isinstance(
                nested,
                dict,
            ):
                continue

            if searched_at is None:

                for key in (
                    "searched_at",
                    "search_time",
                    "search_timestamp",
                ):

                    if nested.get(key):

                        searched_at = str(
                            nested[key]
                        )

                        break

            if supplier_tag is None:

                for key in (
                    "supplier_tag",
                    "supplier",
                    "supplier_code",
                    "provider",
                    "provider_code",
                ):

                    if nested.get(key):

                        supplier_tag = str(
                            nested[key]
                        )

                        break

    return {
        "searched_at": searched_at,
        "supplier_tag": supplier_tag,
    }


def normalize_offer(
    offer: dict[str, Any],
    origin: str,
    dest: str,
) -> dict[str, Any] | None:

    price = parse_price(offer)

    if price is None:
        return None

    stops = int(
        offer.get("stops") or 0
    )

    if stops > MAX_STOPS:
        return None

    cabin = str(
        offer.get("cabin_class")
        or CABIN
    )

    if cabin.lower() not in {
        "economy",
        "econ",
    }:
        return None

    dep = offer.get("departure") or {}
    arr = offer.get("arrival") or {}

    baggage = (
        offer.get("baggage")
        if isinstance(
            offer.get("baggage"),
            dict,
        )
        else {}
    )

    code = str(
        offer.get("airline_code")
        or ""
    ).upper()[:3]

    if not code:

        number = str(
            offer.get("flight_number")
            or ""
        ).upper()

        for prefix in ALLOWED_AIRLINE_CODES:

            if number.startswith(prefix):

                code = prefix

                break

    if code not in ALLOWED_AIRLINE_CODES:
        return None

    known = {
        "airline",
        "airline_code",
        "flight_number",
        "logo_url",
        "departure",
        "arrival",
        "duration",
        "duration_minutes",
        "stops",
        "cabin_class",
        "baggage",
        "is_refundable",
        "price",
        "booking_url",
        "booking_token",
        "booking_token_key",
    }

    extra = {
        k: v
        for k, v in offer.items()
        if k not in known
    }

    dep_date = loc_field(
        dep,
        "date",
    )

    token_meta = extract_token_metadata(
        offer
    )

    normalized = {
        "origin": origin,
        "dest": dest,
        "dep_date": dep_date,

        # EXACT MATCHING KEY
        "flight_key": flight_key(
            offer
        ),

        "flight_number": str(
            offer.get("flight_number")
            or ""
        ),

        "airline": str(
            offer.get("airline")
            or ""
        ),

        "airline_code": code,

        "airline_type": airline_type(
            code
        ),

        "dep_airport": loc_field(
            dep,
            "airport",
        ),

        "arr_airport": loc_field(
            arr,
            "airport",
        ),

        "dep_city": loc_field(
            dep,
            "city",
        ),

        "arr_city": loc_field(
            arr,
            "city",
        ),

        "dep_time": loc_field(
            dep,
            "time",
        )[:5],

        "arr_time": loc_field(
            arr,
            "time",
        )[:5],

        "stops": stops,

        "duration": str(
            offer.get("duration")
            or ""
        ),

        "duration_minutes": offer.get(
            "duration_minutes"
        ),

        "cabin_class": cabin,

        "price_inr": price,

        "currency": (
            (
                offer.get("price")
                or {}
            ).get(
                "currency",
                "INR",
            )
            if isinstance(
                offer.get("price"),
                dict,
            )
            else "INR"
        ),

        "is_refundable": (
            1
            if offer.get(
                "is_refundable"
            )
            else 0
        ),

        "baggage_checkin": str(
            baggage.get("checkin")
            or ""
        ),

        "baggage_cabin": str(
            baggage.get("cabin")
            or ""
        ),

        "baggage_checkin_kg": parse_kg(
            baggage.get("checkin")
        ),

        "baggage_cabin_kg": parse_kg(
            baggage.get("cabin")
        ),

        "seats_remaining": parse_seats(
            offer
        ),

        "searched_at": token_meta[
            "searched_at"
        ],

        "supplier_tag": token_meta[
            "supplier_tag"
        ],

        "extra_json": (
            json.dumps(
                extra,
                ensure_ascii=True,
            )
            if extra
            else ""
        ),
    }

    return normalized


# ---------------------------------------------------------------------------
# Database
# ---------------------------------------------------------------------------

def connect() -> sqlite3.Connection:

    DATA_DIR.mkdir(
        parents=True,
        exist_ok=True,
    )

    conn = sqlite3.connect(
        DB_PATH
    )

    conn.row_factory = sqlite3.Row

    conn.execute(
        "PRAGMA journal_mode=WAL"
    )

    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS search_attempts (
            id INTEGER PRIMARY KEY,
            origin TEXT NOT NULL,
            dest TEXT NOT NULL,
            dep_date TEXT NOT NULL,
            slot TEXT,
            attempted_at TEXT NOT NULL,
            attempt INTEGER NOT NULL,
            status TEXT NOT NULL,
            http_code INTEGER,
            n_offers INTEGER,
            detail TEXT
        );

        CREATE INDEX IF NOT EXISTS idx_search_attempts_at
            ON search_attempts(attempted_at);

        CREATE TABLE IF NOT EXISTS route_watches (
            id INTEGER PRIMARY KEY,
            origin TEXT NOT NULL,
            dest TEXT NOT NULL,
            dep_date TEXT NOT NULL,
            created_at TEXT NOT NULL,
            active INTEGER NOT NULL DEFAULT 1,
            UNIQUE(origin, dest, dep_date)
        );

        CREATE TABLE IF NOT EXISTS flight_watches (
            id INTEGER PRIMARY KEY,
            flight_key TEXT NOT NULL UNIQUE,
            origin TEXT NOT NULL,
            dest TEXT NOT NULL,
            dep_date TEXT NOT NULL,
            flight_number TEXT,
            airline TEXT,
            airline_code TEXT,
            dep_time TEXT,
            arr_time TEXT,
            dep_airport TEXT,
            arr_airport TEXT,
            stops INTEGER,
            created_at TEXT NOT NULL,
            active INTEGER NOT NULL DEFAULT 1,
            supplier_tag TEXT
        );

        CREATE TABLE IF NOT EXISTS flight_quotes (
            id INTEGER PRIMARY KEY,
            flight_key TEXT NOT NULL,
            sampled_at TEXT NOT NULL,
            slot TEXT NOT NULL,

            -- FIRST_ENTRY or MATCHED_ENTRY
            entry_type TEXT NOT NULL DEFAULT 'MATCHED_ENTRY',

            origin TEXT,
            dest TEXT,
            dep_date TEXT,
            days_to_departure INTEGER,
            found INTEGER NOT NULL,
            price_inr REAL,
            currency TEXT,
            flight_number TEXT,
            airline TEXT,
            airline_code TEXT,
            airline_type TEXT,
            dep_airport TEXT,
            arr_airport TEXT,
            dep_time TEXT,
            arr_time TEXT,
            stops INTEGER,
            duration_minutes INTEGER,
            cabin_class TEXT,
            is_refundable INTEGER,
            baggage_checkin TEXT,
            baggage_cabin TEXT,
            baggage_checkin_kg INTEGER,
            baggage_cabin_kg INTEGER,
            seats_remaining INTEGER,
            searched_at TEXT,
            supplier_tag TEXT,
            supplier_changed INTEGER NOT NULL DEFAULT 0,
            n_offers_on_search INTEGER,
            n_nonstop_on_search INTEGER,
            cheapest_on_route_inr REAL,
            price_vs_cheapest REAL,
            extra_json TEXT
        );

        CREATE TABLE IF NOT EXISTS route_best_quotes (
            id INTEGER PRIMARY KEY,
            origin TEXT NOT NULL,
            dest TEXT NOT NULL,
            dep_date TEXT NOT NULL,
            sampled_at TEXT NOT NULL,
            slot TEXT NOT NULL,
            rank INTEGER NOT NULL,
            days_to_departure INTEGER,
            price_inr REAL,
            flight_key TEXT,
            flight_number TEXT,
            airline TEXT,
            airline_code TEXT,
            airline_type TEXT,
            stops INTEGER,
            dep_time TEXT,
            arr_time TEXT,
            duration_minutes INTEGER,
            seats_remaining INTEGER,
            is_refundable INTEGER,
            searched_at TEXT,
            supplier_tag TEXT,
            supplier_changed INTEGER NOT NULL DEFAULT 0,
            n_offers_on_search INTEGER
        );

        CREATE INDEX IF NOT EXISTS idx_flight_quotes_key_time
            ON flight_quotes(flight_key, sampled_at);

        CREATE INDEX IF NOT EXISTS idx_route_best_od_time
            ON route_best_quotes(
                origin,
                dest,
                dep_date,
                sampled_at
            );
        """
    )

    # -----------------------------------------------------------------------
    # Safe migrations for existing databases.
    # -----------------------------------------------------------------------

    migrations = (
        (
            "flight_quotes",
            "searched_at",
            "TEXT",
        ),
        (
            "flight_quotes",
            "supplier_tag",
            "TEXT",
        ),
        (
            "flight_quotes",
            "supplier_changed",
            "INTEGER NOT NULL DEFAULT 0",
        ),
        (
            "flight_quotes",
            "entry_type",
            "TEXT NOT NULL DEFAULT 'MATCHED_ENTRY'",
        ),
        (
            "route_best_quotes",
            "searched_at",
            "TEXT",
        ),
        (
            "route_best_quotes",
            "supplier_tag",
            "TEXT",
        ),
        (
            "route_best_quotes",
            "supplier_changed",
            "INTEGER NOT NULL DEFAULT 0",
        ),
        (
            "flight_watches",
            "supplier_tag",
            "TEXT",
        ),
    )

    for (
        table,
        column,
        definition,
    ) in migrations:

        existing = {
            row["name"]
            for row in conn.execute(
                f"PRAGMA table_info({table})"
            )
        }

        if column not in existing:

            conn.execute(
                f"""
                ALTER TABLE {table}
                ADD COLUMN {column} {definition}
                """
            )

    conn.commit()

    return conn


def expire_past_watches(
    conn: sqlite3.Connection,
    today: str,
) -> None:

    conn.execute(
        """
        UPDATE route_watches
        SET active=0
        WHERE dep_date < ?
        """,
        (today,),
    )

    conn.execute(
        """
        UPDATE flight_watches
        SET active=0
        WHERE dep_date < ?
        """,
        (today,),
    )

    placeholders = ",".join(
        "?" * len(
            ALLOWED_AIRLINE_CODES
        )
    )

    conn.execute(
        f"""
        UPDATE flight_watches
        SET active=0
        WHERE airline_code NOT IN ({placeholders})
           OR airline_code IS NULL
        """,
        tuple(
            ALLOWED_AIRLINE_CODES
        ),
    )

    conn.commit()


def active_route_dates(
    conn: sqlite3.Connection,
) -> list[tuple[str, str, str]]:

    rows = conn.execute(
        """
        SELECT origin, dest, dep_date
        FROM route_watches
        WHERE active=1
        ORDER BY dep_date, origin, dest
        """
    ).fetchall()

    return [
        (
            r["origin"],
            r["dest"],
            r["dep_date"],
        )
        for r in rows
    ]


def active_route_count(
    conn: sqlite3.Connection,
) -> int:

    return conn.execute(
        """
        SELECT COUNT(*)
        FROM route_watches
        WHERE active=1
        """
    ).fetchone()[0]


def enforce_watch_cap(
    conn: sqlite3.Connection,
) -> None:
    """Guarantee at most MAX_ROUTE_DATE_WATCHES active, distinct watches.

    Distinctness is enforced by UNIQUE(origin, dest, dep_date) in the
    schema. This additionally trims any excess (e.g. caused by two
    overlapping runs) by deactivating the most recently created ones.
    """

    excess = (
        active_route_count(conn)
        - MAX_ROUTE_DATE_WATCHES
    )

    if excess <= 0:
        return

    rows = conn.execute(
        """
        SELECT id, origin, dest, dep_date
        FROM route_watches
        WHERE active=1
        ORDER BY created_at DESC, id DESC
        LIMIT ?
        """,
        (excess,),
    ).fetchall()

    for r in rows:

        conn.execute(
            """
            UPDATE route_watches
            SET active=0
            WHERE id=?
            """,
            (r["id"],),
        )

        conn.execute(
            """
            UPDATE flight_watches
            SET active=0
            WHERE origin=?
              AND dest=?
              AND dep_date=?
            """,
            (
                r["origin"],
                r["dest"],
                r["dep_date"],
            ),
        )

    conn.commit()

    print(
        f"Trimmed {len(rows)} excess route watch(es) "
        f"to keep {MAX_ROUTE_DATE_WATCHES} unique watches."
    )


def watched_keys_for(
    conn: sqlite3.Connection,
    origin: str,
    dest: str,
    dep_date: str,
) -> list[str]:

    rows = conn.execute(
        """
        SELECT flight_key
        FROM flight_watches
        WHERE active=1
          AND origin=?
          AND dest=?
          AND dep_date=?
        """,
        (
            origin,
            dest,
            dep_date,
        ),
    ).fetchall()

    return [
        r["flight_key"]
        for r in rows
    ]


def upsert_route_watch(
    conn: sqlite3.Connection,
    origin: str,
    dest: str,
    dep_date: str,
    ts: str,
) -> None:

    conn.execute(
        """
        INSERT INTO route_watches(
            origin,
            dest,
            dep_date,
            created_at,
            active
        )
        VALUES (?, ?, ?, ?, 1)

        ON CONFLICT(origin, dest, dep_date)
        DO UPDATE SET active=1
        """,
        (
            origin,
            dest,
            dep_date,
            ts,
        ),
    )


def upsert_flight_watch(
    conn: sqlite3.Connection,
    offer: dict[str, Any],
    ts: str,
) -> None:

    # IMPORTANT:
    # Do NOT change the original supplier baseline here.
    #
    # The UNIQUE constraint on flight_key means that this exact
    # combination:
    #
    # flight_number + dep_date + dep_airport + arr_airport
    # + stops + duration
    #
    # represents one watched flight identity.

    conn.execute(
        """
        INSERT INTO flight_watches(
            flight_key,
            origin,
            dest,
            dep_date,
            flight_number,
            airline,
            airline_code,
            dep_time,
            arr_time,
            dep_airport,
            arr_airport,
            stops,
            created_at,
            active,
            supplier_tag
        )
        VALUES (
            ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 1, ?
        )

        ON CONFLICT(flight_key)
        DO UPDATE SET active=1
        """,
        (
            offer["flight_key"],
            offer["origin"],
            offer["dest"],
            offer["dep_date"],
            offer["flight_number"],
            offer["airline"],
            offer["airline_code"],
            offer["dep_time"],
            offer["arr_time"],
            offer["dep_airport"],
            offer["arr_airport"],
            offer["stops"],
            ts,
            offer.get("supplier_tag"),
        ),
    )


# ---------------------------------------------------------------------------
# API
# ---------------------------------------------------------------------------

def search_flights(
    origin: str,
    dest: str,
    dep_date: str,
) -> list[dict[str, Any]]:

    params = {
        "from": origin,
        "to": dest,
        "date": dep_date,
        "adults": ADULTS,
        "class": CABIN,
        "limit": 100,
    }

    try:

        resp = requests.get(
            API_URL,
            params=params,
            timeout=HTTP_TIMEOUT,
            headers={
                "Accept": "application/json",
                "User-Agent": (
                    "FlightPrediction/0.1 (research)"
                ),
            },
        )

    except requests.Timeout:

        raise SearchError("timeout")

    except requests.ConnectionError as exc:

        raise SearchError(
            "connection",
            detail=str(exc),
        )

    if resp.status_code == 429:

        raise SearchError(
            "rate_limited",
            429,
            retry_after=int(
                resp.headers.get(
                    "Retry-After"
                )
                or 60
            ),
            detail=resp.text,
        )

    if resp.status_code >= 500:

        raise SearchError(
            "http_5xx",
            resp.status_code,
            detail=resp.text,
        )

    if resp.status_code >= 400:

        # The response body is kept: it is the only way to tell
        # "no flights for this query" from a real endpoint problem.
        raise SearchError(
            f"http_{resp.status_code}",
            resp.status_code,
            detail=resp.text,
        )

    try:

        payload = resp.json()

    except ValueError:

        raise SearchError(
            "bad_json",
            resp.status_code,
            detail=resp.text,
        )

    data = payload.get("data") or {}

    print(
        "RAW DATA KEYS:",
        data.keys(),
    )

    print(
        "RAW TOTAL RESULTS:",
        data.get("total_results"),
    )

    print(
        "RAW SEARCH PAGE:",
        data.get("search_page"),
    )

    print(
        "RAW FLIGHTS COUNT:",
        len(
            data.get("flights") or []
        ),
    )

    if not payload.get("success"):

        raise SearchError(
            "api_failure",
            detail=str(payload),
        )

    flights = (
        payload.get("data") or {}
    ).get("flights") or []

    print(
        f"\n  RAW API OFFERS: "
        f"{len(flights)}"
    )

    offers = []

    rejected_airline = 0
    rejected_stops = 0
    rejected_cabin = 0
    rejected_price = 0

    for raw in flights:

        price = parse_price(raw)

        if price is None:

            rejected_price += 1

            continue

        stops = int(
            raw.get("stops") or 0
        )

        if stops > MAX_STOPS:

            rejected_stops += 1

            continue

        cabin = str(
            raw.get("cabin_class")
            or CABIN
        )

        if cabin.lower() not in {
            "economy",
            "econ",
        }:

            rejected_cabin += 1

            continue

        code = str(
            raw.get("airline_code")
            or ""
        ).upper()[:3]

        if not code:

            number = str(
                raw.get("flight_number")
                or ""
            ).upper()

            for prefix in ALLOWED_AIRLINE_CODES:

                if number.startswith(prefix):

                    code = prefix

                    break

        if code not in ALLOWED_AIRLINE_CODES:

            rejected_airline += 1

            continue

        norm = normalize_offer(
            raw,
            origin,
            dest,
        )

        if norm:
            offers.append(norm)

    print(
        f"  ACCEPTED: {len(offers)}"
    )

    print(
        f"  rejected - airline: "
        f"{rejected_airline}"
    )

    print(
        f"  rejected - stops:   "
        f"{rejected_stops}"
    )

    print(
        f"  rejected - cabin:   "
        f"{rejected_cabin}"
    )

    print(
        f"  rejected - price:   "
        f"{rejected_price}"
    )

    offers.sort(
        key=lambda x: x["price_inr"]
    )

    return offers


# ---------------------------------------------------------------------------
# Recording searches
# ---------------------------------------------------------------------------

def record_search(
    conn: sqlite3.Connection,
    origin: str,
    dest: str,
    dep_date: str,
    offers: list[dict[str, Any]],
    sampled_at: datetime,
    slot: str,
    also_watch_random: bool,
) -> None:

    ts = sampled_at.isoformat(
        timespec="seconds"
    )

    dtd = days_to_dep(
        dep_date,
        sampled_at,
    )

    n_offers = len(offers)

    n_nonstop = sum(
        1
        for o in offers
        if o["stops"] == 0
    )

    cheapest = (
        offers[0]["price_inr"]
        if offers
        else None
    )

    # -----------------------------------------------------------------------
    # VERY IMPORTANT:
    #
    # Capture existing flight keys BEFORE adding random first-entry watches.
    #
    # This allows us to correctly distinguish:
    #
    #     FIRST_ENTRY
    #
    # from:
    #
    #     MATCHED_ENTRY
    #
    # -----------------------------------------------------------------------

    existing_watched_keys = set(
        watched_keys_for(
            conn,
            origin,
            dest,
            dep_date,
        )
    )

    upsert_route_watch(
        conn,
        origin,
        dest,
        dep_date,
        ts,
    )

    # -----------------------------------------------------------------------
    # Select random flight watches for a NEW route/date.
    #
    # One API search gives us all offers, so no extra API call is made.
    # -----------------------------------------------------------------------

    if also_watch_random and offers:

        picks = random.sample(
            offers,
            k=min(
                RANDOM_FLIGHTS_PER_NEW_ROUTE,
                len(offers),
            ),
        )

        for offer in picks:

            upsert_flight_watch(
                conn,
                offer,
                ts,
            )

    # -----------------------------------------------------------------------
    # Record every previously watched flight.
    # -----------------------------------------------------------------------

    current_watched_keys = watched_keys_for(
        conn,
        origin,
        dest,
        dep_date,
    )

    by_key = {
        o["flight_key"]: o
        for o in offers
    }

    for key in current_watched_keys:

        offer = by_key.get(key)

        found = offer is not None

        if offer:

            row = offer

        else:

            row = {
                "flight_key": key,
                "origin": origin,
                "dest": dest,
                "dep_date": dep_date,
                "price_inr": None,
                "currency": "INR",
                "flight_number": None,
                "airline": None,
                "airline_code": None,
                "airline_type": None,
                "dep_airport": None,
                "arr_airport": None,
                "dep_time": None,
                "arr_time": None,
                "stops": None,
                "duration_minutes": None,
                "cabin_class": CABIN,
                "is_refundable": None,
                "baggage_checkin": None,
                "baggage_cabin": None,
                "baggage_checkin_kg": None,
                "baggage_cabin_kg": None,
                "seats_remaining": None,
                "searched_at": None,
                "supplier_tag": None,
                "extra_json": "",
            }

        # -------------------------------------------------------------------
        # FIRST_ENTRY vs MATCHED_ENTRY
        #
        # If this exact flight_key existed before this search:
        #
        #     MATCHED_ENTRY
        #
        # Otherwise:
        #
        #     FIRST_ENTRY
        #
        # This also works if a watched flight is missing from a later API
        # response: it remains MATCHED_ENTRY because the identity was already
        # known, but found=0.
        # -------------------------------------------------------------------

        entry_type = (
            "MATCHED_ENTRY"
            if key in existing_watched_keys
            else "FIRST_ENTRY"
        )

        ratio = None

        if found and cheapest:

            ratio = round(
                row["price_inr"]
                / cheapest,
                4,
            )

        baseline = conn.execute(
            """
            SELECT supplier_tag
            FROM flight_watches
            WHERE flight_key=?
            """,
            (key,),
        ).fetchone()

        baseline_supplier = (
            baseline["supplier_tag"]
            if baseline
            else None
        )

        supplier_changed = int(
            bool(row.get("supplier_tag"))
            and bool(baseline_supplier)
            and row.get("supplier_tag")
            != baseline_supplier
        )

        # Seed supplier baseline if this watch predates
        # supplier tracking.
        if (
            baseline_supplier is None
            and row.get("supplier_tag")
        ):

            conn.execute(
                """
                UPDATE flight_watches
                SET supplier_tag=?
                WHERE flight_key=?
                  AND supplier_tag IS NULL
                """,
                (
                    row["supplier_tag"],
                    key,
                ),
            )

        conn.execute(
            """
            INSERT INTO flight_quotes(
                flight_key,
                sampled_at,
                slot,
                entry_type,
                origin,
                dest,
                dep_date,
                days_to_departure,
                found,
                price_inr,
                currency,
                flight_number,
                airline,
                airline_code,
                airline_type,
                dep_airport,
                arr_airport,
                dep_time,
                arr_time,
                stops,
                duration_minutes,
                cabin_class,
                is_refundable,
                baggage_checkin,
                baggage_cabin,
                baggage_checkin_kg,
                baggage_cabin_kg,
                seats_remaining,
                searched_at,
                supplier_tag,
                supplier_changed,
                n_offers_on_search,
                n_nonstop_on_search,
                cheapest_on_route_inr,
                price_vs_cheapest,
                extra_json
            )
            VALUES (
                ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                ?, ?, ?, ?, ?, ?
            )
            """,
            (
                key,
                ts,
                slot,
                entry_type,
                origin,
                dest,
                dep_date,
                dtd,
                int(found),
                row["price_inr"],
                row.get("currency"),
                row.get("flight_number"),
                row.get("airline"),
                row.get("airline_code"),
                row.get("airline_type"),
                row.get("dep_airport"),
                row.get("arr_airport"),
                row.get("dep_time"),
                row.get("arr_time"),
                row.get("stops"),
                row.get("duration_minutes"),
                row.get("cabin_class"),
                row.get("is_refundable"),
                row.get("baggage_checkin"),
                row.get("baggage_cabin"),
                row.get("baggage_checkin_kg"),
                row.get("baggage_cabin_kg"),
                row.get("seats_remaining"),
                row.get("searched_at"),
                row.get("supplier_tag"),
                supplier_changed,
                n_offers,
                n_nonstop,
                cheapest,
                ratio,
                row.get("extra_json") or "",
            ),
        )

    # -----------------------------------------------------------------------
    # Store route-level best 2.
    # -----------------------------------------------------------------------

    for rank, offer in enumerate(
        offers[:2],
        start=1,
    ):

        conn.execute(
            """
            INSERT INTO route_best_quotes(
                origin,
                dest,
                dep_date,
                sampled_at,
                slot,
                rank,
                days_to_departure,
                price_inr,
                flight_key,
                flight_number,
                airline,
                airline_code,
                airline_type,
                stops,
                dep_time,
                arr_time,
                duration_minutes,
                seats_remaining,
                is_refundable,
                searched_at,
                supplier_tag,
                supplier_changed,
                n_offers_on_search
            )
            VALUES (
                ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                ?, ?
            )
            """,
            (
                origin,
                dest,
                dep_date,
                ts,
                slot,
                rank,
                dtd,
                offer["price_inr"],
                offer["flight_key"],
                offer["flight_number"],
                offer["airline"],
                offer["airline_code"],
                offer["airline_type"],
                offer["stops"],
                offer["dep_time"],
                offer["arr_time"],
                offer["duration_minutes"],
                offer["seats_remaining"],
                offer["is_refundable"],
                offer.get("searched_at"),
                offer.get("supplier_tag"),
                0,
                n_offers,
            ),
        )

    conn.commit()


# ---------------------------------------------------------------------------
# Selecting new route/date watches
# ---------------------------------------------------------------------------

def pick_new_route_dates(
    conn: sqlite3.Connection,
    k: int,
    today: date,
) -> list[tuple[str, str, str]]:
    """Pick k brand-new, distinct (origin, dest, dep_date) triples.

    Builds the full candidate pool, removes every currently active
    watch, then samples WITHOUT replacement. This guarantees:
      - no duplicates inside the returned list,
      - no overlap with existing active watches,
      - no silent shortfall from a capped retry loop.
    """

    if k <= 0:
        return []

    existing = set(
        active_route_dates(conn)
    )

    dates = [
        (
            today
            + timedelta(days=ahead)
        ).isoformat()
        for ahead in range(
            DAYS_AHEAD_MIN,
            DAYS_AHEAD_MAX + 1,
        )
    ]

    pool = [
        (origin, dest, dep)
        for origin, dest in directed_routes()
        for dep in dates
        if (origin, dest, dep) not in existing
    ]

    return random.sample(
        pool,
        k=min(k, len(pool)),
    )


# ---------------------------------------------------------------------------
# Main one-shot collector
# ---------------------------------------------------------------------------

def log_attempt(
    conn: sqlite3.Connection,
    origin: str,
    dest: str,
    dep_date: str,
    slot: str | None,
    attempt: int,
    status: str,
    http_code: int | None,
    n_offers: int | None,
    detail: str,
) -> None:
    """Record one API attempt (success or failure)."""

    conn.execute(
        """
        INSERT INTO search_attempts(
            origin, dest, dep_date, slot, attempted_at,
            attempt, status, http_code, n_offers, detail
        )
        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        """,
        (
            origin,
            dest,
            dep_date,
            slot,
            now_ist().isoformat(timespec="seconds"),
            attempt,
            status,
            http_code,
            n_offers,
            (detail or "")[:500],
        ),
    )

    conn.commit()


def calls_last_hour(
    conn: sqlite3.Connection,
) -> int:
    """API calls made in the last 60 minutes, any run, success or not."""

    cutoff = (
        now_ist() - timedelta(hours=1)
    ).isoformat(timespec="seconds")

    return conn.execute(
        """
        SELECT COUNT(*)
        FROM search_attempts
        WHERE attempted_at >= ?
          AND status != 'budget_exhausted'
        """,
        (cutoff,),
    ).fetchone()[0]


def search_with_retry(
    conn: sqlite3.Connection,
    origin: str,
    dest: str,
    dep_date: str,
    slot: str,
) -> list[dict[str, Any]]:
    """search_flights with typed errors, backoff and an hourly budget guard.

    Raises SearchError if the search still fails. Nothing is written to
    flight_quotes by this function.
    """

    attempt = 0

    while True:

        attempt += 1

        if (
            calls_last_hour(conn)
            >= API_LIMIT_PER_HOUR - API_BUDGET_GUARD
        ):

            log_attempt(
                conn, origin, dest, dep_date, slot,
                attempt, "budget_exhausted", None, None,
                f"{API_LIMIT_PER_HOUR}/hour budget nearly used",
            )

            raise SearchError("budget_exhausted")

        try:

            offers = search_flights(
                origin,
                dest,
                dep_date,
            )

            log_attempt(
                conn, origin, dest, dep_date, slot,
                attempt, "ok", 200, len(offers), "",
            )

            return offers

        except SearchError as exc:

            log_attempt(
                conn, origin, dest, dep_date, slot,
                attempt, exc.kind, exc.code, None, exc.detail,
            )

            max_attempts = SEARCH_ATTEMPTS_BY_KIND.get(
                exc.kind,
                SEARCH_MAX_ATTEMPTS,
            )

            if (
                exc.kind not in RETRYABLE_KINDS
                or attempt >= max_attempts
            ):
                raise

            wait = min(
                exc.retry_after
                or RETRY_BACKOFF_SEC * attempt,
                RETRY_MAX_WAIT_SEC,
            )

            print(
                f"{exc.kind}, retry {attempt}/"
                f"{max_attempts - 1} in {wait}s ...",
                end=" ",
                flush=True,
            )

            time.sleep(wait)


def run_once(
    max_searches: int,
    forced_slot: str | None = None,
) -> int:
    """Run one sampling pass. Returns the number of failed searches."""

    sampled_at = now_ist()

    today = sampled_at.date()

    # IMPORTANT:
    # forced_slot allows a missed sample to be manually backfilled.
    #
    # Example:
    #   current time = 23:00
    #   forced_slot = 0900
    #
    # Database:
    #   sampled_at = 23:00
    #   slot = 0900
    slot = slot_name(
        sampled_at,
        forced_slot,
    )

    cap = max(
        0,
        min(
            max_searches,
            SEARCHES_PER_HOUR,
            API_LIMIT_PER_HOUR
            - API_SAFETY_MARGIN,
        ),
    )

    conn = connect()

    expire_past_watches(
        conn,
        today.isoformat(),
    )

    enforce_watch_cap(conn)

    active_at_start = set(
        active_route_dates(conn)
    )

    n_active = len(active_at_start)

    # ---------------------------------------------------------------
    # First priority:
    # Route/date watches that have not yet been sampled for
    # today's requested logical slot.
    # ---------------------------------------------------------------

    jobs = due_route_dates(
        conn,
        today.isoformat(),
        slot,
        cap,
    )

    # ---------------------------------------------------------------
    # Then fill remaining API capacity with new route/date watches
    # until MAX_ROUTE_DATE_WATCHES is reached.
    # ---------------------------------------------------------------

    remaining = (
        cap - len(jobs)
    )

    need_new = max(
        0,
        MAX_ROUTE_DATE_WATCHES
        - n_active,
    )

    if (
        remaining > 0
        and need_new > 0
    ):

        jobs.extend(
            pick_new_route_dates(
                conn,
                min(
                    remaining,
                    need_new,
                    NEW_ROUTE_DATES_PER_HOUR,
                ),
                today,
            )
        )

    jobs = list(
        dict.fromkeys(jobs)
    )

    if not jobs:

        print(
            f"{sampled_at.isoformat(timespec='seconds')} "
            f"slot={slot} "
            f"nothing due "
            f"(watches={n_active}, "
            f"cap={cap}/hour)"
        )

        conn.close()

        return 0

    print(
        f"{sampled_at.isoformat(timespec='seconds')} "
        f"slot={slot} "
        f"jobs={len(jobs)} "
        f"watches={n_active}/{MAX_ROUTE_DATE_WATCHES} "
        f"cap={cap}/hour "
        f"spread={SPREAD_HOURS}h"
    )

    if forced_slot:

        print(
            f"  MANUAL SLOT OVERRIDE: "
            f"{slot} "
            f"(actual run time "
            f"{sampled_at.strftime('%H:%M')} IST)"
        )

    ok = 0

    failed: list[tuple[str, str, str, str]] = []

    for i, (
        origin,
        dest,
        dep_date,
    ) in enumerate(
        jobs,
        start=1,
    ):

        if (
            (origin, dest, dep_date)
            not in active_at_start
            and active_route_count(conn)
            >= MAX_ROUTE_DATE_WATCHES
        ):

            print(
                f"  [{i}/{len(jobs)}] "
                f"{origin}->{dest} {dep_date} "
                f"skipped (watch cap "
                f"{MAX_ROUTE_DATE_WATCHES} reached)"
            )

            continue

        seed_flights = not watched_keys_for(
            conn,
            origin,
            dest,
            dep_date,
        )

        print(
            f"  [{i}/{len(jobs)}] "
            f"{origin}->{dest} "
            f"{dep_date} ...",
            end=" ",
            flush=True,
        )

        try:

            offers = search_with_retry(
                conn,
                origin,
                dest,
                dep_date,
                slot,
            )

            record_search(
                conn,
                origin,
                dest,
                dep_date,
                offers,
                sampled_at,
                slot,
                also_watch_random=seed_flights,
            )

            cheapest = (
                f"₹{offers[0]['price_inr']:.0f}"
                if offers
                else "none"
            )

            print(
                f"{len(offers)} offers, "
                f"cheapest {cheapest}"
            )

            ok += 1

        except Exception as exc:

            reason = (
                exc.kind
                if isinstance(exc, SearchError)
                else type(exc).__name__
            )

            print(
                f"FAILED: {exc}"
            )

            failed.append(
                (origin, dest, dep_date, reason)
            )

            if (
                isinstance(exc, SearchError)
                and exc.kind == "budget_exhausted"
            ):

                # Nothing more can be searched this hour.
                for o, d, dt in jobs[i:]:

                    failed.append(
                        (o, d, dt, "budget_exhausted")
                    )

                print(
                    f"  hourly API budget used up; "
                    f"{len(jobs) - i} searches not attempted"
                )

                break

        if i < len(jobs):

            time.sleep(
                REQUEST_PAUSE_SEC
            )

    print(
        f"Done. {ok}/{len(jobs)} "
        f"searches saved to {DB_PATH}"
    )

    if failed:

        print(
            f"Failed ({len(failed)}): "
            + ", ".join(
                f"{o}->{d} {dt} ({why})"
                for o, d, dt, why in failed
            )
        )

    export_preview(
        conn,
        sampled_at,
    )

    conn.close()

    return len(failed)


# ---------------------------------------------------------------------------
# Daemon scheduling
# ---------------------------------------------------------------------------

def next_window_hour_wait() -> float:

    now = now_ist()

    windows = sample_window_hours()

    t = (
        now.replace(
            minute=0,
            second=0,
            microsecond=0,
        )
        + timedelta(hours=1)
    )

    for _ in range(48):

        if t.hour in windows:

            return max(
                0.0,
                (
                    t - now
                ).total_seconds(),
            )

        t += timedelta(hours=1)

    return 3600.0


def run_daemon(
    max_searches: int,
) -> None:

    windows = sorted(
        sample_window_hours()
    )

    print(
        f"Daemon: "
        f"{SEARCHES_PER_HOUR} searches/hour "
        f"in IST hours {windows} "
        f"(~{MAX_ROUTE_DATE_WATCHES} "
        f"route-dates per slot, "
        f"{RANDOM_FLIGHTS_PER_NEW_ROUTE} "
        f"random flights each; "
        f"API cap {API_LIMIT_PER_HOUR}/hour)"
    )

    while True:

        if (
            now_ist().hour
            in sample_window_hours()
        ):

            for pass_no in range(
                1,
                DAEMON_MAX_PASSES + 1,
            ):

                failed = run_once(
                    max_searches,
                    forced_slot=None,
                )

                if (
                    not failed
                    or pass_no == DAEMON_MAX_PASSES
                ):
                    break

                # Only route/dates still without a row for this slot
                # are searched again on the next pass.
                print(
                    f"{failed} searches failed; "
                    f"pass {pass_no + 1}/{DAEMON_MAX_PASSES} "
                    f"in {DAEMON_PASS_WAIT_SEC}s"
                )

                time.sleep(DAEMON_PASS_WAIT_SEC)

                if (
                    now_ist().hour
                    not in sample_window_hours()
                ):
                    break

        wait = next_window_hour_wait()

        nxt = (
            now_ist()
            + timedelta(
                seconds=wait
            )
        )

        print(
            f"Sleeping until "
            f"{nxt.isoformat(timespec='seconds')}",
            flush=True,
        )

        time.sleep(wait)


# ---------------------------------------------------------------------------
# Export
# ---------------------------------------------------------------------------

def export_preview(
    conn: sqlite3.Connection | None = None,
    sampled_at: datetime | None = None,
) -> Path:

    close = False

    if conn is None:

        conn = connect()

        close = True

    EXPORT_DIR.mkdir(
        parents=True,
        exist_ok=True,
    )

    stamp = (
        sampled_at or now_ist()
    ).strftime(
        "%Y%m%d_%H%M"
    )

    flight_csv = (
        EXPORT_DIR
        / f"flight_quotes_{stamp}.csv"
    )

    route_csv = (
        EXPORT_DIR
        / f"route_best_{stamp}.csv"
    )

    latest_flight = (
        EXPORT_DIR
        / "flight_quotes_latest.csv"
    )

    latest_route = (
        EXPORT_DIR
        / "route_best_latest.csv"
    )

    flight_cols = [
        r[1]
        for r in conn.execute(
            "PRAGMA table_info(flight_quotes)"
        )
    ]

    route_cols = [
        r[1]
        for r in conn.execute(
            "PRAGMA table_info(route_best_quotes)"
        )
    ]

    def dump(
        sql: str,
        path: Path,
        latest: Path,
        cols: list[str],
    ) -> int:

        rows = conn.execute(
            sql
        ).fetchall()

        for dest in (
            path,
            latest,
        ):

            with dest.open(
                "w",
                newline="",
                encoding="utf-8",
            ) as fh:

                writer = csv.writer(fh)

                writer.writerow(cols)

                for row in rows:

                    writer.writerow(
                        [
                            row[c]
                            for c in cols
                        ]
                    )

        return len(rows)

    n1 = dump(
        """
        SELECT *
        FROM flight_quotes
        ORDER BY sampled_at DESC,
                 origin,
                 dest
        LIMIT 200
        """,
        flight_csv,
        latest_flight,
        flight_cols,
    )

    n2 = dump(
        """
        SELECT *
        FROM route_best_quotes
        ORDER BY sampled_at DESC,
                 origin,
                 dest,
                 rank
        LIMIT 200
        """,
        route_csv,
        latest_route,
        route_cols,
    )

    print(
        f"CSV preview: "
        f"{latest_flight} ({n1} rows), "
        f"{latest_route} ({n2} rows)"
    )

    _print_tables(conn)

    if close:
        conn.close()

    return latest_flight


# ---------------------------------------------------------------------------
# Display
# ---------------------------------------------------------------------------

def _print_tables(
    conn: sqlite3.Connection,
) -> None:

    print(
        "\n=== Flight-level quotes "
        "(latest 8) ==="
    )

    rows = conn.execute(
        """
        SELECT
            origin,
            dest,
            dep_date,
            flight_number,
            dep_airport,
            arr_airport,
            dep_time,
            arr_time,
            stops,
            duration_minutes,
            airline_code,
            airline_type,
            price_inr,
            seats_remaining,
            days_to_departure,
            found,
            sampled_at,
            slot,
            entry_type,
            searched_at,
            supplier_tag,
            supplier_changed
        FROM flight_quotes
        ORDER BY id DESC
        LIMIT 8
        """
    ).fetchall()

    if not rows:
        print("(empty)")

    for r in rows:

        price = (
            f"₹{r['price_inr']:.0f}"
            if r["price_inr"] is not None
            else "MISSING"
        )

        print(
            f"  {r['origin']}->{r['dest']} "
            f"{r['dep_date']} "
            f"{r['flight_number']} "
            f"{r['dep_airport']}->"
            f"{r['arr_airport']} "
            f"{r['dep_time']}-{r['arr_time']} "
            f"stops={r['stops']} "
            f"duration={r['duration_minutes']} "
            f"{r['airline_code']}/"
            f"{r['airline_type']} "
            f"{price} "
            f"seats={r['seats_remaining']} "
            f"dtd={r['days_to_departure']} "
            f"found={r['found']} "
            f"slot={r['slot']} "
            f"entry={r['entry_type']} "
            f"supplier="
            f"{r['supplier_tag'] or 'unknown'}"
            f"{' [CHANGED]' if r['supplier_changed'] else ''}"
        )

    print(
        "\n=== Route best-2 "
        "(latest 8) ==="
    )

    rows = conn.execute(
        """
        SELECT
            origin,
            dest,
            dep_date,
            rank,
            price_inr,
            flight_number,
            airline,
            stops,
            dep_time,
            sampled_at,
            slot
        FROM route_best_quotes
        ORDER BY id DESC
        LIMIT 8
        """
    ).fetchall()

    if not rows:
        print("(empty)")

    for r in rows:

        print(
            f"  {r['origin']}->{r['dest']} "
            f"{r['dep_date']} "
            f"#{r['rank']} "
            f"₹{r['price_inr']:.0f} "
            f"{r['flight_number']} "
            f"{r['airline']} "
            f"stops={r['stops']} "
            f"dep={r['dep_time']} "
            f"slot={r['slot']}"
        )


# ---------------------------------------------------------------------------
# Status
# ---------------------------------------------------------------------------

def print_status() -> None:

    conn = connect()

    n_rw = conn.execute(
        """
        SELECT COUNT(*)
        FROM route_watches
        WHERE active=1
        """
    ).fetchone()[0]

    n_fw = conn.execute(
        """
        SELECT COUNT(*)
        FROM flight_watches
        WHERE active=1
        """
    ).fetchone()[0]

    n_fq = conn.execute(
        """
        SELECT COUNT(*)
        FROM flight_quotes
        """
    ).fetchone()[0]

    n_rq = conn.execute(
        """
        SELECT COUNT(*)
        FROM route_best_quotes
        """
    ).fetchone()[0]

    n_first = conn.execute(
        """
        SELECT COUNT(*)
        FROM flight_quotes
        WHERE entry_type='FIRST_ENTRY'
        """
    ).fetchone()[0]

    n_matched = conn.execute(
        """
        SELECT COUNT(*)
        FROM flight_quotes
        WHERE entry_type='MATCHED_ENTRY'
        """
    ).fetchone()[0]

    print(
        f"DB: {DB_PATH}"
    )

    print(
        f"active route-dates: {n_rw}"
    )

    print(
        f"active flight watches: {n_fw}"
    )

    print(
        f"flight quote rows: {n_fq}"
    )

    print(
        f"route best-2 rows: {n_rq}"
    )

    print(
        f"FIRST_ENTRY rows: {n_first}"
    )

    print(
        f"MATCHED_ENTRY rows: {n_matched}"
    )

    _print_tables(conn)

    conn.close()


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> int:

    parser = argparse.ArgumentParser(
        description=(
            "Track India domestic "
            "economy fares"
        )
    )

    parser.add_argument(
        "command",
        choices=[
            "once",
            "daemon",
            "export",
            "status",
        ],
    )

    parser.add_argument(
        "--max-searches",
        type=int,
        default=SEARCHES_PER_HOUR,
        help=(
            "API searches this run "
            f"(default {SEARCHES_PER_HOUR}, "
            "still capped)"
        ),
    )

    parser.add_argument(
        "--slot",
        type=str,
        default=None,
        help=(
            "Logical sampling slot for "
            "manual backfill: 0900 or 2100. "
            "Only applies to 'once'."
        ),
    )

    args = parser.parse_args()

    # ---------------------------------------------------------------
    # Validate slot before doing anything.
    # ---------------------------------------------------------------

    forced_slot = None

    if args.slot is not None:

        try:

            forced_slot = validate_slot(
                args.slot
            )

        except ValueError as exc:

            parser.error(
                str(exc)
            )

    # ---------------------------------------------------------------
    # Execute command.
    # ---------------------------------------------------------------

    failed_searches = 0

    if args.command == "once":

        failed_searches = run_once(
            args.max_searches,
            forced_slot=forced_slot,
        )

    elif args.command == "daemon":

        if forced_slot is not None:

            parser.error(
                "--slot is only valid "
                "with the 'once' command"
            )

        run_daemon(
            args.max_searches
        )

    elif args.command == "export":

        if forced_slot is not None:

            parser.error(
                "--slot is only valid "
                "with the 'once' command"
            )

        export_preview()

    else:

        if forced_slot is not None:

            parser.error(
                "--slot is only valid "
                "with the 'once' command"
            )

        print_status()

    # Non-zero exit when searches were still failing after retries,
    # so cron / systemd / a wrapper script can notice.
    return 1 if failed_searches else 0


if __name__ == "__main__":
    sys.exit(main())
