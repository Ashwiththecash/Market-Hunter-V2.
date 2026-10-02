#!/usr/bin/env python3
"""
Market Hunter V2

Read-only, paper-only prediction-market arbitrage scanner.

Safety:
- Public market data only.
- No wallets, private keys, API credentials, or live order placement.
- Paper ledger only.
- A result is CERTIFIED only when executable order-book liquidity,
  matching event/settlement evidence, and fee treatment all pass.
"""

from __future__ import annotations

import hashlib
import json
import logging
import math
import os
import re
import sqlite3
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from datetime import datetime, timezone
from decimal import Decimal, ROUND_UP, InvalidOperation
from difflib import SequenceMatcher
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any


API_PREFIX = "/api"
DB_PATH = os.environ.get(
    "MARKET_HUNTER_DB",
    os.path.join(os.path.dirname(__file__), "market_hunter.sqlite3"),
)

POLY_GAMMA = "https://gamma-api.polymarket.com/markets"
POLY_CLOB = "https://clob.polymarket.com"
KALSHI_API = "https://external-api.kalshi.com/trade-api/v2"

HTTP_TIMEOUT = 15
POLY_PAGE_SIZE = 100
POLY_MAX_PAGES = 20
KALSHI_PAGE_SIZE = 100
KALSHI_MAX_PAGES = 20

SCAN_SECONDS = int(os.environ.get("SCAN_SECONDS", "60"))
BOOK_MAX_LEVELS = 50
TARGET_CONTRACTS = Decimal(os.environ.get("TARGET_CONTRACTS", "100"))
MIN_NET_EDGE = Decimal(os.environ.get("MIN_NET_EDGE", "0.0025"))
MAX_STALE_SECONDS = int(os.environ.get("MAX_STALE_SECONDS", "20"))
MATCH_THRESHOLD = Decimal("0.78")
MAX_KALSHI_CANDIDATES_PER_SCAN = 100
MAX_POLY_CANDIDATES_PER_SCAN = 100

STARTING_BALANCE = Decimal("1000")
LOGGER = logging.getLogger("market_hunter")
KALSHI_SERIES_CACHE: dict[str, tuple[float, dict[str, Any]]] = {}
KALSHI_SERIES_CACHE_LOCK = threading.RLock()
KALSHI_SERIES_CACHE_SECONDS = 900


class ApiError(Exception):
    def __init__(self, url: str, message: str, status: int | None = None):
        self.url = url
        self.status = status
        self.message = message
        super().__init__(f"{url}: {message}")


def now_utc() -> datetime:
    return datetime.now(timezone.utc)


def now_iso() -> str:
    return now_utc().isoformat()


def dec(value: Any) -> Decimal | None:
    if value is None or value == "":
        return None
    try:
        x = Decimal(str(value))
        if not x.is_finite():
            return None
        return x
    except (InvalidOperation, ValueError, TypeError):
        return None


def money(value: Decimal) -> Decimal:
    return value.quantize(Decimal("0.00001"), rounding=ROUND_UP)


def dstr(value: Decimal | None) -> str | None:
    return None if value is None else format(value, "f")


def json_dump(value: Any) -> str:
    return json.dumps(value, separators=(",", ":"), sort_keys=True, default=str)


def parse_jsonish(value: Any) -> Any:
    if isinstance(value, (list, dict)):
        return value
    if isinstance(value, str):
        try:
            return json.loads(value)
        except json.JSONDecodeError:
            return None
    return None


def parse_datetime(value: Any) -> datetime | None:
    if not value:
        return None
    text = str(value).strip()
    if not text:
        return None
    if text.endswith("Z"):
        text = text[:-1] + "+00:00"
    try:
        dt = datetime.fromisoformat(text)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except ValueError:
        return None


def fetch_json(url: str) -> Any:
    req = urllib.request.Request(
        url,
        headers={
            "Accept": "application/json",
            "User-Agent": "MarketHunterV2/1.0 public-readonly",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as response:
            raw = response.read()
            try:
                return json.loads(raw.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as exc:
                raise ApiError(url, f"invalid JSON: {exc}", response.status) from exc
    except urllib.error.HTTPError as exc:
        body = exc.read(500).decode("utf-8", errors="replace")
        raise ApiError(url, f"HTTP {exc.code}: {body}", exc.code) from exc
    except urllib.error.URLError as exc:
        raise ApiError(url, f"network error: {exc}", None) from exc


def clamp_price(value: Decimal | None) -> Decimal | None:
    if value is None or value < 0 or value > 1:
        return None
    return value


def text_tokens(text: str) -> set[str]:
    words = re.findall(r"[a-z0-9]+", text.lower())
    stop = {
        "will", "be", "the", "a", "an", "in", "on", "of", "to", "for",
        "by", "at", "this", "that", "before", "after", "from", "and",
        "or", "who", "what", "which", "is", "are", "as", "than", "more",
    }
    return {w for w in words if len(w) > 2 and w not in stop}


def normalize_title(text: str) -> str:
    text = re.sub(r"\s+", " ", text.lower()).strip()
    text = re.sub(r"[^\w\s$%.:/-]", " ", text)
    return text


def title_match(a: dict[str, Any], b: dict[str, Any]) -> dict[str, Any] | None:
    at = normalize_title(str(a.get("title", "")))
    bt = normalize_title(str(b.get("title", "")))
    if not at or not bt:
        return None

    ta = text_tokens(at)
    tb = text_tokens(bt)
    shared = ta & tb
    if len(shared) < 4:
        return None

    seq = SequenceMatcher(None, at, bt).ratio()
    overlap = len(shared) / max(1, min(len(ta), len(tb)))
    score = (Decimal(str(seq)) * Decimal("0.55")) + (
        Decimal(str(overlap)) * Decimal("0.45")
    )

    # Strongly reward matching explicit years/numbers.
    nums_a = set(re.findall(r"\b(?:19|20)\d{2}\b", at))
    nums_b = set(re.findall(r"\b(?:19|20)\d{2}\b", bt))
    if nums_a and nums_b and nums_a != nums_b:
        return None
    if nums_a & nums_b:
        score += Decimal("0.05")

    score = min(Decimal("1"), score)
    if score < MATCH_THRESHOLD:
        return None

    return {
        "score": float(score),
        "sharedTokens": sorted(shared)[:20],
        "sequence": round(seq, 4),
        "tokenOverlap": round(overlap, 4),
    }


def dates_compatible(a: dict[str, Any], b: dict[str, Any]) -> bool:
    da = parse_datetime(a.get("endDate"))
    db = parse_datetime(b.get("endDate"))
    if not da or not db:
        return False
    return abs((da - db).total_seconds()) <= 48 * 3600


def settlement_evidence(a: dict[str, Any], b: dict[str, Any]) -> bool:
    # Certification deliberately requires explicit rule/source text on both sides.
    ar = normalize_title(
        str(a.get("rules") or a.get("description") or "")
    )
    br = normalize_title(
        str(b.get("rules") or b.get("description") or "")
    )
    asrc = normalize_title(str(a.get("resolutionSource") or ""))
    bsrc = normalize_title(str(b.get("resolutionSource") or ""))

    if not ar or not br or not asrc or not bsrc:
        return False

    source_match = SequenceMatcher(None, asrc, bsrc).ratio() >= 0.90
    rule_tokens_a = text_tokens(ar)
    rule_tokens_b = text_tokens(br)
    shared_rules = rule_tokens_a & rule_tokens_b
    rule_overlap = len(shared_rules) / max(1, min(len(rule_tokens_a), len(rule_tokens_b)))
    # Rules are deliberately treated as evidence, not as proof by themselves.
    # Certification still requires the title, expiry and resolution source checks.
    rule_match = (
        SequenceMatcher(None, ar, br).ratio() >= 0.62
        or (len(shared_rules) >= 8 and rule_overlap >= 0.45)
    )
    return source_match and rule_match


def parse_polymarket(item: dict[str, Any]) -> dict[str, Any] | None:
    title = str(item.get("question") or item.get("title") or "").strip()
    condition_id = str(item.get("conditionId") or "").strip()
    if not title or not condition_id:
        return None

    outcomes = parse_jsonish(item.get("outcomes")) or []
    token_ids = parse_jsonish(item.get("clobTokenIds")) or []
    prices = parse_jsonish(item.get("outcomePrices")) or []

    if not isinstance(outcomes, list) or not isinstance(token_ids, list):
        return None

    lowered = [str(x).lower() for x in outcomes]
    try:
        yi = lowered.index("yes")
        ni = lowered.index("no")
    except ValueError:
        if len(token_ids) != 2:
            return None
        yi, ni = 0, 1

    if yi >= len(token_ids) or ni >= len(token_ids):
        return None

    return {
        "source": "Polymarket",
        "marketId": str(item.get("id") or condition_id),
        "conditionId": condition_id,
        "title": title,
        "description": str(item.get("description") or "").strip(),
        "rules": str(item.get("description") or "").strip(),
        "resolutionSource": str(item.get("resolutionSource") or "").strip(),
        "endDate": item.get("endDate") or item.get("end_date"),
        "yesTokenId": str(token_ids[yi]),
        "noTokenId": str(token_ids[ni]),
        "slug": str(item.get("slug") or ""),
        "rawCategory": str(item.get("category") or "").strip().lower(),
        "indicativeYes": (
            dec(prices[yi]) if yi < len(prices) else None
        ),
        "indicativeNo": (
            dec(prices[ni]) if ni < len(prices) else None
        ),
    }


def parse_kalshi(item: dict[str, Any]) -> dict[str, Any] | None:
    ticker = str(item.get("ticker") or "").strip()
    title = str(
        item.get("title")
        or item.get("subtitle")
        or item.get("yes_sub_title")
        or ""
    ).strip()
    if not ticker or not title:
        return None

    rules = str(
        item.get("rules_primary")
        or item.get("rules_secondary")
        or item.get("rules")
        or item.get("subtitle")
        or ""
    ).strip()

    source = str(
        item.get("settlement_sources")
        or item.get("settlement_source")
        or item.get("resolution_source")
        or ""
    ).strip()

    return {
        "source": "Kalshi",
        "marketId": ticker,
        "title": title,
        "description": str(item.get("subtitle") or "").strip(),
        "rules": rules,
        "resolutionSource": source,
        "endDate": (
            item.get("expiration_time")
            or item.get("close_time")
            or item.get("latest_expiration_time")
        ),
        "eventId": str(item.get("event_ticker") or ""),
        "seriesTicker": str(item.get("series_ticker") or ""),
        "raw": item,
    }


def fetch_polymarket_markets() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    markets: list[dict[str, Any]] = []
    pages = 0
    try:
        for page in range(POLY_MAX_PAGES):
            offset = page * POLY_PAGE_SIZE
            params = urllib.parse.urlencode({
                "active": "true",
                "closed": "false",
                "limit": POLY_PAGE_SIZE,
                "offset": offset,
            })
            payload = fetch_json(f"{POLY_GAMMA}?{params}")
            items = payload.get("data", payload) if isinstance(payload, dict) else payload
            if not isinstance(items, list):
                raise ApiError(POLY_GAMMA, "unexpected market-list response", 200)
            pages += 1
            for item in items:
                if isinstance(item, dict):
                    parsed = parse_polymarket(item)
                    if parsed:
                        markets.append(parsed)
            if len(items) < POLY_PAGE_SIZE:
                break
        return markets, {
            "source": "Polymarket",
            "status": "ok",
            "count": len(markets),
            "pages": pages,
            "fetchedAt": now_iso(),
        }
    except Exception as exc:
        return markets, {
            "source": "Polymarket",
            "status": "error",
            "count": len(markets),
            "pages": pages,
            "fetchedAt": now_iso(),
            "error": str(exc)[:500],
        }


def fetch_kalshi_markets() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    markets: list[dict[str, Any]] = []
    cursor = ""
    pages = 0
    try:
        for _ in range(KALSHI_MAX_PAGES):
            params = {
                "status": "open",
                "limit": str(KALSHI_PAGE_SIZE),
            }
            if cursor:
                params["cursor"] = cursor
            url = f"{KALSHI_API}/markets?{urllib.parse.urlencode(params)}"
            payload = fetch_json(url)
            items = payload.get("markets", []) if isinstance(payload, dict) else []
            if not isinstance(items, list):
                raise ApiError(url, "unexpected markets response", 200)
            pages += 1
            for item in items:
                if isinstance(item, dict):
                    parsed = parse_kalshi(item)
                    if parsed:
                        markets.append(parsed)
            cursor = str(payload.get("cursor") or "") if isinstance(payload, dict) else ""
            if not cursor or not items:
                break
        return markets, {
            "source": "Kalshi",
            "status": "ok",
            "count": len(markets),
            "pages": pages,
            "fetchedAt": now_iso(),
        }
    except Exception as exc:
        return markets, {
            "source": "Kalshi",
            "status": "error",
            "count": len(markets),
            "pages": pages,
            "fetchedAt": now_iso(),
            "error": str(exc)[:500],
        }


def parse_poly_levels(book: dict[str, Any], side: str) -> list[tuple[Decimal, Decimal]]:
    rows = book.get(side, [])
    result = []
    if not isinstance(rows, list):
        return result
    for row in rows:
        if not isinstance(row, dict):
            continue
        price = dec(row.get("price"))
        size = dec(row.get("size"))
        if price is not None and size is not None and price > 0 and size > 0:
            result.append((price, size))
    result.sort(key=lambda x: x[0])
    return result


def poly_book(token_id: str) -> dict[str, Any]:
    url = f"{POLY_CLOB}/book?{urllib.parse.urlencode({'token_id': token_id})}"
    return fetch_json(url)


def kalshi_book(ticker: str) -> dict[str, Any]:
    url = f"{KALSHI_API}/markets/{urllib.parse.quote(ticker, safe='')}/orderbook?depth=100"
    return fetch_json(url)


def poly_fee_info(condition_id: str) -> tuple[Decimal | None, str | None]:
    # fd.r/fd.e is the per-market fee metadata used by current CLOB clients.
    url = f"{POLY_CLOB}/clob-markets/{urllib.parse.quote(condition_id, safe='')}"
    payload = fetch_json(url)
    fd = payload.get("fd") if isinstance(payload, dict) else None
    if not isinstance(fd, dict):
        # Null fd is the documented/current representation for fee-free markets.
        return Decimal("0"), "polymarket_fd_null"
    rate = dec(fd.get("r"))
    exponent = dec(fd.get("e"))
    if rate is None:
        return None, None
    if exponent is None:
        exponent = Decimal("1")
    if exponent != Decimal("1"):
        return None, None
    return rate, "polymarket_fd"


def poly_fee(price: Decimal, contracts: Decimal, rate: Decimal) -> Decimal:
    # Current Polymarket help formula: C * feeRate * p * (1-p).
    raw = contracts * rate * price * (Decimal("1") - price)
    return raw.quantize(Decimal("0.00001"), rounding=ROUND_UP)


def kalshi_fee(price: Decimal, contracts: Decimal, coefficient: Decimal) -> Decimal:
    # Current published general prediction-market schedule has used:
    # round up(0.07 * C * P * (1-P)), to the next cent.
    raw = coefficient * contracts * price * (Decimal("1") - price)
    cents = (raw * Decimal("100")).to_integral_value(rounding=ROUND_UP)
    return cents / Decimal("100")


def kalshi_series_info(series_ticker: str) -> dict[str, Any] | None:
    if not series_ticker:
        return None

    now = time.time()
    with KALSHI_SERIES_CACHE_LOCK:
        cached = KALSHI_SERIES_CACHE.get(series_ticker)
        if cached and (now - cached[0]) < KALSHI_SERIES_CACHE_SECONDS:
            return cached[1]

    url = f"{KALSHI_API}/series/{urllib.parse.quote(series_ticker, safe='')}"
    try:
        payload = fetch_json(url)
        info = payload.get("series") if isinstance(payload, dict) else None
        if not isinstance(info, dict):
            return None
        with KALSHI_SERIES_CACHE_LOCK:
            KALSHI_SERIES_CACHE[series_ticker] = (now, info)
        return info
    except Exception as exc:
        LOGGER.warning("series metadata failed ticker=%s error=%s", series_ticker, exc)
        return None


def kalshi_fee_terms(market: dict[str, Any]) -> tuple[Decimal | None, str, dict[str, Any]]:
    """
    Resolve the live public series fee metadata instead of assuming every
    Kalshi market has the same fee.

    Current public Kalshi series metadata exposes fee_type and fee_multiplier.
    The standard quadratic taker coefficient is 0.07. A flat fee structure is
    deliberately excluded because its exact calculation cannot be safely
    inferred from the market record alone.
    """
    info = kalshi_series_info(str(market.get("seriesTicker") or ""))
    if not info:
        return None, "kalshi_series_metadata_unavailable", {}

    fee_type = str(info.get("fee_type") or "").strip().lower()
    multiplier = dec(info.get("fee_multiplier"))
    if multiplier is None or multiplier < 0:
        return None, "kalshi_fee_multiplier_missing", info
    if fee_type not in {"quadratic", "quadratic_with_maker_fees"}:
        return None, f"kalshi_fee_type_{fee_type or 'unknown'}_not_certifiable", info

    # The taker coefficient is the quadratic 0.07 schedule; fee_multiplier
    # scales it per series. Makers are irrelevant because both legs cross the
    # existing book and therefore act as takers.
    rate = Decimal("0.07") * multiplier
    return rate, "kalshi_live_series_fee_metadata", info


def walk_poly_asks(
    token_id: str,
    contracts: Decimal,
    fee_rate: Decimal,
) -> dict[str, Any] | None:
    book = poly_book(token_id)
    asks = parse_poly_levels(book, "asks")
    if not asks:
        return None

    remaining = contracts
    cost = Decimal("0")
    fee = Decimal("0")
    fills = []
    fetched = now_utc()

    for price, size in asks[:BOOK_MAX_LEVELS]:
        take = min(remaining, size)
        if take <= 0:
            continue
        cost += take * price
        fee += poly_fee(price, take, fee_rate)
        fills.append({"price": dstr(price), "contracts": dstr(take)})
        remaining -= take
        if remaining <= 0:
            break

    if remaining > 0:
        return None

    return {
        "contracts": dstr(contracts),
        "cost": dstr(cost),
        "fee": dstr(fee),
        "totalCost": dstr(cost + fee),
        "averagePrice": dstr(cost / contracts),
        "fills": fills,
        "fetchedAt": fetched,
        "fetchedEpoch": time.time(),
    }


def parse_kalshi_bids(payload: dict[str, Any], key: str) -> list[tuple[Decimal, Decimal]]:
    ob = payload.get("orderbook_fp") if isinstance(payload, dict) else None
    if not isinstance(ob, dict):
        return []
    rows = ob.get(key, [])
    result = []
    if not isinstance(rows, list):
        return result
    for row in rows:
        if not isinstance(row, list) or len(row) < 2:
            continue
        price = dec(row[0])
        size = dec(row[1])
        if price is not None and size is not None and 0 < price < 1 and size > 0:
            result.append((price, size))
    result.sort(key=lambda x: x[0], reverse=True)
    return result


def walk_kalshi_buy(
    ticker: str,
    outcome: str,
    contracts: Decimal,
    fee_coefficient: Decimal,
) -> dict[str, Any] | None:
    payload = kalshi_book(ticker)

    # Kalshi's public orderbook_fp contains bids for YES and NO.
    # Buying YES crosses NO bids: YES ask = 1 - NO bid.
    # Buying NO crosses YES bids: NO ask = 1 - YES bid.
    bid_key = "no_dollars" if outcome == "YES" else "yes_dollars"
    bids = parse_kalshi_bids(payload, bid_key)
    if not bids:
        return None

    remaining = contracts
    cost = Decimal("0")
    fee = Decimal("0")
    fills = []

    for opposing_bid, size in bids[:BOOK_MAX_LEVELS]:
        price = Decimal("1") - opposing_bid
        take = min(remaining, size)
        if take <= 0:
            continue
        cost += take * price
        fee += kalshi_fee(price, take, fee_coefficient)
        fills.append({"price": dstr(price), "contracts": dstr(take)})
        remaining -= take
        if remaining <= 0:
            break

    if remaining > 0:
        return None

    return {
        "contracts": dstr(contracts),
        "cost": dstr(cost),
        "fee": dstr(fee),
        "totalCost": dstr(cost + fee),
        "averagePrice": dstr(cost / contracts),
        "fills": fills,
        "fetchedAt": now_utc(),
        "fetchedEpoch": time.time(),
    }


def fresh(book: dict[str, Any]) -> bool:
    ts = book.get("fetchedEpoch")
    return isinstance(ts, (int, float)) and (time.time() - ts) <= MAX_STALE_SECONDS


def pair_opportunity(
    poly: dict[str, Any],
    kalshi: dict[str, Any],
    match: dict[str, Any],
) -> dict[str, Any] | None:
    if not dates_compatible(poly, kalshi):
        return None
    if not settlement_evidence(poly, kalshi):
        return None

    poly_fee_rate, poly_fee_source = poly_fee_info(poly["conditionId"])
    kalshi_fee_rate, kalshi_fee_source, kalshi_fee_meta = kalshi_fee_terms(kalshi)

    # Certification is deliberately impossible when either fee cannot be
    # established without guessing.
    if poly_fee_rate is None or poly_fee_source is None:
        return None
    if kalshi_fee_rate is None:
        return None

    # Direction A: buy YES on Polymarket + NO on Kalshi.
    try:
        p_yes = walk_poly_asks(poly["yesTokenId"], TARGET_CONTRACTS, poly_fee_rate)
        k_no = walk_kalshi_buy(
            kalshi["marketId"], "NO", TARGET_CONTRACTS, kalshi_fee_rate
        )
    except Exception as exc:
        LOGGER.debug("book failure A: %s", exc)
        p_yes, k_no = None, None

    # Direction B: buy NO on Polymarket + YES on Kalshi.
    try:
        p_no = walk_poly_asks(poly["noTokenId"], TARGET_CONTRACTS, poly_fee_rate)
        k_yes = walk_kalshi_buy(
            kalshi["marketId"], "YES", TARGET_CONTRACTS, kalshi_fee_rate
        )
    except Exception as exc:
        LOGGER.debug("book failure B: %s", exc)
        p_no, k_yes = None, None

    candidates = []
    if p_yes and k_no:
        candidates.append(("POLY_YES_KALSHI_NO", p_yes, k_no))
    if p_no and k_yes:
        candidates.append(("POLY_NO_KALSHI_YES", p_no, k_yes))
    if not candidates:
        return None

    direction, leg_a, leg_b = min(
        candidates,
        key=lambda x: Decimal(x[1]["totalCost"]) + Decimal(x[2]["totalCost"]),
    )

    total_cost = Decimal(leg_a["totalCost"]) + Decimal(leg_b["totalCost"])
    payout = TARGET_CONTRACTS
    net = payout - total_cost
    edge = net / payout

    if not fresh(leg_a) or not fresh(leg_b):
        return None
    if net <= 0 or edge < MIN_NET_EDGE:
        return None

    # Final hard checks.
    if Decimal(leg_a["contracts"]) != TARGET_CONTRACTS:
        return None
    if Decimal(leg_b["contracts"]) != TARGET_CONTRACTS:
        return None

    fingerprint = hashlib.sha256(
        json_dump({
            "poly": poly["marketId"],
            "kalshi": kalshi["marketId"],
            "direction": direction,
            "fillsA": leg_a["fills"],
            "fillsB": leg_b["fills"],
        }).encode()
    ).hexdigest()[:16]

    return {
        "id": f"cert_{fingerprint}",
        "status": "CERTIFIED",
        "detectedAt": now_iso(),
        "title": poly["title"],
        "direction": direction,
        "contracts": float(TARGET_CONTRACTS),
        "totalCost": float(total_cost),
        "payout": float(payout),
        "netProfit": float(net),
        "netEdge": float(edge),
        "matchScore": match["score"],
        "matchingEvidence": match,
        "settlementChecks": {
            "datesCompatible": True,
            "rulesAndSourceCompatible": True,
            "sameQuantityBothLegs": True,
        },
        "feeChecks": {
            "polymarketRate": float(poly_fee_rate),
            "polymarketSource": poly_fee_source,
            "kalshiRate": float(kalshi_fee_rate),
            "kalshiSource": kalshi_fee_source,
            "kalshiFeeType": kalshi_fee_meta.get("fee_type"),
            "kalshiFeeMultiplier": kalshi_fee_meta.get("fee_multiplier"),
        },
        "legs": {
            "polymarket": {
                "marketId": poly["marketId"],
                "conditionId": poly["conditionId"],
                "outcome": "YES" if direction == "POLY_YES_KALSHI_NO" else "NO",
                "book": leg_a,
            },
            "kalshi": {
                "ticker": kalshi["marketId"],
                "outcome": "NO" if direction == "POLY_YES_KALSHI_NO" else "YES",
                "book": leg_b,
            },
        },
        "paperOnly": True,
        "liveTrading": False,
    }


class Ledger:
    def __init__(self, path: str):
        self.lock = threading.RLock()
        self.db = sqlite3.connect(path, check_same_thread=False)
        self.db.row_factory = sqlite3.Row
        self.init()

    def init(self) -> None:
        with self.db:
            self.db.executescript(
                """
                CREATE TABLE IF NOT EXISTS settings(
                    key TEXT PRIMARY KEY,
                    value TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS scans(
                    id TEXT PRIMARY KEY,
                    scanned_at TEXT NOT NULL,
                    status TEXT NOT NULL,
                    payload TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS opportunities(
                    id TEXT PRIMARY KEY,
                    detected_at TEXT NOT NULL,
                    payload TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS paper_trades(
                    id TEXT PRIMARY KEY,
                    opportunity_id TEXT NOT NULL,
                    created_at TEXT NOT NULL,
                    amount REAL NOT NULL,
                    expected_pnl REAL NOT NULL,
                    status TEXT NOT NULL,
                    payload TEXT NOT NULL
                );
                """
            )
            self.db.execute(
                "INSERT OR IGNORE INTO settings(key,value) VALUES('balance',?)",
                (str(STARTING_BALANCE),),
            )

    def save_scan(self, payload: dict[str, Any]) -> None:
        with self.lock, self.db:
            self.db.execute(
                "INSERT INTO scans VALUES(?,?,?,?)",
                (
                    uuid.uuid4().hex,
                    payload["scannedAt"],
                    "ok" if payload["sourceStatus"][0]["status"] == "ok"
                    and payload["sourceStatus"][1]["status"] == "ok"
                    else "partial",
                    json_dump(payload),
                ),
            )
            for opp in payload["opportunities"]:
                self.db.execute(
                    "INSERT OR REPLACE INTO opportunities VALUES(?,?,?)",
                    (opp["id"], opp["detectedAt"], json_dump(opp)),
                )

    def latest(self) -> dict[str, Any] | None:
        row = self.db.execute(
            "SELECT payload FROM scans ORDER BY scanned_at DESC LIMIT 1"
        ).fetchone()
        return json.loads(row["payload"]) if row else None

    def opportunities(self, limit: int = 50) -> list[dict[str, Any]]:
        rows = self.db.execute(
            "SELECT payload FROM opportunities ORDER BY detected_at DESC LIMIT ?",
            (max(1, min(limit, 200)),),
        ).fetchall()
        return [json.loads(r["payload"]) for r in rows]

    def trades(self) -> list[dict[str, Any]]:
        rows = self.db.execute(
            "SELECT payload FROM paper_trades ORDER BY created_at DESC LIMIT 100"
        ).fetchall()
        return [json.loads(r["payload"]) for r in rows]

    def create_paper_trade(self, opportunity_id: str, amount: Decimal) -> dict[str, Any]:
        row = self.db.execute(
            "SELECT payload FROM opportunities WHERE id=?",
            (opportunity_id,),
        ).fetchone()
        if not row:
            raise ValueError("Opportunity not found.")
        opp = json.loads(row["payload"])
        ratio = Decimal(str(opp["netProfit"])) / Decimal(str(opp["totalCost"]))
        pnl = amount * ratio
        trade = {
            "id": f"paper_{uuid.uuid4().hex[:12]}",
            "opportunityId": opportunity_id,
            "createdAt": now_iso(),
            "amount": float(amount),
            "expectedPnl": float(pnl),
            "status": "paper-open",
            "paperOnly": True,
            "liveTrading": False,
        }
        with self.lock, self.db:
            self.db.execute(
                "INSERT INTO paper_trades VALUES(?,?,?,?,?,?,?)",
                (
                    trade["id"],
                    opportunity_id,
                    trade["createdAt"],
                    trade["amount"],
                    trade["expectedPnl"],
                    trade["status"],
                    json_dump(trade),
                ),
            )
        return trade


ledger = Ledger(DB_PATH)


def run_scan() -> dict[str, Any]:
    poly, poly_status = fetch_polymarket_markets()
    kalshi, kalshi_status = fetch_kalshi_markets()

    candidates = []
    opportunities = []

    # Build an inverted token index so the scanner can consider the full
    # fetched market sets without doing an all-against-all comparison.
    token_index: dict[str, list[dict[str, Any]]] = {}
    for k in kalshi:
        for token in text_tokens(normalize_title(k["title"])):
            token_index.setdefault(token, []).append(k)

    for p in poly:
        ptokens = text_tokens(normalize_title(p["title"]))
        possible: dict[str, dict[str, Any]] = {}
        for token in ptokens:
            for k in token_index.get(token, []):
                possible[k["marketId"]] = k

        ranked: list[tuple[float, dict[str, Any], dict[str, Any]]] = []
        for k in possible.values():
            match = title_match(p, k)
            if match:
                ranked.append((match["score"], k, match))

        ranked.sort(key=lambda x: x[0], reverse=True)
        for _, k, match in ranked[:3]:
            candidate = {
                "polymarket": p["marketId"],
                "kalshi": k["marketId"],
                "titlePolymarket": p["title"],
                "titleKalshi": k["title"],
                "matchScore": match["score"],
                "settlementEvidence": settlement_evidence(p, k),
                "datesCompatible": dates_compatible(p, k),
            }
            # Only the strongest, structurally plausible matches get book
            # requests; rejected matches are still visible in diagnostics.
            opp = pair_opportunity(p, k, match)
            if opp:
                candidate["status"] = "CERTIFIED"
                opportunities.append(opp)
                candidates.append(candidate)
                break
            candidate["status"] = "REJECTED"
            candidates.append(candidate)

    opportunities.sort(key=lambda x: x["netEdge"], reverse=True)

    result = {
        "scannedAt": now_iso(),
        "sourceStatus": [poly_status, kalshi_status],
        "candidateMatchCount": len(candidates),
        "candidateMatches": candidates[:100],
        "opportunities": opportunities[:100],
        "certifiedCount": len(opportunities),
        "paperOnly": True,
        "liveTrading": False,
    }
    ledger.save_scan(result)
    return result


class Handler(BaseHTTPRequestHandler):
    server_version = "MarketHunterV2/1.0"

    def log_message(self, _fmt: str, *_args: Any) -> None:
        return

    def send_json(self, code: int, payload: Any) -> None:
        body = json.dumps(payload, separators=(",", ":"), default=str).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self) -> None:
        path = urllib.parse.urlparse(self.path).path
        try:
            if path in ("/", "/healthz", f"{API_PREFIX}/healthz"):
                return self.send_json(200, {"status": "healthy", "version": "V2"})
            if path in (f"{API_PREFIX}/status", f"{API_PREFIX}/dashboard"):
                latest = ledger.latest()
                return self.send_json(
                    200,
                    latest or {
                        "status": "waiting",
                        "paperOnly": True,
                        "liveTrading": False,
                    },
                )
            if path == f"{API_PREFIX}/opportunities":
                return self.send_json(200, ledger.opportunities())
            if path == f"{API_PREFIX}/paper-trades":
                return self.send_json(200, ledger.trades())
            return self.send_json(404, {"message": "Route not found."})
        except Exception as exc:
            LOGGER.exception("GET failed")
            return self.send_json(500, {"message": str(exc)})

    def do_POST(self) -> None:
        path = urllib.parse.urlparse(self.path).path
        try:
            if path == f"{API_PREFIX}/scan":
                return self.send_json(200, run_scan())

            if path == f"{API_PREFIX}/paper-trades":
                length = int(self.headers.get("Content-Length", "0"))
                if length > 10000:
                    return self.send_json(400, {"message": "Request too large."})
                payload = json.loads(self.rfile.read(length) or b"{}")
                amount = dec(payload.get("amount"))
                if not payload.get("opportunityId") or amount is None or amount <= 0:
                    return self.send_json(400, {"message": "opportunityId and positive amount required."})
                return self.send_json(
                    201,
                    ledger.create_paper_trade(str(payload["opportunityId"]), amount),
                )

            return self.send_json(404, {"message": "Route not found."})
        except Exception as exc:
            LOGGER.exception("POST failed")
            return self.send_json(500, {"message": str(exc)})


def scanner_loop() -> None:
    while True:
        try:
            result = run_scan()
            LOGGER.info(
                "scan complete certified=%s candidates=%s",
                result["certifiedCount"],
                result["candidateMatchCount"],
            )
        except Exception:
            LOGGER.exception("scanner iteration failed")
        time.sleep(max(30, SCAN_SECONDS))


def main() -> None:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(name)s %(message)s",
    )
    port = int(os.environ.get("PORT", "8000"))
    server = ThreadingHTTPServer(("0.0.0.0", port), Handler)
    threading.Thread(target=scanner_loop, daemon=True, name="scanner").start()
    LOGGER.info("Market Hunter V2 listening on %s", port)
    server.serve_forever()


if __name__ == "__main__":
    main()
