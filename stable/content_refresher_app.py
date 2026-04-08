import json
import math
import mimetypes
import os
import random
import re
import shutil
import tempfile
import threading
import time
import uuid
import webbrowser
import getpass
import socket
import sys
from collections import defaultdict
from io import BytesIO
from zipfile import ZipFile, ZIP_DEFLATED
from concurrent.futures import ThreadPoolExecutor, as_completed
from copy import deepcopy
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import quote, unquote

import requests
import jwt
from PIL import Image, ImageOps, ImageDraw, ImageFont
from flask import Flask, Response, jsonify, request, stream_with_context, send_file
from werkzeug.utils import secure_filename


# ============================================================
# USER CONFIGURATION
# ============================================================
BYNDER_BASE_URL = "https://www.bynder.raymourflanigan.com"
BYNDER_TOKEN_PATH = os.environ.get(
    "CONTENT_REFRESHER_CREDENTIALS_PATH",
    r"C:\bynderAPI\byndercredentials_permanenttoken.json",
)

APP_VERSION = "dev132"

# Required for updates. Fill these in before committing changes.
PRODUCT_SKU_POSITION_METAPROPERTY_ID = "3DD8E8E1-3986-4D8E-BC13EC3E19A10725"
MARKED_FOR_DELETION_METAPROPERTY_ID = "92E8A7DD-281C-4361-82A5F23AEB965FAD"
RELATED_COMPONENTS_METAPROPERTY_ID = "b1edd078-d91c-4716-8016-6b404a8f529a"
MARKED_FOR_DELETION_OPTION_ID = "B184F48F-7A1C-4B61-BA4B91B5DD094F22"
PRODUCT_COLLECTION_METAPROPERTY_ID = "D7F45175-4AFA-4945-93FE13B21F906E83"
PRODUCT_SKU_METAPROPERTY_ID = "06C92AA9-64A1-4329-83C66BE3DC0AB0D2"

HOST = "127.0.0.1"
PORT = 8874
OPEN_BROWSER_ON_START = True
PAGE_LIMIT = 1000
MAX_WORKERS = 12
REQUEST_TIMEOUT = 120
MAX_RETRIES = 8
MAX_REQUESTS_PER_SECOND = 12.0
CHUNK_SIZE_BYTES = 5 * 1024 * 1024
STAGED_UPLOAD_DIR = Path(tempfile.gettempdir()) / "content_refresher_staged_uploads"
STAGED_UPLOAD_DIR.mkdir(parents=True, exist_ok=True)

# Based on your current flow notes, these are the PSA deliverables we want.
ALLOWED_DELIVERABLES = {
    "Product_Image_Carousel",
    "DimensionsDiagram",
    "Product_Grid_Image",
    "Product_Swatch_Detail_Image",
    "Product_Swatch_Image",
}
PHOTO_ASSET_SUBTYPE = "Product_Photography"
PHOTO_EXCLUDED_IMAGE_TYPES = {"Silo", "Styled_Silo", "Swatch", "Video_Shoot_Still"}
REVIEWED_FOR_SITE_DBNAME = "ReviewedforSite"
REVIEWED_FOR_SITE_LABEL = "Reviewedforsite"
PSA_IMAGE_TYPE_DBNAME = "PSA_Image_Type"
PHOTO_TO_PSA_IMAGE_TYPE_MAP = {
    "Detail": "Detail",
    "Lifestyle": "Room_shot",
    "Silo": "Silo",
    "Styled_Silo": "Silo",
    "Swatch": "Swatch_detail",
    "Video_Shoot_Still": "Room_shot",
}
PSA_IMAGE_TYPE_PROMPT_CHOICES = ["Detail", "Room_shot", "Silo", "Swatch_detail"]
SWATCH_PSA_IMAGE_TYPE_LABEL = "Swatch"
DIMENSIONS_PSA_IMAGE_TYPE_LABEL = "Dimensions_diagram_image"
SQUARE_PSA_IMAGE_TYPE_LABEL = "Room_shot"
SWATCH_OPTIONAL_STEP_PATHS = {"RF_Root___Home_Decor___Wall_Art", "RF_Root___Home_Decor___Wall_Decor", "RF_Root___Home_Decor___Hanging_Lights", "RF Root | Home Decor | Hanging Lights"}
SWATCH_OPTIONAL_STEP_PATH_PREFIXES = ("RF_Root___Mattresses", "RF Root | Mattresses")
WALL_ART_SIZING_STEP_PATHS = {"RF_Root___Home_Decor___Wall_Art", "RF_Root___Home_Decor___Wall_Decor"}
# Defensive aliases for game/background scanners so these checks never explode if a future edit
# accidentally renames one constant in one code path.
CHALLENGE_SWATCH_OPTIONAL_STEP_PATHS = SWATCH_OPTIONAL_STEP_PATHS
CHALLENGE_WALL_ART_SIZING_STEP_PATHS = WALL_ART_SIZING_STEP_PATHS
WALL_ART_SIZING_GUIDE_MEDIA_ID = "ed5aad96-4b05-4f8b-8a60-621b9f955fac"
WALL_ART_SIZING_GUIDE_FILENAME = "Image_Carousel_Wall_Art_Sizing_Guide_3000x1688.jpg"

ASSET_SUBTYPE_REQUIRED = "Product_Site_Asset"
MARKED_FOR_DELETION_VALUE_NAME = "Marked_for_Deletion"

STANDARD_CORE_SLOTS = [f"SKU_{n}" for n in range(100, 5000, 100)]
SPECIAL_CAROUSEL_SLOT = "SKU_8000"
CORE_SLOTS = STANDARD_CORE_SLOTS + [SPECIAL_CAROUSEL_SLOT]
SWATCH_DETAIL_SLOTS = [f"SKU_{n}" for n in range(5000, 6000, 100)]
GRID_SLOT = "SKU_grid"
SPECIAL_SLOTS = ["SKU_dimension", "SKU_swatch", "SKU_square"]
ALL_KNOWN_SLOTS = [GRID_SLOT] + CORE_SLOTS + SWATCH_DETAIL_SLOTS + SPECIAL_SLOTS

DELIVERABLE_BY_LANE_SLOT = {
    ("grid", GRID_SLOT): "Product_Grid_Image",
    ("special", "SKU_dimension"): "DimensionsDiagram",
    ("special", "SKU_swatch"): "Product_Swatch_Image",
}


DOWNLOADS_DIR = Path.home() / "Downloads"
DOWNLOADS_DIR.mkdir(parents=True, exist_ok=True)

COLLECTION_OPTIONS_CACHE_PATH = Path.home() / ".content_refresher_collection_options_cache.json"
COLLECTION_OPTIONS_CACHE_MAX_AGE_SECONDS = 24 * 60 * 60
COLLECTION_ASSET_CACHE_MAX_AGE_SECONDS = 10 * 60
COLLECTION_DERIVED_CACHE_MAX_AGE_SECONDS = 10 * 60
COLLECTION_BOARD_CACHE_MAX_AGE_SECONDS = 5 * 60
BYNDER_COLLECTION_CACHE_MAX_AGE_SECONDS = 10 * 60

GAME_SCORE_PATH = Path.home() / ".content_refresher_game_scores.json"
APP_LAUNCH_DIR = Path(os.path.abspath(sys.argv[0] if sys.argv and sys.argv[0] else __file__)).resolve().parent
GOOGLE_SCOREBOARD_CREDENTIALS_FILENAME = "content-refresher-scoreboard-credentials.json"
GOOGLE_SCOREBOARD_CREDENTIALS_PATH = APP_LAUNCH_DIR / GOOGLE_SCOREBOARD_CREDENTIALS_FILENAME
GOOGLE_SCOREBOARD_SPREADSHEET_ID = "1ZzZp8C7ySVPPZQCoRz_RCn5N7iQfXaCOQBAd0GhAZOY"
GOOGLE_SCOREBOARD_TAB_NAME = "scores"
GOOGLE_SCOREBOARD_RANGE = f"{GOOGLE_SCOREBOARD_TAB_NAME}!A:C"
GOOGLE_SCOREBOARD_REFRESH_SECONDS = 20
GAME_QUEUE_PRELOAD_TARGET = 1
GAME_QUEUE_TARGET = 2
GAME_QUEUE_ACTIVE_TOTAL_TARGET = 3
GAME_SCAN_BATCH = 8
GAME_SCAN_MIN_GAP_SECONDS = 45
GAME_LEADERBOARD_WEBHOOK_URL = os.environ.get("CONTENT_REFRESHER_LEADERBOARD_WEBHOOK_URL", "")
GAME_SERVER_QUEUE_WORKER_INTERVAL_SECONDS = 60.0
RECENT_POSITION_OVERRIDE_TTL_SECONDS = 72 * 60 * 60

PHOTO_WATERMARK_ALPHA = 0.46
PHOTO_WATERMARK_TEXT = ("NOT", "FINAL")
PHOTO_WATERMARK_WIDTH_RATIO = 0.86
PHOTO_WATERMARK_HEIGHT_RATIO = 0.80
PHOTO_WATERMARK_LINE_GAP_RATIO = 0.10
SET_DIM_MAX_COMPONENTS = 6

# Product Imagery Onboarding workspace constants
WORKSPACE_CONTENT_REFRESHER = "content_refresher"
WORKSPACE_PIO = "product_imagery_onboarding"
PIO_PLACEHOLDER_GRID_URL = "https://www.bynder.raymourflanigan.com/asset/573a060f-3833-47bf-95f8-4b1e6673860d/XXXX_666666666_3000.jpg"
PIO_CREDENTIALS_FILENAME = "content-refresher-scoreboard-credentials.json"
PIO_WORKFLOW_VALUE = "App_Product_Imagery_Onboarding"
PIO_WORKFLOW_OPTION_ID = "911BFC7C-970F-4AA3-AC2BFA7D3B67E9E0"
PIO_STATUS_LAUNCHED = "App_Launched"
PIO_STATUS_STAGED = "App_Staged"
PIO_STATUS_LIVE = "App_Live"
PIO_SYNC_DO_NOT = "Do_not_sync_to_site"
PIO_SYNC_DO = "Do_sync_to_site"
PIO_DEFAULT_CAROUSEL_SLOTS = [f"SKU_{n}" for n in range(100, 600, 100)]
PIO_DEFAULT_SWATCH_DETAIL_SLOTS = ["SKU_5000", "SKU_5100"]
PIO_ALLOWED_SALES_CHANNELS = {"Full_line", "Online_only", "Outlet__stocked_", "Outlet__online_only_"}
PIO_REQUIRED_IMPORT_HEADERS = ["SKU", "Product Name"]
PIO_OPTIONAL_IMPORT_HEADERS = ["Components", "Length", "Width", "Height", "Features"]
PIO_STEP_HEADER_ROW = "SKU	Product Name	Components	Product Color	Length	Width	Height	Sales Channel	Features"
PIO_BYNDER_SALES_CHANNEL_VALUES = ["Full_line", "Online_only", "Outlet__stocked_", "Outlet__online_only_"]

app = Flask(__name__)

class RateLimiter:
    def __init__(self, rate_per_second: float) -> None:
        self.rate = max(float(rate_per_second or 1.0), 0.1)
        self.min_interval = 1.0 / self.rate
        self._lock = threading.Lock()
        self._last_call = 0.0

    def wait(self) -> None:
        with self._lock:
            now = time.perf_counter()
            elapsed = now - self._last_call
            if elapsed < self.min_interval:
                time.sleep(self.min_interval - elapsed)
                now = time.perf_counter()
            self._last_call = now


RATELIMITER = RateLimiter(MAX_REQUESTS_PER_SECOND)


# ============================================================
# GLOBAL APP STATE
# ============================================================
STATE = {
    "collections": None,
    "board": None,
    "baseline_board": None,
    "last_load": None,
    "last_commit": None,
    "server_messages": [],
    "collection_asset_cache": {},
    "recent_position_overrides": {},
}
STATE["game"] = {
    "active": False,
    "queue": [],
    "current": None,
    "scanner_running": False,
    "last_scan_at": 0.0,
    "lock": threading.Lock(),
}

METAPROPERTY_DBNAME_CACHE: Dict[str, str] = {}
METAPROPERTY_OPTION_VALUE_CACHE: Dict[str, Dict[str, str]] = {}
GOOGLE_SCOREBOARD_CACHE: Dict[str, Any] = {"fetched_at": 0.0, "data": None}
GOOGLE_SCOREBOARD_TOKEN_CACHE: Dict[str, Any] = {"access_token": "", "expires_at": 0.0}

PROPERTY_DB_NAMES: Dict[str, str] = {
    "Product_SKU": "Product_SKU",
    "Product_SKU_Position": "Product_SKU_Position",
    "Marked_for_Deletion": "Marked_for_Deletion_from_Site",
    "Deliverable": "Deliverable",
    "Product_Color": "Product_Color",
    "Product_URL": "Product_URL",
    "Product_Collection": "product_collection",
    "product_collection": "product_collection",
    "Workflow": "Workflow",
    "Workflow_Status": "Workflow_Status",
    "Sync_to_Site": "Sync_to_Site",
    "Sales_Channel": "Sales_Channel",
    "Product_Name__STEP_": "Product_Name__STEP_",
    "Component_SKUs": "Component_SKUs",
    "Asset_Type": "Asset_Type",
    "Asset_Sub_Type": "Asset_Sub_Type",
    "dim_Length": "dim_Length",
    "dim_Width": "dim_Width",
    "dim_Height": "dim_Height",
}

TOTAL_FILL_CHECK_CACHE: Dict[str, bool] = {}
TOTAL_FILL_CHECK_TIMEOUT = 20
TOTAL_FILL_CHECK_SAMPLE_OFFSET = 10
TOTAL_FILL_CHECK_WHITE_THRESHOLD = 245


# ============================================================
# HELPERS - GENERIC
# ============================================================
def log_message(message: str) -> None:
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    text = f"[{timestamp}] {message}"
    print(text)
    STATE["server_messages"].append(text)
    STATE["server_messages"] = STATE["server_messages"][-300:]


def normalize_uuid(value: Any) -> str:
    return re.sub(r"[^0-9a-fA-F]", "", str(value or "")).lower()


def safe_list(value: Any) -> List[Any]:
    if value is None:
        return []
    if isinstance(value, list):
        return value
    return [value]


def string_value(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, list):
        parts = [str(v).strip() for v in value if str(v).strip()]
        return ", ".join(parts)
    return str(value).strip()



def natural_sort_key(value: Any) -> Tuple[Any, ...]:
    text = string_value(value)
    parts = re.split(r'(\d+)', text)
    out: List[Any] = []
    for part in parts:
        if not part:
            continue
        if part.isdigit():
            out.append((0, int(part)))
        else:
            out.append((1, part.lower()))
    return tuple(out)

def boolish(value: Any) -> bool:
    value_str = string_value(value).strip().lower()
    return value_str in {"true", "yes", "1"}


def parse_datetime(value: Any) -> Optional[datetime]:
    text = string_value(value)
    if not text:
        return None
    for candidate in [text.replace("Z", "+00:00"), text]:
        try:
            return datetime.fromisoformat(candidate)
        except Exception:
            pass
    for fmt in ["%Y-%m-%dT%H:%M:%S.%fZ", "%Y-%m-%dT%H:%M:%SZ"]:
        try:
            return datetime.strptime(text, fmt)
        except Exception:
            pass
    return None


def get_fresh_cached_value(cache: Dict[str, Any], key: str, max_age_seconds: int, cache_label: str = "") -> Any:
    entry = cache.get(key)
    if entry is None:
        return None

    if isinstance(entry, dict) and "saved_at" in entry and "value" in entry:
        try:
            age_seconds = time.time() - float(entry.get("saved_at") or 0)
        except Exception:
            age_seconds = max_age_seconds + 1
        if age_seconds <= max_age_seconds:
            return deepcopy(entry.get("value"))
        cache.pop(key, None)
        if cache_label:
            log_message(f"Expired {cache_label} cache for {key} after {int(age_seconds)}s; fetching fresh data.")
        return None

    cache.pop(key, None)
    if cache_label:
        log_message(f"Discarded legacy {cache_label} cache for {key}; fetching fresh data.")
    return None


def set_timed_cached_value(cache: Dict[str, Any], key: str, value: Any) -> None:
    cache[key] = {
        "saved_at": time.time(),
        "value": deepcopy(value),
    }


def load_collection_options_from_disk_cache() -> Optional[List[Dict[str, str]]]:
    try:
        if not COLLECTION_OPTIONS_CACHE_PATH.exists():
            return None
        age_seconds = time.time() - COLLECTION_OPTIONS_CACHE_PATH.stat().st_mtime
        if age_seconds > COLLECTION_OPTIONS_CACHE_MAX_AGE_SECONDS:
            return None
        payload = json.loads(COLLECTION_OPTIONS_CACHE_PATH.read_text(encoding="utf-8"))
        items = payload.get("collections") if isinstance(payload, dict) else None
        if isinstance(items, list) and items:
            normalized = []
            for item in items:
                if not isinstance(item, dict):
                    continue
                normalized.append({
                    "id": string_value(item.get("id")),
                    "label": string_value(item.get("label")),
                })
            return [x for x in normalized if x["id"] and x["label"]] or None
    except Exception as exc:
        log_message(f"Could not read collection options cache: {exc}")
    return None


def save_collection_options_to_disk_cache(items: List[Dict[str, str]]) -> None:
    try:
        payload = {
            "saved_at": datetime.now().isoformat(),
            "collections": items,
        }
        COLLECTION_OPTIONS_CACHE_PATH.write_text(
            json.dumps(payload, ensure_ascii=False),
            encoding="utf-8",
        )
    except Exception as exc:
        log_message(f"Could not write collection options cache: {exc}")
    return None


def load_collection_options(session: requests.Session, force_refresh: bool = False) -> List[Dict[str, str]]:
    if not force_refresh:
        cached_state = STATE.get("collections")
        if isinstance(cached_state, list) and cached_state:
            return cached_state
        cached_disk = load_collection_options_from_disk_cache()
        if cached_disk:
            STATE["collections"] = cached_disk
            return cached_disk
    collections = fetch_metaproperty_options(session, PRODUCT_COLLECTION_METAPROPERTY_ID)
    STATE["collections"] = collections
    save_collection_options_to_disk_cache(collections)
    return collections


def get_recent_position_override(media_id: Any) -> str:
    media_id = string_value(media_id)
    if not media_id:
        return ""
    cache = STATE.setdefault("recent_position_overrides", {})
    entry = cache.get(media_id)
    if not isinstance(entry, dict):
        return ""
    try:
        saved_at = float(entry.get("saved_at") or 0.0)
    except Exception:
        saved_at = 0.0
    if (time.time() - saved_at) > RECENT_POSITION_OVERRIDE_TTL_SECONDS:
        cache.pop(media_id, None)
        return ""
    return string_value(entry.get("position"))


def set_recent_position_override(media_id: Any, position: Any) -> None:
    media_id = string_value(media_id)
    position = string_value(position)
    if not media_id or not position:
        return
    STATE.setdefault("recent_position_overrides", {})[media_id] = {
        "position": position,
        "saved_at": time.time(),
    }


def clear_recent_position_override(media_id: Any) -> None:
    media_id = string_value(media_id)
    if not media_id:
        return
    STATE.setdefault("recent_position_overrides", {}).pop(media_id, None)


def get_local_username() -> str:
    try:
        return getpass.getuser() or "player"
    except Exception:
        return "player"


def get_google_scoreboard_credentials_path() -> Path:
    env_path = string_value(os.environ.get("CONTENT_REFRESHER_SCOREBOARD_CREDENTIALS_PATH"))
    if env_path:
        return Path(env_path).expanduser().resolve()
    return GOOGLE_SCOREBOARD_CREDENTIALS_PATH


def google_scoreboard_is_configured() -> bool:
    try:
        return get_google_scoreboard_credentials_path().exists()
    except Exception:
        return False


def load_google_scoreboard_credentials() -> Dict[str, Any]:
    creds_path = get_google_scoreboard_credentials_path()
    if not creds_path.exists():
        raise FileNotFoundError(f"Google scoreboard credentials file was not found at {creds_path}")
    data = json.loads(creds_path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError("Google scoreboard credentials file is not valid JSON.")
    required = ["client_email", "private_key"]
    missing = [key for key in required if not string_value(data.get(key))]
    if missing:
        raise ValueError(f"Google scoreboard credentials are missing required field(s): {', '.join(missing)}")
    return data


def get_google_scoreboard_access_token(force_refresh: bool = False) -> str:
    now = time.time()
    cached_token = string_value(GOOGLE_SCOREBOARD_TOKEN_CACHE.get("access_token"))
    expires_at = float(GOOGLE_SCOREBOARD_TOKEN_CACHE.get("expires_at") or 0.0)
    if cached_token and not force_refresh and now < max(0.0, expires_at - 60.0):
        return cached_token

    creds = load_google_scoreboard_credentials()
    token_uri = string_value(creds.get("token_uri") or "https://oauth2.googleapis.com/token")
    issued_at = int(now)
    payload = {
        "iss": creds["client_email"],
        "scope": "https://www.googleapis.com/auth/spreadsheets",
        "aud": token_uri,
        "iat": issued_at,
        "exp": issued_at + 3600,
    }
    assertion = jwt.encode(payload, creds["private_key"], algorithm="RS256")
    response = requests.post(
        token_uri,
        data={
            "grant_type": "urn:ietf:params:oauth:grant-type:jwt-bearer",
            "assertion": assertion,
        },
        timeout=30,
    )
    response.raise_for_status()
    token_payload = response.json()
    access_token = string_value(token_payload.get("access_token"))
    if not access_token:
        raise RuntimeError("Google OAuth token response did not include an access token.")
    expires_in = int(token_payload.get("expires_in") or 3600)
    GOOGLE_SCOREBOARD_TOKEN_CACHE["access_token"] = access_token
    GOOGLE_SCOREBOARD_TOKEN_CACHE["expires_at"] = now + expires_in
    return access_token


def google_sheets_request(method: str, url: str, *, params: Optional[Dict[str, Any]] = None, json_payload: Any = None, retry_on_401: bool = True) -> Dict[str, Any]:
    token = get_google_scoreboard_access_token(force_refresh=False)
    headers = {"Authorization": f"Bearer {token}"}
    response = requests.request(method, url, headers=headers, params=params, json=json_payload, timeout=30)
    if response.status_code == 401 and retry_on_401:
        token = get_google_scoreboard_access_token(force_refresh=True)
        headers = {"Authorization": f"Bearer {token}"}
        response = requests.request(method, url, headers=headers, params=params, json=json_payload, timeout=30)
    response.raise_for_status()
    if not response.text.strip():
        return {}
    return response.json()


def normalize_remote_score_rows(values: List[List[Any]]) -> Dict[str, Any]:
    users: Dict[str, Dict[str, Any]] = {}
    if not values:
        return {"users": users}
    for row in values[1:]:
        if not isinstance(row, list) or not row:
            continue
        username = string_value(row[0]).strip()
        if not username:
            continue
        score = 0
        try:
            score = max(0, int(float(string_value(row[1]) or "0")))
        except Exception:
            score = 0
        users[username] = {
            "score": score,
            "last_updated": string_value(row[2]).strip(),
        }
    return {"users": users}


def fetch_remote_game_scores(force_refresh: bool = False) -> Optional[Dict[str, Any]]:
    if not google_scoreboard_is_configured():
        return None
    now = time.time()
    cached = GOOGLE_SCOREBOARD_CACHE.get("data")
    fetched_at = float(GOOGLE_SCOREBOARD_CACHE.get("fetched_at") or 0.0)
    if cached is not None and not force_refresh and (now - fetched_at) < GOOGLE_SCOREBOARD_REFRESH_SECONDS:
        return deepcopy(cached)
    try:
        url = f"https://sheets.googleapis.com/v4/spreadsheets/{GOOGLE_SCOREBOARD_SPREADSHEET_ID}/values/{quote(GOOGLE_SCOREBOARD_RANGE, safe='!:\'')}"
        payload = google_sheets_request("GET", url)
        data = normalize_remote_score_rows(payload.get("values") or [])
        GOOGLE_SCOREBOARD_CACHE["data"] = deepcopy(data)
        GOOGLE_SCOREBOARD_CACHE["fetched_at"] = now
        return data
    except Exception as exc:
        log_message(f"Could not refresh Google scoreboard sheet: {exc}")
        return deepcopy(cached) if cached is not None else None


def merge_score_sources(local_data: Dict[str, Any], remote_data: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    merged = {"users": {}}
    for source in [local_data or {"users": {}}, remote_data or {"users": {}}]:
        for username, entry in (source.get("users") or {}).items():
            prior = merged["users"].get(username) or {}
            score = max(int(prior.get("score") or 0), int((entry or {}).get("score") or 0))
            last_updated = string_value((entry or {}).get("last_updated") or prior.get("last_updated"))
            merged["users"][username] = {"score": score, "last_updated": last_updated}
    return merged


def load_game_scores(force_refresh_remote: bool = False) -> Dict[str, Any]:
    local_data: Dict[str, Any] = {"users": {}}
    try:
        if GAME_SCORE_PATH.exists():
            data = json.loads(GAME_SCORE_PATH.read_text(encoding="utf-8"))
            if isinstance(data, dict):
                local_data = data
    except Exception as exc:
        log_message(f"Could not read game scores: {exc}")
    remote_data = fetch_remote_game_scores(force_refresh=force_refresh_remote)
    merged = merge_score_sources(local_data, remote_data)
    if merged != local_data:
        save_game_scores(merged)
    return merged


def save_game_scores(data: Dict[str, Any]) -> None:
    try:
        GAME_SCORE_PATH.write_text(json.dumps(data, indent=2), encoding="utf-8")
    except Exception as exc:
        log_message(f"Could not write game scores: {exc}")


def upsert_remote_game_score(username: str, score: int, last_updated: str) -> None:
    if not google_scoreboard_is_configured():
        return
    username = string_value(username).strip()
    if not username:
        return
    values_url = f"https://sheets.googleapis.com/v4/spreadsheets/{GOOGLE_SCOREBOARD_SPREADSHEET_ID}/values/{quote(GOOGLE_SCOREBOARD_RANGE, safe='!:\'')}"
    payload = google_sheets_request("GET", values_url)
    values = payload.get("values") or []
    target_row = None
    for idx, row in enumerate(values[1:], start=2):
        if string_value(row[0]).strip().lower() == username.lower():
            target_row = idx
            break
    row_values = [[username, int(score), last_updated]]
    if target_row is None:
        append_url = f"https://sheets.googleapis.com/v4/spreadsheets/{GOOGLE_SCOREBOARD_SPREADSHEET_ID}/values/{quote(GOOGLE_SCOREBOARD_RANGE, safe='!:\'')}:append"
        google_sheets_request("POST", append_url, params={"valueInputOption": "USER_ENTERED", "insertDataOption": "INSERT_ROWS"}, json_payload={"values": row_values})
    else:
        row_range = f"{GOOGLE_SCOREBOARD_TAB_NAME}!A{target_row}:C{target_row}"
        update_url = f"https://sheets.googleapis.com/v4/spreadsheets/{GOOGLE_SCOREBOARD_SPREADSHEET_ID}/values/{quote(row_range, safe='!:\'')}"
        google_sheets_request("PUT", update_url, params={"valueInputOption": "USER_ENTERED"}, json_payload={"values": row_values})
    GOOGLE_SCOREBOARD_CACHE["fetched_at"] = 0.0
    refreshed = fetch_remote_game_scores(force_refresh=True)
    if refreshed is not None:
        save_game_scores(merge_score_sources(load_game_scores(force_refresh_remote=False), refreshed))


def get_game_score_snapshot(force_refresh_remote: bool = False) -> Dict[str, Any]:
    data = load_game_scores(force_refresh_remote=force_refresh_remote)
    users = data.setdefault("users", {})
    username = get_local_username()
    user = users.setdefault(username, {"score": 0})
    leaderboard = sorted(({"user": u, "score": int((v or {}).get("score") or 0)} for u, v in users.items()), key=lambda x: (-x["score"], x["user"].lower()))[:12]
    return {
        "username": username,
        "score": int(user.get("score") or 0),
        "leaderboard": leaderboard,
        "remote_enabled": google_scoreboard_is_configured(),
    }


def update_game_score(delta: int) -> Dict[str, Any]:
    delta = int(delta or 0)
    data = load_game_scores(force_refresh_remote=True)
    users = data.setdefault("users", {})
    username = get_local_username()
    user = users.setdefault(username, {"score": 0})
    user["score"] = max(0, int(user.get("score") or 0) + delta)
    user["last_updated"] = datetime.now(timezone.utc).isoformat()
    save_game_scores(data)
    try:
        upsert_remote_game_score(username, int(user["score"]), user["last_updated"])
    except Exception as exc:
        log_message(f"Google scoreboard update failed; local score was still saved. Error: {exc}")
    snapshot = get_game_score_snapshot(force_refresh_remote=True)
    if GAME_LEADERBOARD_WEBHOOK_URL:
        try:
            requests.post(GAME_LEADERBOARD_WEBHOOK_URL, json={"user": snapshot["username"], "score": snapshot["score"]}, timeout=15)
        except Exception as exc:
            log_message(f"Leaderboard webhook update failed: {exc}")
    return snapshot


def created_sort_key(asset: Dict[str, Any]) -> Tuple[int, float]:
    dt = parse_datetime(asset.get("dateCreated"))
    timestamp = dt.timestamp() if dt else 0.0
    return (1 if is_marked_for_deletion(asset) else 0, -timestamp)


def sort_assets_in_slot(assets: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    return sorted(assets, key=created_sort_key)


def filename_from_original(original_url: str, fallback_name: str) -> str:
    original_url = string_value(original_url)
    if "/original/" in original_url:
        return original_url.split("/original/", 1)[1].split("?", 1)[0].strip() or fallback_name
    return fallback_name

def extension_from_content_type(content_type: str) -> str:
    content_type = string_value(content_type).split(";", 1)[0].strip().lower()
    mapping = {
        "image/jpeg": ".jpg",
        "image/jpg": ".jpg",
        "image/png": ".png",
        "image/webp": ".webp",
        "image/gif": ".gif",
        "image/tiff": ".tif",
        "image/bmp": ".bmp",
        "application/pdf": ".pdf",
    }
    return mapping.get(content_type, "")


def filename_from_content_disposition(content_disposition: str) -> str:
    content_disposition = string_value(content_disposition)
    if not content_disposition:
        return ""
    m = re.search(r"filename\*=UTF-8''([^;]+)", content_disposition)
    if m:
        return unquote(m.group(1))
    m = re.search(r'filename=\"?([^\";]+)', content_disposition)
    if m:
        return m.group(1)
    return ""


def ensure_filename_has_extension(file_name: str, content_type: str = "", original_url: str = "", content_disposition: str = "") -> str:
    name = string_value(file_name) or "asset"
    candidate = filename_from_content_disposition(content_disposition) or name
    suffix = Path(candidate).suffix
    if not suffix and original_url:
        try:
            guessed = Path(original_url.split('?', 1)[0]).suffix
            if guessed:
                suffix = guessed
        except Exception:
            pass
    if not suffix and content_type:
        suffix = extension_from_content_type(content_type)
    if not suffix:
        guessed = mimetypes.guess_extension((string_value(content_type).split(';', 1)[0] or '').strip()) or ''
        suffix = '.jpe' if guessed == '.jpeg' else guessed
    if suffix and not str(candidate).lower().endswith(str(suffix).lower()):
        candidate = f"{Path(candidate).stem or 'asset'}{suffix}"
    return candidate or "asset"


def safe_upload_filename(name: str, fallback_ext: str = ".jpg") -> str:
    cleaned = secure_filename(name or "") or "upload"
    stem = Path(cleaned).stem or "upload"
    ext = Path(cleaned).suffix or fallback_ext
    return f"{stem}{ext}"


def download_source_media_to_tempfile(session: requests.Session, media_id: str, desired_filename: str) -> tuple[Path, tempfile.TemporaryDirectory]:
    fetch_media_by_id(session, media_id)
    original_url = get_media_download_url(session, media_id)
    td = tempfile.TemporaryDirectory(prefix="content_refresher_copy_")
    fallback_ext = Path(desired_filename).suffix or ".jpg"

    def _extract_name_and_ext(resp: requests.Response) -> tuple[str, str]:
        content_disp = resp.headers.get("Content-Disposition", "")
        content_type = resp.headers.get("Content-Type", "")
        server_name = ""
        m = re.search(r"filename\*=UTF-8''([^;]+)", content_disp)
        if m:
            server_name = unquote(m.group(1))
        else:
            m = re.search(r'filename=\"?([^\";]+)', content_disp)
            if m:
                server_name = m.group(1)
        ext = Path(server_name).suffix or Path(desired_filename).suffix or extension_from_content_type(content_type) or fallback_ext
        temp_name = safe_upload_filename(Path(desired_filename).stem + ext, ext)
        return temp_name, ext

    def _write_response(resp: requests.Response) -> Path:
        temp_name, _ = _extract_name_and_ext(resp)
        temp_path = Path(td.name) / temp_name
        with open(temp_path, "wb") as fh:
            for chunk in resp.iter_content(chunk_size=1024 * 1024):
                if chunk:
                    fh.write(chunk)
        return temp_path

    # Fresh presigned S3 URLs are more reliable when fetched with a plain requests call
    # rather than the Bynder session, which may carry extra headers/cookies.
    try:
        with requests.get(original_url, stream=True, timeout=120, allow_redirects=True) as r:
            r.raise_for_status()
            return _write_response(r), td
    except Exception as exc:
        log_message(f"Presigned download failed for {media_id}; retrying via Bynder redirect. Error: {exc}")

    # Fallback: call the Bynder download endpoint directly and follow redirects immediately.
    download_endpoint = f"{BYNDER_BASE_URL}/api/v4/media/{media_id}/download/"
    with session.get(download_endpoint, stream=True, timeout=120, allow_redirects=True) as r:
        r.raise_for_status()
        ctype = (r.headers.get("Content-Type") or "").lower()
        if "application/json" in ctype:
            data = r.json()
            redirect_url = ""
            if isinstance(data, dict):
                for k in ("s3_file", "s3File", "url", "downloadUrl", "download_url", "location"):
                    v = data.get(k)
                    if isinstance(v, str) and v.startswith("http"):
                        redirect_url = v
                        break
                if not redirect_url:
                    for v in data.values():
                        if isinstance(v, str) and v.startswith("http"):
                            redirect_url = v
                            break
            if not redirect_url:
                raise RuntimeError(f"Could not determine redirect URL for media {media_id}")
            with requests.get(redirect_url, stream=True, timeout=120, allow_redirects=True) as r2:
                r2.raise_for_status()
                return _write_response(r2), td
        return _write_response(r), td


def slugify_filename(name: str) -> str:
    clean = re.sub(r"[^A-Za-z0-9._ -]+", "_", name).strip()
    return clean or "content_refresher_log.json"



def option_label_to_id_map(session: requests.Session, metaproperty_id: str) -> Dict[str, str]:
    items = fetch_metaproperty_options(session, metaproperty_id)
    out: Dict[str, str] = {}
    for item in items:
        label = string_value(item.get("label")).strip()
        if label:
            out[label] = string_value(item.get("id"))
        dbn = string_value(item.get("databaseName")).strip()
        if dbn:
            out[dbn] = string_value(item.get("id"))
    return out


def make_option_database_name(label: str) -> str:
    base = re.sub(r"[^A-Za-z0-9]+", "_", string_value(label).strip())
    base = re.sub(r"_+", "_", base).strip("_")
    return base or f"AppOption_{uuid.uuid4().hex[:8]}"


def create_metaproperty_option(session: requests.Session, metaproperty_id: str, label: str) -> Dict[str, str]:
    clean_label = string_value(label).strip()
    if not clean_label:
        raise RuntimeError("Cannot create a blank metaproperty option.")
    database_name = make_option_database_name(clean_label).lower()
    url = f"{BYNDER_BASE_URL}/api/v4/metaproperties/{metaproperty_id}/options/"
    headers = {"Content-Type": "application/x-www-form-urlencoded"}
    payload = {
        "data": json.dumps({
            "name": database_name,
            "label": clean_label,
            "isSelectable": True,
            "zindex": 1,
            "labels": {},
            "externalReference": None,
        })
    }
    errors: List[str] = []
    for attempt in range(1, 4):
        try:
            RATELIMITER.wait()
            response = session.post(url, headers=headers, data=payload, timeout=REQUEST_TIMEOUT)
            if response.status_code == 201:
                try:
                    body = response.json()
                except Exception:
                    body = {}
                option_id = string_value((body or {}).get("id") or (body or {}).get("ID"))
                if option_id:
                    METAPROPERTY_OPTION_VALUE_CACHE.pop(normalize_uuid(metaproperty_id), None)
                    return {"id": option_id, "label": clean_label, "databaseName": database_name}
                refreshed = fetch_metaproperty_options(session, metaproperty_id)
                for item in refreshed:
                    if string_value(item.get("label")).strip().lower() == clean_label.lower():
                        METAPROPERTY_OPTION_VALUE_CACHE.pop(normalize_uuid(metaproperty_id), None)
                        return {
                            "id": string_value(item.get("id")),
                            "label": string_value(item.get("label") or clean_label),
                            "databaseName": string_value(item.get("databaseName") or database_name),
                        }
            if response.status_code == 400:
                try:
                    error_payload = response.json()
                except Exception:
                    error_payload = {}
                message = string_value(error_payload.get("message") or response.text)
                if "already exists" in message.lower():
                    refreshed = fetch_metaproperty_options(session, metaproperty_id)
                    for item in refreshed:
                        if string_value(item.get("label")).strip().lower() == clean_label.lower():
                            METAPROPERTY_OPTION_VALUE_CACHE.pop(normalize_uuid(metaproperty_id), None)
                            return {
                                "id": string_value(item.get("id")),
                                "label": string_value(item.get("label") or clean_label),
                                "databaseName": string_value(item.get("databaseName") or database_name),
                            }
                errors.append(f"{url} [{response.status_code}] {response.text[:240]}")
                continue
            errors.append(f"{url} [{response.status_code}] {response.text[:240]}")
        except Exception as exc:
            errors.append(f"{url} [{type(exc).__name__}] {exc}")
    raise RuntimeError(f"Could not create metaproperty option '{clean_label}'. Details: {' | '.join(errors[-6:])}")


def ensure_metaproperty_option(session: requests.Session, metaproperty_id: str, label: str) -> Dict[str, str]:
    clean_label = string_value(label).strip()
    if not clean_label:
        raise RuntimeError("A metaproperty option label is required.")
    existing = fetch_metaproperty_options(session, metaproperty_id)
    for item in existing:
        if string_value(item.get("label")).strip().lower() == clean_label.lower():
            return {
                "id": string_value(item.get("id")),
                "label": string_value(item.get("label") or clean_label),
                "databaseName": string_value(item.get("databaseName")),
            }
    return create_metaproperty_option(session, metaproperty_id, clean_label)


def parse_component_sku_value(raw_value: Any) -> Tuple[List[str], List[str]]:
    text = string_value(raw_value)
    if not text:
        return [], []
    normalized = text.replace("\n", ";").replace("\r", ";")
    normalized = normalized.replace(",", ";")
    normalized = normalized.replace("; ", ";")
    raw_parts = [p.strip() for p in normalized.split(";")]
    values: List[str] = []
    warnings: List[str] = []
    for idx, part in enumerate(raw_parts):
        if not part:
            warnings.append("Components field contains an empty item.")
            continue
        values.append(part)
    return values, warnings

def group_component_counts(component_skus: List[str]) -> List[Dict[str, Any]]:
    counts: Dict[str, int] = {}
    order: List[str] = []
    for sku in component_skus:
        key = string_value(sku)
        if not key:
            continue
        if key not in counts:
            counts[key] = 0
            order.append(key)
        counts[key] += 1
    return [{"sku": sku, "count": counts[sku]} for sku in order]


def parse_onboarding_paste_rows(raw_text: str, sales_channel_map: Optional[Dict[str, str]] = None) -> Tuple[List[Dict[str, Any]], List[str]]:
    rows: List[Dict[str, Any]] = []
    warnings: List[str] = []
    text = raw_text.replace("\r\n", "\n").replace("\r", "\n").strip("\n")
    if not text.strip():
        raise RuntimeError("Paste STEP Form rows to create a Product Imagery Onboarding board.")
    lines = [line for line in text.split("\n")]
    parsed = [line.split("\t") for line in lines]
    headers = [string_value(x).strip() for x in parsed[0]]
    if not headers:
        raise RuntimeError("Could not read STEP Form header row.")
    header_index = {h: i for i, h in enumerate(headers) if h}
    for req in PIO_REQUIRED_IMPORT_HEADERS:
        if req not in header_index:
            raise RuntimeError(f"Missing required STEP Form column: {req}")
    def cell(parts, col):
        idx = header_index.get(col, -1)
        return string_value(parts[idx]).strip() if 0 <= idx < len(parts) else ""
    sales_channel_map = sales_channel_map or {}
    normalized_sales_map = {string_value(k).strip().lower(): string_value(v).strip() for k, v in sales_channel_map.items() if string_value(k).strip() and string_value(v).strip()}
    for line_no, parts in enumerate(parsed[1:], start=2):
        row = {h: cell(parts, h) for h in headers}
        if not any(string_value(v) for v in row.values()):
            continue
        sku = row.get("SKU", "").strip()
        product_name = row.get("Product Name", "").strip()
        product_color = row.get("Product Color", "").strip()
        raw_sales_channel = row.get("Sales Channel", "").strip()
        sales_channel = normalized_sales_map.get(raw_sales_channel.lower(), raw_sales_channel)
        if not sku or not product_name:
            warnings.append(f"Row {line_no} is missing required values and was skipped.")
            continue
        if sales_channel and sales_channel not in PIO_ALLOWED_SALES_CHANNELS:
            warnings.append(f"Row {line_no} has Sales Channel '{raw_sales_channel}' mapped to invalid Bynder value '{sales_channel}'.")
            continue
        components_raw = row.get("Components", "")
        component_skus, component_warnings = parse_component_sku_value(components_raw)
        for w in component_warnings:
            warnings.append(f"Row {line_no}: {w}")
        rows.append({
            "sku": sku,
            "components_raw": components_raw,
            "component_skus": component_skus,
            "product_name": product_name,
            "product_color": product_color,
            "dim_width": row.get("Width", "").strip(),
            "dim_length": row.get("Length", "").strip(),
            "dim_height": row.get("Height", "").strip(),
            "sales_channel": sales_channel,
            "features": row.get("Features", "").strip(),
        })
    if not rows:
        raise RuntimeError("No valid STEP Form rows were found in the pasted data.")
    return rows, warnings


def pio_base_asset_name(sku: str, slot_key: str, ordinal: int = 1) -> str:
    sku = string_value(sku)
    slot = string_value(slot_key)
    if slot == "SKU_grid":
        lane_name = "grid"
    elif slot == "SKU_dimension":
        lane_name = "dimension"
    elif slot == "SKU_swatch":
        lane_name = "swatch"
    elif slot == "SKU_square":
        lane_name = "square"
    elif re.match(r'^SKU_5\d\d\d$', slot):
        lane_name = "swatchdetail"
    else:
        lane_name = "carousel"
    return f"PIO_{sku}_{lane_name}_{ordinal:02d}"




def pio_slot_ordinal(slot_key: str) -> int:
    slot = string_value(slot_key)
    if slot == 'SKU_grid':
        return 1
    if slot == 'SKU_dimension':
        return 1
    if slot == 'SKU_swatch':
        return 1
    if slot == 'SKU_square':
        return 1
    m = re.match(r'^SKU_(\d+)$', slot)
    if m:
        num = int(m.group(1))
        if 100 <= num < 5000:
            return max(1, num // 100)
        if 5000 <= num < 6000:
            return max(1, ((num - 5000) // 100) + 1)
    return 1

def pio_target_asset_name(sku: str, slot_key: str) -> str:
    stem = pio_base_asset_name(sku, slot_key, pio_slot_ordinal(slot_key))
    return force_jpg_filename(stem, stem)

def create_pio_placeholder_grid_asset(
    session: requests.Session,
    collection_option: Dict[str, str],
    row: Dict[str, Any],
) -> str:
    with tempfile.TemporaryDirectory(prefix="content_refresher_pio_grid_") as td:
        ext = Path(PIO_PLACEHOLDER_GRID_URL.split("?")[0]).suffix or ".jpg"
        temp_path = Path(td) / f"{row['sku']}{ext}"
        resp = requests.get(PIO_PLACEHOLDER_GRID_URL, timeout=REQUEST_TIMEOUT)
        resp.raise_for_status()
        temp_path.write_bytes(resp.content)
        asset_name = pio_base_asset_name(row["sku"], "SKU_grid", 1)
        media_id = upload_new_asset_group_upload(session, temp_path, asset_name)
    metaprops = fetch_metaproperties_map(session)
    fields: List[Tuple[str, Any]] = []
    def set_std(db_name: str, value: Any):
        value_str = string_value(value)
        if not value_str:
            return
        mp = metaprops.get(db_name)
        if not mp:
            return
        mp_id = string_value(mp.get("id"))
        if not mp_id:
            return
        fields.append((f"metaproperty.{mp_id}", value_str))
    def set_opt(db_name: str, value_label: str):
        label = string_value(value_label)
        if not label:
            return
        mp = get_metaproperty_by_candidates(metaprops, db_name, f"property_{db_name}", db_name.lower())
        if not mp:
            return
        mp_id = string_value(mp.get("id"))
        option_id = get_metaproperty_option_value(session, mp_id, label)
        if option_id:
            fields.append((f"metaproperty.{mp_id}", option_id))
    set_std("Product_SKU", row["sku"])
    set_std("Product_Name__STEP_", row["product_name"])
    set_std("Product_Color", row["product_color"])
    set_std("Component_SKUs", ",".join([string_value(x) for x in (row.get("component_skus") or []) if string_value(x)]))
    set_std("dim_Width", row.get("dim_width", ""))
    set_std("dim_Length", row.get("dim_length", ""))
    set_std("dim_Height", row.get("dim_height", ""))
    set_std("Features", row.get("features", ""))
    set_opt("Asset_Type", "Photos")
    set_opt("Asset_Sub-Type", ASSET_SUBTYPE_REQUIRED)
    set_opt("Deliverable", "Product_Grid_Image")
    product_collection_mp = get_metaproperty_by_candidates(metaprops, "product_collection", "Product_Collection", "property_product_collection")
    if product_collection_mp and string_value(collection_option.get("id")):
        fields.append((f"metaproperty.{string_value(product_collection_mp.get('id'))}", string_value(collection_option.get("id"))))
    else:
        set_opt("product_collection", collection_option["label"])
    set_opt("Sales_Channel", row["sales_channel"])
    set_opt("Sync_to_Site", PIO_SYNC_DO_NOT)
    set_opt("Workflow", PIO_WORKFLOW_VALUE)
    set_opt("Workflow_Status", PIO_STATUS_LAUNCHED)
    set_std("Product_SKU_Position", f"{row['sku']}_grid")
    if fields:
        post_media_fields(session, media_id, fields)
    return media_id


def append_pio_board_fields(
    session: requests.Session,
    fields: List[Tuple[str, Any]],
    metaprops_by_dbname: Dict[str, Dict[str, Any]],
    row: Dict[str, Any],
    target_position: str,
) -> None:
    def _set_std(*db_candidates: str, value: Any):
        value_str = string_value(value)
        if not value_str:
            return
        mp = get_metaproperty_by_candidates(metaprops_by_dbname, *db_candidates)
        if not mp:
            return
        mp_id = string_value(mp.get("id"))
        if mp_id:
            fields.append((f"metaproperty.{mp_id}", value_str))

    def _set_opt(value_label: str, *db_candidates: str):
        label = string_value(value_label)
        if not label:
            return
        mp = get_metaproperty_by_candidates(metaprops_by_dbname, *db_candidates)
        if not mp:
            return
        mp_id = string_value(mp.get("id"))
        if not mp_id:
            return
        option_id = get_metaproperty_option_value(session, mp_id, label)
        if option_id:
            fields.append((f"metaproperty.{mp_id}", option_id))

    _set_opt("Photos", "Asset_Type", "property_Asset_Type")
    _set_opt(ASSET_SUBTYPE_REQUIRED, "Asset_Sub-Type", "Asset_Sub_Type", "property_Asset_Sub-Type")
    _set_opt(PIO_WORKFLOW_VALUE, "Workflow", "property_Workflow")
    _set_opt(row.get("workflow_status") or PIO_STATUS_LAUNCHED, "Workflow_Status", "property_Workflow_Status")
    _set_opt(row.get("sync_to_site") or PIO_SYNC_DO_NOT, "Sync_to_Site", "property_Sync_to_Site")
    collection_label = row.get("product_collection") or row.get("collection") or ''
    product_collection_mp = get_metaproperty_by_candidates(metaprops_by_dbname, "product_collection", "Product_Collection", "property_product_collection")
    if product_collection_mp and string_value(collection_label):
        mp_id = string_value(product_collection_mp.get("id"))
        option_id = get_metaproperty_option_value(session, mp_id, collection_label)
        if option_id:
            fields.append((f"metaproperty.{mp_id}", option_id))
    _set_std("Product_SKU", target_sku := string_value(row.get("sku")))
    _set_std("Product_SKU_Position", target_position)
    _set_std("Product_Name__STEP_", row.get("product_name"))
    _set_std("Product_Color", row.get("product_color"))
    _set_std("Component_SKUs", row.get("components_raw") or ",".join([string_value(x) for x in safe_list(row.get("component_skus")) if string_value(x)]))
    _set_std("dim_Length", row.get("dim_length"))
    _set_std("dim_Width", row.get("dim_width"))
    _set_std("dim_Height", row.get("dim_height"))
    _set_std("Features", row.get("features"))
    _set_opt(row.get("sales_channel"), "Sales_Channel", "property_Sales_Channel")


def wait_for_pio_placeholder_ready(session: requests.Session, media_id: str, row_sku: str, collection_label: str, attempts: int = 12, sleep_seconds: float = 2.0) -> Dict[str, Any]:
    expected_position = f"{row_sku}_grid"
    last_media: Dict[str, Any] = {}
    for attempt in range(1, attempts + 1):
        media = fetch_media_by_id(session, media_id)
        last_media = media
        if (
            is_product_site_asset(media)
            and string_value(prop(media, "Product_SKU", "Product_SKU")) == string_value(row_sku)
            and string_value(prop(media, "Product_SKU_Position", "Product_SKU_Position")) == expected_position
            and string_value(prop(media, "Product_Collection", "product_collection") or "").strip().lower() == string_value(collection_label).strip().lower()
        ):
            return media
        if attempt < attempts:
            time.sleep(sleep_seconds)
    return last_media


def fetch_pio_grid_assets(session: requests.Session) -> List[Dict[str, Any]]:
    workflow_option_id = PIO_WORKFLOW_OPTION_ID
    if not workflow_option_id:
        return []
    try:
        workflow_items = fetch_all_media_for_option(session, workflow_option_id)
    except Exception:
        workflow_items = []
    results = []
    for asset in workflow_items:
        if not is_product_site_asset(asset):
            continue
        deliverable_value = compact_text(prop(asset, "Deliverable", "Deliverable"))
        if deliverable_value not in {compact_text("Product_Grid_Image"), compact_text("Product Grid Image")}:
            continue
        workflow_value = compact_text(prop(asset, "Workflow", "Workflow"))
        if workflow_value and workflow_value != compact_text(PIO_WORKFLOW_VALUE):
            continue
        results.append(asset)
    return results


def build_onboarding_collection_summaries(session: requests.Session) -> List[Dict[str, Any]]:
    workflow_items = fetch_pio_grid_assets(session)
    grouped: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for asset in workflow_items:
        collection_value = string_value(prop(asset, "Product_Collection", "product_collection") or prop(asset, "product_collection", "product_collection"))
        label = string_value(collection_value)
        if not label:
            continue
        grouped[label].append(asset)
    summaries: List[Dict[str, Any]] = []
    for label, grid_assets in grouped.items():
        statuses = sorted({prop(a, "Workflow_Status", "Workflow_Status") for a in grid_assets if prop(a, "Workflow_Status", "Workflow_Status")})
        sync_states = sorted({prop(a, "Sync_to_Site", "Sync_to_Site") for a in grid_assets if prop(a, "Sync_to_Site", "Sync_to_Site")})
        latest_dt = max((parse_datetime(a.get("dateCreated")) or datetime.min) for a in grid_assets)
        colors = sorted({string_value(prop(a, 'Product_Color', 'Product_Color')) for a in grid_assets if string_value(prop(a, 'Product_Color', 'Product_Color'))})
        label_display = label + (f" ({', '.join(colors)})" if colors else '')
        summaries.append({
            "id": label,
            "label": label,
            "label_display": label_display,
            "colors": colors,
            "row_count": len({prop(a, "Product_SKU", "Product_SKU") for a in grid_assets if prop(a, "Product_SKU", "Product_SKU")}),
            "workflow_statuses": statuses,
            "sync_states": sync_states,
            "latest": latest_dt.isoformat() if latest_dt != datetime.min else "",
        })
    summaries.sort(key=lambda x: x["label"].lower())
    return summaries




def ensure_row_has_minimum_slots(row: Dict[str, Any], core_slots: List[str], swatch_slots: List[str]) -> None:
    buckets = bucket_assets(row)
    existing_positions = {normalize_position_for_row(a.get('current_position') or a.get('position') or get_asset_position(a), row.get('sku') or '') for a in row.get('assets', [])}
    for slot in core_slots:
        if slot not in existing_positions:
            row.setdefault('assets', []).append(build_empty_slot_placeholder(row, 'core', slot))
    for slot in swatch_slots:
        if slot not in existing_positions:
            row.setdefault('assets', []).append(build_empty_slot_placeholder(row, 'swatch_detail', slot))

def build_empty_slot_placeholder(row: Dict[str, Any], lane: str, slot: str) -> Dict[str, Any]:
    return {'id': f"empty::{row.get('sku')}::{slot}", 'row_id': row.get('row_id'), 'sku': row.get('sku'), 'lane': lane, 'slot_key': slot, 'current_position': exact_position_for_row(string_value(row.get('sku')), slot), 'position': exact_position_for_row(string_value(row.get('sku')), slot), 'file_name':'', 'name':'', 'is_empty_slot':True, 'is_marked_for_deletion':False, 'original_state': {'position':'', 'is_marked_for_deletion':False}}

def build_onboarding_board_for_collection(session: requests.Session, collection_option: Dict[str, str], force_refresh: bool = False) -> Dict[str, Any]:
    collection_option_id = product_collection_option_id = string_value(collection_option.get("id"))
    collection_label = string_value(collection_option.get("label"))

    board_cache = STATE.setdefault("collection_board_cache", {})
    cache_key = f"pio::{collection_option_id or collection_label}"
    if force_refresh:
        board_cache.pop(cache_key, None)
    else:
        cached_board = get_fresh_cached_value(
            board_cache,
            cache_key,
            COLLECTION_BOARD_CACHE_MAX_AGE_SECONDS,
            cache_label="collection board",
        )
        if cached_board is not None:
            log_message(f"Using cached board for {collection_label}.")
            return cached_board

    workflow_grid_assets = fetch_pio_grid_assets(session)
    grid_candidates = []
    for asset in workflow_grid_assets:
        asset_collection = string_value(prop(asset, "Product_Collection", "product_collection") or prop(asset, "product_collection", "product_collection"))
        asset_collection_label = string_value(asset_collection)
        if compact_text(asset_collection_label) == compact_text(collection_label) or compact_text(asset_collection) == compact_text(collection_option_id):
            grid_candidates.append(asset)

    grid_assets_by_sku = defaultdict(list)
    for asset in grid_candidates:
        sku = prop(asset, "Product_SKU", "Product_SKU")
        if sku:
            grid_assets_by_sku[sku].append(asset)

    unique_skus = sorted(grid_assets_by_sku.keys(), key=natural_sort_key)
    log_message(f"Grid anchor SKU count for {collection_label}: {len(unique_skus)}")

    all_assets_by_sku: Dict[str, List[Dict[str, Any]]] = {}
    def asset_worker(sku: str) -> Tuple[str, List[Dict[str, Any]]]:
        items = fetch_assets_for_product_sku(session, "Product_SKU", sku)
        filtered = [a for a in items if is_board_relevant_asset(a, sku)]
        return sku, filtered

    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = {executor.submit(asset_worker, sku): sku for sku in unique_skus}
        for future in as_completed(futures):
            sku, items = future.result()
            all_assets_by_sku[sku] = items
            log_message(f"Fetched all board PSAs for SKU {sku}: {len(items)}")

    rows_by_color: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = {
            executor.submit(build_board_row_from_prefetched_assets, session, sku, all_assets_by_sku.get(sku, []), collection_label, False): sku
            for sku in unique_skus
        }
        for future in as_completed(futures):
            row = future.result()
            if not row:
                continue
            if compact_text(row.get("workflow")) != compact_text(PIO_WORKFLOW_VALUE):
                continue
            row["inactive"] = False
            rows_by_color[string_value(row.get("product_color"))].append(row)

    color_sections = []
    latest_edit = None
    statuses = set()
    sync_states = set()
    for color in sorted(rows_by_color.keys(), key=lambda c: (c or "").lower()):
        section_rows = list(rows_by_color[color])
        section_rows.sort(key=lambda r: (natural_sort_key(r.get("sku") or ""), (r.get("product_name") or "").lower()))
        color_sections.append({"color": color, "rows": section_rows, "photo_available_count": 0})
        for row in section_rows:
            statuses.add(string_value(row.get("workflow_status")))
            sync_states.add(string_value(row.get("sync_to_site")))
            dt = parse_datetime(row.get("date_newest"))
            if dt and (latest_edit is None or dt > latest_edit):
                latest_edit = dt

    board = {
        "collection": collection_option,
        "collection_label": collection_label,
        "loaded_at": datetime.now().isoformat(),
        "color_sections": color_sections,
        "workspace": WORKSPACE_PIO,
        "is_onboarding": True,
        "workflow_statuses": [s for s in sorted(statuses) if s],
        "sync_states": [s for s in sorted(sync_states) if s],
        "latest_edit": latest_edit.isoformat() if latest_edit else "",
    }
    refresh_row_component_links(board)
    set_timed_cached_value(board_cache, cache_key, board)
    return board

def build_onboarding_board_from_created_rows(session: requests.Session, collection_option: Dict[str, str], created_rows: List[Dict[str, Any]]) -> Dict[str, Any]:
    rows_by_color: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    statuses = set()
    sync_states = set()
    latest_edit = None
    for created in created_rows:
        media = created.get("media") or {}
        row = build_board_row_from_prefetched_assets(session, string_value(created.get("sku")), [media], collection_option.get("label") or "")
        if not row:
            continue
        seed = created.get("seed_row") or {}
        if not string_value(row.get("product_name")):
            row["product_name"] = string_value(seed.get("product_name"))
        if not string_value(row.get("product_color")):
            row["product_color"] = string_value(seed.get("product_color"))
        if not string_value(row.get("sales_channel")):
            row["sales_channel"] = string_value(seed.get("sales_channel"))
        if not string_value(row.get("dim_length")):
            row["dim_length"] = string_value(seed.get("dim_length"))
        if not string_value(row.get("dim_width")):
            row["dim_width"] = string_value(seed.get("dim_width"))
        if not string_value(row.get("dim_height")):
            row["dim_height"] = string_value(seed.get("dim_height"))
        if not row.get("component_groups") and seed.get("component_skus"):
            row["component_groups"] = [{"sku": string_value(s), "count": 1} for s in (seed.get("component_skus") or []) if string_value(s)]
        row["inactive"] = False
        color = string_value(row.get("product_color"))
        rows_by_color[color].append(row)
        statuses.add(string_value(row.get("workflow_status")))
        sync_states.add(string_value(row.get("sync_to_site")))
        dt = parse_datetime(row.get("date_newest"))
        if dt and (latest_edit is None or dt > latest_edit):
            latest_edit = dt
    color_sections = []
    for color in sorted(rows_by_color.keys(), key=lambda c: (c or "").lower()):
        section_rows = list(rows_by_color[color])
        section_rows.sort(key=lambda r: (bool(r.get("inactive")), natural_sort_key(r.get("sku") or ""), (r.get("product_name") or "").lower()))
        color_sections.append({
            "color": color,
            "rows": section_rows,
            "photo_available_count": 0,
        })
    board = {
        "collection": collection_option,
        "collection_label": string_value(collection_option.get("label")),
        "loaded_at": datetime.now().isoformat(),
        "color_sections": color_sections,
        "workspace": WORKSPACE_PIO,
        "is_onboarding": True,
        "workflow_statuses": [s for s in sorted(statuses) if s],
        "sync_states": [s for s in sorted(sync_states) if s],
        "latest_edit": latest_edit.isoformat() if latest_edit else "",
    }
    refresh_row_component_links(board)
    return board


def refresh_row_component_links(board: Dict[str, Any]) -> None:
    if not board:
        return
    sku_index: Dict[str, Dict[str, Any]] = {}
    for section in board.get("color_sections", []):
        for row in section.get("rows", []):
            sku_index[string_value(row.get("sku"))] = row
    for section in board.get("color_sections", []):
        for row in section.get("rows", []):
            comp_groups = []
            warnings = list(row.get("component_warnings") or [])
            for group in row.get("component_groups") or []:
                sku = string_value(group.get("sku"))
                linked = sku_index.get(sku)
                if not sku:
                    continue
                malformed = len(sku) != 9
                if malformed:
                    warnings.append(f"Component '{sku}' is malformed.")
                if sku == string_value(row.get("sku")):
                    warnings.append(f"Component '{sku}' matches the parent SKU.")
                if linked is None:
                    warnings.append(f"Component '{sku}' is not present on this board.")
                comp_groups.append({
                    "sku": sku,
                    "count": int(group.get("count") or 1),
                    "product_name": string_value((linked or {}).get("product_name")),
                    "grid_thumb": first_grid_thumb((linked or {})),
                })
            row["component_display_groups"] = comp_groups
            deduped = []
            seen = set()
            for w in warnings:
                if w not in seen:
                    seen.add(w)
                    deduped.append(w)
            row["component_warnings"] = deduped


def first_grid_thumb(row: Dict[str, Any]) -> str:
    if not row:
        return ""
    for asset in row.get("assets", []):
        if string_value(asset.get("slot_key")) == GRID_SLOT and string_value(asset.get("lane")) == "grid":
            return string_value(asset.get("transformBaseUrl"))
    return ""

# ============================================================
# HELPERS - BYNDER SESSION AND REQUESTS
# ============================================================
def load_bynder_token(token_path: str) -> str:
    with open(token_path, "r", encoding="utf-8") as f:
        data = json.load(f)
    token = data.get("permanent_token") or data.get("access_token")
    if not token:
        raise ValueError("No token found in credentials file. Expected 'permanent_token' or 'access_token'.")
    return token


def make_session(token: str) -> requests.Session:
    session = requests.Session()
    session.headers.update(
        {
            "Authorization": f"Bearer {token}",
            "Accept": "application/json",
        }
    )
    return session


def get_session() -> requests.Session:
    token = load_bynder_token(BYNDER_TOKEN_PATH)
    return make_session(token)


def request_with_retries(session: requests.Session, method: str, url: str, **kwargs) -> requests.Response:
    for attempt in range(1, MAX_RETRIES + 1):
        try:
            RATELIMITER.wait()
            response = session.request(method, url, timeout=REQUEST_TIMEOUT, **kwargs)

            if response.status_code == 429:
                retry_after = response.headers.get("Retry-After")
                sleep_time = float(retry_after) if retry_after else min(60, (2 ** attempt) + random.uniform(0.25, 1.5))
                log_message(f"429 received for {url}. Sleeping {sleep_time:.2f}s.")
                time.sleep(sleep_time)
                continue

            if 500 <= response.status_code < 600:
                sleep_time = min(60, (2 ** attempt) + random.uniform(0.25, 1.5))
                log_message(f"Server error {response.status_code} for {url}. Sleeping {sleep_time:.2f}s.")
                time.sleep(sleep_time)
                continue

            response.raise_for_status()
            return response
        except requests.RequestException as exc:
            if attempt == MAX_RETRIES:
                raise
            sleep_time = min(60, (2 ** attempt) + random.uniform(0.25, 1.5))
            log_message(f"Request failed on attempt {attempt} for {url}: {exc}. Sleeping {sleep_time:.2f}s.")
            time.sleep(sleep_time)

    raise RuntimeError(f"Failed request after {MAX_RETRIES} attempts: {url}")


def extract_media_items(payload: Any) -> List[Dict[str, Any]]:
    if isinstance(payload, list):
        return payload
    if isinstance(payload, dict):
        for key in ["items", "results", "media"]:
            if key in payload and isinstance(payload[key], list):
                return payload[key]
    return []


def get_media_count_for_option(session: requests.Session, option_id: str) -> int:
    url = f"{BYNDER_BASE_URL}/api/v4/media/"
    params = {"propertyOptionId": option_id, "limit": 1, "total": 1}
    response = request_with_retries(session, "GET", url, params=params)
    payload = response.json()
    return int(payload.get("total", {}).get("count", 0))


def fetch_media_page_for_option(session: requests.Session, option_id: str, page: int, limit: int = PAGE_LIMIT) -> List[Dict[str, Any]]:
    url = f"{BYNDER_BASE_URL}/api/v4/media/"
    params = {"propertyOptionId": option_id, "limit": limit, "page": page}
    response = request_with_retries(session, "GET", url, params=params)
    return extract_media_items(response.json())


def fetch_all_media_for_option(session: requests.Session, option_id: str, limit: int = PAGE_LIMIT) -> List[Dict[str, Any]]:
    expected_count = get_media_count_for_option(session, option_id)
    log_message(f"Expected asset count for option {option_id}: {expected_count}")
    if expected_count == 0:
        return []

    total_pages = math.ceil(expected_count / limit)
    all_items: List[Dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        futures = {
            executor.submit(fetch_media_page_for_option, session, option_id, page, limit): page
            for page in range(1, total_pages + 1)
        }
        for future in as_completed(futures):
            page = futures[future]
            page_items = future.result()
            all_items.extend(page_items)
            log_message(f"Fetched page {page}/{total_pages} for option {option_id}: {len(page_items)} assets")

    deduped = {}
    for item in all_items:
        media_id = string_value(item.get("id"))
        if media_id:
            deduped[media_id] = item
    final_items = list(deduped.values())
    log_message(f"Retrieved {len(final_items)} unique assets for option {option_id}")
    return final_items


def resolve_database_name_for_metaproperty(session: requests.Session, metaproperty_id: str, fallback: str) -> str:
    target = normalize_uuid(metaproperty_id)
    if target in METAPROPERTY_DBNAME_CACHE:
        return METAPROPERTY_DBNAME_CACHE[target]

    candidate_urls = [
        f"{BYNDER_BASE_URL}/api/v4/metaproperties/{metaproperty_id}/",
        f"{BYNDER_BASE_URL}/api/v4/meta/properties/{metaproperty_id}/",
        f"{BYNDER_BASE_URL}/api/v4/metaproperties/{metaproperty_id}",
        f"{BYNDER_BASE_URL}/api/v4/meta/properties/{metaproperty_id}",
    ]
    for url in candidate_urls:
        try:
            response = request_with_retries(session, "GET", url)
            payload = response.json()
            record = payload if isinstance(payload, dict) else {}
            db_name = record.get("databaseName") or record.get("database_name") or record.get("name")
            if db_name:
                METAPROPERTY_DBNAME_CACHE[target] = str(db_name)
                log_message(f"Resolved metaproperty {metaproperty_id} to database name {db_name}")
                return str(db_name)
        except Exception as exc:
            log_message(f"Metaproperty lookup failed at {url}: {exc}")

    log_message(f"Could not resolve metaproperty {metaproperty_id}; falling back to {fallback}")
    METAPROPERTY_DBNAME_CACHE[target] = fallback
    return fallback


def _extract_option_items(payload: Any) -> List[Dict[str, Any]]:
    if isinstance(payload, list):
        return payload
    if isinstance(payload, dict):
        for key in ["items", "results", "data", "options", "records", "values"]:
            if isinstance(payload.get(key), list):
                return payload[key]
        if payload.get("id") or payload.get("ID"):
            return [payload]
    return []


def _derive_option_label(item: Dict[str, Any]) -> str:
    labels = item.get("labels")
    if isinstance(labels, dict):
        for key in ["en_US", "en-us", "en", "default"]:
            if labels.get(key):
                return string_value(labels.get(key))
        for value in labels.values():
            label = string_value(value)
            if label:
                return label
    for key in ["label", "displayName", "display_name", "name", "text", "value"]:
        label = string_value(item.get(key))
        if label:
            if key == "name" and "_" in label and not string_value(item.get("label")) and not string_value(item.get("displayName")):
                # Humanize a normalized fallback if that's all the API gives us.
                return label.replace("_", " ")
            return label
    db_name = string_value(item.get("databaseName") or item.get("database_name"))
    return db_name.replace("_", " ") if db_name else ""


def fetch_metaproperty_options(session: requests.Session, metaproperty_id: str) -> List[Dict[str, Any]]:
    candidate_urls = [
        f"{BYNDER_BASE_URL}/api/v4/metaproperties/{metaproperty_id}/options/",
        f"{BYNDER_BASE_URL}/api/v4/meta/properties/{metaproperty_id}/options/",
        f"{BYNDER_BASE_URL}/api/v4/metaproperties/{metaproperty_id}/options",
        f"{BYNDER_BASE_URL}/api/v4/meta/properties/{metaproperty_id}/options",
    ]

    for url in candidate_urls:
        try:
            page = 1
            limit = 1000
            normalized_by_id: Dict[str, Dict[str, str]] = {}
            while True:
                params = {"page": page, "limit": limit, "total": 1}
                response = request_with_retries(session, "GET", url, params=params)
                payload = response.json()
                items = _extract_option_items(payload)
                if not items:
                    break

                for item in items:
                    option_id = item.get("id") or item.get("ID")
                    if not option_id:
                        continue
                    label = _derive_option_label(item)
                    database_name = string_value(item.get("databaseName") or item.get("database_name") or item.get("name"))
                    normalized_by_id[str(option_id)] = {
                        "id": str(option_id),
                        "label": label or database_name or str(option_id),
                        "databaseName": database_name or (label or '').replace(' ', '_'),
                    }

                total_obj = payload.get("total") if isinstance(payload, dict) else None
                total_count = None
                if isinstance(total_obj, dict) and total_obj.get("count") is not None:
                    try:
                        total_count = int(total_obj.get("count"))
                    except Exception:
                        total_count = None

                if total_count is not None and len(normalized_by_id) >= total_count:
                    break
                if len(items) < limit:
                    break
                page += 1

            if normalized_by_id:
                normalized = sorted(normalized_by_id.values(), key=lambda x: x["label"].lower())
                return normalized
        except Exception as exc:
            log_message(f"Option retrieval failed at {url}: {exc}")
    raise RuntimeError(f"Unable to retrieve options for metaproperty {metaproperty_id}")


def get_metaproperty_option_value(session: requests.Session, metaproperty_id: str, label_or_dbname: str) -> str:
    target = normalize_uuid(metaproperty_id)
    cache = METAPROPERTY_OPTION_VALUE_CACHE.get(target)
    if cache is None:
        cache = {}
        for item in fetch_metaproperty_options(session, metaproperty_id):
            item_id = string_value(item.get("id"))
            if not item_id:
                continue
            label = string_value(item.get("label")).strip().lower()
            db_name = string_value(item.get("databaseName")).strip().lower()
            if label:
                cache[label] = item_id
            if db_name:
                cache[db_name] = item_id
        METAPROPERTY_OPTION_VALUE_CACHE[target] = cache

    key = string_value(label_or_dbname).strip().lower()
    return cache.get(key, "")


def fetch_assets_for_product_sku(session: requests.Session, product_sku_db_name: str, sku_value: str) -> List[Dict[str, Any]]:
    url = f"{BYNDER_BASE_URL}/api/v4/media/"
    params = {f"property_{product_sku_db_name}": sku_value, "limit": 1000, "page": 1}
    response = request_with_retries(session, "GET", url, params=params)
    payload = response.json()
    items = extract_media_items(payload)
    return items



def update_asset_metadata(session: requests.Session, media_id: str, field_values: Dict[str, str]) -> Dict[str, Any]:
    url = f"{BYNDER_BASE_URL}/api/v4/media/{media_id}/"
    response = request_with_retries(session, "POST", url, data=field_values)
    try:
        payload = response.json()
    except Exception:
        payload = {"text": response.text}
    return {"status_code": response.status_code, "payload": payload}


def post_media_fields(session: requests.Session, media_id: str, fields: List[Tuple[str, Any]]) -> Dict[str, Any]:
    url = f"{BYNDER_BASE_URL}/api/v4/media/{media_id}/"
    response = request_with_retries(session, "POST", url, data=fields)
    try:
        payload = response.json()
    except Exception:
        payload = {"text": response.text}
    return {"status_code": response.status_code, "payload": payload}


def fetch_media_by_id(session: requests.Session, media_id: str) -> Dict[str, Any]:
    url = f"{BYNDER_BASE_URL}/api/v4/media/{media_id}/"
    response = request_with_retries(session, "GET", url, params={"include": "relatedAssets"})
    return response.json()


def fetch_metaproperties_map(session: requests.Session) -> Dict[str, Dict[str, Any]]:
    url = f"{BYNDER_BASE_URL}/api/v4/metaproperties/"
    response = request_with_retries(session, "GET", url, params={"options": 0})
    payload = response.json()
    mp_map: Dict[str, Dict[str, Any]] = {}
    if isinstance(payload, dict):
        for key, mp in payload.items():
            if not isinstance(mp, dict):
                continue
            db = string_value(mp.get("databaseName") or mp.get("database_name") or key)
            mp_id = string_value(mp.get("id"))
            if db and mp_id:
                mp_map[db] = mp
    elif isinstance(payload, list):
        for mp in payload:
            if not isinstance(mp, dict):
                continue
            db = string_value(mp.get("databaseName") or mp.get("database_name"))
            mp_id = string_value(mp.get("id"))
            if db and mp_id:
                mp_map[db] = mp
    return mp_map


def get_metaproperty_by_candidates(metaprops_by_dbname: Dict[str, Dict[str, Any]], *candidates: str) -> Optional[Dict[str, Any]]:
    for candidate in candidates:
        mp = metaprops_by_dbname.get(candidate)
        if mp:
            return mp
    normalized_targets = {string_value(c).strip().lower() for c in candidates if string_value(c).strip()}
    for key, mp in metaprops_by_dbname.items():
        if string_value(key).strip().lower() in normalized_targets:
            return mp
    return None


def get_media_download_url(session: requests.Session, media_id: str) -> str:
    url = f"{BYNDER_BASE_URL}/api/v4/media/{media_id}/download/"
    response = request_with_retries(session, "GET", url)
    data = response.json()
    if isinstance(data, dict):
        for k in ("s3_file", "s3File", "url", "downloadUrl", "download_url", "location"):
            v = data.get(k)
            if isinstance(v, str) and v.startswith("http"):
                return v
        for v in data.values():
            if isinstance(v, str) and v.startswith("http"):
                return v
    raise RuntimeError(f"Could not determine download URL for media {media_id}")


def map_photo_image_type_to_psa_label(image_type: Any) -> str:
    return PHOTO_TO_PSA_IMAGE_TYPE_MAP.get(string_value(image_type).strip(), "")


def get_existing_psa_image_type_label(asset: Dict[str, Any]) -> str:
    value = asset.get(f"property_{PSA_IMAGE_TYPE_DBNAME}")
    if isinstance(value, list):
        return string_value(value[0]) if value else ""
    return string_value(value)


def append_psa_image_type_field(
    session: requests.Session,
    fields: List[Tuple[str, Any]],
    metaprops_by_dbname: Dict[str, Dict[str, Any]],
    psa_image_type_label: str,
) -> None:
    label = string_value(psa_image_type_label).strip()
    if not label:
        return
    mp = metaprops_by_dbname.get(PSA_IMAGE_TYPE_DBNAME)
    if not mp:
        raise RuntimeError(f"Could not find metaproperty {PSA_IMAGE_TYPE_DBNAME}.")
    mp_id = string_value(mp.get("id"))
    if not mp_id:
        raise RuntimeError(f"Metaproperty {PSA_IMAGE_TYPE_DBNAME} is missing an id.")
    option_value = get_metaproperty_option_value(session, mp_id, label)
    if not option_value:
        raise RuntimeError(f"Could not resolve PSA Image Type option '{label}'.")
    fields.append((f"metaproperty.{mp_id}", option_value))


def get_deliverable_override_for_target(target_lane: str, target_slot: str) -> str:
    lane = string_value(target_lane)
    slot = string_value(target_slot)
    if lane == "core":
        return "Product_Image_Carousel"
    if lane == "swatch_detail":
        return "Product_Swatch_Detail_Image"
    return DELIVERABLE_BY_LANE_SLOT.get((lane, slot), "")


def expected_deliverable_for_asset(asset: Dict[str, Any], row_sku: str = "") -> str:
    lane = string_value(asset.get("lane"))
    slot = string_value(asset.get("slot_key")) or normalize_position_for_row(
        asset.get("last_nontrash_position") or asset.get("current_position") or get_asset_position(asset),
        row_sku or string_value(asset.get("sku")) or prop(asset, "Product_SKU", "Product_SKU"),
    )
    if lane == "off_pattern" or lane == "trash":
        return ""
    if lane == "core":
        return "Product_Image_Carousel"
    if lane == "swatch_detail":
        return "Product_Swatch_Detail_Image"
    return DELIVERABLE_BY_LANE_SLOT.get((lane, slot), "")


def append_deliverable_field(
    session: requests.Session,
    fields: List[Tuple[str, Any]],
    metaprops_by_dbname: Dict[str, Dict[str, Any]],
    deliverable_label: str,
) -> None:
    label = string_value(deliverable_label).strip()
    if not label:
        return
    mp = metaprops_by_dbname.get("Deliverable")
    if not mp:
        raise RuntimeError("Could not find metaproperty Deliverable.")
    mp_id = string_value(mp.get("id"))
    if not mp_id:
        raise RuntimeError("Metaproperty Deliverable is missing an id.")
    option_value = get_metaproperty_option_value(session, mp_id, label)
    if not option_value:
        raise RuntimeError(f"Could not resolve Deliverable option '{label}'.")
    fields.append((f"metaproperty.{mp_id}", option_value))


def set_media_deliverable(session: requests.Session, media_id: str, deliverable_label: str) -> None:
    metaprops_by_dbname = fetch_metaproperties_map(session)
    fields: List[Tuple[str, Any]] = []
    append_deliverable_field(session, fields, metaprops_by_dbname, deliverable_label)
    if fields:
        post_media_fields(session, media_id, fields)


def set_media_psa_image_type(session: requests.Session, media_id: str, psa_image_type_label: str) -> None:
    metaprops_by_dbname = fetch_metaproperties_map(session)
    fields: List[Tuple[str, Any]] = []
    append_psa_image_type_field(session, fields, metaprops_by_dbname, psa_image_type_label)
    if fields:
        post_media_fields(session, media_id, fields)


def get_original_image_bytes(session: requests.Session, media_id: str) -> bytes:
    cache = STATE.setdefault("photo_image_cache", {})
    if media_id in cache:
        return cache[media_id]
    url = get_media_download_url(session, media_id)
    resp = requests.get(url, timeout=REQUEST_TIMEOUT)
    resp.raise_for_status()
    cache[media_id] = resp.content
    return resp.content


def open_image_from_media(session: requests.Session, media_id: str) -> Image.Image:
    data = get_original_image_bytes(session, media_id)
    im = Image.open(BytesIO(data))
    im.load()
    if im.mode not in ("RGB", "RGBA"):
        im = im.convert("RGB")
    return im


def prep_square_output_size(src_w: int, src_h: int) -> tuple[int, int]:
    side = max(1, min(int(src_w or 0), int(src_h or 0)))
    output_side = 1000 if side < 1000 else side
    return (output_side, output_side)


def effective_psa_image_type_for_target(target_lane: str, target_slot: str, current_override: str = "") -> str:
    override = string_value(current_override).strip()
    if override:
        return override
    if string_value(target_lane) == "special" and string_value(target_slot) == "SKU_swatch":
        return SWATCH_PSA_IMAGE_TYPE_LABEL
    if string_value(target_lane) == "special" and string_value(target_slot) == "SKU_dimension":
        return DIMENSIONS_PSA_IMAGE_TYPE_LABEL
    if string_value(target_lane) == "special" and string_value(target_slot) == "SKU_square":
        return SQUARE_PSA_IMAGE_TYPE_LABEL
    return ""


def parse_target_size(size_text: str) -> tuple[int, int]:
    m = re.match(r"^(\d+)x(\d+)$", string_value(size_text))
    if not m:
        return (3000, 1688)
    return (int(m.group(1)), int(m.group(2)))


def prep_mode_to_size(mode: str) -> tuple[int, int]:
    mode = string_value(mode)
    if mode == "original":
        return (0, 0)
    if mode == "crop_square":
        return (1000, 1000)
    if mode in {"crop_swatch", "pick_swatch"}:
        return (163, 163)
    if mode in ("crop_2200", "pad_tb_2200"):
        return (3000, 2200)
    if mode == "crop_remove_sides_1688":
        return (3000, 1688)
    return (3000, 1688)


def clamp(n: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, n))


def get_default_offset_y(src_w: int, src_h: int, out_w: int, out_h: int) -> int:
    if not src_w or not src_h:
        return 0
    scaled_h = int(round(src_h * (out_w / src_w)))
    return max(0, (scaled_h - out_h) // 2)


def get_square_crop_bounds(src_w: int, src_h: int, offset_x: int | float | None = None) -> tuple[int, int, int, int]:
    if not src_w or not src_h:
        return (0, 0, 1, 1)
    side = min(src_w, src_h)
    max_off_x = max(0, src_w - side)
    if offset_x is None:
        left = max_off_x // 2
    else:
        left = int(round(float(offset_x)))
    left = int(clamp(left, 0, max_off_x))
    top = max(0, (src_h - side) // 2)
    return (left, top, left + side, top + side)


def get_swatch_crop_bounds(
    src_w: int,
    src_h: int,
    offset_x: int | float | None = None,
    offset_y: int | float | None = None,
    crop_w: int = 163,
    crop_h: int = 163,
) -> tuple[int, int, int, int]:
    if not src_w or not src_h:
        return (0, 0, 1, 1)
    crop_w = max(1, min(int(crop_w), src_w))
    crop_h = max(1, min(int(crop_h), src_h))
    max_off_x = max(0, src_w - crop_w)
    max_off_y = max(0, src_h - crop_h)
    if offset_x is None:
        left = max_off_x // 2
    else:
        left = int(round(float(offset_x)))
    if offset_y is None:
        top = max_off_y // 2
    else:
        top = int(round(float(offset_y)))
    left = int(clamp(left, 0, max_off_x))
    top = int(clamp(top, 0, max_off_y))
    return (left, top, left + crop_w, top + crop_h)


def get_photo_prep_capability(mode: str, src_w: int, src_h: int) -> dict[str, Any]:
    mode = string_value(mode) or "original"
    src_w = int(src_w or 0)
    src_h = int(src_h or 0)
    result: dict[str, Any] = {
        "kind": "good",
        "title": "Ready",
        "detail": "",
        "can_true_crop": True,
        "crop_box_width": 0,
        "crop_box_height": 0,
        "will_upscale": False,
    }
    if src_w <= 0 or src_h <= 0:
        result.update({
            "kind": "warn",
            "title": "Preview unavailable",
            "detail": "The source image dimensions could not be read.",
            "can_true_crop": False,
        })
        return result

    def warn(title: str, detail: str, crop_w: int = 0, crop_h: int = 0, will_upscale: bool = True) -> dict[str, Any]:
        return {
            "kind": "warn",
            "title": title,
            "detail": detail,
            "can_true_crop": False,
            "crop_box_width": int(crop_w or 0),
            "crop_box_height": int(crop_h or 0),
            "will_upscale": bool(will_upscale),
        }

    if mode == "original":
        result.update({
            "kind": "notice",
            "title": "Original size",
            "detail": f"Source image: {src_w}x{src_h}. No crop or resize will be applied.",
            "can_true_crop": False,
            "will_upscale": False,
        })
        return result

    if mode == "crop_square":
        side = min(src_w, src_h)
        result["crop_box_width"] = side
        result["crop_box_height"] = side
        if side < 1000:
            return warn(
                "Square will be enlarged",
                f"Largest true square is {side}x{side}. Output will be upscaled only to 1000x1000.",
                side,
                side,
            )
        result["detail"] = f"Largest native square crop: {side}x{side}. Output stays at that exact size."
        return result

    if mode == "crop_swatch":
        side = min(src_w, src_h)
        result["crop_box_width"] = side
        result["crop_box_height"] = side
        if side < 163:
            return warn(
                "Swatch will be enlarged",
                f"Largest true square is {side}x{side}. Output will be upscaled to 163x163.",
                side,
                side,
            )
        result["detail"] = f"Largest native square crop: {side}x{side}; final output is 163x163."
        return result

    if mode == "pick_swatch":
        crop_w = min(163, src_w)
        crop_h = min(163, src_h)
        result["crop_box_width"] = crop_w
        result["crop_box_height"] = crop_h
        if src_w < 163 or src_h < 163:
            return warn(
                "Swatch box is constrained",
                f"Only {crop_w}x{crop_h} is available from this source. Output will be enlarged to 163x163.",
                crop_w,
                crop_h,
            )
        result["detail"] = "True 163x163 swatch crop is available."
        return result

    if mode == "crop_1688":
        scaled_h = int(round(src_h * (3000 / max(1, src_w))))
        result["crop_box_width"] = 3000
        result["crop_box_height"] = 1688
        if src_w < 3000 or scaled_h < 1688:
            return warn(
                "True crop is not available",
                f"Source is {src_w}x{src_h}. A native 3000x1688 crop is not available without enlarging the image.",
                min(3000, src_w),
                min(1688, scaled_h),
            )
        result["detail"] = "True 3000x1688 crop is available."
        return result

    if mode == "crop_2200":
        scaled_h = int(round(src_h * (3000 / max(1, src_w))))
        result["crop_box_width"] = 3000
        result["crop_box_height"] = 2200
        if src_w < 3000 or scaled_h < 2200:
            return warn(
                "True crop is not available",
                f"Source is {src_w}x{src_h}. A native 3000x2200 crop is not available without enlarging the image.",
                min(3000, src_w),
                min(2200, scaled_h),
            )
        result["detail"] = "True 3000x2200 crop is available."
        return result

    if mode == "crop_remove_sides_1688":
        result["crop_box_width"] = 3000
        result["crop_box_height"] = 1688
        if src_h < 1688 or src_w < 3000:
            return warn(
                "True crop is not available",
                f"Source is {src_w}x{src_h}. This mode will need to enlarge the image to reach 3000x1688.",
                min(3000, src_w),
                min(1688, src_h),
            )
        result["detail"] = "True 3000x1688 crop is available."
        return result

    if mode == "pad_lr_1688":
        result.update({
            "kind": "notice",
            "title": "Padding mode",
            "detail": "This mode keeps the full image and adds white sides instead of cropping.",
            "can_true_crop": False,
            "will_upscale": src_w < 3000 or src_h < 1688,
        })
        return result

    if mode == "pad_tb_2200":
        result.update({
            "kind": "notice",
            "title": "Padding mode",
            "detail": "This mode keeps the full image and adds white top and bottom space instead of cropping.",
            "can_true_crop": False,
            "will_upscale": src_w < 3000 or src_h < 2200,
        })
        return result

    result["detail"] = f"Source image: {src_w}x{src_h}."
    return result


def prepare_photo_result(image: Image.Image, mode: str, flip: bool = False, offset_y: int | float | None = None, offset_x: int | float | None = None) -> Image.Image:
    mode = string_value(mode) or "original"
    out_w, out_h = prep_mode_to_size(mode)
    im = image.convert("RGB")
    if flip:
        im = ImageOps.mirror(im)
    src_w, src_h = im.size

    if mode == "original":
        return im

    if mode == "crop_square":
        bounds = get_square_crop_bounds(src_w, src_h, offset_x)
        square = im.crop(bounds)
        target_w, target_h = prep_square_output_size(src_w, src_h)
        if square.size != (target_w, target_h):
            square = square.resize((target_w, target_h), Image.LANCZOS)
        return square

    if mode == "crop_swatch":
        bounds = get_square_crop_bounds(src_w, src_h, offset_x)
        square = im.crop(bounds)
        return square.resize((out_w, out_h), Image.LANCZOS)

    if mode == "pick_swatch":
        bounds = get_swatch_crop_bounds(src_w, src_h, offset_x, offset_y, out_w, out_h)
        swatch = im.crop(bounds)
        if swatch.size != (out_w, out_h):
            swatch = swatch.resize((out_w, out_h), Image.LANCZOS)
        return swatch

    if mode in ("crop_1688", "crop_2200"):
        scaled_h = int(round(src_h * (out_w / src_w)))
        scaled = im.resize((out_w, scaled_h), Image.LANCZOS)
        max_off = max(0, scaled_h - out_h)
        off = get_default_offset_y(src_w, src_h, out_w, out_h) if offset_y is None else int(round(float(offset_y)))
        off = int(clamp(off, 0, max_off))
        return scaled.crop((0, off, out_w, off + out_h))

    if mode == "crop_remove_sides_1688":
        if not src_w or not src_h:
            return im.resize((out_w, out_h), Image.LANCZOS)
        # This mode should never introduce letterboxing. Prefer a height-first
        # resize and crop equal amounts from the sides. If the source is not
        # wide enough after scaling to 1688 tall, fall back to a cover resize so
        # the output still fills 3000x1688 completely.
        scaled_w = int(round(src_w * (out_h / src_h)))
        if scaled_w >= out_w:
            scaled = im.resize((max(1, scaled_w), out_h), Image.LANCZOS)
            left = max(0, (scaled.size[0] - out_w) // 2)
            return scaled.crop((left, 0, left + out_w, out_h))
        cover_scale = max(out_w / src_w, out_h / src_h)
        cover_w = max(1, int(round(src_w * cover_scale)))
        cover_h = max(1, int(round(src_h * cover_scale)))
        covered = im.resize((cover_w, cover_h), Image.LANCZOS)
        left = max(0, (cover_w - out_w) // 2)
        top = max(0, (cover_h - out_h) // 2)
        return covered.crop((left, top, left + out_w, top + out_h))

    if mode == "pad_lr_1688":
        canvas = Image.new("RGB", (3000, 1688), (255, 255, 255))
        fit = ImageOps.contain(im, (3000, 1688), Image.LANCZOS)
        x = (3000 - fit.size[0]) // 2
        y = (1688 - fit.size[1]) // 2
        canvas.paste(fit, (x, y))
        return canvas

    if mode == "pad_tb_2200":
        canvas = Image.new("RGB", (3000, 2200), (255, 255, 255))
        fit = ImageOps.contain(im, (3000, 2200), Image.LANCZOS)
        x = (3000 - fit.size[0]) // 2
        y = (2200 - fit.size[1]) // 2
        canvas.paste(fit, (x, y))
        return canvas

    return ImageOps.contain(im, (out_w, out_h), Image.LANCZOS)


def render_photo_preview_image(image: Image.Image, mode: str, flip: bool = False, offset_y: int | float | None = None, offset_x: int | float | None = None, preview_max_w: int = 900, preview_max_h: int = 420) -> Image.Image:
    mode = string_value(mode) or "original"
    out_w, out_h = prep_mode_to_size(mode)
    im = image.convert("RGB")
    canvas_outline = (48, 48, 52, 235)

    def _frame_preview(preview_image: Image.Image, add_inner_canvas: bool = False) -> Image.Image:
        framed = preview_image.convert("RGB")
        pad = 10
        bg = Image.new("RGB", (framed.width + (pad * 2), framed.height + (pad * 2)), (255, 255, 255))
        bg.paste(framed, (pad, pad))
        draw_bg = ImageDraw.Draw(bg, "RGBA")
        draw_bg.rounded_rectangle((1, 1, bg.width - 2, bg.height - 2), radius=12, outline=(206, 198, 229, 255), width=2)
        if add_inner_canvas:
            draw_bg.rectangle((pad, pad, pad + framed.width - 1, pad + framed.height - 1), outline=canvas_outline, width=4)
        return bg
    if flip:
        im = ImageOps.mirror(im)
    src_w, src_h = im.size

    if mode == "original":
        preview = im.copy()
        if preview.size[0] > preview_max_w or preview.size[1] > preview_max_h:
            scale = min(preview_max_w / preview.size[0], preview_max_h / preview.size[1], 1.0)
            prev_size = (max(1, int(round(preview.size[0] * scale))), max(1, int(round(preview.size[1] * scale))))
            preview = preview.resize(prev_size, Image.LANCZOS)
        return _frame_preview(preview, add_inner_canvas=True)

    if mode == "crop_square":
        base = im.convert("RGBA")
        left, top, right, bottom = get_square_crop_bounds(src_w, src_h, offset_x)
        overlay = base.copy()
        haze = Image.new("RGBA", overlay.size, (0, 0, 0, 0))
        haze_draw = ImageDraw.Draw(haze, "RGBA")
        if left > 0:
            haze_draw.rectangle((0, 0, left, src_h), fill=(115, 115, 115, 125))
        if right < src_w:
            haze_draw.rectangle((right, 0, src_w, src_h), fill=(115, 115, 115, 125))
        overlay = Image.alpha_composite(overlay, haze)
        draw = ImageDraw.Draw(overlay, "RGBA")
        draw.rectangle((left + 2, top + 2, right - 3, bottom - 3), outline=canvas_outline, width=4)
        scale = min(preview_max_w / overlay.size[0], preview_max_h / overlay.size[1], 1.0)
        prev_size = (max(1, int(round(overlay.size[0] * scale))), max(1, int(round(overlay.size[1] * scale))))
        preview = overlay.resize(prev_size, Image.LANCZOS)
        return _frame_preview(preview.convert("RGB"), add_inner_canvas=False)

    if mode == "crop_swatch":
        base = im.convert("RGBA")
        left, top, right, bottom = get_square_crop_bounds(src_w, src_h, offset_x)
        overlay = base.copy()
        haze = Image.new("RGBA", overlay.size, (0, 0, 0, 0))
        haze_draw = ImageDraw.Draw(haze, "RGBA")
        if left > 0:
            haze_draw.rectangle((0, 0, left, src_h), fill=(115, 115, 115, 125))
        if right < src_w:
            haze_draw.rectangle((right, 0, src_w, src_h), fill=(115, 115, 115, 125))
        overlay = Image.alpha_composite(overlay, haze)
        draw = ImageDraw.Draw(overlay, "RGBA")
        draw.rectangle((left + 2, top + 2, right - 3, bottom - 3), outline=canvas_outline, width=4)
        scale = min(preview_max_w / overlay.size[0], preview_max_h / overlay.size[1], 1.0)
        prev_size = (max(1, int(round(overlay.size[0] * scale))), max(1, int(round(overlay.size[1] * scale))))
        preview = overlay.resize(prev_size, Image.LANCZOS)
        return _frame_preview(preview.convert("RGB"), add_inner_canvas=False)

    if mode == "pick_swatch":
        base = im.convert("RGBA")
        left, top, right, bottom = get_swatch_crop_bounds(src_w, src_h, offset_x, offset_y, out_w, out_h)
        overlay = base.copy()
        haze = Image.new("RGBA", overlay.size, (0, 0, 0, 0))
        haze_draw = ImageDraw.Draw(haze, "RGBA")
        if left > 0:
            haze_draw.rectangle((0, 0, left, src_h), fill=(115, 115, 115, 125))
        if right < src_w:
            haze_draw.rectangle((right, 0, src_w, src_h), fill=(115, 115, 115, 125))
        if top > 0:
            haze_draw.rectangle((left, 0, right, top), fill=(115, 115, 115, 125))
        if bottom < src_h:
            haze_draw.rectangle((left, bottom, right, src_h), fill=(115, 115, 115, 125))
        overlay = Image.alpha_composite(overlay, haze)
        draw = ImageDraw.Draw(overlay, "RGBA")
        draw.rectangle((left + 2, top + 2, right - 3, bottom - 3), outline=canvas_outline, width=4)
        scale = min(preview_max_w / overlay.size[0], preview_max_h / overlay.size[1], 1.0)
        prev_size = (max(1, int(round(overlay.size[0] * scale))), max(1, int(round(overlay.size[1] * scale))))
        preview = overlay.resize(prev_size, Image.LANCZOS)
        return _frame_preview(preview.convert("RGB"), add_inner_canvas=False)

    if mode in ("crop_1688", "crop_2200"):
        scaled_h = int(round(src_h * (out_w / src_w)))
        scaled = im.resize((out_w, scaled_h), Image.LANCZOS).convert("RGBA")
        max_off = max(0, scaled_h - out_h)
        off = get_default_offset_y(src_w, src_h, out_w, out_h) if offset_y is None else int(round(float(offset_y)))
        off = int(clamp(off, 0, max_off))

        overlay = scaled.copy()
        haze = Image.new("RGBA", overlay.size, (0, 0, 0, 0))
        haze_draw = ImageDraw.Draw(haze, "RGBA")
        if off > 0:
            haze_draw.rectangle((0, 0, out_w, off), fill=(115, 115, 115, 125))
        bottom = off + out_h
        if bottom < scaled_h:
            haze_draw.rectangle((0, bottom, out_w, scaled_h), fill=(115, 115, 115, 125))

        overlay = Image.alpha_composite(overlay, haze)
        draw = ImageDraw.Draw(overlay, "RGBA")
        draw.rectangle((2, off + 2, out_w - 3, bottom - 3), outline=canvas_outline, width=4)

        scale = min(preview_max_w / overlay.size[0], preview_max_h / overlay.size[1], 1.0)
        prev_size = (max(1, int(round(overlay.size[0] * scale))), max(1, int(round(overlay.size[1] * scale))))
        preview = overlay.resize(prev_size, Image.LANCZOS)
        return _frame_preview(preview.convert("RGB"), add_inner_canvas=False)

    if mode == "crop_remove_sides_1688":
        if not src_w or not src_h:
            fallback = im.resize((out_w, out_h), Image.LANCZOS)
            scale = min(preview_max_w / fallback.size[0], preview_max_h / fallback.size[1], 1.0)
            prev_size = (max(1, int(round(fallback.size[0] * scale))), max(1, int(round(fallback.size[1] * scale))))
            return _frame_preview(fallback.resize(prev_size, Image.LANCZOS).convert("RGB"), add_inner_canvas=True)
        scaled_w = int(round(src_w * (out_h / src_h)))
        if scaled_w >= out_w:
            scaled = im.resize((max(1, scaled_w), out_h), Image.LANCZOS).convert("RGBA")
            overlay = scaled.copy()
            left = max(0, (scaled.size[0] - out_w) // 2)
            right = left + out_w
            haze = Image.new("RGBA", overlay.size, (0, 0, 0, 0))
            haze_draw = ImageDraw.Draw(haze, "RGBA")
            if left > 0:
                haze_draw.rectangle((0, 0, left, out_h), fill=(115, 115, 115, 125))
            if right < scaled.size[0]:
                haze_draw.rectangle((right, 0, scaled.size[0], out_h), fill=(115, 115, 115, 125))
            overlay = Image.alpha_composite(overlay, haze)
            draw = ImageDraw.Draw(overlay, "RGBA")
            draw.rectangle((left + 2, 2, right - 3, out_h - 3), outline=canvas_outline, width=4)
            scale = min(preview_max_w / overlay.size[0], preview_max_h / overlay.size[1], 1.0)
            prev_size = (max(1, int(round(overlay.size[0] * scale))), max(1, int(round(overlay.size[1] * scale))))
            preview = overlay.resize(prev_size, Image.LANCZOS)
            return _frame_preview(preview.convert("RGB"), add_inner_canvas=False)
        cover_scale = max(out_w / src_w, out_h / src_h)
        cover_w = max(1, int(round(src_w * cover_scale)))
        cover_h = max(1, int(round(src_h * cover_scale)))
        covered = im.resize((cover_w, cover_h), Image.LANCZOS).convert("RGBA")
        overlay = covered.copy()
        left = max(0, (cover_w - out_w) // 2)
        top = max(0, (cover_h - out_h) // 2)
        right = left + out_w
        bottom = top + out_h
        haze = Image.new("RGBA", overlay.size, (0, 0, 0, 0))
        haze_draw = ImageDraw.Draw(haze, "RGBA")
        if left > 0:
            haze_draw.rectangle((0, 0, left, cover_h), fill=(115, 115, 115, 125))
        if right < cover_w:
            haze_draw.rectangle((right, 0, cover_w, cover_h), fill=(115, 115, 115, 125))
        if top > 0:
            haze_draw.rectangle((left, 0, right, top), fill=(115, 115, 115, 95))
        if bottom < cover_h:
            haze_draw.rectangle((left, bottom, right, cover_h), fill=(115, 115, 115, 95))
        overlay = Image.alpha_composite(overlay, haze)
        draw = ImageDraw.Draw(overlay, "RGBA")
        draw.rectangle((left + 2, top + 2, right - 3, bottom - 3), outline=canvas_outline, width=4)
        scale = min(preview_max_w / overlay.size[0], preview_max_h / overlay.size[1], 1.0)
        prev_size = (max(1, int(round(overlay.size[0] * scale))), max(1, int(round(overlay.size[1] * scale))))
        preview = overlay.resize(prev_size, Image.LANCZOS)
        return _frame_preview(preview.convert("RGB"), add_inner_canvas=False)

    final_img = prepare_photo_result(im, mode, False, offset_y, offset_x)
    scale = min(preview_max_w / final_img.size[0], preview_max_h / final_img.size[1], 1.0)
    prev_size = (max(1, int(round(final_img.size[0] * scale))), max(1, int(round(final_img.size[1] * scale))))
    return _frame_preview(final_img.resize(prev_size, Image.LANCZOS), add_inner_canvas=True)


def get_photography_asset_status(asset: Dict[str, Any]) -> str:
    return string_value(
        asset.get("property_Asset_Status")
        or asset.get("Asset_Status")
        or asset.get("asset_status")
        or asset.get("status")
    ).strip()


def photography_asset_is_final(asset: Dict[str, Any]) -> bool:
    return get_photography_asset_status(asset).lower() == "final"


def get_photo_watermark_font(size: int) -> ImageFont.ImageFont:
    candidates = [
        "DejaVuSans-Bold.ttf",
        "arialbd.ttf",
        "Arial Bold.ttf",
        "arial.ttf",
    ]
    for candidate in candidates:
        try:
            return ImageFont.truetype(candidate, size=size)
        except Exception:
            pass
    return ImageFont.load_default()


def compute_text_block_size(draw: ImageDraw.ImageDraw, lines: List[str], font: ImageFont.ImageFont, gap: int) -> Tuple[int, int, List[Tuple[int, int, int, int]]]:
    boxes: List[Tuple[int, int, int, int]] = []
    max_width = 0
    total_height = 0
    for idx, line in enumerate(lines):
        bbox = draw.textbbox((0, 0), line, font=font, align="center", stroke_width=0)
        boxes.append(bbox)
        width = max(0, bbox[2] - bbox[0])
        height = max(0, bbox[3] - bbox[1])
        max_width = max(max_width, width)
        total_height += height
        if idx < len(lines) - 1:
            total_height += gap
    return max_width, total_height, boxes


def apply_photo_watermark(image: Image.Image) -> Image.Image:
    base = image.convert("RGBA")
    base_w, base_h = base.size
    if base_w <= 0 or base_h <= 0:
        return image.convert("RGB") if image.mode != "RGBA" else image

    overlay = Image.new("RGBA", base.size, (255, 255, 255, 0))
    draw = ImageDraw.Draw(overlay)
    lines = [string_value(x) for x in PHOTO_WATERMARK_TEXT if string_value(x)]
    if not lines:
        return base.convert("RGB")

    max_width = int(round(base_w * PHOTO_WATERMARK_WIDTH_RATIO))
    max_height = int(round(base_h * PHOTO_WATERMARK_HEIGHT_RATIO))
    font_size = max(24, int(round(min(base_w, base_h) * 0.24)))
    chosen_font = get_photo_watermark_font(font_size)
    chosen_gap = max(6, int(round(font_size * PHOTO_WATERMARK_LINE_GAP_RATIO)))
    measured = compute_text_block_size(draw, lines, chosen_font, chosen_gap)

    for test_size in range(font_size, 23, -2):
        font = get_photo_watermark_font(test_size)
        gap = max(4, int(round(test_size * PHOTO_WATERMARK_LINE_GAP_RATIO)))
        block_w, block_h, boxes = compute_text_block_size(draw, lines, font, gap)
        if block_w <= max_width and block_h <= max_height:
            chosen_font = font
            chosen_gap = gap
            measured = (block_w, block_h, boxes)
            break

    block_w, block_h, boxes = measured
    y = (base_h - block_h) // 2
    fill_alpha = int(round(255 * PHOTO_WATERMARK_ALPHA))
    fill = (255, 255, 255, fill_alpha)
    stroke_fill = (90, 90, 90, min(255, int(round(fill_alpha * 0.38))))
    stroke_width = max(1, int(round(getattr(chosen_font, 'size', 32) * 0.045)))

    for line, bbox in zip(lines, boxes):
        width = max(0, bbox[2] - bbox[0])
        height = max(0, bbox[3] - bbox[1])
        x = (base_w - width) // 2
        draw.text(
            (x, y),
            line,
            font=chosen_font,
            fill=fill,
            align="center",
            stroke_width=stroke_width,
            stroke_fill=stroke_fill,
        )
        y += height + chosen_gap

    combined = Image.alpha_composite(base, overlay)
    return combined.convert("RGB")

def image_to_png_bytes(image: Image.Image) -> bytes:
    bio = BytesIO()
    image.save(bio, format="PNG")
    return bio.getvalue()


def image_to_jpg_bytes(image: Image.Image) -> bytes:
    bio = BytesIO()
    image.save(bio, format="JPEG", quality=92)
    return bio.getvalue()



def trim_whitespace(image: Image.Image, pad: int = 10) -> Image.Image:
    if image.mode != "RGB":
        image = image.convert("RGB")
    thresh = 245
    w, h = image.size
    px = image.load()
    min_x, min_y = w, h
    max_x, max_y = -1, -1
    for y in range(h):
        for x in range(w):
            r, g, b = px[x, y]
            if r < thresh or g < thresh or b < thresh:
                min_x = min(min_x, x)
                min_y = min(min_y, y)
                max_x = max(max_x, x)
                max_y = max(max_y, y)
    if max_x < 0 or max_y < 0:
        return image
    min_x = max(0, min_x - pad)
    min_y = max(0, min_y - pad)
    max_x = min(w - 1, max_x + pad)
    max_y = min(h - 1, max_y + pad)
    return image.crop((min_x, min_y, max_x + 1, max_y + 1))


def _fit_size(iw: int, ih: int, bw: int, bh: int) -> tuple[int, int]:
    scale = min(bw / max(1, iw), bh / max(1, ih))
    return max(1, int(iw * scale)), max(1, int(ih * scale))


def get_set_dim_layout_boxes(images: List[Image.Image]) -> List[tuple[int, int, int, int]]:
    n = max(0, len(images))
    edge = 10
    gap = 30
    usable_w = 3000 - (2 * edge)
    usable_h = 1688 - (2 * edge)
    x0 = edge
    y0 = edge
    x1 = edge + usable_w
    y1 = edge + usable_h
    if n <= 0:
        return []
    if n == 1:
        return [(x0, y0, x1, y1)]
    if n == 2:
        w0, h0 = images[0].size
        w1, h1 = images[1].size
        a0 = w0 / max(1, h0)
        a1 = w1 / max(1, h1)
        both_wide = a0 > 1.0 and a1 > 1.0
        both_tall = a0 <= 1.0 and a1 <= 1.0
        row_h = (usable_h - gap) // 2
        col_w = (usable_w - gap) // 2
        area_a = math.prod(_fit_size(w0, h0, usable_w, row_h)) + math.prod(_fit_size(w1, h1, usable_w, row_h))
        area_b = math.prod(_fit_size(w0, h0, col_w, usable_h)) + math.prod(_fit_size(w1, h1, col_w, usable_h))
        if both_wide or (not both_tall and area_a >= area_b):
            return [
                (x0, y0, x1, y0 + row_h),
                (x0, y0 + row_h + gap, x1, y1),
            ]
        return [
            (x0, y0, x0 + col_w, y1),
            (x0 + col_w + gap, y0, x1, y1),
        ]
    if n == 3:
        col_w = (usable_w - gap) // 2
        row_h = (usable_h - gap) // 2
        return [
            (x0, y0, x0 + col_w, y0 + row_h),
            (x0 + col_w + gap, y0, x1, y0 + row_h),
            (x0, y0 + row_h + gap, x1, y1),
        ]
    if n == 4:
        col_w = (usable_w - gap) // 2
        row_h = (usable_h - gap) // 2
        return [
            (x0, y0, x0 + col_w, y0 + row_h),
            (x0 + col_w + gap, y0, x1, y0 + row_h),
            (x0, y0 + row_h + gap, x0 + col_w, y1),
            (x0 + col_w + gap, y0 + row_h + gap, x1, y1),
        ]
    if n == 5:
        row_h = (usable_h - gap) // 2
        col_w3 = (usable_w - (2 * gap)) // 3
        col_w2 = (usable_w - gap) // 2
        xA = x0
        xB = x0 + col_w3 + gap
        xC = x0 + (2 * col_w3) + (2 * gap)
        yBtm0 = y0 + row_h + gap
        return [
            (xA, y0, xA + col_w3, y0 + row_h),
            (xB, y0, xB + col_w3, y0 + row_h),
            (xC, y0, x1, y0 + row_h),
            (x0, yBtm0, x0 + col_w2, y1),
            (x0 + col_w2 + gap, yBtm0, x1, y1),
        ]
    row_h = (usable_h - gap) // 2
    col_w = (usable_w - (2 * gap)) // 3
    xA = x0
    xB = x0 + col_w + gap
    xC = x0 + (2 * col_w) + (2 * gap)
    yBtm0 = y0 + row_h + gap
    return [
        (xA, y0, xA + col_w, y0 + row_h),
        (xB, y0, xB + col_w, y0 + row_h),
        (xC, y0, x1, y0 + row_h),
        (xA, yBtm0, xA + col_w, y1),
        (xB, yBtm0, xB + col_w, y1),
        (xC, yBtm0, x1, y1),
    ]


def normalize_set_dim_order(images: List[Image.Image], component_subcats: Optional[List[str]] = None, parent_subcat: str = "") -> tuple[List[Image.Image], List[str]]:
    working_images = list(images)
    working_subcats = list(component_subcats or [""] * len(working_images))
    n = len(working_images)

    if n == 4 and parent_subcat == "Bedroom_Sets" and set(working_subcats) == {"Beds", "Nightstands", "Dressers", "Mirrors"}:
        desired = ["Beds", "Mirrors", "Nightstands", "Dressers"]
        ordered_images = []
        ordered_subcats = []
        for wanted in desired:
            idx = working_subcats.index(wanted)
            ordered_images.append(working_images[idx])
            ordered_subcats.append(working_subcats[idx])
        return ordered_images, ordered_subcats

    if n == 3:
        widest_idx = max(range(n), key=lambda i: working_images[i].size[0])
        if widest_idx != 2:
            order = [i for i in range(n) if i != widest_idx] + [widest_idx]
            working_images = [working_images[i] for i in order]
            working_subcats = [working_subcats[i] for i in order]

    if n == 4:
        idx = sorted(range(n), key=lambda i: working_images[i].size[0], reverse=True)
        order = [idx[0], idx[3], idx[1], idx[2]]
        working_images = [working_images[i] for i in order]
        working_subcats = [working_subcats[i] for i in order]

    if n == 2:
        if working_images[0].size[0] > working_images[1].size[0]:
            working_images = [working_images[1], working_images[0]]
            working_subcats = [working_subcats[1], working_subcats[0]]

    return working_images, working_subcats


def _normalized_set_dim_weights(raw_weights: Optional[List[Any]], count: int) -> List[float]:
    """
    Turn the UI scale percentages into layout weights.

    We intentionally bias this curve harder than a simple linear/square mapping so
    user changes are visually obvious in the compiled preview. A small nudge should
    reclaim or surrender real canvas area, not just create a mathematically tiny box
    delta that is hard to see.
    """
    weights: List[float] = []
    for idx in range(count):
        try:
            val = float((raw_weights or [])[idx])
        except Exception:
            val = 100.0
        val = max(60.0, min(160.0, val))
        ratio = val / 100.0
        # Stronger response curve so 70/80/130/140 style adjustments are visible.
        weight = ratio ** 4.0
        weights.append(max(0.08, weight))
    return weights


def _split_span(total_span: int, weights: List[float]) -> List[int]:
    if not weights:
        return []
    total_weight = sum(max(0.01, float(w)) for w in weights)
    raw = [total_span * (max(0.01, float(w)) / total_weight) for w in weights]
    ints = [max(1, int(math.floor(x))) for x in raw]
    remainder = total_span - sum(ints)
    if remainder > 0:
        order = sorted(range(len(raw)), key=lambda i: raw[i] - ints[i], reverse=True)
        for i in range(remainder):
            ints[order[i % len(order)]] += 1
    elif remainder < 0:
        order = sorted(range(len(raw)), key=lambda i: raw[i] - ints[i])
        for i in range(-remainder):
            idx = order[i % len(order)]
            if ints[idx] > 1:
                ints[idx] -= 1
    return ints


def get_set_dim_layout_boxes_weighted(images: List[Image.Image], raw_weights: Optional[List[Any]] = None) -> List[tuple[int, int, int, int]]:
    n = max(0, len(images))
    edge = 10
    gap = 30
    usable_w = 3000 - (2 * edge)
    usable_h = 1688 - (2 * edge)
    x0 = edge
    y0 = edge
    x1 = edge + usable_w
    y1 = edge + usable_h
    if n <= 0:
        return []
    if n == 1:
        return [(x0, y0, x1, y1)]
    weights = _normalized_set_dim_weights(raw_weights, n)

    def boxes_from_rows(row_heights: List[int], row_width_groups: List[List[int]]) -> List[tuple[int, int, int, int]]:
        boxes: List[tuple[int, int, int, int]] = []
        y = y0
        for row_idx, h in enumerate(row_heights):
            widths = row_width_groups[row_idx]
            x = x0
            for w in widths:
                boxes.append((x, y, x + w, y + h))
                x += w + gap
            y += h + gap
        return boxes

    if n == 2:
        w0, h0 = images[0].size
        w1, h1 = images[1].size
        a0 = w0 / max(1, h0)
        a1 = w1 / max(1, h1)
        both_wide = a0 > 1.0 and a1 > 1.0
        both_tall = a0 <= 1.0 and a1 <= 1.0
        row_h = (usable_h - gap) // 2
        col_w = (usable_w - gap) // 2
        area_a = math.prod(_fit_size(w0, h0, usable_w, row_h)) + math.prod(_fit_size(w1, h1, usable_w, row_h))
        area_b = math.prod(_fit_size(w0, h0, col_w, usable_h)) + math.prod(_fit_size(w1, h1, col_w, usable_h))
        if both_wide or (not both_tall and area_a >= area_b):
            heights = _split_span(usable_h - gap, [weights[0], weights[1]])
            return boxes_from_rows(heights, [[usable_w], [usable_w]])
        widths = _split_span(usable_w - gap, [weights[0], weights[1]])
        return [(x0, y0, x0 + widths[0], y1), (x0 + widths[0] + gap, y0, x1, y1)]

    if n == 3:
        row_heights = _split_span(usable_h - gap, [sum(weights[:2]) / 2.0, weights[2]])
        top_widths = _split_span(usable_w - gap, weights[:2])
        return boxes_from_rows(row_heights, [top_widths, [usable_w]])

    if n == 4:
        row_heights = _split_span(usable_h - gap, [sum(weights[:2]) / 2.0, sum(weights[2:4]) / 2.0])
        top_widths = _split_span(usable_w - gap, weights[:2])
        bottom_widths = _split_span(usable_w - gap, weights[2:4])
        return boxes_from_rows(row_heights, [top_widths, bottom_widths])

    if n == 5:
        row_heights = _split_span(usable_h - gap, [sum(weights[:3]) / 3.0, sum(weights[3:5]) / 2.0])
        top_widths = _split_span(usable_w - (2 * gap), weights[:3])
        bottom_widths = _split_span(usable_w - gap, weights[3:5])
        return boxes_from_rows(row_heights, [top_widths, bottom_widths])

    row_heights = _split_span(usable_h - gap, [sum(weights[:3]) / 3.0, sum(weights[3:6]) / 3.0])
    top_widths = _split_span(usable_w - (2 * gap), weights[:3])
    bottom_widths = _split_span(usable_w - (2 * gap), weights[3:6])
    return boxes_from_rows(row_heights, [top_widths, bottom_widths])


def compose_set_dim_canvas(
    images: List[Image.Image],
    component_subcats: Optional[List[str]] = None,
    parent_subcat: str = "",
    manual_slots: Optional[List[int]] = None,
    scale_percents: Optional[List[int]] = None,
) -> Image.Image:
    trimmed_images = [trim_whitespace(im, 0).convert("RGB") for im in images[:SET_DIM_MAX_COMPONENTS]]
    canvas = Image.new("RGB", (3000, 1688), (255, 255, 255))
    if not trimmed_images:
        return canvas

    count = len(trimmed_images)
    raw_scales: List[float] = []
    for idx in range(count):
        try:
            val = float((scale_percents or [])[idx])
        except Exception:
            val = 100.0
        raw_scales.append(max(60.0, min(160.0, val)))

    if manual_slots is None:
        working_subcats = list(component_subcats or [""] * count)
        ordered_images, ordered_subcats = normalize_set_dim_order(trimmed_images, working_subcats, parent_subcat)
        original_pairs = [(trimmed_images[i], working_subcats[i], raw_scales[i]) for i in range(count)]
        remaining = list(original_pairs)
        ordered_pairs = []
        for img, subcat in zip(ordered_images, ordered_subcats):
            match_idx = next((i for i, pair in enumerate(remaining) if pair[0] is img and pair[1] == subcat), None)
            if match_idx is None:
                match_idx = next((i for i, pair in enumerate(remaining) if pair[0] is img), 0)
            ordered_pairs.append(remaining.pop(match_idx))
    else:
        ordered_pairs: List[Optional[tuple[Image.Image, str, float]]] = [None] * count
        leftovers: List[tuple[Image.Image, str, float]] = []
        working_subcats = list(component_subcats or [""] * count)
        for idx, im in enumerate(trimmed_images):
            slot_idx = int(manual_slots[idx]) if idx < len(manual_slots) else idx
            slot_idx = max(0, min(count - 1, slot_idx))
            pair = (im, working_subcats[idx], raw_scales[idx])
            if ordered_pairs[slot_idx] is None:
                ordered_pairs[slot_idx] = pair
            else:
                leftovers.append(pair)
        for slot_idx in range(count):
            if ordered_pairs[slot_idx] is None and leftovers:
                ordered_pairs[slot_idx] = leftovers.pop(0)
        ordered_pairs = [pair for pair in ordered_pairs if pair is not None]

    ordered_images = [pair[0] for pair in ordered_pairs]
    ordered_raw_scales = [pair[2] for pair in ordered_pairs]

    # Distribute the dims evenly across the full usable canvas while preserving
    # the 10px outer guide and 30px between-dim gap. The scale percentages bias
    # how much space each dim claims inside that evenly distributed layout.
    boxes = get_set_dim_layout_boxes_weighted(ordered_images, ordered_raw_scales)
    for idx, im in enumerate(ordered_images):
        if idx >= len(boxes):
            break
        bx0, by0, bx1, by1 = boxes[idx]
        bw = max(1, bx1 - bx0)
        bh = max(1, by1 - by0)
        iw, ih = im.size
        scale = min(bw / max(1, iw), bh / max(1, ih))
        new_w = max(1, int(round(iw * scale)))
        new_h = max(1, int(round(ih * scale)))
        resized = im.resize((new_w, new_h), Image.LANCZOS)
        paste_x = bx0 + max(0, (bw - new_w) // 2)
        paste_y = by0 + max(0, (bh - new_h) // 2)
        canvas.paste(resized, (paste_x, paste_y))

    return canvas


def reformat_silo_like_image(image: Image.Image, canvas_size: tuple[int, int] = (3000, 1688), margin: int = 10) -> Image.Image:
    """Apply the same core logic as reformat1688_silo.py to a PIL image."""
    im = image.convert("RGBA")
    width, height = im.size
    pixels = im.load()

    min_x, min_y = width, height
    max_x, max_y = 0, 0
    found_content = False

    for y in range(height):
        for x in range(width):
            r, g, b, a = pixels[x, y]
            if a != 0 and not (r == 255 and g == 255 and b == 255):
                found_content = True
                min_x = min(min_x, x)
                min_y = min(min_y, y)
                max_x = max(max_x, x)
                max_y = max(max_y, y)

    if not found_content or min_x > max_x or min_y > max_y:
        raise RuntimeError("Could not find discernible non-white content to reformat.")

    cropped = im.crop((min_x, min_y, max_x + 1, max_y + 1))
    crop_w, crop_h = cropped.size
    if crop_w <= 0 or crop_h <= 0:
        raise RuntimeError("Image content area collapsed to zero size during reformat.")

    canvas_w, canvas_h = canvas_size
    content_area_w = canvas_w - (2 * margin)
    content_area_h = canvas_h - (2 * margin)
    scale = min(content_area_w / crop_w, content_area_h / crop_h)

    new_w = max(1, int(crop_w * scale))
    new_h = max(1, int(crop_h * scale))
    resized = cropped.resize((new_w, new_h), Image.LANCZOS)

    canvas = Image.new("RGB", canvas_size, (255, 255, 255))
    paste_x = (canvas_w - new_w) // 2
    paste_y = (canvas_h - new_h) // 2
    canvas.paste(resized, (paste_x, paste_y), mask=resized)
    return canvas


def save_processed_image_for_upload(image: Image.Image, path: Path) -> None:
    suffix = path.suffix.lower()
    if suffix == '.png':
        image.convert('RGBA').save(path, format='PNG')
    else:
        image.convert('RGB').save(path, format='JPEG', quality=92, optimize=True)


def guess_mime_type(path: Path) -> str:
    mime, _ = mimetypes.guess_type(str(path))
    return mime or "application/octet-stream"


def upload_new_asset_group_upload(session: requests.Session, file_path: Path, asset_name: str) -> str:
    endpoint_resp = request_with_retries(session, "GET", f"{BYNDER_BASE_URL}/api/upload/endpoint")
    endpoint_data = endpoint_resp.json()
    upload_endpoint = endpoint_data.get("endpoint") if isinstance(endpoint_data, dict) else endpoint_data
    if not upload_endpoint:
        raise RuntimeError(f"Could not determine upload endpoint: {endpoint_data}")
    init_payload = {"filename": file_path.name, "filesize": str(file_path.stat().st_size)}
    init_resp = request_with_retries(session, "POST", f"{BYNDER_BASE_URL}/api/upload/init", data=init_payload)
    init_data = init_resp.json()
    multipart_params = init_data.get("multipart_params") or {}
    s3file = init_data.get("s3file") or {}
    upload_id = string_value(s3file.get("uploadid") or init_data.get("id") or init_data.get("uploadId") or init_data.get("upload_id"))
    targetid = string_value(init_data.get("targetid") or init_data.get("targetId") or s3file.get("targetid"))
    base_s3_key = string_value(multipart_params.get("key"))
    bynder_filename_base = string_value(multipart_params.get("filename") or multipart_params.get("Filename") or targetid)
    if not (upload_id and targetid and base_s3_key):
        raise RuntimeError(f"Upload init missing expected values: {init_data}")
    base_s3_key = re.sub(r"/p\d+$", "", base_s3_key)
    bynder_filename_base = re.sub(r"/p\d+$", "", bynder_filename_base)
    file_size = file_path.stat().st_size
    total_chunks = (file_size + CHUNK_SIZE_BYTES - 1) // CHUNK_SIZE_BYTES
    for chunk_number in range(1, total_chunks + 1):
        start = (chunk_number - 1) * CHUNK_SIZE_BYTES
        end = min(start + CHUNK_SIZE_BYTES, file_size)
        with open(file_path, "rb") as fh:
            fh.seek(start)
            chunk_bytes = fh.read(end - start)
        chunk_key = f"{base_s3_key}/p{chunk_number}"
        s3_fields = dict(multipart_params)
        s3_fields["key"] = chunk_key
        s3_fields["Filename"] = chunk_key
        s3_fields["name"] = file_path.name
        s3_fields["chunk"] = str(chunk_number)
        s3_fields["chunks"] = str(total_chunks)
        up_resp = requests.post(upload_endpoint, data=s3_fields, files={"File": (file_path.name, chunk_bytes, guess_mime_type(file_path))}, timeout=REQUEST_TIMEOUT)
        if up_resp.status_code not in (201, 204):
            raise RuntimeError(f"S3 upload failed for {file_path.name}: HTTP {up_resp.status_code} {up_resp.text[:800]}")
        reg_payload = {"chunkNumber": str(chunk_number), "targetid": targetid, "filename": chunk_key}
        request_with_retries(session, "POST", f"{BYNDER_BASE_URL}/api/v4/upload/{quote(upload_id, safe='')}", data=reg_payload, headers={"Content-Type": "application/x-www-form-urlencoded"})
    finalize_payload = {"targetid": targetid, "s3_filename": bynder_filename_base, "chunks": str(total_chunks), "original_filename": file_path.name}
    finalize_resp = request_with_retries(session, "POST", f"{BYNDER_BASE_URL}/api/v4/upload/{quote(upload_id, safe='')}", data=finalize_payload, headers={"Content-Type": "application/x-www-form-urlencoded"})
    fin = finalize_resp.json()
    import_id = string_value(fin.get("importId") or fin.get("importid") or fin.get("id"))
    if not import_id:
        items = fin.get("items") if isinstance(fin, dict) else None
        if isinstance(items, list) and items:
            import_id = string_value(items[0])
    if not import_id:
        raise RuntimeError(f"Finalize missing importId: {fin}")
    ready = False
    last_poll = None
    for _ in range(120):
        poll_resp = request_with_retries(session, "GET", f"{BYNDER_BASE_URL}/api/v4/upload/poll", params={"items": import_id})
        last_poll = poll_resp.json()
        if isinstance(last_poll, dict):
            if last_poll.get("itemsDone"):
                ready = True
                break
            if import_id in last_poll:
                ready = True
                break
        time.sleep(1.0)
    if not ready:
        raise RuntimeError(f"Upload poll timed out: {last_poll}")
    save_resp = request_with_retries(session, "POST", f"{BYNDER_BASE_URL}/api/v4/media/save/{import_id}", data={"name": asset_name})
    save_data = save_resp.json()
    new_media_id = string_value(save_data.get("id") or save_data.get("mediaId") or save_data.get("mediaid") or save_data.get("uuid"))
    if not new_media_id:
        raise RuntimeError(f"Could not determine new media ID from save response: {save_data}")
    return new_media_id


def build_metadata_copy_fields(session: requests.Session, source_media: Dict[str, Any], metaprops_by_dbname: Dict[str, Dict[str, Any]], target_sku: str, target_position: str, target_name: str, deliverable_override_label: str = "", psa_image_type_override_label: str = "") -> List[Tuple[str, Any]]:
    fields: List[Tuple[str, Any]] = []
    skip_db_names = {"Product_SKU", "Product_SKU_Position", "Asset_Identifier"}
    if deliverable_override_label:
        skip_db_names.add("Deliverable")
    if psa_image_type_override_label:
        skip_db_names.add(PSA_IMAGE_TYPE_DBNAME)
    for key, value in source_media.items():
        if not key.startswith("property_"):
            continue
        dbname = key[len("property_"):]
        if dbname in skip_db_names:
            continue
        mp = metaprops_by_dbname.get(dbname)
        if not mp:
            continue
        mp_id = string_value(mp.get("id"))
        if not mp_id:
            continue
        form_key = f"metaproperty.{mp_id}"
        if value is None:
            continue
        if isinstance(value, list):
            for v in value:
                if isinstance(v, dict):
                    vid = v.get("id") or v.get("optionId") or v.get("value")
                    if vid:
                        fields.append((form_key, str(vid)))
                else:
                    if string_value(v):
                        fields.append((form_key, str(v)))
        elif isinstance(value, dict):
            vid = value.get("id") or value.get("optionId") or value.get("value")
            if vid:
                fields.append((form_key, str(vid)))
        else:
            if string_value(value):
                fields.append((form_key, str(value)))
    fields.append((f"metaproperty.{PRODUCT_SKU_METAPROPERTY_ID}", target_sku))
    fields.append((f"metaproperty.{PRODUCT_SKU_POSITION_METAPROPERTY_ID}", target_position))
    if deliverable_override_label:
        append_deliverable_field(session, fields, metaprops_by_dbname, deliverable_override_label)
    if psa_image_type_override_label:
        append_psa_image_type_field(session, fields, metaprops_by_dbname, psa_image_type_override_label)
    asset_identifier_mp = metaprops_by_dbname.get("Asset_Identifier")
    if asset_identifier_mp:
        asset_identifier_mp_id = string_value(asset_identifier_mp.get("id"))
        if asset_identifier_mp_id and string_value(target_name):
            fields.append((f"metaproperty.{asset_identifier_mp_id}", string_value(target_name)))
    fields.append(("name", target_name))
    fields.append(("tags", target_sku))
    return fields


def renamed_copy_filename(original_filename: str, source_sku: str, target_sku: str) -> str:
    original_filename = original_filename or f"{source_sku}.jpg"
    if source_sku and source_sku in original_filename:
        return original_filename.replace(source_sku, target_sku, 1)
    stem, ext = os.path.splitext(original_filename)
    return f"{target_sku}_{stem}{ext or '.jpg'}"


def create_copied_asset_for_target(
    session: requests.Session,
    source_media_id: str,
    source_sku: str,
    target_sku: str,
    target_position: str,
    asset_name: str = "",
    deliverable_override_label: str = "",
    psa_image_type_override_label: str = "",
) -> Dict[str, Any]:
    source_media = fetch_media_by_id(session, source_media_id)
    fallback_name = string_value(source_media.get("name")) or f"{source_media_id}.jpg"
    original_name = filename_from_original(string_value(source_media.get("original")), fallback_name)
    forced_name = string_value(asset_name)
    if forced_name:
        forced_path = Path(forced_name)
        ext = forced_path.suffix or Path(original_name).suffix or ".jpg"
        new_filename = f"{forced_path.stem}{ext}"
    else:
        new_filename = renamed_copy_filename(original_name, source_sku, target_sku)
    temp_path, td = download_source_media_to_tempfile(session, source_media_id, new_filename)
    try:
        target_name = os.path.splitext(Path(new_filename).name)[0]
        new_media_id = upload_new_asset_group_upload(session, temp_path, target_name)
    finally:
        try:
            td.cleanup()
        except Exception:
            pass
    metaprops_by_dbname = fetch_metaproperties_map(session)
    fields = build_metadata_copy_fields(session, source_media, metaprops_by_dbname, target_sku, target_position, target_name, deliverable_override_label, psa_image_type_override_label)
    post_media_fields(session, new_media_id, fields)
    return {"new_media_id": new_media_id, "new_filename": temp_path.name, "target_name": target_name}



class LocalUploadWrapper:
    def __init__(self, path: Path, filename: str) -> None:
        self._path = Path(path)
        self.filename = filename

    def save(self, dst: str | os.PathLike[str]) -> None:
        shutil.copyfile(self._path, Path(dst))


def force_jpg_filename(name: str, fallback_stem: str = "prepared_image") -> str:
    clean = secure_filename(name or "") or fallback_stem
    stem = Path(clean).stem or fallback_stem
    return f"{stem}.jpg"


def apply_prepared_file_to_slot(
    session: requests.Session,
    board: Dict[str, Any],
    row_id: str,
    target_lane: str,
    target_slot: str,
    prepared_file_path: Path,
    psa_image_type_override: str = "",
) -> Dict[str, Any]:
    row = get_row_by_id(board, row_id)
    if not row:
        raise RuntimeError("Target row not found.")
    sku = string_value(row.get("sku"))
    if not sku:
        raise RuntimeError("Target row is missing a SKU.")

    buckets = bucket_assets(row)
    existing_assets = []
    if target_lane == 'grid':
        existing_assets = buckets['grid'].get(GRID_SLOT, [])
    elif target_lane == 'core':
        existing_assets = buckets['core'].get(target_slot, [])
    elif target_lane == 'swatch_detail':
        existing_assets = buckets['swatch_detail'].get(target_slot, [])
    elif target_lane == 'special':
        existing_assets = buckets['special'].get(target_slot, [])
    else:
        raise RuntimeError("Prepared drops are only supported for Grid, Product Carousel, Swatch Detail, and Special Slots.")

    with tempfile.TemporaryDirectory(prefix='content_refresher_prepared_slot_') as td:
        prepared_name = force_jpg_filename(prepared_file_path.name, "prepared_image")
        temp_path = Path(td) / prepared_name
        shutil.copyfile(prepared_file_path, temp_path)

        if existing_assets:
            target_asset = existing_assets[0]
            target_media_id = target_asset.get('copy_source_media_id') if target_asset.get('pending_upload') else target_asset.get('id')
            if not target_media_id:
                raise RuntimeError("Could not determine target media for new version upload.")
            existing_name = string_value(target_asset.get('file_name') or target_asset.get('name')) or prepared_name
            target_name = force_jpg_filename(existing_name, Path(prepared_name).stem or "prepared_image")
            version_path = temp_path
            if temp_path.name != target_name:
                version_path = Path(td) / target_name
                shutil.copyfile(temp_path, version_path)
            upload_new_version_to_media(session, target_media_id, version_path, target_name)
            if string_value(psa_image_type_override):
                set_media_psa_image_type(session, target_media_id, psa_image_type_override)
            mark_asset_uploaded_notice(target_asset, 'new_version', 'New version uploaded to this slot. Reload to view.')
            if string_value(psa_image_type_override):
                target_asset["property_" + PSA_IMAGE_TYPE_DBNAME] = psa_image_type_override
            return {"message": "Prepared image was updated. Reload to see it!", "kind": "updated"}

        profile = resolve_new_asset_profile(row, target_lane, target_slot, prepared_name, compact_text(string_value(board.get('workspace'))) == compact_text(WORKSPACE_PIO))
        exemplar = profile.get("exemplar")
        if not exemplar:
            raise RuntimeError("Could not find a source asset in this row to borrow metadata from for the upload.")

        target_name = force_jpg_filename(profile.get("target_name") or prepared_name, Path(prepared_name).stem or "prepared_image")
        target_slot = string_value(profile.get("target_slot") or target_slot)
        target_path = temp_path
        if temp_path.name != target_name:
            target_path = Path(td) / target_name
            shutil.copyfile(temp_path, target_path)

        target_position = exact_position_for_row(sku, target_slot)
        target_stem = Path(target_name).stem
        new_media_id = upload_new_asset_group_upload(session, target_path, target_stem)
        source_media_id = exemplar.get('copy_source_media_id') if exemplar.get('pending_upload') else exemplar.get('id')
        if not source_media_id:
            raise RuntimeError("Could not determine source media for metadata copy.")
        source_media = fetch_media_by_id(session, source_media_id)
        metaprops_by_dbname = fetch_metaproperties_map(session)
        effective_psa_image_type = string_value(psa_image_type_override or profile.get("psa_image_type_override") or "")
        fields = build_metadata_copy_fields(session, source_media, metaprops_by_dbname, sku, target_position, target_stem, profile.get("deliverable_override", ""), effective_psa_image_type)
        post_media_fields(session, new_media_id, fields)
        placeholder = build_uploaded_new_asset_placeholder(exemplar, sku, target_position, target_name, target_lane, target_slot, new_media_id, profile.get("deliverable_override", ""), effective_psa_image_type)
        row.setdefault('assets', []).append(placeholder)
        return {"message": "Prepared image was added. Reload to see it!", "kind": "added"}


def apply_prepared_media_to_slot(
    session: requests.Session,
    board: Dict[str, Any],
    row_id: str,
    target_lane: str,
    target_slot: str,
    media_id: str,
    prep_mode: str,
    flip: bool,
    offset_y: Any,
    offset_x: Any = None,
    psa_image_type_override: str = "",
) -> Dict[str, Any]:
    psa_image_type_override = effective_psa_image_type_for_target(target_lane, target_slot, psa_image_type_override)
    if string_value(prep_mode) == 'original' and not bool(flip):
        temp_path, td = download_source_media_to_tempfile(session, media_id, f"prepared_original_{media_id}.jpg")
        try:
            return apply_prepared_file_to_slot(session, board, row_id, target_lane, target_slot, temp_path, psa_image_type_override)
        finally:
            try:
                td.cleanup()
            except Exception:
                pass
    img = open_image_from_media(session, media_id)
    result = prepare_photo_result(img, prep_mode, flip, offset_y, offset_x)
    out_w, out_h = result.size
    with tempfile.TemporaryDirectory(prefix="content_refresher_prepped_drop_") as td:
        temp_path = Path(td) / f"prepared_{out_w}x{out_h}{'_flip' if flip else ''}.jpg"
        result = result.convert("RGB")
        result.save(temp_path, format="JPEG", quality=92, optimize=True)
        return apply_prepared_file_to_slot(session, board, row_id, target_lane, target_slot, temp_path, psa_image_type_override)


def upload_new_version_to_media(session: requests.Session, media_id: str, file_path: Path, file_name: str) -> Dict[str, Any]:
    file_name = secure_filename(file_name or file_path.name or "upload.bin") or "upload.bin"
    if not Path(file_name).suffix:
        file_name = f"{Path(file_name).name}{(file_path.suffix or '.jpg')}"

    # Follow the proven massVersionUpdater flow as literally as possible.
    endpoint_resp = request_with_retries(session, "GET", f"{BYNDER_BASE_URL}/api/upload/endpoint")
    endpoint_data = endpoint_resp.json()
    upload_endpoint = endpoint_data.get("endpoint") if isinstance(endpoint_data, dict) else endpoint_data
    if not upload_endpoint:
        raise RuntimeError(f"Could not determine upload endpoint: {endpoint_data}")

    file_size = file_path.stat().st_size
    init_payload = {"filename": file_name, "filesize": str(file_size)}
    init_resp = request_with_retries(session, "POST", f"{BYNDER_BASE_URL}/api/upload/init", data=init_payload)
    init_data = init_resp.json()
    s3file = init_data.get("s3file") or {}
    upload_id = string_value(s3file.get("uploadid") or init_data.get("uploadid") or init_data.get("id"))
    target_id = string_value(s3file.get("targetid") or init_data.get("targetid") or init_data.get("targetId"))
    s3_filename = string_value(init_data.get("s3_filename"))
    base_params = dict(init_data.get("multipart_params") or {})
    if not (upload_id and target_id and s3_filename and base_params):
        raise RuntimeError(f"Upload init missing expected values: {init_data}")

    total_chunks = (file_size // CHUNK_SIZE_BYTES) + (1 if file_size % CHUNK_SIZE_BYTES else 0)
    with open(file_path, "rb") as fh:
        for i in range(1, total_chunks + 1):
            chunk = fh.read(CHUNK_SIZE_BYTES)
            params = base_params.copy()
            params.update({
                "chunk": str(i),
                "chunks": str(total_chunks),
                "Filename": f"{s3_filename}/p{i}",
                "key": f"{s3_filename}/p{i}",
                "name": f"{s3_filename}/p{i}",
            })
            up = requests.post(upload_endpoint, data=params, files={"file": (file_name, chunk)}, timeout=REQUEST_TIMEOUT)
            up.raise_for_status()
            request_with_retries(
                session,
                "POST",
                f"{BYNDER_BASE_URL}/api/v4/upload/{upload_id}/",
                data={"chunkNumber": i, "targetid": target_id, "filename": params["Filename"]},
            )

    fin_resp = request_with_retries(
        session,
        "POST",
        f"{BYNDER_BASE_URL}/api/v4/upload/{upload_id}/",
        data={
            "targetid": target_id,
            "s3_filename": s3_filename,
            "chunks": str(total_chunks),
            "original_filename": file_name,
        },
    )
    fin_data = fin_resp.json()
    import_id = string_value(fin_data.get("importId") or fin_data.get("importid") or fin_data.get("id"))
    if not import_id:
        raise RuntimeError(f"No importId returned from finalize: {fin_data}")

    start_time = time.time()
    while True:
        poll_resp = request_with_retries(session, "GET", f"{BYNDER_BASE_URL}/api/v4/upload/poll/", params={"items": import_id})
        poll_data = poll_resp.json()
        if import_id in safe_list(poll_data.get("itemsDone")):
            break
        if import_id in safe_list(poll_data.get("itemsFailed")) or import_id in safe_list(poll_data.get("itemsRejected")):
            raise RuntimeError(f"Upload processing failed for importId {import_id}")
        if time.time() - start_time > 300:
            raise RuntimeError(f"Polling timed out for importId {import_id}")
        time.sleep(1)

    save_resp = request_with_retries(session, "POST", f"{BYNDER_BASE_URL}/api/v4/media/{media_id}/save/{import_id}/")
    payload = save_resp.json() if save_resp.content else {}
    return {"status_code": save_resp.status_code, "payload": payload}


def pick_lane_exemplar_asset(row: Dict[str, Any], target_lane: str) -> Optional[Dict[str, Any]]:
    candidates = [a for a in row.get("assets", []) if not a.get("pending_upload") and not a.get("is_marked_for_deletion") and a.get("lane") == target_lane]
    if candidates:
        uploaded_candidates = [a for a in candidates if a.get('asset_mode_uploaded') and (a.get('copy_source_media_id') or a.get('id'))]
        pool = uploaded_candidates or candidates
        return sorted(pool, key=lambda a: a.get("dateCreated") or "", reverse=True)[0]
    candidates = [a for a in row.get("assets", []) if not a.get("pending_upload") and not a.get("is_marked_for_deletion")]
    if candidates:
        return sorted(candidates, key=lambda a: a.get("dateCreated") or "", reverse=True)[0]
    return None


def lane_slot_sequence(target_lane: str) -> List[str]:
    if target_lane == 'core':
        return CORE_SLOTS
    if target_lane == 'swatch_detail':
        return SWATCH_DETAIL_SLOTS
    if target_lane == 'special':
        return SPECIAL_SLOTS
    if target_lane == 'grid':
        return [GRID_SLOT]
    return []


def pick_left_exemplar_asset(row: Dict[str, Any], target_lane: str, target_slot: str) -> Optional[Dict[str, Any]]:
    buckets = bucket_assets(row)
    seq = lane_slot_sequence(target_lane)
    if target_slot in seq:
        idx = seq.index(target_slot)
        for slot in reversed(seq[:idx]):
            lane_bucket = buckets['grid'] if target_lane == 'grid' else buckets.get(target_lane, {})
            items = lane_bucket.get(slot, [])
            candidates = [a for a in items if not a.get('pending_upload') and not a.get('is_marked_for_deletion')]
            uploaded_candidates = [a for a in candidates if a.get('asset_mode_uploaded') and (a.get('copy_source_media_id') or a.get('id'))]
            if uploaded_candidates:
                return uploaded_candidates[0]
            if candidates:
                return candidates[0]
    return pick_lane_exemplar_asset(row, target_lane)


def derive_cru_filename(row: Dict[str, Any], target_lane: str, exemplar_asset: Dict[str, Any], uploaded_original_name: str) -> str:
    exemplar_file = string_value(exemplar_asset.get("file_name") or exemplar_asset.get("name") or "asset.jpg") or "asset.jpg"
    exemplar_path = Path(exemplar_file)
    uploaded_ext = Path(uploaded_original_name or "").suffix or exemplar_path.suffix or ".jpg"
    base_stem = re.sub(r"_CRU\d+$", "", exemplar_path.stem, flags=re.IGNORECASE) or exemplar_path.stem or "asset"
    existing_full = set()
    existing_stems = set()
    for asset in row.get("assets", []) or []:
        if string_value(asset.get("lane")) != target_lane:
            continue
        file_name = string_value(asset.get("file_name") or asset.get("name"))
        if file_name:
            existing_full.add(file_name.lower())
            existing_stems.add(Path(file_name).stem.lower())
    i = 1
    while True:
        candidate = f"{base_stem}_CRU{i}{uploaded_ext}"
        candidate_stem = Path(candidate).stem.lower()
        if candidate.lower() not in existing_full and candidate_stem not in existing_stems:
            return candidate
        i += 1


def pick_any_asset_for_sku(row: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    candidates = [a for a in row.get("assets", []) if not a.get("pending_upload") and not a.get("is_marked_for_deletion")]
    if not candidates:
        return None
    uploaded_candidates = [a for a in candidates if a.get("asset_mode_uploaded") and (a.get("copy_source_media_id") or a.get("id"))]
    pool = uploaded_candidates or candidates
    return sorted(pool, key=lambda a: a.get("dateCreated") or "", reverse=True)[0]


def pick_last_carousel_lane_asset(row: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    buckets = bucket_assets(row)
    for slot in reversed(CORE_SLOTS):
        items = buckets["core"].get(slot, [])
        candidates = [a for a in items if not a.get("pending_upload") and not a.get("is_marked_for_deletion")]
        uploaded_candidates = [a for a in candidates if a.get("asset_mode_uploaded") and (a.get("copy_source_media_id") or a.get("id"))]
        pool = uploaded_candidates or candidates
        if pool:
            return pool[0]
    return None


def lane_has_non_deleted_assets(row: Dict[str, Any], lane: str) -> bool:
    buckets = bucket_assets(row)
    if lane == "core":
        return any(buckets["core"].get(slot) for slot in CORE_SLOTS)
    if lane == "swatch_detail":
        return any(buckets["swatch_detail"].get(slot) for slot in SWATCH_DETAIL_SLOTS)
    return False


def resolve_new_asset_profile(row: Dict[str, Any], target_lane: str, target_slot: str, uploaded_original_name: str, is_pio: bool = False) -> Dict[str, Any]:
    sku = string_value(row.get("sku") or "").strip()
    if target_lane == "grid":
        exemplar = pick_last_carousel_lane_asset(row) or pick_any_asset_for_sku(row)
        forced_stem = pio_target_asset_name(sku, 'SKU_grid') if is_pio else force_jpg_filename(f"{sku}_grid_CRU" if sku else "SKU_grid_CRU", f"{sku}_grid_CRU" if sku else "SKU_grid_CRU")
        return {
            "exemplar": exemplar,
            "target_slot": GRID_SLOT,
            "deliverable_override": "Product_Grid_Image",
            "target_name": forced_stem,
        }

    if target_lane == "special" and target_slot in {"SKU_dimension", "SKU_swatch", "SKU_square"}:
        exemplar = pick_last_carousel_lane_asset(row) or pick_any_asset_for_sku(row)
        special_map = {
            "SKU_dimension": ("DimensionsDiagram", f"{sku}_dimension_CRU" if sku else "SKU_dimension_CRU"),
            "SKU_swatch": ("Product_Swatch_Image", f"{sku}_swatch_CRU" if sku else "SKU_swatch_CRU"),
            "SKU_square": ("MetaCarouselSquare", f"{sku}_square_CRU" if sku else "SKU_square_CRU"),
        }
        deliverable_override, forced_stem = special_map[target_slot]
        if is_pio:
            forced_stem = pio_target_asset_name(sku, target_slot)
        return {
            "exemplar": exemplar,
            "target_slot": target_slot,
            "deliverable_override": deliverable_override,
            "psa_image_type_override": (
                SWATCH_PSA_IMAGE_TYPE_LABEL if target_slot == "SKU_swatch"
                else DIMENSIONS_PSA_IMAGE_TYPE_LABEL if target_slot == "SKU_dimension"
                else SQUARE_PSA_IMAGE_TYPE_LABEL if target_slot == "SKU_square"
                else ""
            ),
            "target_name": forced_stem if is_pio else force_jpg_filename(forced_stem, forced_stem),
        }

    if target_lane == "core" and not lane_has_non_deleted_assets(row, "core"):
        exemplar = pick_any_asset_for_sku(row)
        forced_stem = pio_target_asset_name(sku, 'SKU_100') if is_pio else f"{sku}_carousel_CRU" if sku else "SKU_carousel_CRU"
        return {
            "exemplar": exemplar,
            "target_slot": "SKU_100",
            "deliverable_override": "Product_Image_Carousel",
            "target_name": forced_stem if is_pio else force_jpg_filename(forced_stem, forced_stem),
        }

    if target_lane == "swatch_detail" and not lane_has_non_deleted_assets(row, "swatch_detail"):
        exemplar = pick_any_asset_for_sku(row)
        forced_stem = pio_target_asset_name(sku, 'SKU_5000') if is_pio else f"{sku}_swatchDetail_CRU" if sku else "SKU_swatchDetail_CRU"
        return {
            "exemplar": exemplar,
            "target_slot": "SKU_5000",
            "deliverable_override": "Product_Swatch_Detail_Image",
            "target_name": force_jpg_filename(forced_stem, forced_stem),
        }

    exemplar = pick_left_exemplar_asset(row, target_lane, target_slot) or pick_lane_exemplar_asset(row, target_lane) or pick_any_asset_for_sku(row)
    target_name = pio_target_asset_name(sku, target_slot) if is_pio else derive_cru_filename(row, target_lane, exemplar, uploaded_original_name) if exemplar else force_jpg_filename(uploaded_original_name or "prepared_image", "prepared_image")
    return {
        "exemplar": exemplar,
        "target_slot": target_slot,
        "deliverable_override": get_deliverable_override_for_target(target_lane, target_slot),
        "target_name": target_name,
    }


def stage_uploaded_file(uploaded_file_storage) -> Path:
    original_name = secure_filename(uploaded_file_storage.filename or 'upload.bin') or 'upload.bin'
    staged_name = f"{uuid.uuid4().hex}__{original_name}"
    staged_path = STAGED_UPLOAD_DIR / staged_name
    uploaded_file_storage.save(staged_path)
    return staged_path


def cleanup_staged_file(path_text: str) -> None:
    try:
        if path_text:
            Path(path_text).unlink(missing_ok=True)
    except Exception:
        pass


def build_pending_new_asset(source_asset: Dict[str, Any], target_sku: str, target_position: str, staged_path: Path, target_name: str, deliverable_override: str = "", psa_image_type_override: str = "") -> Dict[str, Any]:
    clone = deepcopy(source_asset)
    clone["id"] = f"pending-file::{uuid.uuid4()}"
    clone["sku"] = target_sku
    clone["pending_upload"] = True
    clone["pending_upload_kind"] = "new_asset"
    clone["copy_source_media_id"] = source_asset.get("copy_source_media_id") or source_asset.get("id")
    clone["copy_source_sku"] = source_asset.get("copy_source_sku") or source_asset.get("sku") or source_asset.get("source_sku") or ""
    clone["source_sku"] = clone["copy_source_sku"]
    clone["staged_file_path"] = str(staged_path)
    clone["file_name"] = target_name
    clone["name"] = os.path.splitext(target_name)[0]
    clone["is_marked_for_deletion"] = False
    clone["original_state"] = {"position": "", "is_marked_for_deletion": False}
    clone["current_position"] = target_position
    clone["last_nontrash_position"] = target_position
    clone["pending_message"] = "Pending new asset upload"
    clone["size_warning"] = ""
    clone["pending_file_local_name"] = Path(staged_path).name.split('__',1)[-1]
    clone["deliverable_override"] = string_value(deliverable_override)
    clone["deliverable"] = string_value(deliverable_override or source_asset.get("deliverable") or "")
    clone["psa_image_type_override"] = string_value(psa_image_type_override)
    return clone


def mark_pending_new_version(asset: Dict[str, Any], staged_path: Path, target_name: str) -> None:
    asset["pending_upload"] = True
    asset["pending_upload_kind"] = "new_version"
    asset["staged_file_path"] = str(staged_path)
    asset["pending_message"] = "Pending new version upload"
    asset["file_name"] = target_name
    asset["name"] = os.path.splitext(target_name)[0]


def mark_asset_uploaded_notice(asset: Dict[str, Any], kind: str, message: str) -> None:
    asset["asset_mode_uploaded"] = kind
    asset["asset_mode_message"] = message


def build_uploaded_new_asset_placeholder(source_asset: Dict[str, Any], target_sku: str, target_position: str, target_name: str, target_lane: str, target_slot: str, new_media_id: str = '', deliverable_override: str = '', psa_image_type_override: str = '') -> Dict[str, Any]:
    clone = deepcopy(source_asset)
    clone["id"] = new_media_id or f"uploaded-placeholder::{uuid.uuid4()}"
    clone["copy_source_media_id"] = new_media_id or source_asset.get("copy_source_media_id") or source_asset.get("id") or ''
    clone["sku"] = target_sku
    clone["lane"] = target_lane
    clone["slot_key"] = target_slot
    clone["current_position"] = target_position
    clone["last_nontrash_position"] = target_position
    clone["is_marked_for_deletion"] = False
    clone["asset_mode_uploaded"] = "new_asset"
    clone["asset_mode_message"] = "New asset uploaded to this slot. Reload to view."
    clone["file_name"] = target_name
    clone["name"] = os.path.splitext(target_name)[0]
    clone["original_state"] = {"position": target_position, "is_marked_for_deletion": False, "deliverable": string_value(deliverable_override or source_asset.get("deliverable") or "")}
    clone["dateCreated"] = datetime.now().isoformat()
    clone["transformBaseUrl"] = ""
    clone["original"] = ""
    clone["size_warning"] = ""
    clone["deliverable_override"] = string_value(deliverable_override)
    clone["deliverable"] = string_value(deliverable_override or source_asset.get("deliverable") or "")
    clone["psa_image_type_override"] = string_value(psa_image_type_override)
    clone.pop("pending_upload", None)
    clone.pop("pending_upload_kind", None)
    clone.pop("pending_message", None)
    clone.pop("staged_file_path", None)
    return clone


def apply_uploaded_file_to_slot(session: requests.Session, board: Dict[str, Any], row_id: str, target_lane: str, target_slot: str, uploaded_file_storage, psa_image_type_override: str = "") -> str:
    psa_image_type_override = effective_psa_image_type_for_target(target_lane, target_slot, psa_image_type_override)
    row = get_row_by_id(board, row_id)
    if not row:
        raise RuntimeError("Target row not found.")
    sku = string_value(row.get("sku"))
    if not sku:
        raise RuntimeError("Target row is missing a SKU.")

    buckets = bucket_assets(row)
    existing_assets = []
    if target_lane == 'grid':
        existing_assets = buckets['grid'].get(GRID_SLOT, [])
    elif target_lane == 'core':
        existing_assets = buckets['core'].get(target_slot, [])
    elif target_lane == 'swatch_detail':
        existing_assets = buckets['swatch_detail'].get(target_slot, [])
    elif target_lane == 'special':
        existing_assets = buckets['special'].get(target_slot, [])
    else:
        raise RuntimeError("File drops are only supported for Grid, Product Carousel, Swatch Detail, and Special Slots.")

    with tempfile.TemporaryDirectory(prefix='content_refresher_filedrop_') as td:
        original_name = secure_filename(uploaded_file_storage.filename or 'upload.bin') or 'upload.bin'
        temp_path = Path(td) / original_name
        uploaded_file_storage.save(temp_path)

        if existing_assets:
            target_asset = existing_assets[0]
            target_media_id = target_asset.get('copy_source_media_id') if target_asset.get('pending_upload') else target_asset.get('id')
            if not target_media_id:
                raise RuntimeError("Could not determine target media for new version upload.")
            target_name = string_value(target_asset.get('file_name') or target_asset.get('name')) or original_name
            if not Path(target_name).suffix:
                target_name = f"{target_name}{(temp_path.suffix or '.jpg')}"
            version_path = temp_path
            if temp_path.name != target_name:
                version_path = Path(td) / target_name
                shutil.copyfile(temp_path, version_path)
            upload_new_version_to_media(session, target_media_id, version_path, target_name)
            if string_value(psa_image_type_override):
                set_media_psa_image_type(session, target_media_id, psa_image_type_override)
                target_asset["property_" + PSA_IMAGE_TYPE_DBNAME] = psa_image_type_override
            mark_asset_uploaded_notice(target_asset, 'new_version', 'New version uploaded to this slot. Reload to view.')
            return {"message": "Asset was updated. Reload to see it!", "kind": "updated"}

        profile = resolve_new_asset_profile(row, target_lane, target_slot, original_name, compact_text(string_value(board.get('workspace'))) == compact_text(WORKSPACE_PIO))
        exemplar = profile.get("exemplar")
        if not exemplar:
            raise RuntimeError("Could not find a source asset in this row to borrow metadata from for the upload.")

        target_name = force_jpg_filename(profile.get("target_name") or original_name, Path(original_name).stem or "upload")
        target_slot = string_value(profile.get("target_slot") or target_slot)
        target_path = temp_path
        if temp_path.name != target_name:
            target_path = Path(td) / target_name
            shutil.copyfile(temp_path, target_path)

        target_position = exact_position_for_row(sku, target_slot)
        target_stem = os.path.splitext(target_name)[0]
        new_media_id = upload_new_asset_group_upload(session, target_path, target_stem)
        source_media_id = exemplar.get('copy_source_media_id') if exemplar.get('pending_upload') else exemplar.get('id')
        if not source_media_id:
            raise RuntimeError("Could not determine source media for metadata copy.")
        source_media = fetch_media_by_id(session, source_media_id)
        metaprops_by_dbname = fetch_metaproperties_map(session)
        effective_psa_image_type = string_value(psa_image_type_override or profile.get("psa_image_type_override") or "")
        fields = build_metadata_copy_fields(session, source_media, metaprops_by_dbname, sku, target_position, target_stem, profile.get("deliverable_override", ""), effective_psa_image_type)
        post_media_fields(session, new_media_id, fields)
        placeholder = build_uploaded_new_asset_placeholder(exemplar, sku, target_position, target_name, target_lane, target_slot, new_media_id, profile.get("deliverable_override", ""), effective_psa_image_type)
        row.setdefault('assets', []).append(placeholder)
        return {"message": "Asset was added. Reload to see it!", "kind": "added"}


# ============================================================
# HELPERS - CONTENT REFRESHER LOGIC
# ============================================================
def is_marked_for_deletion(asset: Dict[str, Any]) -> bool:
    value = asset.get(f"property_{PROPERTY_DB_NAMES['Marked_for_Deletion']}")
    for item in safe_list(value):
        text = string_value(item)
        if not text:
            continue
        if normalize_uuid(text) == normalize_uuid(MARKED_FOR_DELETION_OPTION_ID):
            return True
        if text == MARKED_FOR_DELETION_VALUE_NAME:
            return True
    return False


def is_allowed_deliverable(asset: Dict[str, Any]) -> bool:
    return prop(asset, "Deliverable", "Deliverable") in ALLOWED_DELIVERABLES


def is_board_relevant_asset(asset: Dict[str, Any], sku: str = "") -> bool:
    if not is_product_site_asset(asset):
        return False
    normalized_position = normalize_position_for_row(get_asset_position(asset), sku or prop(asset, "Product_SKU", "Product_SKU"))
    if normalized_position == "SKU_square":
        return True
    return is_allowed_deliverable(asset)


def is_product_site_asset(asset: Dict[str, Any]) -> bool:
    return string_value(asset.get("property_Asset_Sub-Type")) == ASSET_SUBTYPE_REQUIRED


def prop(asset: Dict[str, Any], logical_name: str, fallback_db_name: Optional[str] = None) -> str:
    db_name = PROPERTY_DB_NAMES.get(logical_name) or fallback_db_name or logical_name
    value = asset.get(f"property_{db_name}")
    if value is None and fallback_db_name and fallback_db_name != db_name:
        value = asset.get(f"property_{fallback_db_name}")
    return string_value(value)


def get_asset_position(asset: Dict[str, Any]) -> str:
    media_id = string_value(asset.get("id"))
    actual = prop(asset, "Product_SKU_Position", "Product_SKU_Position")
    override = get_recent_position_override(media_id)
    if actual and override and normalize_uuid(actual) == normalize_uuid(override):
        clear_recent_position_override(media_id)
        return actual
    return override or actual


def exact_position_for_row(row_sku: str, normalized_slot: str) -> str:
    if not row_sku:
        return normalized_slot
    if normalized_slot == GRID_SLOT:
        return f"{row_sku}_grid"
    if normalized_slot.startswith("SKU_"):
        suffix = normalized_slot[4:]
        return f"{row_sku}_{suffix}"
    return f"{row_sku}_{normalized_slot.replace('SKU_', '')}"


def normalize_position_for_row(position: str, row_sku: str) -> str:
    pos = string_value(position)
    sku = string_value(row_sku)
    if not pos:
        return ""
    if pos == GRID_SLOT or pos in CORE_SLOTS or pos in SWATCH_DETAIL_SLOTS or pos in SPECIAL_SLOTS:
        return pos
    prefix = f"{sku}_"
    if sku and pos.startswith(prefix):
        suffix = pos[len(prefix):]
        if suffix == 'grid':
            return GRID_SLOT
        if suffix in {'dimension', 'swatch', 'square'}:
            return f"SKU_{suffix}"
        if suffix.isdigit():
            num = int(suffix)
            if num == 8000:
                return SPECIAL_CAROUSEL_SLOT
            if 100 <= num <= 4900 and num % 100 == 0:
                return f"SKU_{num}"
            if 5000 <= num <= 5900 and num % 100 == 0:
                return f"SKU_{num}"
    return ""


def get_lane_and_slot_for_row(position: str, row_sku: str) -> Tuple[str, str]:
    normalized = normalize_position_for_row(position, row_sku)
    if normalized == GRID_SLOT:
        return 'grid', GRID_SLOT
    if normalized in CORE_SLOTS:
        return 'core', normalized
    if normalized in SWATCH_DETAIL_SLOTS:
        return 'swatch_detail', normalized
    if normalized in SPECIAL_SLOTS:
        return 'special', normalized
    return 'off_pattern', string_value(position)




def get_related_asset_ids_for_metaproperty(media: Dict[str, Any], related_metaproperty_id: str) -> List[str]:
    target = normalize_uuid(related_metaproperty_id)
    related_assets = media.get("relatedAssets")
    if related_assets is None:
        return []

    if isinstance(related_assets, dict):
        ra_iter = list(related_assets.values())
    elif isinstance(related_assets, list):
        ra_iter = related_assets
    else:
        return []

    ids: List[str] = []
    for entry in ra_iter:
        if not isinstance(entry, dict):
            continue
        mpid = entry.get("metaPropertyId") or entry.get("metapropertyId") or entry.get("meta_property_id") or ""
        if normalize_uuid(str(mpid)) != target:
            continue
        for key in ("id", "mediaId", "assetId", "relatedAssetId"):
            val = string_value(entry.get(key))
            if val:
                ids.append(val)
        for coll_key in ("items", "media", "related", "assets", "relatedAssets"):
            nested = entry.get(coll_key) or []
            if isinstance(nested, dict):
                nested = list(nested.values())
            if not isinstance(nested, list):
                continue
            for item in nested:
                if isinstance(item, dict):
                    for key in ("id", "mediaId", "assetId", "relatedAssetId", "media_id"):
                        val = string_value(item.get(key))
                        if val:
                            ids.append(val)
                elif isinstance(item, str) and item:
                    ids.append(item)
        for coll_key in ("mediaIds", "assetIds", "relatedIds"):
            nested = entry.get(coll_key) or []
            if isinstance(nested, list):
                for item in nested:
                    if isinstance(item, str) and item:
                        ids.append(item)

    seen=set(); out=[]
    for mid in ids:
        if mid not in seen:
            seen.add(mid); out.append(mid)
    return out

def get_component_skus_for_grid_asset(session: requests.Session, grid_asset: Dict[str, Any]) -> List[str]:
    grid_media_id = string_value(grid_asset.get("id"))
    if not grid_media_id:
        return []
    try:
        full_grid = fetch_media_by_id(session, grid_media_id)
    except Exception:
        full_grid = grid_asset

    raw_component_value = full_grid.get("property_Component_SKUs")
    if not string_value(raw_component_value):
        return []

    media_ids = get_related_asset_ids_for_metaproperty(full_grid, RELATED_COMPONENTS_METAPROPERTY_ID)
    component_skus: List[str] = []
    seen=set()
    for media_id in media_ids:
        try:
            media = fetch_media_by_id(session, media_id)
            sku = string_value(media.get("property_Product_SKU")) or prop(media, "Product_SKU", "Product_SKU")
            if sku and sku not in seen:
                seen.add(sku)
                component_skus.append(sku)
        except Exception:
            continue
    return component_skus


def get_component_skus_for_grid_asset_cached(session: requests.Session, grid_asset: Optional[Dict[str, Any]]) -> List[str]:
    if not grid_asset:
        return []
    grid_media_id = string_value(grid_asset.get("id"))
    if not grid_media_id:
        return []
    cache = STATE.setdefault("component_sku_cache", {})
    if grid_media_id in cache:
        return list(cache[grid_media_id])
    component_skus = get_component_skus_for_grid_asset(session, grid_asset)
    cache[grid_media_id] = list(component_skus)
    return list(component_skus)

def get_dimensions_asset_for_sku(session: requests.Session, sku: str) -> Optional[Dict[str, Any]]:
    if not sku:
        return None
    items = fetch_assets_for_product_sku(session, "Product_SKU", sku)
    candidates: List[Dict[str, Any]] = []
    for item in items:
        position = normalize_position_for_row(get_asset_position(item), sku)
        if position == "SKU_dimension" and not is_marked_for_deletion(item):
            candidates.append(item)
    if not candidates:
        return None
    candidates = sort_assets_in_slot(candidates)
    best = candidates[0]
    return {
        "sku": sku,
        "dim_media_id": string_value(best.get("id")),
        "component_subcat": prop(best, "Product_Sub-Category", "Product_Sub-Category"),
        "name": string_value(best.get("name")),
    }


def get_dimensions_asset_for_sku_cached(session: requests.Session, sku: str) -> Optional[Dict[str, Any]]:
    cache = STATE.setdefault("component_dim_cache", {})
    key = string_value(sku)
    if key in cache:
        cached = cache.get(key)
        return deepcopy(cached) if cached else None
    found = get_dimensions_asset_for_sku(session, key)
    cache[key] = deepcopy(found) if found else None
    return deepcopy(found) if found else None


def build_set_dim_compile_info_for_row(session: requests.Session, row: Dict[str, Any]) -> tuple[bool, List[Dict[str, Any]], str]:
    component_skus = [string_value(x) for x in safe_list(row.get("component_skus")) if string_value(x)]
    if not component_skus:
        return False, [], "No linked component SKUs were found."
    if len(component_skus) > SET_DIM_MAX_COMPONENTS:
        return False, [], f"Set dim compile currently supports up to {SET_DIM_MAX_COMPONENTS} components."
    components: List[Dict[str, Any]] = []
    missing: List[str] = []
    for sku in component_skus:
        found = get_dimensions_asset_for_sku_cached(session, sku)
        if found and found.get("dim_media_id"):
            components.append(found)
        else:
            missing.append(sku)
    if missing:
        return False, components, f"Missing dimensions for: {', '.join(missing)}"
    return True, components, ""

def get_status_from_grid_asset(grid_asset: Dict[str, Any]) -> str:
    dropped = prop(grid_asset, "Dropped", "Dropped")
    visible = prop(grid_asset, "Visible_on_Website", "Visible_on_Website")
    if dropped == "False" and visible == "True":
        return "Active"
    return "Inactive"


def get_color_label(grid_asset: Dict[str, Any]) -> str:
    return prop(grid_asset, "Product_Color", "Product_Color") or "(No Color)"


def get_slot_family(position: str) -> str:
    if position == GRID_SLOT:
        return "grid"
    if position in CORE_SLOTS:
        return "core"
    if position in SWATCH_DETAIL_SLOTS:
        return "swatch_detail"
    if position in SPECIAL_SLOTS:
        return "special"
    return "off_pattern"



def get_cached_total_fill_issue(asset: Dict[str, Any]) -> bool:
    media_id = string_value(asset.get("id"))
    if media_id and media_id in TOTAL_FILL_CHECK_CACHE:
        return bool(TOTAL_FILL_CHECK_CACHE.get(media_id))

    psa_type = compact_text(get_existing_psa_image_type_label(asset) or asset.get("property_" + PSA_IMAGE_TYPE_DBNAME) or asset.get("psa_image_type"))
    if psa_type != "roomshot":
        if media_id:
            TOTAL_FILL_CHECK_CACHE[media_id] = False
        return False

    transform_url = string_value(asset.get("transformBaseUrl"))
    if not transform_url:
        if media_id:
            TOTAL_FILL_CHECK_CACHE[media_id] = False
        return False

    check_url = transform_url
    if "?" in check_url:
        check_url += "&io=transform:scale,width:320&quality=70"
    else:
        check_url += "?io=transform:scale,width:320&quality=70"

    result = False
    try:
        resp = requests.get(check_url, timeout=TOTAL_FILL_CHECK_TIMEOUT)
        resp.raise_for_status()
        with Image.open(BytesIO(resp.content)) as im:
            rgb = im.convert("RGB")
            w, h = rgb.size
            if w > 22 and h > 22:
                off = min(TOTAL_FILL_CHECK_SAMPLE_OFFSET, max(1, (min(w, h) // 4)))
                pts = [
                    (off, off),
                    (w - off - 1, off),
                    (off, h - off - 1),
                    (w - off - 1, h - off - 1),
                ]
                result = all(all(channel >= TOTAL_FILL_CHECK_WHITE_THRESHOLD for channel in rgb.getpixel(pt)) for pt in pts)
    except Exception:
        result = False

    if media_id:
        TOTAL_FILL_CHECK_CACHE[media_id] = result
    return result


def get_total_fill_warning(asset: Dict[str, Any]) -> str:
    if get_cached_total_fill_issue(asset):
        return "Needs total fill: room shot has white corners 10px from each edge."
    return ""


def is_total_fill_warning_text(text: Any) -> bool:
    return "needstotalfill" in compact_text(text)


def asset_is_cleanup_total_fill_candidate(asset: Dict[str, Any], row: Optional[Dict[str, Any]] = None) -> bool:
    if not is_total_fill_warning_text(asset.get("size_warning")):
        return False
    slot_key = string_value(
        asset.get("slot_key")
        or normalize_position_for_row(
            asset.get("current_position"),
            string_value((row or {}).get("sku") or asset.get("sku") or ""),
        )
    )
    if slot_key in {"SKU_grid", "SKU_100"}:
        return True
    if slot_key != "SKU_200":
        return False
    sales_channel = row.get("sales_channel") if isinstance(row, dict) else asset.get("sales_channel")
    return sales_channel_has_full_line(sales_channel)


def row_counts_as_active(row: Optional[Dict[str, Any]]) -> bool:
    status = string_value((row or {}).get("product_status")).strip().lower()
    if not status:
        return True
    return status == "active"


def expected_dimensions_for_slot(slot_key: str) -> Tuple[int, int]:
    if slot_key == "SKU_grid":
        return (3000, 2200)
    if slot_key == "SKU_swatch":
        return (163, 163)
    if slot_key == "SKU_square":
        return (1000, 1000)
    return (3000, 1688)


def compute_dimension_warning(asset: Dict[str, Any]) -> str:
    slot_key = string_value(asset.get("slot_key")) or normalize_position_for_row(asset.get("current_position"), asset.get("sku"))
    if slot_key == "off_pattern":
        return ""
    width = int(asset.get("width") or 0)
    height = int(asset.get("height") or 0)
    total_fill_warning = get_total_fill_warning(asset)
    if slot_key == "SKU_square":
        dimension_warning = ""
        if width > 0 and height > 0:
            if not (width == height and width >= 1000):
                dimension_warning = f"Size {width}x{height}; expected square and at least 1000x1000"
        return "; ".join(part for part in [dimension_warning, total_fill_warning] if part)
    if width <= 0 or height <= 0:
        return total_fill_warning
    expected_w, expected_h = expected_dimensions_for_slot(slot_key)
    dimension_warning = "" if (width == expected_w and height == expected_h) else f"Size {width}x{height}; expected {expected_w}x{expected_h}"
    return "; ".join(part for part in [dimension_warning, total_fill_warning] if part)


def refresh_row_asset_flags(row: Dict[str, Any]) -> None:
    for asset in row.get("assets", []):
        asset["size_warning"] = compute_dimension_warning(asset)
    row["square_make_recommended"] = bool(row_needs_make_square(row))
    row["square_make_tooltip"] = "This SKU has at least one room shot. You might be able to make a nice square image out of it." if row.get("square_make_recommended") else ""


def asset_to_client_model(asset: Dict[str, Any], sku: str, position_override: Optional[str] = None, lane_override: Optional[str] = None, slot_key_override: Optional[str] = None) -> Dict[str, Any]:
    original = string_value(asset.get("original"))
    name = string_value(asset.get("name"))
    file_name = filename_from_original(original, name)
    position = string_value(position_override) or get_asset_position(asset)
    deleted = is_marked_for_deletion(asset)
    lane, slot_key = get_lane_and_slot_for_row(position, sku)
    if lane_override:
        lane = lane_override
    if slot_key_override:
        slot_key = slot_key_override
    display_lane = "trash" if deleted else lane
    return {
        "id": string_value(asset.get("id")),
        "name": name,
        "file_name": file_name,
        "sku": sku,
        "source_sku": sku,
        "dateCreated": string_value(asset.get("dateCreated")),
        "original": original,
        "transformBaseUrl": string_value(asset.get("transformBaseUrl")),
        "deliverable": prop(asset, "Deliverable", "Deliverable"),
        "psa_image_type": get_existing_psa_image_type_label(asset),
        "current_position": position,
        "last_nontrash_position": position,
        "slot_key": slot_key,
        "lane": display_lane,
        "is_marked_for_deletion": deleted,
        "width": int(asset.get("width") or 0),
        "height": int(asset.get("height") or 0),
        "pending_upload": False,
        "asset_status": get_photography_asset_status(asset),
        "is_final": photography_asset_is_final(asset),
        "copy_source_media_id": string_value(asset.get("id")),
        "copy_source_sku": sku,
        "asset_status": get_photography_asset_status(asset),
        "is_final": photography_asset_is_final(asset),
        "original_state": {
            "position": position,
            "is_marked_for_deletion": deleted,
            "deliverable": prop(asset, "Deliverable", "Deliverable"),
        "psa_image_type": get_existing_psa_image_type_label(asset),
        },
        "meta": {
            "productSkuPosition": position,
            "productSku": prop(asset, "Product_SKU", "Product_SKU"),
            "productColor": prop(asset, "Product_Color", "Product_Color"),
        },
    }



def fetch_collection_assets_cached(session: requests.Session, option_id: str, force_refresh: bool = False) -> List[Dict[str, Any]]:
    cache = STATE.setdefault("collection_asset_cache", {})
    if force_refresh:
        cache.pop(option_id, None)
    else:
        cached = get_fresh_cached_value(
            cache,
            option_id,
            COLLECTION_ASSET_CACHE_MAX_AGE_SECONDS,
            cache_label="collection asset",
        )
        if cached is not None:
            return cached
    items = fetch_all_media_for_option(session, option_id)
    set_timed_cached_value(cache, option_id, items)
    return items


def invalidate_collection_caches(option_id: str = "") -> None:
    target = string_value(option_id)
    for key in ("collection_asset_cache", "collection_derived_cache", "collection_board_cache"):
        cache = STATE.setdefault(key, {})
        if target:
            cache.pop(target, None)
        else:
            cache.clear()
    if not target:
        STATE.setdefault("component_sku_cache", {}).clear()
        STATE.setdefault("component_dim_cache", {}).clear()


def replace_row_in_board(board: Dict[str, Any], row_id: str, new_row: Dict[str, Any]) -> bool:
    target = string_value(row_id)
    for section in board.get("color_sections", []):
        rows = section.get("rows", [])
        for idx, row in enumerate(rows):
            if string_value(row.get("row_id")) == target or string_value(row.get("sku")) == target:
                rows[idx] = new_row
                return True
    return False

def parse_photo_tags(asset: Dict[str, Any]) -> List[str]:
    raw = asset.get("tags")
    parts: List[str] = []
    if isinstance(raw, list):
        for item in raw:
            parts.append(string_value(item))
    else:
        parts.append(string_value(raw))
    # Some portals also expose tags text elsewhere; harmless fallback.
    extra = string_value(asset.get("property_tags") or asset.get("property_Tags"))
    if extra:
        parts.append(extra)
    blob = " ".join(parts)
    matches = re.findall(r"(?<![A-Za-z0-9])[A-Za-z0-9]{9}(?![A-Za-z0-9])", blob)
    out: List[str] = []
    seen = set()
    for m in matches:
        if m not in seen:
            seen.add(m)
            out.append(m)
    return out

def parse_all_photo_tags(asset: Dict[str, Any]) -> List[str]:
    raw = asset.get("tags")
    parts: List[str] = []
    if isinstance(raw, list):
        for item in raw:
            value = string_value(item)
            if value:
                parts.append(value)
    else:
        value = string_value(raw)
        if value:
            parts.append(value)
    extra = string_value(asset.get("property_tags") or asset.get("property_Tags"))
    if extra:
        for part in re.split(r"[,;]", extra):
            value = string_value(part)
            if value:
                parts.append(value)
    out: List[str] = []
    seen = set()
    for part in parts:
        for token in re.split(r"[\s,;]+", string_value(part)):
            token = string_value(token)
            if token and token not in seen:
                seen.add(token)
                out.append(token)
    return out

def get_reviewed_for_site_values(asset: Dict[str, Any]) -> List[str]:
    raw = asset.get(f"property_{REVIEWED_FOR_SITE_DBNAME}")
    values: List[str] = []
    if isinstance(raw, list):
        for item in raw:
            if isinstance(item, dict):
                label = string_value(item.get("label") or item.get("name") or item.get("value") or item.get("databaseName"))
                if label:
                    values.append(label)
            else:
                label = string_value(item)
                if label:
                    values.append(label)
    elif isinstance(raw, dict):
        label = string_value(raw.get("label") or raw.get("name") or raw.get("value") or raw.get("databaseName"))
        if label:
            values.append(label)
    else:
        label = string_value(raw)
        if label:
            values.extend([x.strip() for x in re.split(r"[,;|]", label) if x.strip()])
    seen = set()
    out: List[str] = []
    for value in values:
        key = value.strip().lower()
        if key and key not in seen:
            seen.add(key)
            out.append(value.strip())
    return out


def photo_asset_is_reviewed_for_site(asset: Dict[str, Any]) -> bool:
    return any(string_value(v).strip().lower() == REVIEWED_FOR_SITE_LABEL.lower() for v in get_reviewed_for_site_values(asset))

def photo_asset_to_client_model(asset: Dict[str, Any], matching_skus: List[str]) -> Dict[str, Any]:
    original = string_value(asset.get("original"))
    name = string_value(asset.get("name"))
    file_name = filename_from_original(original, name)
    tags = parse_photo_tags(asset)
    all_tags = parse_all_photo_tags(asset)
    matching = [t for t in tags if t in set(matching_skus)]
    fp = asset.get("activeOriginalFocusPoint") or {}
    reviewed_values = get_reviewed_for_site_values(asset)
    return {
        "id": string_value(asset.get("id")),
        "name": name,
        "file_name": file_name,
        "dateCreated": string_value(asset.get("dateCreated")),
        "original": original,
        "transformBaseUrl": string_value(asset.get("transformBaseUrl")),
        "width": int(asset.get("width") or 0),
        "height": int(asset.get("height") or 0),
        "source": prop(asset, "Source", "Source"),
        "season": prop(asset, "Season", "Season"),
        "image_type": prop(asset, "ImageType", "ImageType"),
        "asset_status": get_photography_asset_status(asset),
        "is_final": photography_asset_is_final(asset),
        "reviewed_for_site": photo_asset_is_reviewed_for_site(asset),
        "reviewed_for_site_values": reviewed_values,
        "tags": tags,
        "sku_tags": tags,
        "all_tags": all_tags,
        "matching_skus": matching,
        "focus_x": int(fp.get("x") or 0) if fp else 0,
        "focus_y": int(fp.get("y") or 0) if fp else 0,
    }

def is_available_product_photography_asset(asset: Dict[str, Any], color: Optional[str] = None) -> bool:
    subtype = string_value(asset.get("property_Asset_Sub-Type"))
    if subtype != PHOTO_ASSET_SUBTYPE:
        return False
    image_type = string_value(asset.get("property_ImageType"))
    if image_type in PHOTO_EXCLUDED_IMAGE_TYPES:
        return False
    if color is not None and string_value(asset.get("property_Product_Color")) != string_value(color):
        return False
    return True


def count_available_product_photography_by_color(raw_collection_assets: List[Dict[str, Any]]) -> Dict[str, int]:
    counts: Dict[str, int] = defaultdict(int)
    for asset in raw_collection_assets:
        if not is_available_product_photography_asset(asset):
            continue
        color = string_value(asset.get("property_Product_Color"))
        if color:
            counts[color] += 1
    return counts


def get_media_count_for_keyword(session: requests.Session, keyword: str) -> int:
    url = f"{BYNDER_BASE_URL}/api/v4/media/"
    params = {"keyword": keyword, "limit": 1, "total": 1}
    response = request_with_retries(session, "GET", url, params=params)
    payload = response.json()
    return int(payload.get("total", {}).get("count", 0))


def fetch_media_page_for_keyword(session: requests.Session, keyword: str, page: int, limit: int = PAGE_LIMIT) -> List[Dict[str, Any]]:
    url = f"{BYNDER_BASE_URL}/api/v4/media/"
    params = {"keyword": keyword, "limit": limit, "page": page}
    response = request_with_retries(session, "GET", url, params=params)
    return extract_media_items(response.json())


def fetch_all_media_for_keyword(session: requests.Session, keyword: str, limit: int = PAGE_LIMIT) -> List[Dict[str, Any]]:
    expected_count = get_media_count_for_keyword(session, keyword)
    log_message(f"Expected asset count for keyword {keyword}: {expected_count}")
    if expected_count == 0:
        return []

    total_pages = math.ceil(expected_count / limit)
    all_items: List[Dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=min(MAX_WORKERS, total_pages or 1)) as executor:
        futures = {
            executor.submit(fetch_media_page_for_keyword, session, keyword, page, limit): page
            for page in range(1, total_pages + 1)
        }
        for future in as_completed(futures):
            page = futures[future]
            page_items = future.result()
            all_items.extend(page_items)
            log_message(f"Fetched page {page}/{total_pages} for keyword {keyword}: {len(page_items)} assets")

    deduped: Dict[str, Dict[str, Any]] = {}
    for item in all_items:
        media_id = string_value(item.get("id"))
        if media_id:
            deduped[media_id] = item
    final_items = list(deduped.values())
    log_message(f"Retrieved {len(final_items)} unique assets for keyword {keyword}")
    return final_items


def build_additional_photography_payload_for_sku(
    session: requests.Session,
    sku: str,
    matching_skus: List[str],
    existing_ids: List[str],
) -> List[Dict[str, Any]]:
    existing = {string_value(x) for x in existing_ids if string_value(x)}
    raw_matches = fetch_all_media_for_keyword(session, sku)
    items: List[Dict[str, Any]] = []
    seen: set[str] = set()
    for asset in raw_matches:
        if not is_available_product_photography_asset(asset):
            continue
        media_id = string_value(asset.get("id"))
        if not media_id or media_id in existing or media_id in seen:
            continue
        tags = parse_photo_tags(asset)
        if sku not in tags:
            continue
        seen.add(media_id)
        items.append(photo_asset_to_client_model(asset, matching_skus))
    items.sort(key=lambda a: string_value(a.get("dateCreated")), reverse=True)
    return items


def build_photography_payload_for_color(session: requests.Session, collection_option: Dict[str, str], color: str, color_matching_skus: List[str]) -> Dict[str, Any]:
    option_id = collection_option["id"]
    raw_collection_assets = fetch_collection_assets_cached(session, option_id)
    photos: List[Dict[str, Any]] = [a for a in raw_collection_assets if is_available_product_photography_asset(a, color)]
    photos.sort(key=lambda a: string_value(a.get("dateCreated")), reverse=True)
    return {
        "collection": collection_option,
        "color": color,
        "items": [photo_asset_to_client_model(a, color_matching_skus) for a in photos],
        "loaded_at": datetime.now().isoformat(),
    }


def build_board_row_from_prefetched_assets(
    session: requests.Session,
    sku: str,
    sku_assets: List[Dict[str, Any]],
    collection_label: str,
    is_non_collection: bool = False,
) -> Optional[Dict[str, Any]]:
    filtered_assets = [a for a in sku_assets if is_board_relevant_asset(a, sku)]
    if not filtered_assets:
        return None
    grid_group = [a for a in filtered_assets if normalize_position_for_row(get_asset_position(a), sku) == GRID_SLOT]
    grid_group = sort_assets_in_slot(grid_group)
    newest_grid = max(grid_group, key=lambda a: parse_datetime(a.get("dateCreated")) or datetime.min) if grid_group else None
    anchor = newest_grid or max(filtered_assets, key=lambda a: parse_datetime(a.get("dateCreated")) or datetime.min)
    status = get_status_from_grid_asset(anchor)
    color = get_color_label(anchor)

    oldest_dt = None
    newest_dt = None
    for a in filtered_assets:
        dt = parse_datetime(a.get("dateCreated"))
        if dt is None:
            continue
        if oldest_dt is None or dt < oldest_dt:
            oldest_dt = dt
        if newest_dt is None or dt > newest_dt:
            newest_dt = dt

    client_assets = [asset_to_client_model(a, sku) for a in filtered_assets]
    component_raw = prop(newest_grid or anchor, "Component_SKUs", "Component_SKUs")
    if component_raw:
        component_skus, component_warnings = parse_component_sku_value(component_raw)
    else:
        component_skus = get_component_skus_for_grid_asset_cached(session, newest_grid)
        component_warnings = []
    row = {
        "row_id": sku,
        "sku": sku,
        "product_color": color,
        "sales_channel": prop(anchor, "Sales_Channel", "Sales_Channel"),
        "product_status": status,
        "product_name": prop(anchor, "Product_Name__STEP_", "Product_Name__STEP_"),
        "product_url": prop(anchor, "Product_URL", "Product_URL"),
        "mattress_size": prop(anchor, "Mattress_Size", "Mattress_Size"),
        "component_skus": component_skus,
        "components_raw": component_raw,
        "component_groups": group_component_counts(component_skus),
        "component_warnings": component_warnings,
        "component_display_groups": [],
        "product_collection": prop(anchor, "Product_Collection", "product_collection") or collection_label,
        "product_subcategory": prop(anchor, "Product_Sub-Category", "Product_Sub-Category"),
        "dropped": prop(anchor, "Dropped", "Dropped"),
        "visible_on_website": prop(anchor, "Visible_on_Website", "Visible_on_Website"),
        "step_path": prop(anchor, "STEP_Path", "STEP_Path"),
        "dim_width": prop(anchor, "dim_Width", "dim_Width"),
        "dim_length": prop(anchor, "dim_Length", "dim_Length"),
        "dim_height": prop(anchor, "dim_Height", "dim_Height"),
        "features": prop(anchor, "Features", "Features"),
        "workflow": prop(anchor, "Workflow", "Workflow"),
        "workflow_status": prop(anchor, "Workflow_Status", "Workflow_Status"),
        "sync_to_site": prop(anchor, "Sync_to_Site", "Sync_to_Site"),
        "date_oldest": oldest_dt.isoformat() if oldest_dt else "",
        "date_newest": newest_dt.isoformat() if newest_dt else "",
        "inactive": status != "Active",
        "assets": client_assets,
        "overflow_warnings": [],
        "commit_failures": [],
        "is_non_collection": bool(is_non_collection),
    }
    set_dim_ready, set_dim_components, set_dim_reason = build_set_dim_compile_info_for_row(session, row)
    row["set_dim_compile_ready"] = bool(set_dim_ready)
    row["set_dim_compile_reason"] = set_dim_reason
    row["set_dim_components"] = set_dim_components
    refresh_row_asset_flags(row)
    return row


def build_board_row_for_sku(session: requests.Session, sku: str, collection_label: str = "") -> Optional[Dict[str, Any]]:
    items = fetch_assets_for_product_sku(session, "Product_SKU", sku)
    return build_board_row_from_prefetched_assets(
        session,
        sku,
        items,
        collection_label,
        is_non_collection=True,
    )


def has_additional_photography_for_sku(session: requests.Session, sku: str, existing_ids: List[str]) -> bool:
    existing = {string_value(x) for x in existing_ids if string_value(x)}
    expected_count = get_media_count_for_keyword(session, sku)
    if expected_count <= 0:
        return False
    limit = 250
    total_pages = math.ceil(expected_count / limit)
    for page in range(1, total_pages + 1):
        raw_matches = fetch_media_page_for_keyword(session, sku, page, limit)
        for asset in raw_matches:
            if not is_available_product_photography_asset(asset):
                continue
            media_id = string_value(asset.get("id"))
            if not media_id or media_id in existing:
                continue
            if sku in parse_photo_tags(asset):
                return True
        if len(raw_matches) < limit:
            break
    return False


def insert_non_collection_row(board: Dict[str, Any], row: Dict[str, Any]) -> None:
    sections = board.setdefault("color_sections", [])
    sku = string_value(row.get("sku"))
    for section in sections:
        if string_value(section.get("color")) == "Non-Collection SKUs":
            existing_rows = section.setdefault("rows", [])
            if any(string_value(r.get("sku")) == sku for r in existing_rows):
                return
            existing_rows.insert(0, row)
            return
    sections.insert(0, {
        "color": "Non-Collection SKUs",
        "rows": [row],
        "photo_available_count": 0,
        "is_non_collection": True,
    })


def build_board_for_collection(session: requests.Session, product_collection_option: Dict[str, str], force_refresh: bool = False) -> Dict[str, Any]:
    collection_option_id = product_collection_option["id"]
    collection_label = product_collection_option["label"]

    board_cache = STATE.setdefault("collection_board_cache", {})
    if force_refresh:
        board_cache.pop(collection_option_id, None)
    else:
        cached_board = get_fresh_cached_value(
            board_cache,
            collection_option_id,
            COLLECTION_BOARD_CACHE_MAX_AGE_SECONDS,
            cache_label="collection board",
        )
        if cached_board is not None:
            log_message(f"Using cached board for {collection_label}.")
            return cached_board

    raw_collection_assets = fetch_collection_assets_cached(session, collection_option_id, force_refresh=force_refresh)

    derived_cache = STATE.setdefault("collection_derived_cache", {})
    if force_refresh:
        derived_cache.pop(collection_option_id, None)
        derived = None
    else:
        derived = get_fresh_cached_value(
            derived_cache,
            collection_option_id,
            COLLECTION_DERIVED_CACHE_MAX_AGE_SECONDS,
            cache_label="derived collection",
        )

    if derived is None:
        photo_counts_by_color = count_available_product_photography_by_color(raw_collection_assets)
        psa_assets = [a for a in raw_collection_assets if is_product_site_asset(a)]
        grid_candidates = [a for a in psa_assets if prop(a, "Deliverable", "Deliverable") == "Product_Grid_Image"]
        grid_assets_by_sku = defaultdict(list)
        for asset in grid_candidates:
            sku = prop(asset, "Product_SKU", "Product_SKU")
            if sku:
                grid_assets_by_sku[sku].append(asset)

        unique_skus = sorted(grid_assets_by_sku.keys(), key=natural_sort_key)
        log_message(f"Grid anchor SKU count for {collection_label}: {len(unique_skus)}")

        all_assets_by_sku: Dict[str, List[Dict[str, Any]]] = {}

        def asset_worker(sku: str) -> Tuple[str, List[Dict[str, Any]]]:
            items = fetch_assets_for_product_sku(session, "Product_SKU", sku)
            filtered = [a for a in items if is_board_relevant_asset(a, sku)]
            return sku, filtered

        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
            futures = {executor.submit(asset_worker, sku): sku for sku in unique_skus}
            for future in as_completed(futures):
                sku, items = future.result()
                all_assets_by_sku[sku] = items
                log_message(f"Fetched all board PSAs for SKU {sku}: {len(items)}")

        def row_worker(sku: str) -> Tuple[str, Optional[Dict[str, Any]], str]:
            row = build_board_row_from_prefetched_assets(
                session,
                sku,
                all_assets_by_sku.get(sku, []),
                collection_label,
                is_non_collection=False,
            )
            color = string_value(row.get("product_color")) if row else ""
            return sku, row, color

        rows_by_sku: Dict[str, Dict[str, Any]] = {}
        rows_by_color: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
        with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
            futures = {executor.submit(row_worker, sku): sku for sku in unique_skus}
            for future in as_completed(futures):
                sku, row, color = future.result()
                if not row:
                    continue
                rows_by_sku[sku] = row
                rows_by_color[color].append(row)

        derived = {
            "photo_counts_by_color": deepcopy(photo_counts_by_color),
            "unique_skus": list(unique_skus),
            "rows_by_sku": deepcopy(rows_by_sku),
            "rows_by_color": deepcopy(rows_by_color),
        }
        set_timed_cached_value(derived_cache, collection_option_id, derived)
    else:
        photo_counts_by_color = deepcopy(derived.get("photo_counts_by_color", {}))
        unique_skus = list(derived.get("unique_skus", []))
        rows_by_sku = deepcopy(derived.get("rows_by_sku", {}))
        rows_by_color = defaultdict(list, deepcopy(derived.get("rows_by_color", {})))
        log_message(f"Using cached derived collection data for {collection_label}: {len(unique_skus)} SKUs.")

    color_sections = []
    for color in sorted(rows_by_color.keys(), key=lambda c: (c or "").lower()):
        section_rows = list(rows_by_color[color])
        section_rows.sort(key=lambda r: (bool(r.get("inactive")), natural_sort_key(r.get("sku") or ""), (r.get("product_name") or "").lower()))
        color_sections.append({
            "color": color,
            "rows": section_rows,
            "photo_available_count": photo_counts_by_color.get(color, 0),
        })

    board = {
        "collection": product_collection_option,
        "loaded_at": datetime.now().isoformat(),
        "color_sections": color_sections,
    }
    total_rows = sum(len(section.get("rows", [])) for section in color_sections)
    log_message(f"Built board for {collection_label}: {total_rows} rows across {len(color_sections)} color sections.")
    set_timed_cached_value(board_cache, collection_option_id, board)
    return board


# ============================================================
# HELPERS - STATE / CHANGE COMPUTATION
# ============================================================
def get_row_by_id(board: Dict[str, Any], row_id: str) -> Optional[Dict[str, Any]]:
    target = string_value(row_id)
    for section in board.get("color_sections", []):
        for row in section.get("rows", []):
            if string_value(row.get("row_id")) == target or string_value(row.get("sku")) == target:
                return row
    return None


def get_row_containing_asset(board: Dict[str, Any], asset_id: str) -> Optional[Dict[str, Any]]:
    target = string_value(asset_id)
    for section in board.get("color_sections", []):
        for row in section.get("rows", []):
            for asset in row.get("assets", []):
                if string_value(asset.get("id")) == target:
                    return row
    return None

def get_asset_by_id(board: Dict[str, Any], asset_id: str) -> Optional[Dict[str, Any]]:
    row = get_row_containing_asset(board, asset_id)
    if not row:
        return None
    for asset in row.get("assets", []):
        if asset.get("id") == asset_id:
            return asset
    return None

def queue_deliverable_fix_on_board(board: Dict[str, Any], asset_id: str) -> Tuple[Dict[str, Any], str, str]:
    asset = get_asset_by_id(board, asset_id)
    if asset is None:
        raise ValueError("Asset not found on current board.")
    row = get_row_by_id(board, string_value(asset.get("row_id")))
    row_sku = string_value(row.get("sku")) if row else ""
    expected = expected_deliverable_for_asset(asset, row_sku)
    if not expected:
        raise ValueError("This asset does not have an expected Deliverable for its current lane.")
    asset["deliverable_override"] = expected
    asset["deliverable"] = expected
    original = asset.setdefault("original_state", {})
    if "deliverable" not in original:
        original["deliverable"] = string_value(asset.get("deliverable") or "")
    return board, string_value(row.get("row_id")) if row else "", expected



def sanitize_copy_warning(target_lane: str) -> bool:
    return target_lane != "swatch_detail"


def remove_pending_copy_from_board(board: Dict[str, Any], asset_id: str, target_pos: str = "", source_media_id: str = "", target_sku: str = "") -> bool:
    removed = False
    for section in board.get("color_sections", []):
        for row in section.get("rows", []):
            pending_before = len([a for a in (row.get("assets") or []) if a.get("pending_upload") and string_value(a.get("pending_upload_kind") or "") == "copy"])
            row["assets"] = [
                a for a in (row.get("assets") or [])
                if not (
                    a.get("pending_upload")
                    and string_value(a.get("pending_upload_kind") or "") == "copy"
                    and (
                        (asset_id and string_value(a.get("id")) == string_value(asset_id))
                        or (
                            source_media_id
                            and target_sku
                            and target_pos
                            and string_value(a.get("copy_source_media_id")) == string_value(source_media_id)
                            and string_value(a.get("sku")) == string_value(target_sku)
                            and string_value(a.get("current_position")) == string_value(target_pos)
                        )
                        or (
                            source_media_id
                            and target_sku
                            and string_value(a.get("copy_source_media_id")) == string_value(source_media_id)
                            and string_value(a.get("sku")) == string_value(target_sku)
                        )
                    )
                )
            ]
            pending_after = len([a for a in (row.get("assets") or []) if a.get("pending_upload") and string_value(a.get("pending_upload_kind") or "") == "copy"])
            if pending_after != pending_before:
                row["overflow_warnings"] = []
                refresh_row_asset_flags(row)
                removed = True
    return removed


def make_pending_copy_asset(source_asset: Dict[str, Any], target_sku: str, profile: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
    clone = deepcopy(source_asset)
    profile = profile or {}
    clone["id"] = f"pending-copy::{uuid.uuid4()}"
    clone["sku"] = target_sku
    clone["source_sku"] = source_asset.get("copy_source_sku") or source_asset.get("source_sku") or source_asset.get("sku") or ""
    clone["pending_upload"] = True
    clone["pending_upload_kind"] = "copy"
    clone["pending_message"] = "Pending copy upload"
    clone["copy_source_media_id"] = source_asset.get("copy_source_media_id") or source_asset.get("id")
    clone["copy_source_sku"] = source_asset.get("copy_source_sku") or source_asset.get("sku") or source_asset.get("source_sku") or ""
    clone["deliverable_override"] = string_value(profile.get("deliverable_override") or "")
    clone["psa_image_type_override"] = string_value(profile.get("psa_image_type_override") or get_existing_psa_image_type_label(source_asset) or "")
    target_name = string_value(profile.get("target_name") or source_asset.get("file_name") or source_asset.get("name") or "")
    if target_name:
        clone["file_name"] = target_name
        clone["name"] = os.path.splitext(target_name)[0]
    clone["is_marked_for_deletion"] = False
    clone["original_state"] = {"position": "", "is_marked_for_deletion": False}
    clone["lane"] = "off_pattern"
    clone["slot_key"] = ""
    clone["current_position"] = ""
    clone["last_nontrash_position"] = ""
    clone["size_warning"] = ""
    return clone


def bucket_assets(row: Dict[str, Any]) -> Dict[str, Dict[str, List[Dict[str, Any]]]]:
    buckets = {
        "grid": {GRID_SLOT: []},
        "core": {slot: [] for slot in CORE_SLOTS},
        "swatch_detail": {slot: [] for slot in SWATCH_DETAIL_SLOTS},
        "special": {slot: [] for slot in SPECIAL_SLOTS},
        "trash": {"trash": []},
        "off_pattern": {"off_pattern": []},
    }
    for asset in row.get("assets", []):
        if asset.get("is_empty_slot"):
            continue
        lane = asset.get("lane")
        position = asset.get("slot_key") or normalize_position_for_row(asset.get("last_nontrash_position") or asset.get("current_position"), row.get("sku"))
        if lane == "grid":
            buckets["grid"][GRID_SLOT].append(asset)
        elif lane == "core":
            if position in buckets["core"]:
                buckets["core"][position].append(asset)
            else:
                buckets["off_pattern"]["off_pattern"].append(asset)
        elif lane == "swatch_detail":
            if position in buckets["swatch_detail"]:
                buckets["swatch_detail"][position].append(asset)
            else:
                buckets["off_pattern"]["off_pattern"].append(asset)
        elif lane == "special":
            if position in buckets["special"]:
                buckets["special"][position].append(asset)
            else:
                buckets["off_pattern"]["off_pattern"].append(asset)
        elif lane == "trash":
            buckets["trash"]["trash"].append(asset)
        else:
            buckets["off_pattern"]["off_pattern"].append(asset)

    for group_map in buckets.values():
        for key, items in group_map.items():
            group_map[key] = sort_assets_in_slot(items)
    return buckets


def apply_bucket_state_to_row(row: Dict[str, Any], buckets: Dict[str, Dict[str, List[Dict[str, Any]]]]) -> None:
    updated_assets = []

    sku = row.get("sku", "")

    for asset in buckets["grid"][GRID_SLOT]:
        asset["lane"] = "grid"
        asset["slot_key"] = GRID_SLOT
        asset["current_position"] = exact_position_for_row(sku, GRID_SLOT)
        asset["last_nontrash_position"] = asset["current_position"]
        updated_assets.append(asset)

    for slot in CORE_SLOTS:
        for asset in buckets["core"][slot]:
            asset["lane"] = "core"
            asset["slot_key"] = slot
            asset["current_position"] = exact_position_for_row(sku, slot)
            asset["last_nontrash_position"] = asset["current_position"]
            updated_assets.append(asset)

    for slot in SWATCH_DETAIL_SLOTS:
        for asset in buckets["swatch_detail"][slot]:
            asset["lane"] = "swatch_detail"
            asset["slot_key"] = slot
            asset["current_position"] = exact_position_for_row(sku, slot)
            asset["last_nontrash_position"] = asset["current_position"]
            updated_assets.append(asset)

    for slot in SPECIAL_SLOTS:
        for asset in buckets["special"][slot]:
            asset["lane"] = "special"
            asset["slot_key"] = slot
            asset["current_position"] = exact_position_for_row(sku, slot)
            asset["last_nontrash_position"] = asset["current_position"]
            updated_assets.append(asset)

    for asset in buckets["trash"]["trash"]:
        asset["lane"] = "trash"
        asset["slot_key"] = normalize_position_for_row(asset.get("last_nontrash_position") or asset.get("current_position"), sku)
        asset["current_position"] = asset.get("last_nontrash_position") or asset.get("current_position")
        updated_assets.append(asset)

    for asset in buckets["off_pattern"]["off_pattern"]:
        asset["lane"] = "off_pattern"
        asset["slot_key"] = normalize_position_for_row(asset.get("current_position"), sku)
        updated_assets.append(asset)

    row["assets"] = updated_assets
    refresh_row_asset_flags(row)


def mark_asset_deleted(asset: Dict[str, Any], deleted: bool) -> None:
    asset["is_marked_for_deletion"] = deleted


def remove_asset_from_all_buckets(asset_id: str, buckets: Dict[str, Dict[str, List[Dict[str, Any]]]]) -> Optional[Dict[str, Any]]:
    for lane_map in buckets.values():
        for key, items in lane_map.items():
            for idx, item in enumerate(items):
                if item.get("id") == asset_id:
                    return items.pop(idx)
    return None


def move_asset_to_trash(row: Dict[str, Any], buckets: Dict[str, Dict[str, List[Dict[str, Any]]]], asset: Dict[str, Any]) -> None:
    mark_asset_deleted(asset, True)
    buckets["trash"]["trash"].append(asset)
    buckets["trash"]["trash"] = sort_assets_in_slot(buckets["trash"]["trash"])


def compact_lane_groups(slot_map: Dict[str, List[Dict[str, Any]]], slots: List[str]) -> None:
    groups = [list(slot_map[s]) for s in slots if slot_map[s]]
    while len(groups) < len(slots):
        groups.append([])
    for idx, slot in enumerate(slots):
        slot_map[slot] = groups[idx]


def insert_into_group_lane(
    row: Dict[str, Any],
    buckets: Dict[str, Dict[str, List[Dict[str, Any]]]],
    asset: Dict[str, Any],
    target_lane: str,
    target_slot: str,
) -> None:
    slots = CORE_SLOTS if target_lane == "core" else SWATCH_DETAIL_SLOTS
    slot_map = buckets[target_lane]
    groups = [list(slot_map[s]) for s in slots]
    target_index = slots.index(target_slot)

    existing_group = groups[target_index]
    new_asset = asset
    mark_asset_deleted(new_asset, False)
    groups[target_index] = [new_asset]

    carry_group = existing_group
    overflow_asset_names = []
    for idx in range(target_index + 1, len(groups)):
        old_group = groups[idx]
        groups[idx] = carry_group
        carry_group = old_group

    if carry_group:
        for overflow_asset in carry_group:
            overflow_asset_names.append(overflow_asset.get("file_name") or overflow_asset.get("name") or overflow_asset.get("id"))
            move_asset_to_trash(row, buckets, overflow_asset)

    for idx, slot in enumerate(slots):
        slot_map[slot] = groups[idx]

    compact_lane_groups(slot_map, slots)

    if overflow_asset_names:
        lane_label = "carousel" if target_lane == "core" else "swatch detail"
        for name in overflow_asset_names:
            row.setdefault("overflow_warnings", []).append(
                f"{name} was moved to the trash because you've reached the maximum allowed assets in the {lane_label} lane."
            )


def assign_to_exact_slot(
    buckets: Dict[str, Dict[str, List[Dict[str, Any]]]],
    asset: Dict[str, Any],
    target_lane: str,
    target_slot: str,
    row: Dict[str, Any],
) -> None:
    if target_lane == "grid":
        lane_map = buckets["grid"]
    else:
        lane_map = buckets["special"]

    existing = list(lane_map[target_slot])
    lane_map[target_slot] = []
    for displaced in existing:
        mark_asset_deleted(displaced, True)
        move_asset_to_trash(row, buckets, displaced)

    mark_asset_deleted(asset, False)
    lane_map[target_slot] = [asset]


def apply_move(board: Dict[str, Any], row_id: str, asset_id: str, target_lane: str, target_slot: Optional[str]) -> Dict[str, Any]:
    target_row = get_row_by_id(board, row_id)
    if not target_row:
        raise ValueError(f"Row {row_id} not found")

    source_row = get_row_containing_asset(board, asset_id)
    if not source_row:
        raise ValueError(f"Asset {asset_id} not found")

    target_row["overflow_warnings"] = []
    target_buckets = bucket_assets(target_row)

    if source_row.get("row_id") == target_row.get("row_id"):
        asset = remove_asset_from_all_buckets(asset_id, target_buckets)
        if not asset:
            raise ValueError(f"Asset {asset_id} not found in row {row_id}")
    else:
        source_asset = next((a for a in source_row.get("assets", []) if a.get("id") == asset_id), None)
        if not source_asset:
            raise ValueError(f"Asset {asset_id} not found in source row")
        original_name = string_value(source_asset.get("file_name") or source_asset.get("name") or "copied_asset.jpg")
        profile = resolve_new_asset_profile(target_row, target_lane, target_slot or "", original_name, compact_text(string_value(board.get('workspace'))) == compact_text(WORKSPACE_PIO))
        asset = make_pending_copy_asset(source_asset, target_row.get("sku", ""), profile)
        target_slot = string_value(profile.get("target_slot") or target_slot)
        if sanitize_copy_warning(target_lane):
            target_row.setdefault("overflow_warnings", []).append(
                f"{source_asset.get('file_name') or source_asset.get('name') or source_asset.get('id')} will be copied from SKU {source_asset.get('copy_source_sku') or source_asset.get('source_sku') or source_row.get('sku')} to SKU {target_row.get('sku')}."
            )

    deliverable_override = get_deliverable_override_for_target(target_lane, target_slot or "")
    asset["deliverable_override"] = deliverable_override
    if deliverable_override:
        asset["deliverable"] = deliverable_override

    if target_lane == "trash":
        move_asset_to_trash(target_row, target_buckets, asset)
    elif target_lane == "core":
        insert_into_group_lane(target_row, target_buckets, asset, "core", target_slot)
    elif target_lane == "swatch_detail":
        insert_into_group_lane(target_row, target_buckets, asset, "swatch_detail", target_slot)
    elif target_lane == "grid":
        assign_to_exact_slot(target_buckets, asset, "grid", GRID_SLOT, target_row)
    elif target_lane == "special":
        if target_slot not in SPECIAL_SLOTS:
            raise ValueError(f"Invalid special target slot {target_slot}")
        assign_to_exact_slot(target_buckets, asset, "special", target_slot, target_row)
    elif target_lane == "off_pattern":
        mark_asset_deleted(asset, False)
        target_buckets["off_pattern"]["off_pattern"].append(asset)
    else:
        raise ValueError(f"Unknown target lane {target_lane}")

    apply_bucket_state_to_row(target_row, target_buckets)
    return board


def compute_change_summary(board: Dict[str, Any]) -> Dict[str, List[Dict[str, Any]]]:
    grouped = {"New copied assets": [], "Position changes": [], "Marked for deletion": [], "Restored from deletion": []}
    for section in board.get("color_sections", []):
        for row in section.get("rows", []):
            for asset in row.get("assets", []):
                original = asset.get("original_state", {})
                current_position = asset.get("current_position")
                current_deleted = bool(asset.get("is_marked_for_deletion"))
                original_position = original.get("position")
                original_deleted = bool(original.get("is_marked_for_deletion"))

                if asset.get("pending_upload"):
                    grouped["New copied assets"].append(
                        {
                            "asset_id": asset["id"],
                            "sku": row["sku"],
                            "asset_name": asset["file_name"],
                            "thumb": asset.get("transformBaseUrl"),
                            "description": f"Will be copied from SKU {asset.get('copy_source_sku') or asset.get('source_sku') or ''} into {current_position or '(unplaced)'}",
                        }
                    )
                if current_position != original_position:
                    grouped["Position changes"].append(
                        {
                            "asset_id": asset["id"],
                            "sku": row["sku"],
                            "asset_name": asset["file_name"],
                            "thumb": asset.get("transformBaseUrl"),
                            "description": f"{original_position or '(blank)'} -> {current_position or '(blank)'}",
                        }
                    )
                if current_deleted and not original_deleted:
                    grouped["Marked for deletion"].append(
                        {
                            "asset_id": asset["id"],
                            "sku": row["sku"],
                            "asset_name": asset["file_name"],
                            "thumb": asset.get("transformBaseUrl"),
                            "description": "Will be marked for deletion from site",
                        }
                    )
                if original_deleted and not current_deleted:
                    grouped["Restored from deletion"].append(
                        {
                            "asset_id": asset["id"],
                            "sku": row["sku"],
                            "asset_name": asset["file_name"],
                            "thumb": asset.get("transformBaseUrl"),
                            "description": f"Will be restored and placed in {current_position}",
                        }
                    )
    return grouped


def write_commit_log(log_payload: Dict[str, Any]) -> str:
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    filename = f"content_refresher_commit_log_{timestamp}.json"
    out_path = DOWNLOADS_DIR / filename
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(log_payload, f, indent=2)
    return str(out_path)


def validate_update_config() -> List[str]:
    missing = []
    if PRODUCT_SKU_POSITION_METAPROPERTY_ID.startswith("PUT_"):
        missing.append("PRODUCT_SKU_POSITION_METAPROPERTY_ID")
    if MARKED_FOR_DELETION_METAPROPERTY_ID.startswith("PUT_"):
        missing.append("MARKED_FOR_DELETION_METAPROPERTY_ID")
    return missing


def commit_changes(board: Dict[str, Any], session: requests.Session) -> Dict[str, Any]:
    missing = validate_update_config()
    if missing:
        raise RuntimeError(
            "You need to fill in these config values before committing changes: " + ", ".join(missing)
        )

    metaprops_by_dbname = fetch_metaproperties_map(session)

    copy_jobs = []
    update_jobs = []
    for section in board.get("color_sections", []):
        for row in section.get("rows", []):
            row["commit_failures"] = []
            for asset in row.get("assets", []):
                original = asset.get("original_state", {})
                current_position = asset.get("current_position")
                current_deleted = bool(asset.get("is_marked_for_deletion"))
                original_position = original.get("position")
                original_deleted = bool(original.get("is_marked_for_deletion"))

                if asset.get("pending_upload"):
                    if current_deleted and asset.get("pending_upload_kind") != "new_version":
                        continue
                    pending_kind = asset.get("pending_upload_kind") or "copy"
                    if pending_kind == "copy":
                        copy_jobs.append(
                            {
                                "row_id": row["row_id"],
                                "target_sku": row["sku"],
                                "target_position": current_position,
                                "asset_name": asset["file_name"],
                                "source_media_id": asset.get("copy_source_media_id") or asset.get("id"),
                                "source_sku": asset.get("copy_source_sku") or asset.get("source_sku") or "",
                                "deliverable_override": asset.get("deliverable_override") or "",
                                "psa_image_type_override": effective_psa_image_type_for_target(asset.get("lane") or "", normalize_position_for_row(current_position, row.get("sku") or ""), asset.get("psa_image_type_override") or get_existing_psa_image_type_label(asset) or ""),
                            }
                        )
                    else:
                        update_jobs.append(
                            {
                                "row_id": row["row_id"],
                                "media_id": asset.get("id"),
                                "sku": row["sku"],
                                "asset_name": asset.get("file_name") or asset.get("name") or "upload",
                                "payload": {},
                                "job_type": pending_kind,
                                "staged_file_path": asset.get("staged_file_path") or "",
                                "source_media_id": asset.get("copy_source_media_id") or asset.get("id"),
                                "source_sku": asset.get("copy_source_sku") or asset.get("source_sku") or "",
                                "target_position": current_position,
                                "psa_image_type_override": effective_psa_image_type_for_target(asset.get("lane") or "", normalize_position_for_row(current_position, row.get("sku") or ""), asset.get("psa_image_type_override") or get_existing_psa_image_type_label(asset) or ""),
                            }
                        )
                    continue

                payload = {}
                current_slot_key = normalize_position_for_row(current_position, row.get("sku") or "")
                if current_position != original_position:
                    payload[f"metaproperty.{PRODUCT_SKU_POSITION_METAPROPERTY_ID}"] = current_position
                if current_deleted != original_deleted:
                    payload[f"metaproperty.{MARKED_FOR_DELETION_METAPROPERTY_ID}"] = MARKED_FOR_DELETION_OPTION_ID if current_deleted else ""

                current_deliverable = string_value(asset.get("deliverable") or asset.get("deliverable_override") or "")
                original_deliverable = string_value(original.get("deliverable") or "")
                if current_deliverable != original_deliverable:
                    deliverable_fields: List[Tuple[str, Any]] = []
                    append_deliverable_field(session, deliverable_fields, metaprops_by_dbname, current_deliverable)
                    for field_key, field_value in deliverable_fields:
                        payload[field_key] = field_value


                if current_slot_key in {"SKU_swatch", "SKU_dimension", "SKU_square"}:
                    psa_label = (
                        SWATCH_PSA_IMAGE_TYPE_LABEL if current_slot_key == "SKU_swatch"
                        else DIMENSIONS_PSA_IMAGE_TYPE_LABEL if current_slot_key == "SKU_dimension"
                        else SQUARE_PSA_IMAGE_TYPE_LABEL
                    )
                    psa_fields: List[Tuple[str, Any]] = []
                    append_psa_image_type_field(session, psa_fields, metaprops_by_dbname, psa_label)
                    for field_key, field_value in psa_fields:
                        payload[field_key] = field_value

                if payload:
                    update_jobs.append(
                        {
                            "row_id": row["row_id"],
                            "media_id": asset["id"],
                            "sku": row["sku"],
                            "asset_name": asset["file_name"],
                            "payload": payload,
                        }
                    )

    results = []
    success_count = 0
    failure_count = 0

    for job in copy_jobs:
        try:
            response = create_copied_asset_for_target(
                session,
                job["source_media_id"],
                job["source_sku"],
                job["target_sku"],
                job["target_position"],
                job.get("asset_name") or "",
                job.get("deliverable_override") or "",
                job.get("psa_image_type_override") or "",
            )
            results.append({**job, "success": True, "response": response, "job_type": "copy"})
            new_media_id = string_value(((response or {}).get("new_media_id") if isinstance(response, dict) else "") or ((response or {}).get("id") if isinstance(response, dict) else ""))
            if new_media_id:
                set_recent_position_override(new_media_id, job["target_position"])
            success_count += 1
            log_message(f"Created copied asset from {job['source_media_id']} for SKU {job['target_sku']} in position {job['target_position']}.")
        except Exception as exc:
            failure_count += 1
            error_text = str(exc)
            results.append({**job, "success": False, "error": error_text, "job_type": "copy"})
            row = get_row_by_id(board, job["row_id"])
            if row is not None:
                row.setdefault("commit_failures", []).append(
                    {"asset_name": job["asset_name"], "media_id": job["source_media_id"], "error": error_text}
                )
            log_message(f"Failed to create copied asset from {job['source_media_id']} for SKU {job['target_sku']}: {error_text}")

    for job in update_jobs:
        try:
            if job.get("job_type") == "new_version":
                staged_path = Path(job.get("staged_file_path") or "")
                response = upload_new_version_to_media(session, job["media_id"], staged_path, job["asset_name"])
                if string_value(job.get("psa_image_type_override")):
                    set_media_psa_image_type(session, job["media_id"], job.get("psa_image_type_override") or "")
                cleanup_staged_file(str(staged_path))
                results.append({**job, "success": True, "response": response})
                success_count += 1
                log_message(f"Uploaded pending new version onto {job['media_id']} ({job['asset_name']}) successfully.")
                continue
            if job.get("job_type") == "new_asset":
                staged_path = Path(job.get("staged_file_path") or "")
                source_media = fetch_media_by_id(session, job["source_media_id"])
                target_pos = normalize_position_for_row(job.get("target_position") or '', job.get('sku') or '')
                if compact_text((get_row_by_id(board, job.get('row_id') or '') or {}).get('workflow')) == compact_text(PIO_WORKFLOW_VALUE):
                    target_name = Path(pio_target_asset_name(job.get('sku') or '', target_pos or 'SKU_100')).stem
                else:
                    target_name = os.path.splitext(job["asset_name"])[0]
                new_media_id = upload_new_asset_group_upload(session, staged_path, target_name)
                fields = build_metadata_copy_fields(session, source_media, metaprops_by_dbname, job["sku"], job["target_position"], target_name, job.get("deliverable_override") or "", job.get("psa_image_type_override") or "")
                row = get_row_by_id(board, job.get("row_id") or "")
                if compact_text((row or {}).get("workflow")) == compact_text(PIO_WORKFLOW_VALUE):
                    append_pio_board_fields(session, fields, metaprops_by_dbname, row or {}, job.get("target_position") or "")
                post_media_fields(session, new_media_id, fields)
                cleanup_staged_file(str(staged_path))
                response = {"new_media_id": new_media_id}
                results.append({**job, "success": True, "response": response})
                set_recent_position_override(new_media_id, job["target_position"])
                success_count += 1
                log_message(f"Uploaded pending new asset for SKU {job['sku']} into {job['target_position']} successfully.")
                continue
            response = update_asset_metadata(session, job["media_id"], job["payload"])
            results.append({**job, "success": True, "response": response})
            if f"metaproperty.{PRODUCT_SKU_POSITION_METAPROPERTY_ID}" in (job.get("payload") or {}):
                set_recent_position_override(job["media_id"], (job.get("payload") or {}).get(f"metaproperty.{PRODUCT_SKU_POSITION_METAPROPERTY_ID}"))
            success_count += 1
            log_message(f"Updated asset {job['media_id']} ({job['asset_name']}) successfully.")
        except Exception as exc:
            failure_count += 1
            error_text = str(exc)
            results.append({**job, "success": False, "error": error_text})
            row = get_row_by_id(board, job["row_id"])
            if row is not None:
                row.setdefault("commit_failures", []).append(
                    {
                        "asset_name": job["asset_name"],
                        "media_id": job.get("media_id") or job.get("source_media_id"),
                        "error": error_text,
                    }
                )
            log_message(f"Failed to process job for {job.get('media_id') or job.get('source_media_id')} ({job['asset_name']}): {error_text}")

    log_payload = {
        "committed_at": datetime.now().isoformat(),
        "collection": board.get("collection"),
        "success_count": success_count,
        "failure_count": failure_count,
        "results": results,
    }
    log_path = write_commit_log(log_payload)

    successful_row_ids = sorted({
        string_value(item.get("row_id"))
        for item in results
        if item.get("success") and string_value(item.get("row_id"))
    })

    return {
        "success_count": success_count,
        "failure_count": failure_count,
        "results": results,
        "success_row_ids": successful_row_ids,
        "log_path": log_path,
        "all_succeeded": failure_count == 0,
    }


# ============================================================
# API ROUTES
# ============================================================
@app.route("/")
def index() -> Response:
    return Response(INDEX_HTML, mimetype="text/html")


def ensure_collections_loaded() -> List[Dict[str, str]]:
    if STATE.get("collections") is None:
        cached = load_collection_options_from_disk_cache()
        if cached:
            STATE["collections"] = cached
        else:
            token = load_bynder_token(BYNDER_TOKEN_PATH)
            session = make_session(token)
            collections = fetch_metaproperty_options(session, PRODUCT_COLLECTION_METAPROPERTY_ID)
            STATE["collections"] = collections
            save_collection_options_to_disk_cache(collections)
    return STATE.get("collections") or []


def filter_board_to_colors(board: Dict[str, Any], color_names: List[str]) -> Dict[str, Any]:
    wanted = {string_value(c) for c in (color_names or []) if string_value(c)}
    if not wanted:
        return deepcopy(board)
    clone = deepcopy(board)
    clone["color_sections"] = [deepcopy(section) for section in board.get("color_sections", []) if string_value(section.get("color")) in wanted]
    return clone


def is_swatch_optional_step_path(step_path: Any) -> bool:
    step_path_text = string_value(step_path).strip()
    normalized = step_path_text.replace(" | ", "___").replace("|", "___").replace(" ", "_")
    if step_path_text in CHALLENGE_SWATCH_OPTIONAL_STEP_PATHS or normalized in CHALLENGE_SWATCH_OPTIONAL_STEP_PATHS:
        return True
    return any(step_path_text.startswith(prefix) or normalized.startswith(prefix.replace(" | ", "___").replace("|", "___").replace(" ", "_")) for prefix in SWATCH_OPTIONAL_STEP_PATH_PREFIXES)


def row_requires_swatch(row: Dict[str, Any]) -> bool:
    step_path = string_value(row.get("step_path") or row.get("property_STEP_Path") or "")
    return not is_swatch_optional_step_path(step_path)


def row_requires_wall_art_sizing(row: Dict[str, Any]) -> bool:
    step_path = string_value(row.get("step_path") or row.get("property_STEP_Path") or "")
    return step_path in CHALLENGE_WALL_ART_SIZING_STEP_PATHS


def compact_text(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "", string_value(value).strip().lower())


def sales_channel_has_full_line(value: Any) -> bool:
    return "fullline" in compact_text(value)


def row_needs_make_square(row: Dict[str, Any]) -> bool:
    if string_value(row.get("product_status")).strip().lower() != "active":
        return False
    if not sales_channel_has_full_line(row.get("sales_channel")):
        return False
    live_assets = [a for a in (row.get("assets") or []) if not a.get("is_marked_for_deletion") and not a.get("is_empty_slot")]
    has_room_shot_carousel = any(
        string_value(a.get("lane")) == "core" and compact_text(a.get("psa_image_type")) == "roomshot"
        for a in live_assets
    )
    if not has_room_shot_carousel:
        return False
    square_assets = [
        a for a in live_assets
        if string_value(a.get("slot_key") or normalize_position_for_row(a.get("current_position"), row.get("sku") or "")) == "SKU_square"
    ]
    if not square_assets:
        return True
    square_types = [compact_text(a.get("psa_image_type")) for a in square_assets]
    if any(t and t != "silo" for t in square_types):
        return False
    return any(t == "silo" for t in square_types)


def raw_assets_need_make_square(anchor: Dict[str, Any], sku_assets: List[Dict[str, Any]], sku: str) -> bool:
    if string_value(get_status_from_grid_asset(anchor)).strip().lower() != "active":
        return False
    if not sales_channel_has_full_line(prop(anchor, "Sales_Channel", "Sales_Channel")):
        return False
    live_assets = [a for a in (sku_assets or []) if not is_marked_for_deletion(a)]
    has_room_shot_carousel = any(
        get_lane_and_slot_for_row(get_asset_position(a), sku)[0] == "core" and compact_text(get_existing_psa_image_type_label(a)) == "roomshot"
        for a in live_assets
    )
    if not has_room_shot_carousel:
        return False
    square_assets = [a for a in live_assets if normalize_position_for_row(get_asset_position(a), sku) == "SKU_square"]
    if not square_assets:
        return True
    square_types = [compact_text(get_existing_psa_image_type_label(a)) for a in square_assets]
    if any(t and t != "silo" for t in square_types):
        return False
    return any(t == "silo" for t in square_types)


def candidate_sort_key(candidate: Dict[str, Any]) -> Tuple[int, float]:
    return (
        -int(candidate.get("issue_total") or 0),
        float(candidate.get("random_rank") or 0.0),
    )


def compute_row_issue_summary(row: Dict[str, Any], include_missing_dims: bool = True) -> Dict[str, int]:
    live_assets = [a for a in (row.get("assets") or []) if not a.get("is_marked_for_deletion") and not a.get("is_empty_slot")]
    dup_counts: Dict[str, int] = {}
    size_issue_count = 0
    for asset in live_assets:
        warning_text = string_value(asset.get("size_warning"))
        if warning_text and (not is_total_fill_warning_text(warning_text) or asset_is_cleanup_total_fill_candidate(asset, row)):
            size_issue_count += 1
        lane = string_value(asset.get("lane"))
        if lane in {"off_pattern", "trash"}:
            continue
        key = string_value(asset.get("last_nontrash_position") or asset.get("current_position") or asset.get("slot_key"))
        if key:
            dup_counts[key] = dup_counts.get(key, 0) + 1
    has_grid = any(a.get("slot_key") == "SKU_grid" or string_value(a.get("current_position")).endswith("_grid") for a in live_assets)
    has_100 = any(a.get("slot_key") == "SKU_100" or string_value(a.get("current_position")).endswith("_100") for a in live_assets)
    has_swatch = any(a.get("slot_key") == "SKU_swatch" or string_value(a.get("current_position")).endswith("_swatch") for a in live_assets)
    has_dim = any(a.get("slot_key") == "SKU_dimension" or string_value(a.get("current_position")).endswith("_dimension") for a in live_assets)
    has_8000 = any(a.get("slot_key") == "SKU_8000" or string_value(a.get("current_position")).endswith("_8000") for a in live_assets)
    off_pattern = sum(1 for a in live_assets if string_value(a.get("lane")) == "off_pattern")
    issues = {
        "missing_grid": 0 if has_grid else 1,
        "missing_100": 0 if has_100 else 1,
        "missing_swatch": 0 if (has_swatch or not row_requires_swatch(row)) else 1,
        "missing_dimension": 0 if has_dim else 1,
        "missing_wall_art_sizing": 0 if (has_8000 or not row_requires_wall_art_sizing(row)) else 1,
        "compilable_set_dim": 1 if (not has_dim and bool(row.get("set_dim_compile_ready"))) else 0,
        "make_square": 1 if bool(row.get("square_make_recommended")) else 0,
        "off_pattern": off_pattern,
        "duplicate_slot": sum(1 for v in dup_counts.values() if v > 1),
        "wrong_deliverable": sum(1 for a in live_assets if string_value(a.get("lane")) not in {"off_pattern", "trash"} and string_value(a.get("deliverable") or a.get("deliverable_override") or "") != expected_deliverable_for_asset(a, string_value(row.get("sku")))),
        "size_warnings": size_issue_count,
    }
    if not include_missing_dims:
        issues["missing_dimension"] = 0
    issues["total"] = sum(int(v or 0) for k, v in issues.items() if k != "total")
    return issues


def compute_board_issue_summary(board: Dict[str, Any], include_missing_dims: bool = True) -> Dict[str, Any]:
    summary = {
        "missing_grid": 0, "missing_100": 0, "missing_swatch": 0, "missing_dimension": 0,
        "missing_wall_art_sizing": 0, "compilable_set_dim": 0, "make_square": 0, "off_pattern": 0, "duplicate_slot": 0, "wrong_deliverable": 0, "size_warnings": 0, "total": 0,
        "rows": {},
    }
    for section in board.get("color_sections", []):
        for row in section.get("rows", []):
            if not row_counts_as_active(row):
                continue
            row_summary = compute_row_issue_summary(row, include_missing_dims=include_missing_dims)
            if row_summary["total"]:
                summary["rows"][string_value(row.get("row_id") or row.get("sku"))] = row_summary
            for key in ["missing_grid", "missing_100", "missing_swatch", "missing_dimension", "missing_wall_art_sizing", "compilable_set_dim", "make_square", "off_pattern", "duplicate_slot", "wrong_deliverable", "size_warnings"]:
                summary[key] += int(row_summary.get(key) or 0)
    summary["total"] = sum(summary[k] for k in ["missing_grid", "missing_100", "missing_swatch", "missing_dimension", "missing_wall_art_sizing", "compilable_set_dim", "make_square", "off_pattern", "duplicate_slot", "wrong_deliverable", "size_warnings"])
    return summary


def build_game_candidate_from_color(collection_option: Dict[str, str], color_name: str, issue_summary: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "key": f"{string_value(collection_option.get('id'))}::{color_name}",
        "collection": deepcopy(collection_option or {}),
        "color": color_name,
        "issues": deepcopy(issue_summary),
        "issue_total": int(issue_summary.get("total") or 0),
        "random_rank": random.random(),
    }


def _lane_presence_from_assets_for_sku(assets: List[Dict[str, Any]], sku: str) -> Dict[str, bool]:
    live_assets = [a for a in (assets or []) if not is_marked_for_deletion(a)]
    positions = {normalize_position_for_row(get_asset_position(a), sku) for a in live_assets}
    return {
        "has_grid": GRID_SLOT in positions,
        "has_100": f"{sku}_100" in positions,
        "has_swatch": f"{sku}_swatch" in positions,
        "has_dim": f"{sku}_dimension" in positions,
        "has_8000": f"{sku}_8000" in positions,
    }


def scan_collection_for_game_candidates(session: requests.Session, collection_option: Dict[str, str]) -> List[Dict[str, Any]]:
    collection_option_id = string_value(collection_option.get("id"))
    collection_label = string_value(collection_option.get("label"))
    raw_collection_assets = fetch_collection_assets_cached(session, collection_option_id, force_refresh=False)
    psa_assets = [a for a in raw_collection_assets if is_product_site_asset(a)]
    by_color_sku: Dict[str, Dict[str, List[Dict[str, Any]]]] = defaultdict(lambda: defaultdict(list))
    for asset in psa_assets:
        sku = prop(asset, "Product_SKU", "Product_SKU")
        if not sku:
            continue
        color = get_color_label(asset)
        by_color_sku[color][sku].append(asset)

    candidates: List[Dict[str, Any]] = []
    for color_name, sku_map in by_color_sku.items():
        summary = {
            "missing_grid": 0, "missing_100": 0, "missing_swatch": 0, "missing_dimension": 0,
            "missing_wall_art_sizing": 0, "compilable_set_dim": 0, "make_square": 0, "off_pattern": 0, "duplicate_slot": 0, "wrong_deliverable": 0, "size_warnings": 0, "total": 0,
            "rows": {},
        }
        for sku, sku_assets in sku_map.items():
            grid_assets = [a for a in sku_assets if normalize_position_for_row(get_asset_position(a), sku) == GRID_SLOT]
            anchor = max(grid_assets or sku_assets, key=lambda a: parse_datetime(a.get("dateCreated")) or datetime.min)
            if not row_counts_as_active({"product_status": get_status_from_grid_asset(anchor)}):
                continue
            step_path = prop(anchor, "STEP_Path", "STEP_Path")
            lane = _lane_presence_from_assets_for_sku(sku_assets, sku)
            dup_counts: Dict[str, int] = {}
            off_pattern_count = 0
            wrong_deliverable_count = 0
            for asset in [a for a in sku_assets if not is_marked_for_deletion(a)]:
                lane_name, slot_name = get_lane_and_slot_for_row(get_asset_position(asset), sku)
                if lane_name == "off_pattern":
                    off_pattern_count += 1
                    continue
                if lane_name == "trash":
                    continue
                if slot_name:
                    dup_counts[slot_name] = dup_counts.get(slot_name, 0) + 1
                expected = get_deliverable_override_for_target(lane_name, slot_name)
                current_deliverable = prop(asset, "Deliverable", "Deliverable")
                if expected and current_deliverable != expected:
                    wrong_deliverable_count += 1
            row_summary = {
                "missing_grid": 0 if lane["has_grid"] else 1,
                "missing_100": 0 if lane["has_100"] else 1,
                "missing_swatch": 0 if (lane["has_swatch"] or is_swatch_optional_step_path(step_path)) else 1,
                "missing_dimension": 0,
                "missing_wall_art_sizing": 0 if (lane["has_8000"] or step_path not in CHALLENGE_WALL_ART_SIZING_STEP_PATHS) else 1,
                "compilable_set_dim": 0,
                "make_square": 1 if raw_assets_need_make_square(anchor, sku_assets, sku) else 0,
                "off_pattern": off_pattern_count,
                "duplicate_slot": sum(1 for v in dup_counts.values() if v > 1),
                "wrong_deliverable": wrong_deliverable_count,
                "size_warnings": sum(
                    1
                    for a in [x for x in sku_assets if not is_marked_for_deletion(x)]
                    for modeled in [asset_to_client_model(a, sku, position_override=get_asset_position(a))]
                    if string_value(compute_dimension_warning(modeled))
                    and (
                        not is_total_fill_warning_text(compute_dimension_warning(modeled))
                        or asset_is_cleanup_total_fill_candidate(modeled, {
                            "sku": sku,
                            "sales_channel": prop(anchor, "Sales_Channel", "Sales_Channel"),
                        })
                    )
                ),
            }
            row_summary["total"] = sum(int(v or 0) for k, v in row_summary.items() if k != "total")
            if row_summary["total"]:
                summary["rows"][sku] = row_summary
            for key in ["missing_grid", "missing_100", "missing_swatch", "missing_wall_art_sizing", "compilable_set_dim", "make_square", "off_pattern", "duplicate_slot", "wrong_deliverable", "size_warnings"]:
                summary[key] += int(row_summary.get(key) or 0)
        summary["total"] = sum(summary[k] for k in ["missing_grid", "missing_100", "missing_swatch", "missing_wall_art_sizing", "compilable_set_dim", "make_square", "off_pattern", "duplicate_slot", "wrong_deliverable", "size_warnings"])
        if int(summary.get("total") or 0) > 0:
            candidates.append(build_game_candidate_from_color(collection_option, color_name, summary))
    candidates.sort(key=candidate_sort_key)
    log_message(f"Scanned lightweight game candidates for {collection_label}: {len(candidates)} candidate colorways")
    return candidates


def _scan_game_queue_candidates(sync: bool = False, stop_after_first: bool = False, target_count: Optional[int] = None) -> None:
    game = STATE["game"]
    if target_count is None:
        with game["lock"]:
            target_count = GAME_QUEUE_TARGET if bool(game.get("active")) else GAME_QUEUE_PRELOAD_TARGET
    target_count = max(0, int(target_count or 0))
    try:
        collections = ensure_collections_loaded()
        if not collections or target_count <= 0:
            return
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        pool = list(collections)
        random.shuffle(pool)
        scanned = 0
        for collection_option in pool:
            with game["lock"]:
                existing_keys = {string_value(c.get("key")) for c in (game.get("queue") or [])}
                current_key = string_value((game.get("current") or {}).get("key"))
                if len(game.get("queue") or []) >= target_count:
                    break
            if scanned >= GAME_SCAN_BATCH:
                break
            scanned += 1
            try:
                queued_any = False
                for candidate in scan_collection_for_game_candidates(session, collection_option):
                    key = string_value(candidate.get("key"))
                    with game["lock"]:
                        if key and key != current_key and key not in existing_keys and len(game.get("queue") or []) < target_count:
                            game.setdefault("queue", []).append(candidate)
                            game["queue"].sort(key=candidate_sort_key)
                            existing_keys.add(key)
                            queued_any = True
                            log_message(f"Queued Cleanup Challenge candidate: {candidate['collection'].get('label')} / {candidate['color']}")
                if stop_after_first and queued_any:
                    break
            except Exception as exc:
                log_message(f"Game queue scan skipped {collection_option.get('label')}: {exc}")
    finally:
        with game["lock"]:
            game["scanner_running"] = False


def ensure_game_queue_ready(min_ready: int = 1, timeout_seconds: float = 10.0, target_count: Optional[int] = None) -> bool:
    game = STATE["game"]
    if target_count is None:
        with game["lock"]:
            target_count = GAME_QUEUE_TARGET if bool(game.get("active")) else GAME_QUEUE_PRELOAD_TARGET
    with game["lock"]:
        ready_count = len(game.get("queue") or [])
        scanner_running = bool(game.get("scanner_running"))
    if ready_count >= min_ready:
        return True
    if not scanner_running:
        with game["lock"]:
            game["scanner_running"] = True
            game["last_scan_at"] = time.time()
        _scan_game_queue_candidates(sync=True, stop_after_first=(min_ready <= 1), target_count=target_count)
    start = time.time()
    while time.time() - start < timeout_seconds:
        with game["lock"]:
            if len(game.get("queue") or []) >= min_ready:
                return True
            running = bool(game.get("scanner_running"))
        if not running:
            with game["lock"]:
                game["scanner_running"] = True
                game["last_scan_at"] = time.time()
            _scan_game_queue_candidates(sync=True, stop_after_first=(min_ready <= 1), target_count=target_count)
            with game["lock"]:
                if len(game.get("queue") or []) >= min_ready:
                    return True
        time.sleep(0.15)
    with game["lock"]:
        return len(game.get("queue") or []) >= min_ready


def maybe_start_game_queue_fill(force: bool = False, target_count: Optional[int] = None) -> None:
    game = STATE["game"]
    with game["lock"]:
        ready_count = len(game.get("queue") or [])
        active = bool(game.get("active"))
        if target_count is None:
            target_count = GAME_QUEUE_TARGET if active else GAME_QUEUE_PRELOAD_TARGET
        if game.get("scanner_running"):
            return
        if not force and ready_count >= target_count:
            return
        if not force and (time.time() - float(game.get("last_scan_at") or 0)) < GAME_SCAN_MIN_GAP_SECONDS:
            return
        game["scanner_running"] = True
        game["last_scan_at"] = time.time()

    def _worker() -> None:
        _scan_game_queue_candidates(sync=False, stop_after_first=False, target_count=target_count)

    threading.Thread(target=_worker, daemon=True).start()


def start_server_side_game_queue_worker() -> None:
    game = STATE["game"]
    if game.get("server_queue_worker_started"):
        return
    game["server_queue_worker_started"] = True

    def _loop() -> None:
        while True:
            try:
                with game["lock"]:
                    should_fill = bool(game.get("active")) and len(game.get("queue") or []) < GAME_QUEUE_TARGET and not game.get("scanner_running")
                if should_fill:
                    maybe_start_game_queue_fill(force=True, target_count=GAME_QUEUE_TARGET)
            except Exception as exc:
                log_message(f"Server-side game queue worker error: {exc}")
            time.sleep(GAME_SERVER_QUEUE_WORKER_INTERVAL_SECONDS)

    threading.Thread(target=_loop, daemon=True).start()


def hydrate_game_candidate(candidate: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    collection = deepcopy(candidate.get("collection") or {})
    color_name = string_value(candidate.get("color"))
    if not string_value(collection.get("id")) or not color_name:
        return None
    token = load_bynder_token(BYNDER_TOKEN_PATH)
    session = make_session(token)
    board = build_board_for_collection(session, collection, force_refresh=False)
    board = filter_board_to_colors(board, [color_name])
    issues = compute_board_issue_summary(board, include_missing_dims=False)
    if int(issues.get("total") or 0) <= 0:
        log_message(f"Skipped stale Cleanup Challenge candidate: {collection.get('label')} / {color_name}")
        return None
    hydrated = deepcopy(candidate)
    hydrated["board"] = board
    hydrated["issues"] = deepcopy(issues)
    hydrated["issue_total"] = int(issues.get("total") or 0)
    STATE["game"]["current"] = hydrated
    return board


def pop_next_game_candidate(force_fill: bool = True) -> Optional[Dict[str, Any]]:
    game = STATE["game"]
    if force_fill and not game.get("queue"):
        ensure_game_queue_ready(min_ready=1, timeout_seconds=10.0)
    with game["lock"]:
        if not game.get("queue"):
            return None
        candidate = game["queue"].pop(0)
        return deepcopy(candidate)


def get_next_hydrated_game_board(force_fill: bool = True, max_attempts: int = 24) -> tuple[Optional[Dict[str, Any]], bool]:
    """Return the next valid hydrated challenge board.

    Keeps walking the queued lightweight candidates, silently skipping any that
    turn out to be stale by hydration time. Returns (board, had_candidates).
    """
    game = STATE["game"]
    had_candidates = False
    attempts = 0
    while attempts < max_attempts:
        attempts += 1
        candidate = pop_next_game_candidate(force_fill=force_fill)
        force_fill = False
        if candidate is None:
            if not had_candidates:
                ensure_game_queue_ready(min_ready=1, timeout_seconds=12.0, target_count=max(1, GAME_QUEUE_TARGET))
                candidate = pop_next_game_candidate(force_fill=False)
            if candidate is None:
                break
        had_candidates = True
        board = hydrate_game_candidate(candidate)
        if board is not None:
            return board, True
    with game["lock"]:
        game["current"] = None
    maybe_start_game_queue_fill(force=False)
    return None, had_candidates


def game_status_payload() -> Dict[str, Any]:
    snapshot = get_game_score_snapshot(force_refresh_remote=True)
    game = STATE["game"]
    with game["lock"]:
        current = deepcopy(game.get("current")) if game.get("current") else None
        queue_len = len(game.get("queue") or [])
        active = bool(game.get("active"))
    return {
        "active": active,
        "queue_length": queue_len,
        "current": current and {
            "collection": current.get("collection"),
            "color": current.get("color"),
            "issue_total": current.get("issue_total"),
            "issues": current.get("issues"),
        },
        "score": snapshot["score"],
        "username": snapshot["username"],
        "leaderboard": snapshot["leaderboard"],
        "leaderboard_remote": bool(snapshot.get("remote_enabled")),
    }


@app.route("/api/messages")
def api_messages() -> Response:
    return jsonify({"messages": STATE["server_messages"][-100:]})


@app.route("/api/collections")
def api_collections() -> Response:
    try:
        source = "memory"
        if STATE["collections"] is None:
            cached = load_collection_options_from_disk_cache()
            if cached:
                STATE["collections"] = cached
                source = "local_cache"
                log_message(f"Loaded {len(cached)} Product Collection options from local cache.")
            else:
                token = load_bynder_token(BYNDER_TOKEN_PATH)
                session = make_session(token)
                collections = fetch_metaproperty_options(session, PRODUCT_COLLECTION_METAPROPERTY_ID)
                STATE["collections"] = collections
                save_collection_options_to_disk_cache(collections)
                source = "bynder"
                log_message(f"Loaded {len(collections)} Product Collection options from Bynder.")
        return jsonify({"collections": STATE["collections"], "source": source})
    except Exception as exc:
        return jsonify({"error": str(exc)}), 500


def fetch_all_bynder_collections_cached(session: requests.Session, force_refresh: bool = False) -> List[Dict[str, Any]]:
    cache = STATE.setdefault("bynder_collection_cache", {})
    key = "all"
    if force_refresh:
        cache.pop(key, None)
    else:
        cached = get_fresh_cached_value(cache, key, BYNDER_COLLECTION_CACHE_MAX_AGE_SECONDS, cache_label="Bynder collection")
        if cached is not None:
            return cached
    url = f"{BYNDER_BASE_URL}/api/v4/collections"
    page = 1
    limit = 100
    out: List[Dict[str, Any]] = []
    while True:
        resp = request_with_retries(session, "GET", url, params={"page": page, "limit": limit})
        payload = resp.json()
        items = payload if isinstance(payload, list) else payload.get("items") or payload.get("results") or payload.get("collections") or []
        if not items:
            break
        for item in items:
            if not isinstance(item, dict):
                continue
            out.append({
                "id": string_value(item.get("id")),
                "name": string_value(item.get("name") or item.get("label") or item.get("title")),
                "description": string_value(item.get("description")),
                "assetCount": int(item.get("assetCount") or item.get("asset_count") or item.get("count") or 0),
            })
        if len(items) < limit:
            break
        page += 1
    out = [x for x in out if x.get("id") and x.get("name")]
    out.sort(key=lambda x: x["name"].lower())
    set_timed_cached_value(cache, key, out)
    return out


def fetch_all_media_for_bynder_collection(session: requests.Session, collection_id: str, limit: int = PAGE_LIMIT) -> List[Dict[str, Any]]:
    url = f"{BYNDER_BASE_URL}/api/v4/media/"
    resp = request_with_retries(session, "GET", url, params={"collectionId": collection_id, "limit": 1, "total": 1})
    payload = resp.json()
    expected_count = int(payload.get("total", {}).get("count", 0))
    if expected_count <= 0:
        return []
    total_pages = math.ceil(expected_count / limit)
    items: List[Dict[str, Any]] = []
    for page in range(1, total_pages + 1):
        r = request_with_retries(session, "GET", url, params={"collectionId": collection_id, "limit": limit, "page": page})
        items.extend(extract_media_items(r.json()))
    deduped: Dict[str, Dict[str, Any]] = {}
    for item in items:
        media_id = string_value(item.get("id"))
        if media_id:
            deduped[media_id] = item
    return list(deduped.values())


@app.route('/api/bynder/collections', methods=['GET'])
def api_bynder_collections() -> Response:
    try:
        session = get_session()
        collections = fetch_all_bynder_collections_cached(session, force_refresh=False)
        return jsonify({"collections": collections})
    except Exception as exc:
        log_message(f"Bynder collection listing failed: {exc}")
        return jsonify({"error": str(exc)}), 500


def find_random_unreviewed_photography_candidate(session: requests.Session, collections: List[Dict[str, str]]) -> Optional[Dict[str, Any]]:
    pool = list(collections or [])
    random.shuffle(pool)
    for collection_option in pool:
        try:
            raw_collection_assets = fetch_collection_assets_cached(session, string_value(collection_option.get("id")))
            by_color: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
            for asset in raw_collection_assets:
                if not is_available_product_photography_asset(asset):
                    continue
                if photo_asset_is_reviewed_for_site(asset):
                    continue
                color_name = string_value(asset.get("property_Product_Color"))
                if not color_name:
                    continue
                by_color[color_name].append(asset)
            if not by_color:
                continue
            color_name = random.choice(list(by_color.keys()))
            color_assets = by_color.get(color_name) or []
            random.shuffle(color_assets)
            sample = color_assets[0] if color_assets else {}
            return {
                "collection": deepcopy(collection_option),
                "color": color_name,
                "photo_count": len(color_assets),
                "sample_media_id": string_value(sample.get("id")),
            }
        except Exception as exc:
            log_message(f"Random collection scan skipped {collection_option.get('label')}: {exc}")
    return None


def get_board_matching_skus_for_color(board: Dict[str, Any], color: str) -> List[str]:
    target = string_value(color)
    for section in (board or {}).get("color_sections", []):
        if string_value(section.get("color")) == target:
            return [string_value(r.get("sku")) for r in section.get("rows", []) if string_value(r.get("sku"))]
    return []


@app.route("/api/launch_random_collection", methods=["POST"])
def api_launch_random_collection() -> Response:
    try:
        collections = ensure_collections_loaded()
        if not collections:
            return jsonify({"error": "No Product Collection options are loaded yet."}), 404

        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        candidate = find_random_unreviewed_photography_candidate(session, collections)
        if candidate is None:
            return jsonify({"error": "Could not find a Product Collection with unreviewed available Product Photography."}), 404

        collection_option = deepcopy(candidate.get("collection") or {})
        color_name = string_value(candidate.get("color"))
        if not string_value(collection_option.get("id")) or not color_name:
            return jsonify({"error": "Random launch candidate was incomplete."}), 500

        board = build_board_for_collection(session, collection_option, force_refresh=False)
        board = filter_board_to_colors(board, [color_name])
        matching_skus = get_board_matching_skus_for_color(board, color_name)
        photography_payload = build_photography_payload_for_color(session, collection_option, color_name, matching_skus)

        STATE["board"] = board
        STATE["baseline_board"] = deepcopy(board)
        STATE["last_load"] = datetime.now().isoformat()
        STATE["game"]["active"] = False
        STATE["game"]["current"] = None

        log_message(f"Launched random collection {collection_option.get('label')} / {color_name} with {len(photography_payload.get('items') or [])} available photography assets.")

        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
            "game": game_status_payload(),
            "photography_autoload": photography_payload,
            "random_launch": {
                "collection": collection_option,
                "color": color_name,
                "photo_count": int(candidate.get("photo_count") or len(photography_payload.get("items") or [])),
                "sample_media_id": string_value(candidate.get("sample_media_id")),
            },
        })
    except Exception as exc:
        log_message(f"Random collection launch failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/load_collection", methods=["POST"])
def api_load_collection() -> Response:
    try:
        payload = request.get_json(force=True)
        option_id = string_value(payload.get("option_id"))
        if not option_id:
            return jsonify({"error": "option_id is required"}), 400

        collections = STATE["collections"] or []
        collection_option = next((c for c in collections if c["id"] == option_id), None)
        if collection_option is None:
            token = load_bynder_token(BYNDER_TOKEN_PATH)
            session = make_session(token)
            collections = fetch_metaproperty_options(session, PRODUCT_COLLECTION_METAPROPERTY_ID)
            STATE["collections"] = collections
            collection_option = next((c for c in collections if c["id"] == option_id), None)

        if collection_option is None:
            return jsonify({"error": f"Could not find Product Collection option {option_id}"}), 404

        force_refresh = bool(payload.get("force_refresh"))
        if force_refresh:
            invalidate_collection_caches(option_id)
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        board = build_board_for_collection(session, collection_option, force_refresh=force_refresh)
        color_filter = [string_value(x) for x in (payload.get("color_filter") or []) if string_value(x)]
        if color_filter:
            board = filter_board_to_colors(board, color_filter)
        STATE["board"] = board
        STATE["baseline_board"] = deepcopy(board)
        STATE["last_load"] = datetime.now().isoformat()
        if not payload.get("game_mode"):
            STATE["game"]["active"] = False
            STATE["game"]["current"] = None

        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
            "game": game_status_payload(),
        })
    except Exception as exc:
        log_message(f"Collection load failed: {exc}")
        return jsonify({"error": str(exc)}), 500



@app.route("/api/game/status")
def api_game_status() -> Response:
    try:
        game = STATE["game"]
        with game["lock"]:
            active = bool(game.get("active"))
            ready_count = len(game.get("queue") or [])
        if active:
            if ready_count < GAME_QUEUE_TARGET:
                maybe_start_game_queue_fill(force=False, target_count=GAME_QUEUE_TARGET)
        else:
            if ready_count < GAME_QUEUE_PRELOAD_TARGET:
                maybe_start_game_queue_fill(force=False, target_count=GAME_QUEUE_PRELOAD_TARGET)
        return jsonify(game_status_payload())
    except Exception as exc:
        return jsonify({"error": str(exc)}), 500


@app.route("/api/game/ensure_queue", methods=["POST"])
def api_game_ensure_queue() -> Response:
    try:
        game = STATE['game']
        with game['lock']:
            ready_count = len(game.get('queue') or [])
            active = bool(game.get('active'))
        if active and ready_count < GAME_QUEUE_TARGET:
            maybe_start_game_queue_fill(force=False, target_count=GAME_QUEUE_TARGET)
        elif (not active) and ready_count < GAME_QUEUE_PRELOAD_TARGET:
            maybe_start_game_queue_fill(force=False, target_count=GAME_QUEUE_PRELOAD_TARGET)
        return jsonify(game_status_payload())
    except Exception as exc:
        return jsonify({"error": str(exc)}), 500


@app.route("/api/game/launch", methods=["POST"])
def api_game_launch() -> Response:
    try:
        game = STATE["game"]
        with game["lock"]:
            has_ready_candidate = bool(game.get("queue"))
        board, had_candidates = get_next_hydrated_game_board(force_fill=not has_ready_candidate, max_attempts=max(24, GAME_QUEUE_TARGET * 3))
        if board is None:
            ensure_game_queue_ready(min_ready=1, timeout_seconds=10.0)
            board, had_candidates = get_next_hydrated_game_board(force_fill=False, max_attempts=max(24, GAME_QUEUE_TARGET * 3))
        if board is None:
            maybe_start_game_queue_fill(force=True)
            message = "No Cleanup Challenge board is ready yet. Please try again in a moment."
            if had_candidates:
                message = "Queued challenge candidates were stale by the time they loaded. The queue is refreshing."
            return jsonify({"error": message}), 503
        STATE["game"]["active"] = True
        STATE["board"] = deepcopy(board)
        STATE["baseline_board"] = deepcopy(board)
        STATE["last_load"] = datetime.now().isoformat()
        maybe_start_game_queue_fill(force=False, target_count=GAME_QUEUE_TARGET)
        return jsonify({"board": STATE["board"], "summary": compute_change_summary(STATE["board"]), "game": game_status_payload()})
    except Exception as exc:
        log_message(f"Game launch failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/game/next", methods=["POST"])
def api_game_next() -> Response:
    try:
        payload = request.get_json(force=True) if request.data else {}
        action = string_value(payload.get("action") or "next")
        if action == "exit":
            STATE["game"]["active"] = False
            STATE["game"]["current"] = None
            return jsonify({"ok": True, "game": game_status_payload()})
        maybe_start_game_queue_fill(force=False, target_count=GAME_QUEUE_TARGET)
        board, had_candidates = get_next_hydrated_game_board(force_fill=False, max_attempts=max(24, GAME_QUEUE_TARGET * 3))
        if board is None:
            ensure_game_queue_ready(min_ready=1, timeout_seconds=10.0)
            board, had_candidates = get_next_hydrated_game_board(force_fill=False, max_attempts=max(24, GAME_QUEUE_TARGET * 3))
        if board is None:
            maybe_start_game_queue_fill(force=True)
            message = "No Cleanup Challenge board is ready yet."
            if had_candidates:
                message = "Queued Cleanup Challenge candidates were stale by the time they loaded. The queue is refreshing."
            return jsonify({"error": message}), 503
        STATE["game"]["active"] = True
        STATE["board"] = deepcopy(board)
        STATE["baseline_board"] = deepcopy(board)
        STATE["last_load"] = datetime.now().isoformat()
        maybe_start_game_queue_fill(force=True, target_count=GAME_QUEUE_TARGET)
        return jsonify({"board": STATE["board"], "summary": compute_change_summary(STATE["board"]), "game": game_status_payload(), "action": action})
    except Exception as exc:
        log_message(f"Game next failed: {exc}")
        return jsonify({"error": str(exc)}), 500




@app.route("/api/game/reload_current", methods=["POST"])
def api_game_reload_current() -> Response:
    try:
        game = STATE.get("game") or {}
        current = game.get("current") if game.get("active") else None
        if not current:
            return jsonify({"error": "No active Cleanup Challenge is loaded."}), 400
        collection = current.get("collection") or {}
        color_name = string_value(current.get("color"))
        if not collection or not string_value(collection.get("id")) or not color_name:
            return jsonify({"error": "Current Cleanup Challenge is missing collection/color context."}), 400

        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        collection_id = string_value(collection.get("id"))
        invalidate_collection_caches(collection_id)
        refreshed = build_board_for_collection(session, collection, force_refresh=True)
        board = filter_board_to_colors(refreshed, [color_name])
        STATE["board"] = board
        STATE["baseline_board"] = deepcopy(board)
        STATE["last_load"] = datetime.now().isoformat()

        old_total = int((current.get("issues") or {}).get("total") or current.get("issue_total") or 0)
        new_issues = compute_board_issue_summary(board, include_missing_dims=False)
        new_total = int(new_issues.get("total") or 0)
        resolved = max(0, old_total - new_total)
        if resolved:
            update_game_score(resolved)
        current["issues"] = new_issues
        current["issue_total"] = new_total
        STATE["game"]["current"] = current

        completed = new_total == 0
        if completed:
            maybe_start_game_queue_fill(force=False)

        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
            "game": {**game_status_payload(), "resolved": resolved, "completed": completed, "remaining": new_total, "advanced": False},
        })
    except Exception as exc:
        log_message(f"Game reload failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/load_photography", methods=["POST"])
def api_load_photography() -> Response:
    try:
        if STATE["board"] is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        option_id = string_value(payload.get("option_id"))
        color = string_value(payload.get("color"))
        if not option_id or not color:
            return jsonify({"error": "option_id and color are required"}), 400

        collections = STATE["collections"] or []
        collection_option = next((c for c in collections if c["id"] == option_id), None)
        if collection_option is None:
            return jsonify({"error": "Could not find Product Collection option."}), 404

        color_rows = []
        for section in STATE["board"].get("color_sections", []):
            if string_value(section.get("color")) == color:
                color_rows = section.get("rows", [])
                break
        matching_skus = [string_value(r.get("sku")) for r in color_rows if string_value(r.get("sku"))]

        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        payload = build_photography_payload_for_color(session, collection_option, color, matching_skus)
        return jsonify(payload)
    except Exception as exc:
        log_message(f"Photography load failed: {exc}")
        return jsonify({"error": str(exc)}), 500



@app.route('/api/onboarding/load_collection_photography', methods=['POST'])
def api_onboarding_load_collection_photography() -> Response:
    try:
        session = get_session()
        payload = request.get_json(force=True) or {}
        collection_id = string_value(payload.get('collection_id'))
        collection_name = string_value(payload.get('collection_name'))
        if not collection_id:
            return jsonify({'error':'Missing Bynder collection id.'}), 400
        raw_assets = fetch_all_media_for_bynder_collection(session, collection_id)
        items = [photo_asset_to_client_model(asset, []) for asset in sorted(raw_assets, key=lambda a: string_value(a.get('dateCreated')), reverse=True)]
        return jsonify({'collection_label': collection_name or '', 'items': items})
    except Exception as exc:
        log_message(f'Onboarding collection photography load failed: {exc}')
        return jsonify({'error': str(exc)}), 500

@app.route("/api/mark_photo_reviewed", methods=["POST"])
def api_mark_photo_reviewed() -> Response:
    try:
        payload = request.get_json(force=True)
        media_id = string_value(payload.get("media_id") or payload.get("source_media_id"))
        if not media_id:
            return jsonify({"error": "media_id is required"}), 400

        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        metaprops_by_dbname = fetch_metaproperties_map(session)
        reviewed_mp = metaprops_by_dbname.get(REVIEWED_FOR_SITE_DBNAME)
        if not reviewed_mp:
            return jsonify({"error": f"Could not find metaproperty {REVIEWED_FOR_SITE_DBNAME}."}), 404

        reviewed_mp_id = string_value(reviewed_mp.get("id"))
        reviewed_option_value = get_metaproperty_option_value(session, reviewed_mp_id, REVIEWED_FOR_SITE_LABEL)
        if not reviewed_option_value:
            return jsonify({"error": f"Could not resolve option {REVIEWED_FOR_SITE_LABEL}."}), 404

        post_media_fields(session, media_id, [(f"metaproperty.{reviewed_mp_id}", reviewed_option_value)])
        log_message(f"Marked photography asset {media_id} as reviewed for site.")
        return jsonify({
            "ok": True,
            "media_id": media_id,
            "reviewed_for_site": True,
            "reviewed_for_site_values": [REVIEWED_FOR_SITE_LABEL],
            "notice": {"kind": "success", "text": "Photography asset marked as reviewed for site."},
        })
    except Exception as exc:
        log_message(f"Mark photo reviewed failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/pull_additional_photography_for_sku", methods=["POST"])
def api_pull_additional_photography_for_sku() -> Response:
    try:
        if STATE["board"] is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        option_id = string_value(payload.get("option_id"))
        sku = string_value(payload.get("sku"))
        existing_ids = payload.get("existing_ids") or []
        if not sku:
            return jsonify({"error": "sku is required"}), 400

        board = STATE["board"]
        row = None
        section_color = ""
        matching_skus: List[str] = []
        for section in board.get("color_sections", []):
            for candidate in section.get("rows", []):
                if string_value(candidate.get("sku")) == sku:
                    row = candidate
                    section_color = string_value(section.get("color"))
                    matching_skus = [string_value(r.get("sku")) for r in section.get("rows", []) if string_value(r.get("sku"))]
                    break
            if row:
                break
        if row is None:
            return jsonify({"error": "Could not find SKU on the current board."}), 404

        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        items = build_additional_photography_payload_for_sku(session, sku, matching_skus, existing_ids)
        return jsonify({
            "sku": sku,
            "color": section_color,
            "items": items,
            "added_count": len(items),
        })
    except Exception as exc:
        log_message(f"Additional photography pull failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/check_additional_photography_for_skus", methods=["POST"])
def api_check_additional_photography_for_skus() -> Response:
    try:
        if STATE["board"] is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        skus = [string_value(x) for x in (payload.get("skus") or []) if string_value(x)]
        existing_ids = payload.get("existing_ids") or []
        if not skus:
            return jsonify({"availability": {}})
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        availability: Dict[str, bool] = {}
        with ThreadPoolExecutor(max_workers=min(4, len(skus) or 1)) as executor:
            futures = {executor.submit(has_additional_photography_for_sku, session, sku, existing_ids): sku for sku in skus}
            for future in as_completed(futures):
                sku = futures[future]
                availability[sku] = bool(future.result())
        return jsonify({"availability": availability})
    except Exception as exc:
        log_message(f"Additional photography availability check failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/load_non_collection_sku", methods=["POST"])
def api_load_non_collection_sku() -> Response:
    try:
        if STATE["board"] is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        sku = string_value(payload.get("sku"))
        if not sku:
            return jsonify({"error": "sku is required"}), 400
        board = STATE["board"]
        for section in board.get("color_sections", []):
            for row in section.get("rows", []):
                if string_value(row.get("sku")) == sku:
                    return jsonify({"board": board, "summary": compute_change_summary(board), "sku": sku, "already_present": True})
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        row = build_board_row_for_sku(session, sku, string_value(board.get("collection", {}).get("label")))
        if row is None:
            return jsonify({"error": f"Could not find Product Site Assets for SKU {sku}."}), 404
        insert_non_collection_row(board, row)
        return jsonify({"board": board, "summary": compute_change_summary(board), "sku": sku, "row": row, "already_present": False})
    except Exception as exc:
        log_message(f"Non-collection SKU load failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/photo_prep_preview", methods=["POST"])
def api_photo_prep_preview() -> Response:
    try:
        payload = request.get_json(force=True)
        media_id = string_value(payload.get("media_id") or payload.get("source_media_id"))
        if not media_id:
            return jsonify({"error": "media_id is required"}), 400
        mode = string_value(payload.get("mode") or "crop_1688")
        flip = bool(payload.get("flip"))
        offset_y = payload.get("offset_y")
        offset_x = payload.get("offset_x")
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        img = open_image_from_media(session, media_id)
        apply_watermark = bool(payload.get("apply_watermark"))
        result = render_photo_preview_image(img, mode, flip, offset_y, offset_x)
        if apply_watermark:
            result = apply_photo_watermark(result)
        return send_file(BytesIO(image_to_png_bytes(result)), mimetype="image/png")
    except Exception as exc:
        log_message(f"Photo prep preview failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/photo_prep_download", methods=["POST"])
def api_photo_prep_download() -> Response:
    try:
        payload = request.get_json(force=True)
        items = payload.get("items") or []
        if not isinstance(items, list) or not items:
            return jsonify({"error": "At least one item is required"}), 400
        flip = bool(payload.get("flip"))
        mode = string_value(payload.get("mode") or "crop_1688")
        out_w, out_h = prep_mode_to_size(mode)
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        if len(items) == 1:
            item = items[0]
            media_id = string_value(item.get("media_id") or item.get("source_media_id"))
            name = string_value(item.get("name")) or media_id
            offset_y = item.get("offset_y")
            offset_x = item.get("offset_x")
            img = open_image_from_media(session, media_id)
            result = prepare_photo_result(img, mode, flip, offset_y, offset_x)
            fname = f"{Path(name).stem}_{out_w}x{out_h}{'_flip' if flip else ''}.jpg"
            return send_file(BytesIO(image_to_jpg_bytes(result)), mimetype="image/jpeg", as_attachment=True, download_name=fname)
        bio = BytesIO()
        with ZipFile(bio, 'w', ZIP_DEFLATED) as zf:
            for item in items:
                media_id = string_value(item.get("media_id") or item.get("source_media_id"))
                name = string_value(item.get("name")) or media_id
                offset_y = item.get("offset_y")
                offset_x = item.get("offset_x")
                img = open_image_from_media(session, media_id)
                result = prepare_photo_result(img, mode, flip, offset_y, offset_x)
                fname = f"{Path(name).stem}_{out_w}x{out_h}{'_flip' if flip else ''}.jpg"
                zf.writestr(fname, image_to_jpg_bytes(result))
        bio.seek(0)
        return send_file(bio, mimetype='application/zip', as_attachment=True, download_name=f"photo_prep_{mode}{'_flip' if flip else ''}.zip")
    except Exception as exc:
        log_message(f"Photo prep download failed: {exc}")
        return jsonify({"error": str(exc)}), 500



def build_set_dim_canvas_for_row(session: requests.Session, row: Dict[str, Any], slot_assignments: Optional[List[int]] = None, scale_percents: Optional[List[int]] = None) -> Image.Image:
    components = [c for c in safe_list(row.get("set_dim_components")) if isinstance(c, dict) and string_value(c.get("dim_media_id"))]
    if not components:
        raise RuntimeError("No compiled set-dim components are available for this SKU.")
    images: List[Image.Image] = []
    subcats: List[str] = []
    comps = components[:SET_DIM_MAX_COMPONENTS]
    def _load_comp(comp: Dict[str, Any]) -> tuple[Image.Image, str]:
        img = open_image_from_media(session, string_value(comp.get("dim_media_id")))
        return trim_whitespace(img, 0).convert("RGB"), string_value(comp.get("component_subcat"))
    with ThreadPoolExecutor(max_workers=min(MAX_WORKERS, max(1, len(comps)))) as executor:
        for img, subcat in executor.map(_load_comp, comps):
            images.append(img)
            subcats.append(subcat)
    manual_slots = None
    if slot_assignments:
        manual_slots = [max(0, min(len(images) - 1, int(x))) for x in slot_assignments[:len(images)]]
    return compose_set_dim_canvas(images, subcats, string_value(row.get("product_subcategory")), manual_slots, scale_percents)


@app.route("/api/set_dim_compile_preview", methods=["POST"])
def api_set_dim_compile_preview() -> Response:
    try:
        board = STATE.get("board")
        if board is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        row_id = string_value(payload.get("row_id"))
        row = get_row_by_id(board, row_id)
        if not row:
            return jsonify({"error": "Row not found."}), 404
        slot_assignments = payload.get("slot_assignments") or []
        scale_percents = payload.get("scale_percents") or []
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        result = build_set_dim_canvas_for_row(session, row, slot_assignments, scale_percents)
        return send_file(BytesIO(image_to_png_bytes(result)), mimetype="image/png")
    except Exception as exc:
        log_message(f"Set dim compile preview failed: {exc}")
        return jsonify({"error": str(exc)}), 500



@app.route("/api/set_dim_component_thumb/<media_id>", methods=["GET"])
def api_set_dim_component_thumb(media_id: str) -> Response:
    try:
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        img = open_image_from_media(session, string_value(media_id))
        img = trim_whitespace(img, 0).convert("RGB")
        img.thumbnail((220, 160), Image.LANCZOS)
        return send_file(BytesIO(image_to_png_bytes(img)), mimetype="image/png")
    except Exception as exc:
        log_message(f"Set dim component thumb failed for {media_id}: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/set_dim_compile_apply", methods=["POST"])
def api_set_dim_compile_apply() -> Response:
    try:
        board = STATE.get("board")
        if board is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        mode = string_value(payload.get("mode")) or "positions"
        if mode != "assets":
            return jsonify({"error": "Compiled set dims are only available in Update assets mode."}), 400
        row_id = string_value(payload.get("row_id"))
        row = get_row_by_id(board, row_id)
        if not row:
            return jsonify({"error": "Row not found."}), 404
        buckets = bucket_assets(row)
        if buckets.get("special", {}).get("SKU_dimension"):
            return jsonify({"error": "This SKU already has a dimensions asset."}), 400
        if not bool(row.get("set_dim_compile_ready")):
            return jsonify({"error": string_value(row.get("set_dim_compile_reason")) or "This SKU is not eligible for compiled set dims."}), 400
        slot_assignments = payload.get("slot_assignments") or []
        scale_percents = payload.get("scale_percents") or []
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        result_image = build_set_dim_canvas_for_row(session, row, slot_assignments, scale_percents)
        with tempfile.TemporaryDirectory(prefix="content_refresher_set_dim_") as td:
            target_name = force_jpg_filename(f"{string_value(row.get('sku'))}_compiled_set_dim.jpg", "compiled_set_dim")
            temp_path = Path(td) / target_name
            result_image.save(temp_path, format="JPEG", quality=92, optimize=True)
            result = apply_prepared_file_to_slot(
                session,
                board,
                row_id,
                "special",
                "SKU_dimension",
                temp_path,
                psa_image_type_override=DIMENSIONS_PSA_IMAGE_TYPE_LABEL,
            )
        message = result.get("message") if isinstance(result, dict) else string_value(result)
        notice_html = 'Compiled set dim was added. <button type="button" class="inline-link" data-reload-board>Reload</button> to see it!'
        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
            "notice": {"kind": "success", "text": message, "html": notice_html},
            "asset_mode_refresh_pending": True,
            "dirty_row_ids": [row_id] if row_id else [],
        })
    except Exception as exc:
        log_message(f"Set dim compile apply failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/queue_deliverable_fix", methods=["POST"])
def api_queue_deliverable_fix() -> Response:
    try:
        if STATE["board"] is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        asset_id = string_value(payload.get("asset_id"))
        if not asset_id:
            return jsonify({"error": "asset_id is required."}), 400
        board, row_id, expected = queue_deliverable_fix_on_board(STATE["board"], asset_id)
        STATE["board"] = board
        STATE["summary"] = compute_change_summary(STATE["board"])
        return jsonify({
            "board": STATE["board"],
            "summary": STATE["summary"],
            "dirty_row_ids": [row_id] if row_id else [],
            "notice": {"kind": "success", "text": f"Deliverable queued to update to {expected}."},
        })
    except Exception as exc:
        log_message(f"Queue deliverable fix failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/move", methods=["POST"])
def api_move() -> Response:
    try:
        if STATE["board"] is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        row_id = string_value(payload.get("row_id"))
        asset_id = string_value(payload.get("asset_id"))
        target_lane = string_value(payload.get("target_lane"))
        target_slot = string_value(payload.get("target_slot")) or None
        STATE["board"] = apply_move(STATE["board"], row_id, asset_id, target_lane, target_slot)
        return jsonify({"board": STATE["board"], "summary": compute_change_summary(STATE["board"])})
    except Exception as exc:
        log_message(f"Move failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/remove_pending_copy", methods=["POST"])
def api_remove_pending_copy() -> Response:
    try:
        if STATE["board"] is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        asset_id = string_value(payload.get("asset_id"))
        target_pos = string_value(payload.get("target_pos"))
        source_media_id = string_value(payload.get("source_media_id"))
        target_sku = string_value(payload.get("target_sku"))
        removed = remove_pending_copy_from_board(STATE["board"], asset_id, target_pos, source_media_id, target_sku)
        if not removed:
            return jsonify({"error": "Pending copy not found.", "board": STATE["board"], "summary": compute_change_summary(STATE["board"])}), 404
        return jsonify({"board": STATE["board"], "summary": compute_change_summary(STATE["board"])})
    except Exception as exc:
        log_message(f"Remove pending copy failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/apply_wall_art_sizing_guide", methods=["POST"])
def api_apply_wall_art_sizing_guide() -> Response:
    try:
        payload = request.get_json(force=True)
        row_id = string_value(payload.get("row_id"))
        if not row_id:
            return jsonify({"error": "row_id is required."}), 400
        board = STATE.get("board")
        row = get_row_by_id(board, row_id) if board else None
        if not row:
            return jsonify({"error": "Target row not found."}), 404
        if not row_requires_wall_art_sizing(row):
            return jsonify({"error": "This SKU does not require the wall art sizing guide."}), 400
        live_assets = [a for a in (row.get("assets") or []) if not a.get("is_marked_for_deletion") and not a.get("is_empty_slot")]
        has_8000 = any(string_value(a.get("slot_key")) == "SKU_8000" or string_value(a.get("current_position")).endswith("_8000") for a in live_assets)
        if has_8000:
            return jsonify({"error": "This SKU already has a wall art sizing guide in SKU_8000."}), 400

        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        sku = string_value(row.get("sku"))
        target_position = exact_position_for_row(sku, SPECIAL_CAROUSEL_SLOT)
        target_filename = f"{sku}_wall_art_sizing_guide_3000x1688.jpg" if sku else WALL_ART_SIZING_GUIDE_FILENAME
        result = create_copied_asset_for_target(
            session,
            WALL_ART_SIZING_GUIDE_MEDIA_ID,
            "",
            sku,
            target_position,
            asset_name=target_filename,
        )
        source_asset = fetch_media_by_id(session, WALL_ART_SIZING_GUIDE_MEDIA_ID)
        placeholder = build_uploaded_new_asset_placeholder(
            source_asset,
            sku,
            target_position,
            target_filename,
            "core",
            SPECIAL_CAROUSEL_SLOT,
            result.get("new_media_id") or "",
            "",
            string_value(source_asset.get(f"property_{PSA_IMAGE_TYPE_DBNAME}"))
        )
        row.setdefault("assets", []).append(placeholder)
        STATE["summary"] = compute_change_summary(STATE["board"])
        return jsonify({
            "board": STATE["board"],
            "summary": STATE["summary"],
            "asset_mode_refresh_pending": True,
            "dirty_row_ids": [row_id],
            "notice": {
                "kind": "success",
                "text": "Wall art sizing guide was added to SKU_8000. Reload to see it."
            }
        })
    except Exception as exc:
        log_message(f"Wall art sizing guide apply failed: {exc}")
        return jsonify({"error": str(exc)}), 500


def _fixed_asset_refresh_ready(row: Optional[Dict[str, Any]], media_id: str, fix_type: str) -> bool:
    if not row:
        return False
    asset = None
    for candidate in row.get("assets", []):
        if string_value(candidate.get("id")) == string_value(media_id):
            asset = candidate
            break
    if not asset:
        return False
    warning_text = string_value(asset.get("size_warning"))
    width = int(asset.get("width") or 0)
    height = int(asset.get("height") or 0)
    if fix_type == "swatch":
        return width == 163 and height == 163 and not warning_text
    if fix_type == "grid":
        return width == 3000 and height == 2200 and not is_total_fill_warning_text(warning_text)
    if fix_type in {"dim", "silo"}:
        return width == 3000 and height == 1688 and not is_total_fill_warning_text(warning_text)
    return bool(width and height)


def poll_for_fixed_asset_row(
    session: requests.Session,
    board: Dict[str, Any],
    row_id: str,
    media_id: str,
    collection_label: str,
    fix_type: str,
    timeout_seconds: float = 12.0,
    sleep_seconds: float = 1.5,
) -> Tuple[Optional[Dict[str, Any]], bool]:
    started = time.time()
    latest_row = get_row_by_id(board, row_id)
    while (time.time() - started) < timeout_seconds:
        refreshed_row = build_board_row_for_sku(session, string_value((latest_row or {}).get("sku") or row_id), collection_label)
        if refreshed_row:
            latest_row = refreshed_row
            if _fixed_asset_refresh_ready(refreshed_row, media_id, fix_type):
                return refreshed_row, True
        time.sleep(sleep_seconds)
    return latest_row, False


@app.route("/api/fix_asset_version", methods=["POST"])
def api_fix_asset_version() -> Response:
    try:
        board = STATE.get("board")
        if board is None:
            return jsonify({"error": "No collection is currently loaded."}), 400

        payload = request.get_json(force=True)
        mode = string_value(payload.get("mode"))
        if mode != "assets":
            return jsonify({"error": "Asset fixes are only available in Update assets mode."}), 400

        media_id = string_value(payload.get("media_id") or payload.get("source_media_id"))
        fix_type = string_value(payload.get("fix_type"))
        if not media_id or not fix_type:
            return jsonify({"error": "media_id and fix_type are required."}), 400

        asset = get_asset_by_id(board, media_id)
        if not asset:
            return jsonify({"error": "Asset not found on the current board."}), 404
        if asset.get("pending_upload"):
            return jsonify({"error": "Pending assets cannot be auto-fixed."}), 400

        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        image = open_image_from_media(session, media_id)
        target_name = force_jpg_filename(string_value(asset.get("file_name") or asset.get("name") or "asset"), "asset")

        if fix_type == "swatch":
            if image.width != image.height:
                return jsonify({"error": "Swatch auto-fix only works when the current image is already square."}), 400
            processed = image.resize((163, 163), Image.LANCZOS).convert('RGB')
            success_text = "Swatch was resized to 163x163 and uploaded as a new version."
        elif fix_type in {"dim", "silo"}:
            processed = reformat_silo_like_image(image)
            success_text = "Asset was reformatted to 3000x1688 and uploaded as a new version."
        elif fix_type == "grid":
            processed = reformat_silo_like_image(image, canvas_size=(3000, 2200))
            success_text = "Grid asset was reformatted to 3000x2200 and uploaded as a new version."
        else:
            return jsonify({"error": f"Unsupported fix_type: {fix_type}"}), 400

        with tempfile.TemporaryDirectory(prefix="content_refresher_fix_asset_") as td:
            temp_path = Path(td) / target_name
            save_processed_image_for_upload(processed, temp_path)
            upload_new_version_to_media(session, media_id, temp_path, target_name)

        mark_asset_uploaded_notice(asset, "new_version", "New version uploaded to this slot. Reload to view.")
        dirty_row_ids: List[str] = []
        target_row = get_row_containing_asset(board, media_id)
        refresh_resolved = False
        if target_row:
            row_id = string_value(target_row.get("row_id") or target_row.get("sku"))
            dirty_row_ids.append(row_id)
            refreshed_row, refresh_resolved = poll_for_fixed_asset_row(
                session,
                board,
                row_id,
                media_id,
                string_value(board.get("collection", {}).get("label")),
                fix_type,
            )
            if refreshed_row:
                replace_row_in_board(board, row_id, refreshed_row)
                baseline = STATE.get("baseline_board")
                if baseline is not None:
                    replace_row_in_board(baseline, row_id, deepcopy(refreshed_row))

        notice_html = f'{success_text} <button type="button" class="inline-link" data-reload-board>Reload</button> to see it!'
        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
            "notice": {"kind": "success", "text": success_text, "html": notice_html},
            "asset_mode_refresh_pending": (not refresh_resolved),
            "dirty_row_ids": [] if refresh_resolved else dirty_row_ids,
        })
    except Exception as exc:
        log_message(f"Fix asset version failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/download/<path:asset_id>")
def api_download(asset_id: str) -> Response:
    try:
        board = STATE.get("board")
        if board is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        asset = get_asset_by_id(board, asset_id)
        source_media_id = asset_id
        file_name = "asset"
        original_url = ""
        if asset is not None:
            source_media_id = asset.get("copy_source_media_id") if asset.get("pending_upload") else asset.get("id")
            file_name = asset.get("file_name") or asset.get("name") or "asset"
            original_url = string_value(asset.get("original"))
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)

        upstream = None
        if original_url:
            try:
                upstream = requests.get(original_url, stream=False, timeout=120, allow_redirects=True)
                upstream.raise_for_status()
            except Exception as exc:
                log_message(f"Direct original download failed for {source_media_id}: {exc}")
                upstream = None

        if upstream is None:
            try:
                download_url = get_media_download_url(session, source_media_id)
                upstream = requests.get(download_url, stream=False, timeout=120, allow_redirects=True)
                upstream.raise_for_status()
            except Exception as exc:
                log_message(f"Presigned download failed for {source_media_id}; retrying via Bynder redirect. Error: {exc}")
                download_endpoint = f"{BYNDER_BASE_URL}/api/v4/media/{source_media_id}/download/"
                with session.get(download_endpoint, stream=True, timeout=120, allow_redirects=True) as r:
                    r.raise_for_status()
                    ctype = (r.headers.get("Content-Type") or "").lower()
                    if "application/json" in ctype:
                        data = r.json()
                        redirect_url = ""
                        if isinstance(data, dict):
                            for k in ("s3_file", "s3File", "url", "downloadUrl", "download_url", "location"):
                                v = data.get(k)
                                if isinstance(v, str) and v.startswith("http"):
                                    redirect_url = v
                                    break
                            if not redirect_url:
                                for v in data.values():
                                    if isinstance(v, str) and v.startswith("http"):
                                        redirect_url = v
                                        break
                        if not redirect_url:
                            raise RuntimeError(f"Could not determine redirect URL for media {source_media_id}")
                        upstream = requests.get(redirect_url, stream=False, timeout=120, allow_redirects=True)
                        upstream.raise_for_status()
                    else:
                        content = r.content
                        mime = r.headers.get("Content-Type") or mimetypes.guess_type(file_name)[0] or "application/octet-stream"
                        headers = {
                            "Content-Disposition": f'attachment; filename="{file_name}"',
                            "Content-Length": str(len(content)),
                            "Cache-Control": "no-store",
                        }
                        return Response(content, mimetype=mime, headers=headers)

        mime = upstream.headers.get("Content-Type") or mimetypes.guess_type(file_name)[0] or "application/octet-stream"
        content = upstream.content

        def _resolve_download_name(base_name: str, source_url: str, response_obj) -> str:
            candidate = string_value(base_name) or "asset"
            header_name = ""
            try:
                content_disp = response_obj.headers.get("Content-Disposition", "") or ""
                m = re.search(r"filename\*=UTF-8''([^;]+)", content_disp)
                if m:
                    header_name = unquote(m.group(1))
                else:
                    m = re.search(r'filename=\"?([^\";]+)', content_disp)
                    if m:
                        header_name = m.group(1)
            except Exception:
                header_name = ""
            if header_name:
                candidate = header_name
            if not Path(candidate).suffix:
                url_name = Path(unquote((source_url or "").split("?", 1)[0])).name
                ext = Path(url_name).suffix
                if not ext:
                    ext = extension_from_content_type(response_obj.headers.get("Content-Type") or mime)
                if ext:
                    candidate = f"{candidate}{ext}"
            return candidate or "asset"

        resolved_name = _resolve_download_name(file_name, original_url or getattr(upstream, 'url', '') or '', upstream)
        headers = {
            "Content-Disposition": f'attachment; filename="{resolved_name}"',
            "Content-Length": str(len(content)),
            "Cache-Control": "no-store",
        }
        return Response(content, mimetype=mime, headers=headers)
    except Exception as exc:
        log_message(f"Download failed for {asset_id}: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/prepared_add_as_new_version", methods=["POST"])
def api_prepared_add_as_new_version() -> Response:
    try:
        board = STATE.get("board")
        if board is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        mode = string_value(payload.get("mode"))
        if mode != "assets":
            return jsonify({"error": "Prepared version updates are only available in Update assets mode."}), 400
        media_id = string_value(payload.get("media_id") or payload.get("source_media_id"))
        prep_mode = string_value(payload.get("prep_mode") or "crop_1688")
        flip = bool(payload.get("flip"))
        offset_y = payload.get("offset_y")
        offset_x = payload.get("offset_x")
        file_name = string_value(payload.get("file_name")) or "prepared_image.jpg"
        if not media_id:
            return jsonify({"error": "media_id is required"}), 400

        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        img = open_image_from_media(session, media_id)
        result = prepare_photo_result(img, prep_mode, flip, offset_y, offset_x)

        with tempfile.TemporaryDirectory(prefix="content_refresher_prepped_version_") as td:
            target_name = force_jpg_filename(file_name, "prepared_image")
            temp_path = Path(td) / target_name
            result = result.convert("RGB")
            result.save(temp_path, format="JPEG", quality=92, optimize=True)
            upload_new_version_to_media(session, media_id, temp_path, target_name)

        target_asset = get_asset_by_id(board, media_id)
        dirty_row_ids: List[str] = []
        if target_asset:
            mark_asset_uploaded_notice(target_asset, "new_version", "New version uploaded to this slot. Reload to view.")
            target_row = get_row_containing_asset(board, media_id)
            if target_row:
                dirty_row_ids.append(string_value(target_row.get("row_id") or target_row.get("sku")))

        notice_html = 'Modified image was uploaded as a new version. <button type="button" class="inline-link" data-reload-board>Reload</button> to see it!'
        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
            "notice": {"kind": "success", "text": "Modified image was uploaded as a new version.", "html": notice_html},
            "asset_mode_refresh_pending": True,
            "dirty_row_ids": dirty_row_ids,
        })
    except Exception as exc:
        log_message(f"Prepared add-as-new-version failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/prepared_drop_upload", methods=["POST"])
def api_prepared_drop_upload() -> Response:
    try:
        board = STATE.get("board")
        if board is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        mode = string_value(payload.get("mode")) or "positions"
        if mode != "assets":
            return jsonify({"error": "Prepared image drops are only available in Update assets mode."}), 400
        row_id = string_value(payload.get("row_id"))
        target_lane = string_value(payload.get("target_lane"))
        target_slot = string_value(payload.get("target_slot"))
        media_id = string_value(payload.get("media_id") or payload.get("source_media_id") or payload.get("asset_id") or ((payload.get("item") or {}).get("media_id" if isinstance(payload.get("item"), dict) else "") if False else ""))
        if not media_id:
            item = payload.get("item")
            if isinstance(item, dict):
                media_id = string_value(item.get("media_id") or item.get("source_media_id"))
        prep_mode = string_value(payload.get("prep_mode") or "original")
        flip = bool(payload.get("flip"))
        offset_y = payload.get("offset_y")
        offset_x = payload.get("offset_x")
        if not media_id:
            return jsonify({"error": "media_id is required"}), 400
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        psa_image_type_override = string_value(payload.get("psa_image_type_override"))
        result = apply_prepared_media_to_slot(session, board, row_id, target_lane, target_slot, media_id, prep_mode, flip, offset_y, offset_x, psa_image_type_override)
        message = result.get("message") if isinstance(result, dict) else string_value(result)
        kind_word = result.get("kind") if isinstance(result, dict) else "updated"
        notice_html = f'Prepared image was {kind_word}. <button type="button" class="inline-link" data-reload-board>Reload</button> to see it!'
        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
            "notice": {"kind": "success", "text": message, "html": notice_html},
            "asset_mode_refresh_pending": True,
            "dirty_row_ids": [row_id] if row_id else [],
        })
    except Exception as exc:
        log_message(f"Prepared drop upload failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/file_drop_upload", methods=["POST"])
def api_file_drop_upload() -> Response:
    try:
        board = STATE.get("board")
        if board is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        mode = string_value(request.form.get("mode")) or "positions"
        if mode != "assets":
            return jsonify({"error": "File uploads are only available in Update assets mode."}), 400
        row_id = string_value(request.form.get("row_id"))
        target_lane = string_value(request.form.get("target_lane"))
        target_slot = string_value(request.form.get("target_slot"))
        upload = request.files.get("file")
        if not upload:
            return jsonify({"error": "No file was provided."}), 400
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        psa_image_type_override = string_value(request.form.get("psa_image_type_override"))
        result = apply_uploaded_file_to_slot(session, board, row_id, target_lane, target_slot, upload, psa_image_type_override)
        message = result.get("message") if isinstance(result, dict) else string_value(result)
        kind_word = result.get("kind") if isinstance(result, dict) else "updated"
        notice_html = f'Assets were {kind_word}. <button type="button" class="inline-link" data-reload-board>Reload</button> to see them!'
        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
            "notice": {"kind": "success", "text": message, "html": notice_html},
            "asset_mode_refresh_pending": True,
            "dirty_row_ids": [row_id] if row_id else [],
        })
    except Exception as exc:
        log_message(f"File drop upload failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/discard", methods=["POST"])
def api_discard() -> Response:
    try:
        if STATE["baseline_board"] is None:
            return jsonify({"error": "No loaded collection state is available to discard back to."}), 400
        STATE["board"] = deepcopy(STATE["baseline_board"])
        return jsonify({"board": STATE["board"], "summary": compute_change_summary(STATE["board"])})
    except Exception as exc:
        log_message(f"Discard failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/refresh_rows", methods=["POST"])
def api_refresh_rows() -> Response:
    try:
        board = STATE.get("board")
        if board is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        payload = request.get_json(force=True)
        row_ids = [string_value(x) for x in safe_list(payload.get("row_ids")) if string_value(x)]
        if not row_ids:
            return jsonify({"error": "row_ids are required"}), 400
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        collection_label = string_value(board.get("collection", {}).get("label"))
        refreshed = []
        for row_id in row_ids:
            existing_row = get_row_by_id(board, row_id)
            if not existing_row:
                continue
            new_row = build_board_row_for_sku(session, string_value(existing_row.get("sku") or row_id), collection_label)
            if not new_row:
                continue
            if not existing_row.get("is_non_collection"):
                new_row["is_non_collection"] = False
                new_row["product_color"] = existing_row.get("product_color") or new_row.get("product_color")
            replaced = replace_row_in_board(board, row_id, new_row)
            baseline = STATE.get("baseline_board")
            if baseline is not None:
                replace_row_in_board(baseline, row_id, deepcopy(new_row))
            if replaced:
                refreshed.append(string_value(new_row.get("row_id") or new_row.get("sku") or row_id))
        collection_id = string_value(board.get("collection", {}).get("id"))
        if collection_id:
            set_timed_cached_value(STATE.setdefault("collection_board_cache", {}), collection_id, board)
        return jsonify({"board": board, "summary": compute_change_summary(board), "refreshed_row_ids": refreshed})
    except Exception as exc:
        log_message(f"Row refresh failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/commit", methods=["POST"])
def api_commit() -> Response:
    try:
        if STATE["board"] is None:
            return jsonify({"error": "No collection is currently loaded."}), 400
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        result = commit_changes(STATE["board"], session)
        STATE["last_commit"] = result

        game_payload = game_status_payload()
        if result["all_succeeded"]:
            invalidate_collection_caches(string_value(STATE["board"]["collection"].get("id")))
            current_game = STATE["game"].get("current") if STATE["game"].get("active") else None
            if current_game:
                return jsonify({
                    "commit": result,
                    "board": STATE["board"],
                    "summary": compute_change_summary(STATE["board"]),
                    "refreshed": False,
                    "game": {**game_status_payload(), "resolved": 0, "completed": False, "remaining": int((current_game.get("issues") or {}).get("total") or current_game.get("issue_total") or 0), "pending_verification": True},
                })

            return jsonify({
                "commit": result,
                "board": STATE["board"],
                "summary": compute_change_summary(STATE["board"]),
                "refreshed": False,
                "game": game_status_payload(),
                "pending_verification": True,
            })

        return jsonify({
            "commit": result,
            "board": STATE["board"],
            "summary": compute_change_summary(STATE["board"]),
            "refreshed": False,
            "game": game_payload,
        })
    except Exception as exc:
        log_message(f"Commit failed: {exc}")
        return jsonify({"error": str(exc)}), 500



@app.route("/api/onboarding/boards")
def api_onboarding_boards() -> Response:
    try:
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        summaries = build_onboarding_collection_summaries(session)
        return jsonify({"boards": summaries})
    except Exception as exc:
        log_message(f"Onboarding board listing failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/onboarding/create_board", methods=["POST"])
def api_onboarding_create_board() -> Response:
    try:
        payload = request.get_json(force=True)
        collection_option_id = string_value(payload.get("collection_option_id"))
        collection_label = string_value(payload.get("collection_label"))
        pasted_rows = string_value(payload.get("pasted_rows"))
        sales_channel_map = payload.get("sales_channel_map") if isinstance(payload.get("sales_channel_map"), dict) else {}
        if not collection_option_id and not collection_label:
            return jsonify({"error": "collection_label is required"}), 400
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        collections = load_collection_options(session)
        collection_option = None
        if collection_option_id:
            collection_option = next((c for c in collections if string_value(c.get("id")) == collection_option_id), None)
        if collection_option is None and collection_label:
            target = collection_label.strip().lower()
            collection_option = next((c for c in collections if string_value(c.get("label")).strip().lower() == target), None)
        if not collection_option and collection_label:
            created_option = ensure_metaproperty_option(session, PRODUCT_COLLECTION_METAPROPERTY_ID, collection_label)
            collections = load_collection_options(session, force_refresh=True)
            collection_option = next((c for c in collections if string_value(c.get("id")) == string_value(created_option.get("id"))), None)
            if not collection_option:
                collection_option = {"id": string_value(created_option.get("id")), "label": string_value(created_option.get("label") or collection_label)}
            log_message(f"Created Product Collection option for Product Imagery Onboarding: {collection_option.get('label')}")
        if not collection_option:
            return jsonify({"error": f'Could not create or map Product Collection value "{collection_label or collection_option_id}" in Bynder.'}), 400
        rows, warnings = parse_onboarding_paste_rows(pasted_rows, sales_channel_map=sales_channel_map)
        created = []
        existing_skus = []
        for row in rows:
            sku = string_value(row.get("sku"))
            existing_assets = [a for a in fetch_assets_for_product_sku(session, "Product_SKU", sku) if is_board_relevant_asset(a, sku)]
            if existing_assets:
                existing_skus.append(sku)
                workflow_fields = []
                for asset in existing_assets:
                    media_id = string_value(asset.get("id"))
                    if not media_id:
                        continue
                    fields = []
                    append_pio_board_fields(session, fields, fetch_metaproperties_map(session), row, string_value(prop(asset, "Product_SKU_Position", "Product_SKU_Position")))
                    # keep slot metadata from asset, but refresh dims/workflow/sync
                    if fields:
                        post_media_fields(session, media_id, fields)
                continue
            media_id = create_pio_placeholder_grid_asset(session, collection_option, row)
            created.append({"sku": row.get("sku"), "media_id": media_id, "seed_row": row})
        time.sleep(0.75)
        if created:
            def _fetch_created_media(entry: Dict[str, Any]) -> Dict[str, Any]:
                media = fetch_media_by_id(session, string_value(entry.get("media_id")))
                entry["media"] = media
                return entry
            with ThreadPoolExecutor(max_workers=min(MAX_WORKERS, max(1, len(created)))) as executor:
                created = list(executor.map(_fetch_created_media, created))
        invalidate_collection_caches(string_value(collection_option.get("id")))
        board = build_onboarding_board_for_collection(session, collection_option, force_refresh=True)
        STATE["board"] = board
        STATE["baseline_board"] = deepcopy(board)
        STATE["last_load"] = datetime.now().isoformat()
        STATE["workspace"] = WORKSPACE_PIO
        log_message(f"Created Product Imagery Onboarding board for {collection_option['label']}: {len(created)} placeholder grids. Existing Product Site Assets were loaded for any matching SKUs already in Bynder.")
        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
            "warnings": warnings,
            "workspace": WORKSPACE_PIO,
            "collection_option_id": string_value(collection_option.get("id")),
        })
    except Exception as exc:
        log_message(f"Onboarding board creation failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/onboarding/load_board", methods=["POST"])
def api_onboarding_load_board() -> Response:
    try:
        payload = request.get_json(force=True)
        collection_option_id = string_value(payload.get("collection_option_id"))
        collection_label = string_value(payload.get("collection_label"))
        force_refresh = bool(payload.get("force_refresh"))
        if not collection_option_id and not collection_label:
            return jsonify({"error": "collection_label or collection_option_id is required"}), 400
        if not collection_label:
            collection_label = collection_option_id
        collection_option = {"id": collection_option_id or collection_label, "label": collection_label}
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        board = build_onboarding_board_for_collection(session, collection_option, force_refresh=force_refresh)
        if not board.get("color_sections"):
            for _ in range(4):
                time.sleep(2.0)
                board = build_onboarding_board_for_collection(session, collection_option, force_refresh=True)
                if board.get("color_sections"):
                    break
        STATE["board"] = board
        STATE["baseline_board"] = deepcopy(board)
        STATE["last_load"] = datetime.now().isoformat()
        STATE["workspace"] = WORKSPACE_PIO
        recent_warning = ""
        latest_edit = parse_datetime(board.get("latest_edit"))
        if latest_edit:
            now_dt = datetime.now(latest_edit.tzinfo) if latest_edit.tzinfo else datetime.now()
            if (now_dt - latest_edit).total_seconds() < 15 * 60:
                recent_warning = "Someone may have edited this board recently."
        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
            "workspace": WORKSPACE_PIO,
            "recent_warning": recent_warning,
        })
    except Exception as exc:
        log_message(f"Onboarding board load failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/onboarding/update_workflow_state", methods=["POST"])
def api_onboarding_update_workflow_state() -> Response:
    try:
        board = STATE.get("board")
        if board is None:
            return jsonify({"error": "No board is loaded."}), 400
        payload = request.get_json(force=True)
        workflow_status = string_value(payload.get("workflow_status"))
        sync_to_site = string_value(payload.get("sync_to_site"))
        if not workflow_status or not sync_to_site:
            return jsonify({"error": "workflow_status and sync_to_site are required."}), 400
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        metaprops = fetch_metaproperties_map(session)
        status_mp = metaprops.get("Workflow_Status")
        sync_mp = metaprops.get("Sync_to_Site")
        workflow_mp = metaprops.get("Workflow")
        if not status_mp or not sync_mp or not workflow_mp:
            return jsonify({"error": "Could not resolve workflow metaproperties."}), 500
        status_value = get_metaproperty_option_value(session, string_value(status_mp.get("id")), workflow_status)
        sync_value = get_metaproperty_option_value(session, string_value(sync_mp.get("id")), sync_to_site)
        workflow_value = get_metaproperty_option_value(session, string_value(workflow_mp.get("id")), PIO_WORKFLOW_VALUE)
        if not status_value or not sync_value or not workflow_value:
            return jsonify({"error": "Could not resolve workflow option values."}), 500
        updated_media_ids = set()
        for section in board.get("color_sections", []):
            for row in section.get("rows", []):
                if compact_text(row.get("workflow")) != compact_text(PIO_WORKFLOW_VALUE):
                    continue
                row["workflow_status"] = workflow_status
                row["sync_to_site"] = sync_to_site
                for asset in row.get("assets", []):
                    media_id = string_value(asset.get("id"))
                    if not media_id or media_id.startswith("empty::") or media_id in updated_media_ids:
                        continue
                    fields=[(f"metaproperty.{string_value(status_mp.get('id'))}", status_value),(f"metaproperty.{string_value(sync_mp.get('id'))}", sync_value)]
                    post_media_fields(session, media_id, fields)
                    updated_media_ids.add(media_id)
        board["workflow_statuses"] = [workflow_status]
        board["sync_states"] = [sync_to_site]
        STATE["board"] = board
        STATE["baseline_board"] = deepcopy(board)
        return jsonify({"board": board, "summary": compute_change_summary(board)})
    except Exception as exc:
        log_message(f"Onboarding workflow state update failed: {exc}")
        return jsonify({"error": str(exc)}), 500


@app.route("/api/onboarding/go_live", methods=["POST"])
def api_onboarding_go_live() -> Response:
    try:
        if STATE.get("board") is None:
            return jsonify({"error": "No board is loaded."}), 400
        board = STATE["board"]
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        metaprops = fetch_metaproperties_map(session)
        sync_mp = metaprops.get("Sync_to_Site")
        status_mp = metaprops.get("Workflow_Status")
        if not sync_mp or not status_mp:
            return jsonify({"error": "Required metaproperties for go live were not found."}), 500
        sync_mp_id = string_value(sync_mp.get("id"))
        status_mp_id = string_value(status_mp.get("id"))
        sync_value = get_metaproperty_option_value(session, sync_mp_id, PIO_SYNC_DO)
        status_value = get_metaproperty_option_value(session, status_mp_id, PIO_STATUS_LIVE)
        changed_ids = []
        seen = set()
        for section in board.get("color_sections", []):
            for row in section.get("rows", []):
                for asset in row.get("assets", []):
                    media_id = string_value(asset.get("copy_source_media_id") or asset.get("id"))
                    if not media_id or media_id in seen:
                        continue
                    seen.add(media_id)
                    post_media_fields(session, media_id, [
                        (f"metaproperty.{sync_mp_id}", sync_value),
                        (f"metaproperty.{status_mp_id}", status_value),
                    ])
                    changed_ids.append(media_id)
        collection_option = board.get("collection") or {}
        option_id = string_value(collection_option.get("id"))
        invalidate_collection_caches(option_id)
        refreshed = build_onboarding_board_for_collection(session, collection_option, force_refresh=True)
        STATE["board"] = refreshed
        STATE["baseline_board"] = deepcopy(refreshed)
        return jsonify({"board": refreshed, "summary": compute_change_summary(refreshed), "updated_count": len(changed_ids)})
    except Exception as exc:
        log_message(f"Onboarding go-live failed: {exc}")
        return jsonify({"error": str(exc)}), 500

# ============================================================
# HTML / CSS / JS
# ============================================================
INDEX_HTML = r'''
<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>Content Refresher</title>
<link rel="icon" type="image/svg+xml" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'%3E%3Cpath fill='%234f245e' d='M32 54s-4.7-3.9-9.9-8.4C13.6 38.3 6 31.8 6 21.8 6 13.9 12.3 8 20.1 8c4.9 0 9 2.3 11.9 6.2C34.9 10.3 39 8 43.9 8 51.7 8 58 13.9 58 21.8c0 10-7.6 16.5-16.1 23.8C36.7 50.1 32 54 32 54z'/%3E%3C/svg%3E" />
<link rel="icon" type="image/svg+xml" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'%3E%3Cpath fill='%238a5bb0' d='M32 55s-3.8-2.8-7.6-6.1C13.8 39.7 6 32.9 6 22.4 6 14.5 12.1 9 19.4 9c5 0 9.2 2.5 12.6 7 3.4-4.5 7.6-7 12.6-7C51.9 9 58 14.5 58 22.4c0 10.5-7.8 17.3-18.4 26.5C35.8 52.2 32 55 32 55z'/%3E%3C/svg%3E" />
<style>
  :root {
    --rf-ink: #1f2937;
    --rf-navy: #4f245e;
    --rf-blue: #8a5bb0;
    --rf-blue-soft: #efe5f6;
    --rf-sand: #f7f1fa;
    --rf-card: #ffffff;
    --rf-border: #dbc9e7;
    --rf-green: #2e7d32;
    --rf-green-soft: #eaf7ee;
    --rf-red: #a93d36;
    --rf-red-soft: #fdeceb;
    --rf-gold: #b38600;
    --rf-gold-soft: #fff8db;
    --rf-shadow: 0 8px 24px rgba(20, 34, 56, 0.08);
    --rf-radius: 16px;
    --rf-radius-sm: 10px;
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    font-family: Inter, Segoe UI, Arial, sans-serif;
    color: var(--rf-ink);
    background: linear-gradient(180deg, #faf7fe 0%, #f2ecfb 100%);
  }
  .shell {
    display: grid;
    grid-template-columns: 280px minmax(0, 1fr) 300px;
    gap: 12px;
    padding: 12px;
    align-items: start;
  }
  .brand-panel, .launcher, .side, .board-wrap {
    min-width: 0;
  }
  .panel.brand-panel {
    background: linear-gradient(90deg, var(--rf-navy), var(--rf-blue));
    color: white;
    padding: 14px 16px;
  }
  .brand-panel h1 {
    margin: 0 0 8px 0;
    font-size: 18px;
    letter-spacing: .2px;
  }
  .brand-panel .sub {
    opacity: .95;
    font-size: 12px;
    line-height: 1.25;
    max-width: 170px;
  }
.workspace-switch-row { display:flex; align-items:center; justify-content:space-between; gap:10px; }
  .workspace-select { width:auto; min-width: 170px; padding:6px 10px; border-radius:10px; border:1px solid rgba(255,255,255,.35); background: rgba(255,255,255,.16); color:#fff; }
  .workspace-select option { color:#1f2937; }
  .workspace-menu-btn { width:34px; height:34px; border-radius:10px; border:1px solid rgba(255,255,255,.35); background:rgba(255,255,255,.16); color:#fff; font-size:18px; line-height:1; cursor:pointer; }
  .workspace-menu { position:absolute; top:40px; right:0; background:#fff; border:1px solid var(--rf-border); border-radius:12px; padding:6px; min-width:220px; box-shadow:0 10px 24px rgba(29,19,48,.16); z-index:40; color:var(--rf-purple); }
  .workspace-menu-item { width:100%; text-align:left; padding:10px 12px; border:0; background:transparent; border-radius:10px; color:var(--rf-purple) !important; font-weight:700; cursor:pointer; opacity:1 !important; text-shadow:none !important; }
  .workspace-menu-item:hover { background:#f4edf9; color:var(--rf-purple) !important; }
  .workspace-menu-item.active { background:#f4edf9; color:var(--rf-purple) !important; }
  .pio-modal-overlay { position:fixed; inset:0; background:rgba(21,11,34,.38); display:flex; align-items:center; justify-content:center; z-index:2600; padding:20px; }
  .pio-modal-card { width:min(760px, 100%); background:#fff; border:1px solid var(--rf-border); border-radius:18px; box-shadow:0 18px 48px rgba(28,16,45,.24); padding:18px; display:grid; gap:14px; }
  .pio-modal-title { font-size:22px; font-weight:900; color:var(--rf-purple); }
  .pio-map-table { display:grid; grid-template-columns:minmax(180px, 1fr) minmax(220px, 1fr); gap:8px 12px; align-items:center; }
  .pio-map-head { font-size:12px; font-weight:900; color:var(--rf-purple); text-transform:uppercase; letter-spacing:.03em; }
  .pio-map-cell { font-size:14px; color:var(--rf-text); }
  .pio-map-cell select { width:100%; }
  .pio-modal-actions { display:flex; justify-content:flex-end; gap:10px; }
  .pio-meta-grid { display:grid; grid-template-columns: repeat(2, minmax(140px, 1fr)); gap:8px; margin-top:8px; }
  .component-tree { position:relative; margin-top:8px; }
  .component-tree summary { cursor:pointer; font-weight:700; font-size:12px; color:var(--rf-navy); display:flex; align-items:center; justify-content:space-between; gap:8px; padding:4px 8px; border:1px solid var(--rf-border); border-radius:10px; background:#faf7ff; list-style:none; user-select:none; }
  .component-tree summary::-webkit-details-marker { display:none; }
  .component-tree .summary-caret { font-size:11px; color:#6c5b84; }
  .component-tree[open] .summary-caret { transform:rotate(180deg); }
  
  .photo-prep-details { border:1px solid var(--rf-border); border-radius:12px; background:#fff; padding:0; }
  .photo-prep-details > summary { cursor:pointer; list-style:none; padding:8px 10px; font-weight:700; color:var(--rf-purple); }
  .photo-prep-details > summary::-webkit-details-marker { display:none; }
  .photo-prep-details[open] > summary { border-bottom:1px solid var(--rf-border); }
  .photo-prep-details .photo-prep-options, .photo-prep-details .photo-prep-focusbox { margin:10px; }
  .meta-measure-boxes { display:flex; gap:4px; flex-wrap:nowrap; align-items:center; justify-content:space-between; }
  .measure-chip { flex:1 1 0; min-width:0; text-align:center; border:1px solid var(--rf-border); border-radius:8px; padding:4px 4px; font-size:10.5px; font-weight:700; background:#fff; white-space:nowrap; }
  .component-flyout { position:absolute; top:0; left:calc(100% + 10px); min-width:340px; max-width:520px; z-index:14; border:1px solid var(--rf-border); border-radius:14px; background:#fff; box-shadow:0 12px 28px rgba(29,19,48,.16); padding:10px; }
  .component-chip-row { display:flex; flex-wrap:wrap; gap:8px; margin-top:8px; }
  .component-chip { border:1px solid var(--rf-border); border-radius:999px; background:#fff; padding:4px 8px; font-size:12px; }
  .component-visual-grid { display:grid; grid-template-columns: repeat(auto-fit, minmax(100px, 1fr)); gap:10px; margin-top:0; }
  .component-visual-card { border:1px solid var(--rf-border); border-radius:12px; background:#fff; padding:8px; font-size:12px; }
  .component-visual-card img { width:100%; height:86px; object-fit:contain; background:#f5f7fa; border-radius:8px; display:block; }
  .component-warning-list { margin-top:8px; display:grid; gap:6px; }
  .component-warning-chip { font-size:12px; color:var(--rf-red); background:var(--rf-red-soft); border:1px solid #f0b8b3; border-radius:999px; padding:4px 8px; display:inline-flex; }
  .collection-status-select { width:100%; min-width:220px; height:42px; border:1px solid #c6d8cf; border-radius:14px; background:#d8e4dd; color:#2f6b41; font-size:13px; line-height:1.25; font-weight:700; padding:10px 40px 10px 12px; box-shadow: inset 0 1px 0 rgba(255,255,255,.45); }
  .collection-status-select.pio-header-select { min-width:300px; width:300px; }
  .collection-status-select option { color:#203229; background:#fff; }
  .btn-preflight { background:#2f9e44; color:#fff; border:1px solid #25863a; box-shadow: 0 8px 18px rgba(47,158,68,.18); }
  .btn-preflight:hover { filter: brightness(1.02); }

  .pio-top-actions { display:flex; align-items:center; gap:8px; flex-wrap:nowrap; min-width:0; }
  .pio-top-actions .collection-status-mount { width:auto; flex:0 0 auto; min-width:300px; }
  .pio-top-actions .btn-preflight { flex:0 0 auto; white-space:nowrap; }
  .pio-header-select-compact { min-width: 300px; width: 300px; max-width: min(52vw, 300px); }
  .sku-inline-actions { display:flex; align-items:center; gap:6px; flex-wrap:wrap; margin-top:4px; }
  .sku-inline-top { display:flex; align-items:center; justify-content:space-between; gap:8px; }
  .sku-inline-top .sku-text { font-weight:700; }
  .sku-inline-top .photo-mini-btn { padding:3px 8px; min-height:24px; line-height:1.1; }
  .photo-pio-row.filters { display:flex; align-items:center; gap:8px; flex-wrap:nowrap; }
  .photo-pio-row.filters select { min-width: 150px; max-width: 180px; }
  .photo-tag-cloud { display:flex; flex-wrap:wrap; gap:6px; margin-top:8px; }
  .photo-tag-chip { border:1px solid var(--rf-border); border-radius:999px; background:#fff; padding:3px 7px; font-size:11px; color:var(--rf-text); }

  .panel {
    background: var(--rf-card);
    border: 1px solid var(--rf-border);
    border-radius: var(--rf-radius);
    box-shadow: var(--rf-shadow);
  }
  .top-shell {
    display: grid;
    grid-template-columns: 280px minmax(455px, 1fr) 255px minmax(215px, 0.7fr) 205px;
    gap: 12px;
    grid-column: 1 / -1;
    position: sticky;
    top: 0;
    z-index: 40;
    background: linear-gradient(180deg, #faf7fe 0%, #f2ecfb 100%);
    padding-top: 0;
  }
  .side .panel { max-height: calc(100vh - 20px); overflow: auto; }
  .color-body.collapsed { display: none; }
  .color-body { overflow-x: auto; }
   .color-toggle {
    white-space: nowrap;
 border: 0; background: transparent; color: var(--rf-navy); font-weight: 800; cursor: pointer; }
  .top-notices { display: grid; gap: 8px; margin-bottom: 6px; min-width: 0; }
  .missing-notice { padding: 10px 12px; border-radius: 12px; background: #fff6db; border: 1px solid #ead48b; color: #6d5500; font-size: 13px; cursor: pointer; text-align: left; width: 100%; }
  .missing-notice strong { color: #523d00; }

  .mode-panel { padding: 8px 10px; transition: background .18s ease, border-color .18s ease, box-shadow .18s ease; }
  .mode-panel.assets-mode { background: linear-gradient(180deg, #eef5ff, #e3efff); border-color:#b8cff7; box-shadow: 0 8px 20px rgba(34, 99, 214, .10); }
  .mode-panel .panel-title { font-size: 12px; font-weight: 800; letter-spacing: .04em; color: var(--rf-navy); text-transform: uppercase; margin: 0 0 6px 0; }
  .mode-help { font-size: 12px; color: #6d5a77; line-height: 1.18; margin-bottom: 6px; }
  .mode-options { display: grid; gap: 6px; }
  .mode-option { display: flex; align-items: center; gap: 8px; font-weight: 700; color: var(--rf-navy); cursor: pointer; }
  .mode-option input { accent-color: var(--rf-purple); }
  .mode-banner { display:none; }
  .notifications-panel { padding: 12px; min-width: 0; }
  .notifications-header { display:flex; align-items:center; justify-content:space-between; gap:10px; margin:0 0 8px 0; }
  .notifications-panel .panel-title { font-size: 12px; font-weight: 800; letter-spacing: .04em; color: var(--rf-navy); text-transform: uppercase; margin: 0; }
  .notifications-clear-btn { width:28px; height:28px; padding:0; border-radius:999px; display:inline-flex; align-items:center; justify-content:center; font-size:14px; line-height:1; }
  .notifications-clear-btn[disabled] { opacity:.45; cursor:not-allowed; }
  .notifications-panel .top-notices { margin: 0; }
  .notifications-empty { padding: 10px 12px; border-radius: 12px; background: #faf7ff; border: 1px dashed var(--rf-border); color: #6d5a77; font-size: 13px; overflow-wrap:anywhere; }

  .always-sticky {
    position: sticky;
    top: 0;
    z-index: 34;
    background: white;
    box-shadow: 0 2px 8px rgba(79,36,94,.08);
  }
  .sticky-board-tools {
    position: sticky;
    top: 0;
    z-index: 28;
    background: white;
    border-top: 1px solid rgba(79,36,94,.10);
    box-shadow: 0 2px 8px rgba(79,36,94,.06);
  }
  .meta-cell.status-inactive { background: #fff4cf; border-color: #e5ba3c; }
  .sku-row.inactive { background: #fcfcfc; }
  .sku-row.inactive .meta-grid, .sku-row.inactive .lane-title, .sku-row.inactive .slot-label { opacity: .78; }
  .sku-row.inactive .asset-card, .sku-row.inactive .asset-card *, .sku-row.inactive img { opacity: 1 !important; }
  .top-slot-layout { grid-template-columns: auto auto minmax(180px, 1fr); }

   .launcher {
    padding: 12px 14px;
    display: grid;
    gap: 12px;
  }
  .rowline {
    display: flex;
    gap: 10px;
    flex-wrap: wrap;
    align-items: center;
  }
  label.small {
    display: block;
    font-size: 12px;
    font-weight: 700;
    color: var(--rf-navy);
    margin-bottom: 6px;
  }
  input[type="text"], select, .btn, input[type="range"] {
    font: inherit;
  }
  input[type="text"], select {
    width: 100%;
    border: 1px solid var(--rf-border);
    border-radius: 12px;
    padding: 11px 12px;
    background: white;
  }
  .select-wrap {
    display: block;
  }
  .btn {
    border: 0;
    border-radius: 12px;
    padding: 9px 14px;
    cursor: pointer;
    font-weight: 700;
  }
  .btn-primary {
    background: linear-gradient(90deg, var(--rf-navy), var(--rf-blue));
    color: white;
  }
  .btn-secondary {
    background: var(--rf-blue-soft);
    color: var(--rf-navy);
  }
  .btn-disabled-mode { opacity:.52; filter: grayscale(.25); cursor:not-allowed; }
  .btn-commit {
    background: linear-gradient(90deg, #0f7b4c, #3aa66a);
    color: white;
  }
  .btn-reload-flashing {
    animation: reloadPulse 1.05s ease-in-out infinite;
    box-shadow: 0 0 0 0 rgba(79,36,94,.35);
  }
  @keyframes reloadPulse {
    0% { box-shadow: 0 0 0 0 rgba(79,36,94,.36); }
    70% { box-shadow: 0 0 0 10px rgba(79,36,94,0); }
    100% { box-shadow: 0 0 0 0 rgba(79,36,94,0); }
  }
  .wait-overlay {
    position: fixed;
    inset: 0;
    background: rgba(28, 22, 31, .42);
    display: none;
    align-items: center;
    justify-content: center;
    z-index: 9999;
    backdrop-filter: blur(2px);
  }
  .wait-overlay.open { display: flex; }
  .wait-card {
    width: min(480px, 92vw);
    background: white;
    border: 1px solid var(--rf-border);
    border-radius: 18px;
    box-shadow: 0 20px 48px rgba(0,0,0,.22);
    padding: 18px 18px 16px;
  }
  .wait-card h3 {
    margin: 0 0 8px;
    font-size: 18px;
    color: var(--rf-navy);
  }
  .wait-card p {
    margin: 0 0 10px;
    color: #6d5a77;
    line-height: 1.35;
    font-size: 14px;
  }
  .wait-status {
    margin-top: 10px;
    padding: 10px 12px;
    background: #faf7fe;
    border: 1px solid #e3d4f7;
    border-radius: 12px;
    color: var(--rf-navy);
    font-size: 13px;
  }
  .idle-overlay {
    position: fixed;
    inset: 0;
    background: rgba(28, 22, 31, .44);
    display: none;
    align-items: center;
    justify-content: center;
    z-index: 10010;
    backdrop-filter: blur(2px);
  }
  .idle-overlay.open { display: flex; }
  .idle-card {
    width: min(560px, 92vw);
    background: white;
    border: 1px solid var(--rf-border);
    border-radius: 18px;
    box-shadow: 0 20px 48px rgba(0,0,0,.24);
    padding: 20px 20px 18px;
  }
  .idle-card h3 {
    margin: 0 0 8px;
    font-size: 20px;
    color: var(--rf-navy);
  }
  .idle-card p {
    margin: 0 0 10px;
    color: #6d5a77;
    line-height: 1.45;
    font-size: 14px;
  }
  .idle-actions {
    display: flex;
    justify-content: flex-end;
    gap: 10px;
    margin-top: 14px;
    flex-wrap: wrap;
  }
  .statusbar {
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: 12px;
    padding: 12px 18px;
    border-top: 1px solid var(--rf-border);
    background: var(--rf-sand);
    border-bottom-left-radius: var(--rf-radius);
    border-bottom-right-radius: var(--rf-radius);
  }
  .board-wrap {
    display: none;
    gap: 18px;
    grid-column: 1 / -1;
    align-items: start;
    grid-template-columns: var(--photo-panel-width, 0px) minmax(0, 1fr);
  }
  .board-main {
    max-height: calc(100vh - var(--top-shell-height, 74px) - 10px);
    overflow: auto;
    min-width: 0;
  }

  .upload-target-pending {
    box-shadow: inset 0 0 0 3px #2d8f52, 0 0 0 2px rgba(45,143,82,.18) !important;
    background: linear-gradient(180deg, rgba(45,143,82,.08), rgba(45,143,82,.02)) !important;
  }
  .board-wrap, .board-main, #boardHost { width: 100%; min-width: 0; }
  .photo-empty.filter-none-strong { border:2px dashed #b98cd9; background:#fbf7fe; color:#5a2d86; font-weight:700; }

  .photo-shell {
    position: relative;
    max-height: calc(100vh - var(--top-shell-height, 74px) - 10px);
    overflow: hidden;
    display: flex;
    flex-direction: column;
    border-color: #cfe5d4;
    background: linear-gradient(180deg, #f7fbf7 0%, #f2f6f2 100%);
    min-width: 0;
  }
  .photo-shell.collapsed {
    width: 64px !important;
    min-width: 64px !important;
  }
  .photo-shell.collapsed .photo-header {
    flex-direction: column;
    align-items: center;
    justify-content: flex-start;
    gap: 10px;
    padding: 12px 6px;
    min-height: 210px;
    background: linear-gradient(180deg, #ecf8ef 0%, #f7fbf7 100%);
  }
  .photo-shell.collapsed .photo-sub { display:none; }
  .photo-shell.collapsed .photo-header-actions { flex-direction: column; width: 100%; align-items:center; }
  .photo-shell.collapsed .photo-toolbar,
  .photo-shell.collapsed .photo-body,
  .photo-shell.collapsed #photoClearBtn,
  .photo-shell.collapsed .photo-resize-handle { display:none; }
  .photo-shell.collapsed .panel-title {
    writing-mode: vertical-rl;
    transform: rotate(180deg);
    letter-spacing: .08em;
    color: #2f6b41;
    font-size: 13px;
  }
  .photo-resize-handle {
    position: absolute; top: 0; right: 0; width: 8px; height: 100%;
    cursor: col-resize; background: linear-gradient(180deg, rgba(84,130,92,.12), rgba(84,130,92,.02));
  }
  .photo-header { display:flex; justify-content:space-between; gap:10px; align-items:flex-start; padding: 12px 14px 10px; border-bottom:1px solid #d8e7da; background: linear-gradient(180deg, #eef7ef, #f7fbf7); }
  .photo-sub { font-size: 12px; color: #55705a; line-height: 1.35; max-width: 250px; }
  .photo-header-actions { display:flex; gap:8px; flex-wrap:wrap; align-items:center; }
  .photo-mini-btn { padding: 8px 10px; }
  .photo-review-btn { padding: 5px 7px; font-size: 10px; line-height: 1.04; border-radius: 9px; }
  .photo-prep-actions .photo-mini-btn { padding: 6px 8px; font-size: 11px; line-height: 1.08; border-radius: 10px; }
  .photo-pull-btn { padding: 6px 8px; font-size: 12px; line-height: 1.15; }
  .photo-pull-btn-checking { animation: photoPullCheckingPulse 1.2s ease-in-out infinite; }
  .photo-toolbar { padding: 10px 14px; border-bottom:1px solid #d8e7da; background:#f7fbf7; display:flex; justify-content:space-between; align-items:center; gap:10px; flex-wrap:wrap; }
  .photo-body { flex:1; overflow:auto; padding: 12px; }
  .photo-prep-drawer { position: sticky; top: 0; z-index: 30; isolation:isolate; border:1px solid #cddfd0; background: linear-gradient(180deg,#f8fcf8,#eef7ef); border-radius:16px; padding:8px; margin-bottom:10px; box-shadow:0 8px 18px rgba(65,98,71,.08); }
  .photo-prep-drawer h4 { margin:0 0 4px; font-size:14px; color:#2f5134; }

  .set-dim-drawer {
    background:linear-gradient(180deg,#f4f8f1 0%,#eef6ea 100%);
    border:1px solid #d7e6cf;
    border-radius:16px;
    padding:10px;
    margin:10px 0 0;
    position:relative;
    z-index:3;
  }
  .set-dim-drawer h4 { margin:0 0 4px; font-size:14px; color:#27498f; }
  .set-dim-drawer .set-dim-preview-wrap { margin-top:10px; border-radius:14px; padding:10px; background:#fff; border:1px solid #d7e3fb; }
  .set-dim-drawer img { width:100%; height:auto; display:block; border-radius:10px; }
  .set-dim-grid { display:grid; grid-template-columns:repeat(auto-fit,minmax(175px,1fr)); gap:10px; margin-top:10px; }
  .set-dim-item { background:#fff !important; border:1px solid #d7e3fb; border-radius:12px; padding:8px; font-size:12px; opacity:1; filter:none; }
  .set-dim-item.dragging { opacity:.55; }
  .set-dim-slot-title { display:block; font-weight:700; color:#3559a8; margin-bottom:6px; }
  .set-dim-slot-thumb { height:78px; border:1px solid #d7e3fb; border-radius:10px; background:#ffffff !important; display:flex; align-items:center; justify-content:center; overflow:hidden; margin-bottom:8px; box-shadow:none; }
  .set-dim-slot-thumb img { width:auto; height:auto; max-width:100%; max-height:100%; border-radius:0; background:#ffffff !important; opacity:1; filter:none; mix-blend-mode:normal; }
  .set-dim-item select { width:100%; border:1px solid #c9d7f3; border-radius:8px; padding:6px 8px; font:inherit; background:#fff; }
  .set-dim-control-label { font-size:11px; font-weight:700; text-transform:uppercase; letter-spacing:.03em; color:#5f76aa; margin-bottom:4px; }
  .set-dim-scale-row { display:grid; grid-template-columns:auto minmax(0,1fr) auto auto; gap:6px; align-items:center; }
  .set-dim-scale-row input[type=range] { width:100%; }
  .set-dim-scale-value { min-width:44px; text-align:right; font-weight:700; color:#3559a8; }
  .set-dim-rerender-row { display:flex; justify-content:flex-end; margin-top:10px; }
  .set-dim-rerender-btn { min-width:160px; }
  .empty-slot-actions { margin-top:6px; display:flex; justify-content:flex-start; }
  .photo-prep-top { display:flex; justify-content:space-between; align-items:center; gap:12px; }
  .photo-prep-sub { font-size:12px; color:#55705a; line-height:1.35; }
  .photo-prep-controls { display:grid; gap:8px; margin-top:6px; }
  .photo-prep-row { display:flex; flex-wrap:wrap; gap:10px; align-items:center; }
  .photo-prep-row label { font-size:12px; color:#415346; display:flex; align-items:center; gap:6px; }
  .photo-prep-preview-wrap { display:grid; grid-template-columns:minmax(0,1fr); gap:8px; align-items:start; }
  .photo-prep-preview-meta { display:grid; gap:6px; }
  .photo-prep-status { display:flex; align-items:flex-start; gap:8px; border-radius:12px; padding:8px 10px; border:1px solid #cfe1d4; background:#f7fcf8; color:#315037; }
  .photo-prep-status.warn { background:#fff5f2; border-color:#f0c5b8; color:#8a4630; }
  .photo-prep-status.notice { background:#f7f4ff; border-color:#ddd0ef; color:#5a4684; }
  .photo-prep-status-icon { width:24px; height:24px; border-radius:999px; display:grid; place-items:center; flex:0 0 auto; font-size:14px; font-weight:900; background:rgba(49,80,55,.1); }
  .photo-prep-status.warn .photo-prep-status-icon { background:rgba(138,70,48,.12); }
  .photo-prep-status.notice .photo-prep-status-icon { background:rgba(90,70,132,.12); }
  .photo-prep-status-title { font-size:12px; font-weight:900; line-height:1.2; }
  .photo-prep-status-detail { font-size:11px; line-height:1.35; margin-top:2px; }
  .photo-prep-preview { border:1px solid #d7e6da; background:white; border-radius:14px; min-height:145px; display:flex; align-items:center; justify-content:center; overflow:hidden; position:relative; }
  .photo-prep-preview.warn { border-color:#efc2b4; box-shadow: inset 0 0 0 2px rgba(232,128,91,.12); }
  .photo-prep-preview.notice { border-color:#ddd0ef; }
  .photo-prep-preview-badge { position:absolute; top:10px; left:10px; z-index:2; display:inline-flex; align-items:center; gap:6px; padding:7px 10px; border-radius:999px; background:rgba(49,80,55,.94); color:#fff; font-size:11px; font-weight:900; letter-spacing:.01em; box-shadow:0 8px 18px rgba(49,80,55,.18); }
  .photo-prep-preview.warn .photo-prep-preview-badge { background:rgba(168,78,42,.96); }
  .photo-prep-preview.notice .photo-prep-preview-badge { background:rgba(90,70,132,.96); }
  .photo-prep-preview-canvas { width:100%; display:flex; align-items:center; justify-content:center; padding:12px; border:2px solid rgba(96,74,143,.72); border-radius:12px; background:linear-gradient(180deg,#ffffff,#fbf9ff); box-shadow:0 0 0 2px rgba(96,74,143,.14), inset 0 0 0 1px rgba(96,74,143,.12); position:relative; }
  .photo-prep-preview-canvas::after { content:''; position:absolute; inset:6px; border:1px dashed rgba(96,74,143,.34); border-radius:8px; pointer-events:none; }
  .photo-prep-preview img { width:100%; height:auto; display:block; max-height:220px; object-fit:contain; border:3px solid rgba(96,74,143,.88); border-radius:10px; background:#fff; box-shadow:0 0 0 1px rgba(96,74,143,.18); position:relative; z-index:1; }
  .bulk-fix-pill { display:inline-flex; align-items:center; justify-content:center; padding:2px 9px; border-radius:999px; background:#e7f6ea; color:#1f7a34; font-size:11px; font-weight:800; line-height:1.1; text-decoration:none; border:1px solid #b9e2c1; cursor:pointer; }
  .bulk-fix-pill.is-active { background:#d9eefc; border-color:#8cc2ee; color:#1e5f9d; }
  .photo-prep-details > summary { list-style:none; display:flex; align-items:center; justify-content:space-between; gap:10px; cursor:pointer; }
  .photo-prep-details > summary::-webkit-details-marker { display:none; }
  .photo-prep-summary-caret { font-size:14px; line-height:1; color:#6f5888; transition:transform .18s ease; }
  .photo-prep-details[open] .photo-prep-summary-caret { transform:rotate(180deg); }
  .asset-card.bulk-fix-target { box-shadow:0 0 0 3px rgba(69,132,255,.92), 0 0 0 6px rgba(69,132,255,.18); border-color:rgba(69,132,255,.92); }
  .photo-prep-preview-drag { width:100%; display:flex; align-items:center; justify-content:center; cursor:grab; }
  .photo-prep-preview-drag.dragging { cursor:grabbing; opacity:.96; }
  .photo-prep-filmstrip { display:none; }
  .photo-prep-film-btn { display:flex; gap:8px; align-items:center; border:1px solid #d6e5d9; background:white; border-radius:12px; padding:6px; cursor:pointer; }
  .photo-prep-film-btn.active { border-color:#5ea870; box-shadow:0 0 0 2px rgba(94,168,112,.18); }
  .photo-prep-film-btn img { width:42px; height:42px; object-fit:contain; background:#f4f7f4; border-radius:8px; }
  .photo-prep-actions { display:flex; gap:8px; flex-wrap:wrap; justify-content:flex-end; align-items:center; }
  .photo-prep-toolbar { display:grid; grid-template-columns:minmax(0,1fr); gap:8px; align-items:start; }
  .photo-prep-left { display:grid; gap:6px; }
  .photo-prep-focusbox { display:flex; flex-wrap:wrap; gap:10px; align-items:center; border:1px solid #d7e6da; background:#fff; border-radius:12px; padding:8px 10px; max-width:560px; }
  .photo-focus-pad { display:flex; flex-wrap:nowrap; gap:6px; align-items:center; justify-content:flex-start; }
  .photo-focus-pad-stack { display:grid; gap:8px; }
  .photo-focus-row { display:flex; gap:6px; align-items:center; justify-content:flex-start; }
  .photo-focus-pad button { width:34px; height:34px; border-radius:10px; border:1px solid #cddfd0; background:linear-gradient(180deg,#ffffff 0%, #f2faf3 100%); color:#315037; cursor:pointer; line-height:1; display:grid; place-items:center; box-shadow:0 4px 10px rgba(49,80,55,.08); transition:transform .12s ease, box-shadow .12s ease, border-color .12s ease; }
  .photo-focus-pad button:hover { transform:translateY(-1px); box-shadow:0 6px 12px rgba(49,80,55,.12); border-color:#b6d0bb; }
  .photo-focus-pad button:active { transform:translateY(0); }
  .photo-focus-pad svg { width:18px; height:18px; stroke:currentColor; fill:none; stroke-width:1.85; stroke-linecap:round; stroke-linejoin:round; }
  .photo-focus-pad button.jump { background:linear-gradient(180deg,#f4fbf5 0%, #e8f5ea 100%); }
  .photo-focus-pad .blank { display:none; }
  .photo-focus-meta { display:grid; gap:4px; font-size:12px; color:#4f6355; }
  .photo-focus-chip { display:inline-flex; align-items:center; gap:6px; padding:4px 8px; border-radius:999px; background:#eef6ef; border:1px solid #d7e6da; font-size:12px; color:#35543b; }
  .photo-prep-active { display:none; }
  .photo-prep-options { display:grid; grid-template-columns:repeat(2, minmax(180px, 1fr)); gap:8px 12px; align-items:start; }
  .photo-prep-options label { font-size:11px; color:#415346; display:flex; align-items:flex-start; gap:6px; line-height:1.2; }
  .photo-prep-note { font-size:10.5px; color:#5d7463; line-height:1.25; }
  .photo-shell.collapsed #photoToggleBtn {
    width: 44px;
    height: 44px;
    min-height: 44px;
    padding: 0;
    border-radius: 999px;
    border-color: #86c697;
    background: linear-gradient(180deg, #60b873 0%, #4e9f61 100%);
    color: #fff;
    box-shadow: 0 8px 18px rgba(63, 132, 79, .22);
    font-size: 20px;
    font-weight: 900;
  }
  .photo-shell.collapsed #photoToggleBtn::after {
    content: '>';
    display: block;
    transform: translateX(1px);
  }
  .photo-shell.collapsed #photoToggleBtn { font-size: 0; }
  .photo-select-badge { position:absolute; top:10px; right:10px; width:36px; height:36px; border-radius:999px; border:2px solid rgba(79,36,94,.38); background:rgba(255,255,255,.96); display:none; align-items:center; justify-content:center; color:white; font-weight:700; font-size:18px; box-shadow:0 4px 16px rgba(0,0,0,.14); z-index:5; cursor:pointer; }
  .photo-tile:hover .photo-select-badge, .photo-tile.selected .photo-select-badge { display:flex; }
  .photo-tile.selected { border-color:#5ea870; box-shadow:0 0 0 2px rgba(94,168,112,.18), 0 8px 18px rgba(56,90,61,.12); }
  .photo-tile.selected .photo-select-badge { background:#5ea870; border-color:#5ea870; }
  .photo-image-wrap { position:relative; }
  .photo-empty { border:1px dashed #b8cfbc; background:#fbfefb; border-radius:16px; padding:18px; color:#55705a; font-size:13px; }
  .photo-grid { display:grid; gap:12px; grid-template-columns: repeat(auto-fill, minmax(var(--photo-tile-min, 220px), 1fr)); position:relative; z-index:1; }
  .photo-tile { background:white; border:1px solid #d6e5d9; border-radius:14px; box-shadow: 0 6px 16px rgba(56,90,61,.08); overflow:hidden; display:flex; flex-direction:column; }
  .photo-tile.dragover { border-color: #56a06a; box-shadow: 0 0 0 2px rgba(86,160,106,.18); }
  .photo-tile img { width:100%; height: var(--photo-thumb-height, 170px); object-fit: contain; display:block; background:#f4f7f4; padding: 4px; }
  .photo-meta { padding: 8px 10px; display:grid; gap:4px; }
  .photo-name { font-size:12px; font-weight:700; color: var(--rf-navy); overflow-wrap:anywhere; }
  .photo-name a { color: inherit; text-decoration: underline; text-decoration-color: rgba(30, 64, 175, 0.28); }
  .photo-name a:hover { text-decoration-color: rgba(30, 64, 175, 0.62); }
  .photo-line { font-size:11px; color:#5b6a5e; }
  .photo-line.photo-season { font-weight:700; color:#314f76; }
  .photo-actions { display:flex; gap:8px; flex-wrap:wrap; }
  .photo-actions a { font-size:11px; color: var(--rf-blue); text-decoration:none; }
  .photo-review-row { display:flex; justify-content:flex-start; margin-top:6px; }
  .photo-review-status { font-size:12px; color:#2d6a3f; font-weight:700; }
  .photo-skus { border-top:1px solid #e2ece3; background:#fafdfa; }
  .photo-skus-toggle { width:100%; border:0; background:transparent; padding:8px 10px; cursor:pointer; text-align:left; font-weight:700; color:#3d6b49; }
  .photo-skus-body { display:none; padding:0 10px 10px; }
  .photo-skus-body.open { display:block; }
  .photo-tag, .photo-sku-jump { display:inline-flex; margin:4px 6px 0 0; padding:5px 8px; border-radius:999px; font-size:11px; }
  .photo-tag { background:#eef4ef; color:#56665a; border:1px solid #d9e6db; }
  .photo-sku-jump { border:1px solid #a7c7b1; background:#ecf7ef; color:#2f6b3f; cursor:pointer; }

   .collection-header {
    padding: 10px 14px;
    display: grid;
    grid-template-columns: 1fr auto;
    gap: 12px;
    align-items: center;
    border-bottom: 1px solid #eee6fa;
  }
  .collection-header h2 {
    margin: 0 0 6px 0;
    font-size: 18px;
  }
  .muted { color: #5e6c7a; font-size: 13px; }
  .controls {
    display: flex;
    gap: 10px;
    flex-wrap: wrap;
    align-items: center;
    justify-content: flex-end;
  }
   .color-section {
    margin-top: 12px;
    border: 1px solid #d9c8f0;
    border-radius: 18px;
    overflow: hidden;
    background: linear-gradient(180deg, #fffefe, #fbf8ff);
    box-shadow: var(--rf-shadow);
  }
   .color-header {
    display:flex;
    justify-content:space-between;
    align-items:center;
    gap:12px;

    background: linear-gradient(90deg, #f2ebfd, #faf7ff);
    border-bottom: 1px solid #e1d4f6;
    padding: 10px 14px;
    font-weight: 800;
    color: var(--rf-navy);
    position: relative;
    z-index: 1;
    display: flex;
    justify-content: space-between;
    align-items: center;
    cursor: pointer;
  }
  .sku-row {
    padding: 12px;
    border-top: 1px solid #edf1f5;
  }
  .sku-row.inactive {
    background: #fbfbfb;
  }
  .sku-row.inactive .meta-cell,
  .sku-row.inactive .lane-title,
  .sku-row.inactive .slot-label,
  .sku-row.inactive .slot.dropzone,
  .sku-row.inactive .empty-slot,
  .sku-row.inactive .open-download,
  .sku-row.inactive .date-line,
  .sku-row.inactive .dimension-warning {
    opacity: .82;
  }
  .sku-row.inactive .asset-card,
  .sku-row.inactive .asset-card *,
  .sku-row.inactive .asset-thumb-wrap,
  .sku-row.inactive .asset-thumb,
  .sku-row.inactive img {
    opacity: 1 !important;
    filter: none !important;
  }
  .sku-row.inactive .meta-cell.status-inactive {
    background: #ffe6b5;
    border-color: #d89a1d;
    box-shadow: inset 0 0 0 1px rgba(216,154,29,.18);
    opacity: 1;
  }
   .row-layout {
    display: grid;
    grid-template-columns: 168px minmax(0, 1fr);
    gap: 14px;
    align-items: start;
  }
  .row-layout > div:last-child {
    min-width: 0;
  }
  .meta-grid {
    display: grid;
    grid-template-columns: 1fr;
    gap: 8px;
    margin-bottom: 0;
  }
  .meta-cell {
    background: #f7f9fb;
    border: 1px solid #e1e8f0;
    border-radius: 12px;
    padding: 7px 9px;
    width: 160px;
    min-width: 160px;
    max-width: 160px;
  }
  .meta-cell .k {
    font-size: 11px;
    font-weight: 800;
    color: var(--rf-navy);
    text-transform: uppercase;
    letter-spacing: .4px;
    margin-bottom: 4px;
    white-space: nowrap;
  }
  .meta-cell .v {
    font-size: 13px;
    overflow-wrap: anywhere;
  }
  .top-slot-layout {
    display: grid;
    grid-template-columns: max-content max-content minmax(220px, 1fr);
    gap: 12px;
    align-items: start;
  }
  .slot-row.tight {
    overflow-x: visible;
    flex-wrap: wrap;
  }
  .slot-row.tight.swatch-detail-inline {
    flex-wrap: nowrap;
    overflow-x: auto;
  }
  .lane-block.compact {
    margin-top: 0;
  }
  .lane-block {
    margin-top: 12px;
  }
  .lane-title {
    font-size: 13px;
    font-weight: 800;
    color: var(--rf-navy);
    margin: 0 0 8px 0;
  }
  .slot-row {
    display: flex;
    gap: 8px;
    overflow-x: auto;
    padding-bottom: 8px;
  }
   .slot {
    min-width: var(--slot-width, 130px);
    width: var(--slot-width, 130px);
    background: white;
    border: 1px dashed #c7d2dd;
    border-radius: 14px;
    padding: 6px;
    display: flex;
    flex-direction: column;
    gap: 6px;
    min-height: 134px;
  }
  .slot.special { min-width: calc(var(--slot-width, 116px) + 18px); width: calc(var(--slot-width, 116px) + 18px); }
  .slot.trash {
    background: #fff7f7;
    border-color: #f2b4af;
    min-width: calc(var(--slot-width, 116px) + 48px);
    width: calc(var(--slot-width, 116px) + 48px);
  }
  .slot.offpattern {
    background: #fffdf3;
    border-color: #e7d58a;
    min-width: calc(var(--slot-width, 116px) + 48px);
    width: calc(var(--slot-width, 116px) + 48px);
  }
  .slot.dragover {
    border-color: var(--rf-blue);
    background: #f1f7fd;
  }
  .slot.slot-missing-critical {
    background: #6f1d1b;
    border-color: #4d0f0d;
    box-shadow: inset 0 0 0 1px rgba(255,255,255,0.08);
  }
  .slot.slot-missing-critical .slot-label,
  .slot.slot-missing-critical .empty {
    color: #fff1ef;
  }
  .slot.slot-make-square {
    background: #fff5f5;
    border-color: #d95c5c;
    box-shadow: inset 0 0 0 1px rgba(217, 92, 92, 0.14);
  }
  .slot.slot-make-square .slot-label {
    color: #9b1c1c;
  }
  .make-square-hint {
    display: inline-flex;
    align-items: center;
    gap: 6px;
    font-weight: 800;
    color: #b42318;
    cursor: help;
  }
  .slot-label {
    font-size: 11px;
    font-weight: 800;
    color: #4f6071;
    text-transform: uppercase;
    letter-spacing: .3px;
  }
  .asset-card {
    background: white;
    border: 1px solid #d9e2ea;
    border-radius: 12px;
    overflow: hidden;
    cursor: grab;
    box-shadow: 0 4px 10px rgba(25, 38, 55, 0.05);
  }
  .asset-card.changed {
    border: 3px solid var(--rf-green);
  }
  .asset-card.deleted { border: 3px solid var(--rf-red); }
  .asset-card.restored { border: 3px solid var(--rf-blue); }
  .asset-card.offpattern { border: 3px solid var(--rf-gold); }
  .asset-card.pending-copy { border: 3px solid #00A3E0; box-shadow: 0 0 0 1px rgba(0,163,224,.18); }
  .asset-card.asset-uploaded { border: 3px solid var(--rf-green); box-shadow: 0 0 0 1px rgba(52,140,75,.18); }
  .asset-card.bad-dimensions { background: #fff1f1; border-color: #e7a7a7; }
  .asset-card img {
    width: 100%;
    height: var(--thumb-height, 84px);
    object-fit: contain;
    display: block;
    background: #f1f4f7;
    padding: 3px;
  }
  .slot.trash .asset-card img {
    height: calc(var(--thumb-height, 84px) * 0.54);
  }
  .slot.trash .asset-card {
    transform: scale(0.75);
    transform-origin: top left;
    margin-bottom: -20px;
  }
  .asset-meta {
    padding: 1px 4px 3px 4px;
    display: grid;
    gap: 0;
  }
  .asset-name {
    font-size: 11px;
    font-weight: 700;
    line-height: 1.25;
    word-break: break-word;
  }
  .asset-date {
    font-size: 10px;
    color: #6b7785;
    line-height: 1.05;
  }
  .asset-date-row {
    display:flex;
    align-items:center;
    justify-content:flex-start;
    gap:8px;
  }
  .asset-date-left {
    min-width:0;
    flex:1 1 auto;
  }
  .asset-fix-pill-row {
    margin-top: 4px;
    display: flex;
    justify-content: flex-start;
    margin-bottom: 8px;
  }
  .asset-fix-action {
    display: inline-flex;
    align-items: center;
    justify-content: center;
    padding: 2px 8px;
    border-radius: 999px;
    background: #e7f6ea;
    color: #1f7a34;
    font-size: 10px;
    font-weight: 800;
    line-height: 1.1;
    text-decoration: none;
    border: 1px solid #b9e2c1;
    white-space: nowrap;
  }
  .asset-size-warning {
    margin-top: 4px;
    font-size: 10px;
    line-height: 1.15;
    color:#a93d36;
    font-weight:700;
    white-space: normal;
  }
  .asset-actions {
    display: flex;
    flex-wrap: wrap;
    gap: 6px;
    margin-top: 0;
    line-height: 1.1;
    justify-content: flex-start;
  }
  .asset-actions a {
    font-size: 10px;
    color: var(--rf-blue);
    text-decoration: none;
    display: inline-flex;
    max-width: 100%;
  }
  .warning-chip {
    margin-top: 8px;
    padding: 9px 10px;
    border-radius: 12px;
    background: var(--rf-red-soft);
    color: #7d2d27;
    border: 1px solid #efb3af;
    font-size: 12px;
    display: flex;
    justify-content: space-between;
    gap: 8px;
  }
  .warning-chip button {
    border: 0; background: transparent; cursor: pointer; color: inherit; font-weight: 800;
  }
  .asset-fix-action {
    display:inline-flex;
    margin-left:0;
    color:#2f8f45;
    font-weight:800;
    cursor:pointer;
    text-decoration:none;
    white-space:nowrap;
    flex:0 0 auto;
    align-self:flex-start;
  }
  .asset-fix-action:hover { text-decoration:underline; }
  .summary-header {
    padding: 2px 8px;
    border-bottom: 1px solid var(--rf-border);
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: 8px;
    min-height: 24px;
    margin: 0;
    cursor:pointer;
    user-select:none;
  }
  .summary-header h3 {
    margin: 0;
    font-size: 12px;
    font-weight: 700;
    line-height: 1.1;
    color: var(--rf-navy);
  }
  .summary-header .summary-caret { font-size:11px; color:#6c5b84; }
  .summary-body {
    padding: 10px 14px 14px;
    display: none;
    gap: 12px;
  }
  .summary-body.open { display: grid; }
  .summary-group h4 {
    margin: 6px 0 8px;
    font-size: 13px;
    color: var(--rf-navy);
  }
  .summary-item {
    display: grid;
    grid-template-columns: 56px 1fr;
    gap: 10px;
    padding: 8px;
    border: 1px solid #e3eaf2;
    border-radius: 12px;
    margin-bottom: 8px;
    cursor: pointer;
    background: white;
  }
  .summary-item img {
    width: 56px; height: 56px; object-fit: cover; border-radius: 8px; background: #f2f5f8;
  }
  .summary-item .name { font-size: 12px; font-weight: 700; }
  .summary-item .desc { font-size: 11px; color: #667587; }
  .server-log {
    padding: 3px 6px 6px;
    border-top: 1px solid var(--rf-border);
    background: #fafbfd;
    font-family: Consolas, monospace;
    font-size: 11px;
    max-height: 180px;
    overflow: auto;
    white-space: pre-wrap;
  }
  .notes-panel {
    padding: 3px 6px 6px;
    border-top: 1px solid var(--rf-border);
    background: #fafdfb;
    display: none;
  }
  .notes-panel.open { display: block; }
  .notes-panel.open { display: block; }
  .notes-list { display: grid; gap: 8px; }
  .note-row { display:grid; grid-template-columns: 20px 1fr; gap:8px; align-items:start; }
  .note-check { margin-top: 8px; }
  .note-row textarea {
    width: 100%;
    min-height: 48px;
    resize: vertical;
    border: 1px solid var(--rf-border);
    border-radius: 10px;
    padding: 8px 10px;
    font: inherit;
    background: white;
  }
  .empty {
    font-size: 12px;
    color: #6d7886;
    padding: 6px;
  }
   .notice {
    overflow-wrap: anywhere;

    padding: 12px 14px;
    border-radius: 12px;
    border: 1px solid #d8e4ef;
    background: #f3f8fc;
    color: var(--rf-navy);
    font-size: 13px;
  }
  .success {
    background: var(--rf-green-soft);
    border-color: #b8dfc1;
    color: #25612a;
  }
  .error {
    background: var(--rf-red-soft);
    border-color: #efb3af;
    color: #812f2b;
  }
   .panel-notice-wrap {
    max-height: 132px;
    overflow-y: auto;
    padding-right: 4px;
 display:grid; gap:8px; }
  .panel-notice { display:flex; align-items:flex-start; justify-content:space-between; gap:10px; width:100%; text-align:left; cursor:pointer; overflow:hidden; }
  .panel-notice .text { flex:1; min-width:0; overflow-wrap:anywhere; word-break:break-word; }
  .panel-notice .dismiss { border:none; background:transparent; color:inherit; font-weight:800; cursor:pointer; padding:0 2px; flex-shrink:0; }
  .notifications-panel { overflow:hidden; }
  .inline-link { background:none; border:none; color:inherit; text-decoration:underline; cursor:pointer; font:inherit; padding:0; }
  .hidden { display: none !important; }
  @media (max-width: 1700px) {
    .inline-launch-group { grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); }
    .launch-button-col { grid-column: 1 / -1; padding-top: 0; }
    .launch-button-stack { grid-template-columns: 1fr; grid-template-rows: auto; }
    .launcher-lower-row { grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); }
    .launcher-random-row { grid-column: 1 / -1; }
    .collection-status-mount { max-width: 100%; }
  }

  @media (max-width: 1400px) {
    .shell { grid-template-columns: 1fr; }
    .top-shell { grid-template-columns: 1fr; position: static; }
    .brand-panel .sub { max-width: none; }
    .board-wrap { grid-column: auto; grid-template-columns: 1fr; }
    .photo-shell { max-height:none; width:auto !important; min-width:0 !important; }
    .board-main { max-height:none; }
    .row-layout { grid-template-columns: 1fr; }
    .top-slot-layout { grid-template-columns: 1fr; }
     .color-header {
    display:flex;
    justify-content:space-between;
    align-items:center;
    gap:12px;
 top: 0; }
    .sticky-board-tools { position: static; }
    .inline-launch-group { grid-template-columns: 1fr; }
    .launch-button-col { grid-column: auto; padding-top: 0; }
    .launch-button-stack { grid-template-columns: 1fr; grid-template-rows: auto; }
    .launcher-lower-row { grid-template-columns: 1fr; }
    .launcher-random-row { grid-column: auto; }
    .collection-status-mount { max-width: none; }
  }

  @media (max-width: 760px) {
    .launch-button-stack { grid-template-columns: 1fr; }
    .launcher-lower-row { align-items:flex-start; }
    .launcher-checkbox-row .mode-option { white-space:normal; }
    .collection-status-mount { min-width: 0; max-width: none; }
  }

  .inactive-all-badge {
    display:inline-flex; align-items:center; gap:6px;
    background:#efe5f2; color:#7e4c2f; border:1px solid #d8bddf;
    border-radius:999px; padding:4px 8px; font-size:12px; font-weight:700;
  }
  .row-highlight {
    position: relative;
    background: linear-gradient(180deg, rgba(220,252,231,.94) 0%, rgba(240,253,244,.98) 100%);
    box-shadow:
      0 0 0 2px rgba(134,239,172,.95),
      0 0 0 7px rgba(187,247,208,.62),
      0 0 30px rgba(134,239,172,.62);
    border-radius: 10px;
    transition: background .24s ease, box-shadow .24s ease, transform .24s ease;
    animation: rowGlowPulse 1.15s ease-in-out 0s 3;
  }
  @keyframes rowGlowPulse {
    0% {
      box-shadow:
        0 0 0 2px rgba(134,239,172,.95),
        0 0 0 6px rgba(187,247,208,.38),
        0 0 16px rgba(134,239,172,.34);
      transform: scale(1);
    }
    50% {
      box-shadow:
        0 0 0 2px rgba(134,239,172,1),
        0 0 0 9px rgba(187,247,208,.70),
        0 0 38px rgba(134,239,172,.78);
      transform: scale(1.002);
    }
    100% {
      box-shadow:
        0 0 0 2px rgba(134,239,172,.95),
        0 0 0 6px rgba(187,247,208,.38),
        0 0 16px rgba(134,239,172,.34);
      transform: scale(1);
    }
  }
  .meta-cell.components .v button, .meta-cell.components .v a { margin:2px 4px 2px 0; }
  .asset-undo-copy { margin-top:4px; background:#fff; border:1px solid #9cb8e8; color:#1f5fbf; border-radius:8px; font-size:11px; padding:3px 6px; cursor:pointer; }
  .select-wrap { display:grid; gap:8px; align-content:start; }
  .inline-launch-group {
    display:grid;
    grid-template-columns:minmax(165px,0.95fr) minmax(190px,1.08fr) minmax(152px,170px);
    gap:10px;
    align-items:end;
  }
  .launch-field { min-width:0; }
  .launch-field label.small { margin-bottom:5px; }
  .launch-button-col {
    min-width:0;
    display:flex;
    align-items:flex-end;
    padding-top:18px;
  }
  .inline-launch-group .btn { width:100%; white-space:normal; line-height:1.1; padding:10px 12px; min-height:46px; display:flex; align-items:center; justify-content:center; text-align:center; overflow-wrap:anywhere; }
  .launch-button-stack { display:grid; grid-template-columns:1fr; grid-template-rows:auto; gap:8px; width:100%; align-self:end; }
  .launch-button-stack .btn { min-height:46px; }
  .launch-button-stack .btn.btn-compact { min-height:36px; padding:7px 10px; font-size:13px; }
  .launcher-lower-row {
    display:grid;
    grid-template-columns:minmax(165px,0.95fr) minmax(190px,1.08fr) minmax(152px,170px);
    align-items:center;
    gap:10px;
    margin-top:0;
  }
  .launcher-checkbox-row { margin-top:0; display:flex; align-items:center; min-height:0; }
  .launcher-checkbox-row .mode-option { margin:0; white-space:nowrap; }
  .collection-status-mount { margin-top:0; min-height:0; min-width:0; max-width:none; width:100%; }
  .collection-status-pill { padding:10px 12px; border-radius:14px; border:1px solid #c6d8cf; background:#d8e4dd; color:#2f6b41; font-size:13px; line-height:1.25; font-weight:500; box-shadow: inset 0 1px 0 rgba(255,255,255,.45); }
  .launcher-random-row { min-width:0; display:flex; align-items:center; }
  .launcher-random-row .btn { width:100%; }
  .collection-status-pill.notice { background:#eef2f6; border-color:#d9e2ec; color:#5c6670; }
  .collection-status-pill.error { background:#fdeceb; border-color:#f0c1bc; color:#a0463e; }
  .photo-collapsed-tease { display:grid; place-items:center; gap:8px; padding:18px 4px 8px; color:#4f8d5f; }
  .photo-collapsed-arrow { width:36px; height:36px; border-radius:999px; display:grid; place-items:center; background:linear-gradient(180deg, #69bf7d 0%, #57a86a 100%); color:#fff; font-size:18px; font-weight:900; box-shadow:0 8px 16px rgba(70,132,85,.22); }
  .photo-collapsed-spark { writing-mode:vertical-rl; transform:rotate(180deg); font-size:10px; letter-spacing:.14em; text-transform:uppercase; color:#71a57d; font-weight:800; }
  .photo-watermark-text { position:absolute; inset:0; display:flex; flex-direction:column; align-items:center; justify-content:center; gap:.02em; pointer-events:none; user-select:none; font-weight:900; text-align:center; line-height:.84; letter-spacing:.02em; color:rgba(255,255,255,0.46); text-shadow:0 2px 6px rgba(60,60,60,0.28); }
  .photo-watermark-text span:first-child { font-size: clamp(40px, 23%, 68px); }
  .photo-watermark-text span:last-child { font-size: clamp(48px, 29%, 84px); }
  @keyframes photoPullCheckingPulse { 0% { opacity: .82; } 50% { opacity: 1; } 100% { opacity: .82; } }
  .slot-highlight { box-shadow: 0 0 0 4px rgba(58,166,106,.95), 0 0 34px rgba(58,166,106,.65) !important; background: rgba(58,166,106,.12) !important; animation: slotFadeOut 5s ease forwards; }
  @keyframes slotFadeOut { 0% { box-shadow: 0 0 0 4px rgba(58,166,106,.95), 0 0 34px rgba(58,166,106,.65); background: rgba(58,166,106,.12); } 100% { box-shadow: 0 0 0 0 rgba(58,166,106,0), 0 0 0 rgba(58,166,106,0); background: rgba(58,166,106,0); } }

  .game-modes-panel { padding: 4px 12px 6px; border-top: 1px solid #efe5f6; display: grid; gap: 6px; }
  .game-mode-card { border: 1px solid var(--rf-border); border-radius: 14px; padding: 10px; background: linear-gradient(180deg,#fbf8ff,#f3ebfb); }
  .game-mode-launch { display:flex; gap:10px; align-items:flex-start; cursor:pointer; }
  .game-mode-icon { width: 44px; height: 44px; border-radius: 14px; display:flex; align-items:center; justify-content:center; position:relative; overflow:hidden; background: linear-gradient(135deg,#4f245e,#8a5bb0); color:white; font-size:22px; box-shadow: 0 8px 20px rgba(79,36,94,.18); }
  .game-mode-icon .tool-duo { position:relative; width:24px; height:24px; display:block; }
  .game-mode-icon .tool-duo .tool { position:absolute; inset:0; display:flex; align-items:center; justify-content:center; transform-origin:center; transition: transform .18s ease, filter .22s ease, opacity .22s ease; }
  .game-mode-icon .tool-duo .hammer { transform: rotate(-20deg) translate(-3px, -1px); filter: grayscale(1) saturate(.55) brightness(.8); opacity:.72; }
  .game-mode-icon .tool-duo .wrench { transform: rotate(25deg) translate(3px, 1px); filter: grayscale(1) saturate(.55) brightness(.8); opacity:.72; }
  .game-mode-icon.ready { background: linear-gradient(135deg,#4f245e 0%,#7d3bc0 42%,#b46cff 100%); box-shadow: 0 10px 24px rgba(123,44,191,.26); }
  .game-mode-icon.ready::after { content:''; position:absolute; inset:-20%; background: radial-gradient(circle at center, rgba(255,255,255,.32), rgba(255,255,255,0) 56%); animation: gameIconPulse 1.8s ease-in-out infinite; pointer-events:none; }
  .game-mode-icon.ready .tool-duo .hammer { filter: none; opacity:1; transform: rotate(-20deg) translate(-3px, -1px) scale(1.06); }
  .game-mode-icon.ready .tool-duo .wrench { filter: none; opacity:1; transform: rotate(25deg) translate(3px, 1px) scale(1.06); }
  .game-mode-icon.empty { background: linear-gradient(135deg,#6f6377,#8a7f92); box-shadow:none; }
  .game-mode-icon.empty .tool-duo .hammer,
  .game-mode-icon.empty .tool-duo .wrench { filter: grayscale(1) saturate(.18) brightness(.72); opacity:.42; }
  @keyframes gameIconPulse { 0%,100% { transform: scale(.85); opacity:.2; } 50% { transform: scale(1.15); opacity:.6; } }
  .game-mode-title { font-weight: 800; color: var(--rf-navy); margin: 0 0 4px; }
  .game-mode-sub { color:#6d5a77; font-size:12px; line-height:1.35; }
  .game-scoreboard { display:grid; grid-template-columns:1fr 1fr; gap:8px; }
  .game-score-pill { border-radius: 12px; background:#fff; border:1px solid var(--rf-border); padding:8px 10px; }
  .game-score-pill .k { font-size:11px; color:#7b6885; text-transform:uppercase; font-weight:800; letter-spacing:.04em; }
  .game-score-pill .v { font-size:18px; color:var(--rf-navy); font-weight:800; margin-top:2px; }
  .game-actions { display:flex; gap:8px; flex-wrap:wrap; }
  .game-mini-btn { padding:8px 12px; border-radius:999px; border:0; cursor:pointer; font-weight:800; }
  .game-mini-btn.primary { background: linear-gradient(90deg,#7b2cbf,#c77dff); color:#fff; border:1px solid rgba(255,255,255,0.35); box-shadow:0 8px 18px rgba(123,44,191,0.28), inset 0 1px 0 rgba(255,255,255,0.18); }
  .game-mini-btn.pass { background:#fff5e8; color:#8a5a00; border:1px solid #edd7ad; }
  .game-mini-btn.exit { background:#f3f0f7; color:#5b4965; border:1px solid #ddd0e8; }
  .game-leaderboard { display:grid; gap:6px; }
  .game-leader-row { display:flex; justify-content:space-between; gap:8px; font-size:12px; color:#5f4d69; padding:6px 8px; border-radius:10px; background:#fff; border:1px solid #eee2f6; }
  .game-mode-icon-only { display:flex; align-items:center; justify-content:flex-start; padding:2px 0 0; }
  .game-mode-icon-only button { border:0; background:transparent; padding:0; cursor:pointer; display:flex; align-items:flex-start; justify-content:flex-start; }
  .game-mode-icon-only .game-mode-icon { width:29px; height:29px; font-size:14px; border-radius:10px; }
  .game-mode-icon-only .game-mode-icon .tool-duo { width:16px; height:16px; }
  .game-mode-icon-only .game-mode-icon .tool-duo .hammer { transform: rotate(-20deg) translate(-2px, -1px); }
  .game-mode-icon-only .game-mode-icon .tool-duo .wrench { transform: rotate(24deg) translate(2px, 1px); }
  .brand-mini-top .game-mode-icon .tool-duo { width:18px; height:18px; }
  .brand-panel.game-active { padding: 10px 12px; }
  .brand-mini-game { display:grid; grid-template-columns: 1fr; gap:6px; color:#fff; }
  .brand-mini-top { display:flex; align-items:center; gap:8px; }
  .brand-mini-top .game-mode-icon { width:30px; height:30px; border-radius:10px; font-size:16px; box-shadow:none; flex:0 0 auto; }
  .brand-mini-title-wrap { min-width:0; }
  .brand-mini-kicker { font-size:9px; line-height:1; letter-spacing:.12em; text-transform:uppercase; opacity:.85; font-weight:800; }
  .brand-mini-title { font-size:14px; line-height:1.05; font-weight:900; margin-top:2px; }
  .brand-mini-sub { font-size:10px; line-height:1.15; opacity:.92; margin-top:2px; }
  .brand-mini-grid { display:grid; grid-template-columns:1fr 1fr 1fr; gap:5px; }
  .brand-mini-pill { border-radius:10px; background:rgba(255,255,255,.14); border:1px solid rgba(255,255,255,.18); padding:5px 6px; min-width:0; }
  .brand-mini-pill.wide { grid-column:1 / -1; }
  .brand-mini-pill .k { font-size:8px; line-height:1; text-transform:uppercase; letter-spacing:.08em; font-weight:800; opacity:.84; }
  .brand-mini-pill .v { font-size:13px; line-height:1.05; font-weight:900; margin-top:3px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  .brand-mini-pill .s { font-size:9px; line-height:1.15; opacity:.9; margin-top:3px; }
  .brand-mini-actions { display:grid; grid-template-columns:1fr 1fr 1fr; gap:4px; align-items:center; margin-top:2px; }
  .brand-mini-actions .game-mini-btn { padding:4px 6px; font-size:10px; line-height:1.1; min-height:28px; }
  .brand-mini-actions .game-mini-btn.primary { filter:saturate(1.12) brightness(1.03); }
  .brand-mini-leader { display:grid; gap:5px; }
  .brand-mini-leader-toggle { display:flex; align-items:center; justify-content:space-between; gap:8px; width:100%; border:1px solid rgba(255,255,255,.16); background:rgba(255,255,255,.08); color:#fff; border-radius:10px; padding:6px 8px; cursor:pointer; font:inherit; }
  .brand-mini-leader-title { font-size:8px; line-height:1; text-transform:uppercase; letter-spacing:.1em; font-weight:800; opacity:.84; }
  .brand-mini-leader-caret { font-size:11px; opacity:.9; }
  .brand-mini-leader-rows { display:grid; gap:3px; }
  .brand-mini-leader-row { display:flex; justify-content:space-between; gap:6px; padding:3px 5px; border-radius:8px; background:rgba(255,255,255,.12); border:1px solid rgba(255,255,255,.16); font-size:9px; line-height:1.1; }

  .wait-mini-game { margin-top: 14px; padding: 14px; border-radius: 16px; border: 1px solid #eadcf8; background: linear-gradient(180deg,#fcf9ff,#f5eefc); display:none; }
  .wait-mini-game.open { display:block; }
  .wait-mini-top { display:flex; align-items:center; justify-content:space-between; gap:12px; margin-bottom:8px; }
  .wait-mini-title { font-weight:800; color:var(--rf-navy); font-size:16px; }
  .wait-mini-score { font-size:13px; color:#6d5a77; }
  .wait-mini-score strong { color:var(--rf-purple); font-size:18px; }
  .wait-mini-sub { margin:0 0 10px; font-size:12px; color:#7a6884; }
  .wait-mini-board { position:relative; height:300px; border-radius:16px; border:1px dashed #dcc7f0; background:
      radial-gradient(circle at 18% 20%, rgba(255,255,255,.85), rgba(255,255,255,0) 24%),
      linear-gradient(180deg,#fffaf3 0%,#f8f1ff 100%);
      overflow:hidden; }
  .wait-mini-bunny { position:absolute; width:92px; height:92px; border-radius:999px; border:1px solid #dcbef5; background: linear-gradient(180deg,#ffffff,#f4e7ff); box-shadow:0 10px 24px rgba(123,44,191,.18); display:flex; align-items:center; justify-content:center; cursor:pointer; user-select:none; font-size:42px; transition: left .34s ease, top .34s ease, transform .12s ease, box-shadow .12s ease; touch-action: manipulation; }
  .wait-mini-bunny:hover { transform: scale(1.05) rotate(-4deg); box-shadow:0 12px 28px rgba(123,44,191,.22); }
  .wait-mini-bunny:active { transform: scale(.95); }
  .wait-mini-hint { margin-top:8px; font-size:12px; color:#8a7794; min-height:18px; }

  .game-celebration { position:fixed; inset:0; pointer-events:none; display:none; align-items:center; justify-content:center; z-index:10030; }
  .game-celebration.show { display:flex; }
  .game-celebration-card { min-width:min(420px,90vw); background:rgba(79,36,94,.95); color:white; border-radius:20px; padding:22px 26px; box-shadow:0 24px 60px rgba(0,0,0,.22); text-align:center; animation:gameCelebrate .9s ease; }
  .game-celebration-card h3 { margin:0 0 8px; font-size:28px; }
  .game-celebration-card p { margin:0; opacity:.94; }
  .issue-zero-burst { position:fixed; inset:0; pointer-events:none; overflow:hidden; z-index:10035; }
  .issue-zero-burst::before { content:''; position:fixed; inset:0; opacity:0; background: radial-gradient(circle at var(--flash-x,50%) var(--flash-y,18%), rgba(122,213,140,.24), rgba(122,213,140,0) 34%), linear-gradient(180deg, rgba(255,255,255,.14), rgba(255,255,255,0)); animation: issueZeroFlash 5s ease forwards; }
  .issue-zero-banner { position:fixed; left:50%; top:84px; transform:translateX(-50%); padding:14px 20px; border-radius:999px; background:rgba(26,104,53,.94); color:#fff; border:1px solid rgba(188,241,203,.7); box-shadow:0 16px 40px rgba(15,68,36,.22); font-weight:900; letter-spacing:.01em; font-size:15px; display:flex; align-items:center; gap:10px; animation: issueZeroBanner 5s cubic-bezier(.18,.84,.24,1) forwards; }
  .issue-zero-banner .burst-emoji { font-size:18px; filter: drop-shadow(0 1px 0 rgba(255,255,255,.24)); }
  .issue-zero-particle { position:fixed; left:0; top:0; opacity:0; will-change:transform, opacity; animation: issueZeroFall var(--dur,5s) cubic-bezier(.2,.76,.22,1) forwards; animation-delay: var(--delay,0s); }
  .issue-zero-particle.confetti { border-radius: 3px; box-shadow: 0 1px 0 rgba(255,255,255,.3) inset; }
  .issue-zero-particle.streamer { width: 7px; height: 24px; border-radius: 999px; box-shadow: 0 1px 0 rgba(255,255,255,.26) inset; }
  .issue-zero-particle.furniture { font-size: var(--size,24px); line-height:1; filter: drop-shadow(0 3px 6px rgba(0,0,0,.14)); }
  @keyframes issueZeroFlash { 0% { opacity:0; } 10% { opacity:1; } 34% { opacity:.82; } 100% { opacity:0; } }
  @keyframes issueZeroBanner { 0% { opacity:0; transform:translateX(-50%) translateY(10px) scale(.92); } 12% { opacity:1; transform:translateX(-50%) translateY(0) scale(1); } 72% { opacity:1; transform:translateX(-50%) translateY(0) scale(1); } 100% { opacity:0; transform:translateX(-50%) translateY(-10px) scale(.98); } }
  @keyframes issueZeroFall {
    0% { opacity: 0; transform: translate3d(0,0,0) rotate(0deg) scale(.72); }
    7% { opacity: 1; }
    18% { opacity: 1; transform: translate3d(var(--burst-x,0px), var(--lift-y,-100px), 0) rotate(var(--burst-rot,50deg)) scale(1.08); }
    55% { opacity: 1; transform: translate3d(calc(var(--tx,0px) * .52), calc(45vh + var(--mid-y,0px)), 0) rotate(calc(var(--rot,540deg) * .55)) scale(1); }
    82% { opacity: 1; }
    100% { opacity: 0; transform: translate3d(var(--tx,0px), calc(100vh + 160px), 0) rotate(var(--rot,540deg)) scale(.98); }
  }
  @keyframes gameCelebrate { 0% { transform: scale(.82) translateY(22px); opacity:0; } 100% { transform: scale(1) translateY(0); opacity:1; } }


.challenge-issue-pill {
  display:inline-flex;
  align-items:center;
  gap:8px;
  padding:8px 12px;
  border-radius:999px;
  font-size:13px;
  font-weight:800;
  letter-spacing:.01em;
  color:#7f2222;
  background:#fff1f1;
  border:1px solid #efb7b7;
  box-shadow:0 1px 0 rgba(0,0,0,.03);
}
.challenge-issue-pill.good {
  color:#196b37;
  background:#ecfbf1;
  border-color:#9fd7b3;
}
.challenge-issue-pill .num {
  display:inline-flex;
  align-items:center;
  justify-content:center;
  min-width:22px;
  height:22px;
  padding:0 6px;
  border-radius:999px;
  background:rgba(127,34,34,.12);
}
.challenge-issue-pill.good .num {
  background:rgba(25,107,55,.12);
}

</style>
</head>
<body>
  <div class="shell">
    <div class="top-shell">
      <div class="panel brand-panel" id="brandPanel">
      <div id="brandPanelMount">
        <h1>Content Refresher</h1>
        <div class="sub">Live Bynder board for Product Collection image cleanup, slotting, and safe staged updates.</div>
      </div>
    </div>

    <div class="panel launcher" id="launcherPanel"><div id="launcherPanelMount"></div></div>

    <div class="panel mode-panel" id="modePanel">
      <div class="panel-title">Mode</div>
      <div class="mode-help" id="modeHelp">Update positions stages reorder, trash, restore, and cross-SKU copy changes. File uploads are disabled in this mode.</div>
      <div class="mode-options">
        <label class="mode-option"><input type="radio" name="appMode" value="positions" checked /> Update positions</label>
        <label class="mode-option"><input type="radio" name="appMode" value="assets" /> Update assets</label>
      </div>

      </div>

    <div class="panel notifications-panel">
      <div class="notifications-header">
        <div class="panel-title">Notifications</div>
        <button type="button" class="btn btn-secondary notifications-clear-btn" id="clearNotificationsBtn" title="Clear dismissible notifications" aria-label="Clear dismissible notifications">&#129529;</button>
      </div>
      <div id="boardNotifications"><div class="notifications-empty">No collection notifications yet.</div></div>
    </div>

      <div class="side">
        <div class="panel">
        <div class="summary-header" data-toggle-target="summary">
          <h3>Queued changes</h3>
          <span class="summary-caret" id="toggleSummaryBtn" aria-hidden="true">▾</span>
        </div>
        <div class="summary-body" id="summaryBody"></div>
        <div class="summary-header" style="margin-top:0;" data-toggle-target="log">
          <h3>Server log</h3>
          <span class="summary-caret" id="toggleLogBtn" aria-hidden="true">▾</span>
        </div>
        <div class="server-log" id="serverLog" style="display:none;"></div>
        <div class="summary-header" style="margin-top:0;">
          <h3>Game modes</h3>
        </div>
        <div class="game-modes-panel" id="gameModesPanel"></div>
        </div>
      </div>
    </div>
    <div class="game-celebration" id="gameCelebration"></div>
    <div class="issue-zero-burst" id="issueZeroBurst"></div>

    <div class="board-wrap" id="boardWrap">
      <div class="panel photo-shell collapsed" id="photoShell">
        <div class="photo-resize-handle" id="photoResizeHandle"></div>
        <div class="photo-header">
          <div>
            <div class="panel-title">Photography</div>
            <div class="photo-sub" id="photoSub">Reference panel for available product photography in the selected collection/color.</div>
          </div>
          <div class="photo-header-actions">
            <button type="button" class="btn btn-secondary photo-mini-btn" id="photoToggleBtn">Expand</button>
            <button type="button" class="btn btn-secondary photo-mini-btn" id="photoClearBtn">Clear panel</button>
          </div>
        </div>
        <div class="photo-toolbar">
          <label class="small" style="margin:0;">Panel thumbnail size
            <input type="range" id="photoThumbSize" min="120" max="260" value="170" />
          </label>
          <label class="small" style="margin:0; display:flex; align-items:center; gap:6px;">
            <input type="checkbox" id="hideFpoToggle" onchange="setHideFpo(this.checked)" />
            Hide FPO
          </label>
          <label class="small" style="margin:0; display:flex; align-items:center; gap:6px;">
            <input type="checkbox" id="hideReviewedToggle" onchange="setHideReviewed(this.checked)" />
            Hide reviewed
          </label>
        </div>
        <div class="photo-body" id="photoBody">
          <div class="photo-empty">Pull available product photography from a color header to load this panel.</div>
        </div>
      </div>

      <div class="panel board-main" id="boardMain">
        <div class="collection-header sticky-board-tools always-sticky">
          <div>
            <h2 id="collectionTitle">Collection</h2>
            <div class="muted" id="collectionMeta"></div>
          </div>
          <div class="controls">
            <div id="challengeIssuePill" class="challenge-issue-pill" style="display:none;"></div>
            <div id="bulkFixSiloWrap" style="display:none; align-items:center; gap:8px;">
              <button type="button" class="bulk-fix-pill" id="bulkFixSiloBtn">Bulk fix silo</button>
              <button type="button" class="btn btn-primary btn-reload-flashing" id="bulkFixSiloGoBtn" style="display:none;">Proceed</button>
            </div>
            <button type="button" class="btn btn-secondary btn-compact" id="pioClearBoardBtn" ${state.workspace === 'product_imagery_onboarding' && state.board ? '' : 'disabled'} title="Removes this board from your screen only. The Bynder assets stay exactly where they are.">Remove Board</button>
            <label class="small" style="margin:0;">
              Thumbnail size
              <input type="range" id="thumbSize" min="70" max="170" value="84" />
            </label>
            <button type="button" class="btn btn-secondary" id="reloadBtn">Reload From Bynder</button>
            <button type="button" class="btn btn-secondary" id="discardBtn">Discard Changes</button>
            <button type="button" class="btn btn-commit" id="commitBtn">Update in Bynder</button>
          </div>
        </div>
        <div id="boardHost" style="padding: 0 18px 18px;"></div>
        <div class="statusbar">
          <div id="commitStatus" class="muted">No queued changes yet.</div>
          <div id="queuedCount" class="muted"></div>
        </div>
      </div>
    </div>
    <div class="wait-overlay" id="waitOverlay">
    <div class="wait-card">
      <h3 id="waitOverlayTitle">Giving Bynder a moment...</h3>
      <p id="waitOverlayBody">Your updates went through. Waiting 30 seconds before checking for refreshed metadata.</p>
      <div class="wait-status" id="waitStatus">Standing by...</div>
      <div class="wait-mini-game" id="waitMiniGame">
        <div class="wait-mini-top">
          <div class="wait-mini-title">Boop the dust bunny</div>
          <div class="wait-mini-score">Boops: <strong id="waitMiniScore">0</strong></div>
        </div>
        <p class="wait-mini-sub">Boop the floof while Bynder does its little metadata paperwork.</p>
        <div class="wait-mini-board" id="waitMiniBoard">
          <button type="button" class="wait-mini-bunny" id="waitMiniBunny" onpointerdown="boopWaitMiniBunny(event)" aria-label="Boop the dust bunny">🐇</button>
        </div>
        <div class="wait-mini-hint" id="waitMiniHint">A larger bunny. A kinder pace. Considerably more boopable.</div>
      </div>
    </div>
  </div>
  <div class="idle-overlay" id="idleOverlay">
    <div class="idle-card">
      <h3>This board has been idle for 30+ minutes.</h3>
      <p>To reduce the chance of working from stale Bynder data, we recommend reloading this collection before making more changes.</p>
      <p>You can reload now or keep working with the board as it currently stands.</p>
      <div class="idle-actions">
        <button type="button" class="btn btn-secondary" id="idleDismissBtn">Dismiss</button>
        <button type="button" class="btn btn-secondary" id="idleKeepWorkingBtn">Keep Working</button>
        <button type="button" class="btn btn-primary" id="idleReloadBtn">Reload From Bynder</button>
      </div>
    </div>
  </div>

<script>

const APP_UI_STATE_KEY = 'content_refresher_ui_state_v1';
function saveUIState() {
  try {
    const payload = {
      workspace: state.workspace,
      loadedCollectionOptionId: state.loadedCollectionOptionId || '',
      onboardingCurrentBoardId: (state.onboarding && state.onboarding.currentBoardId) || '',
      mode: state.mode,
      hideInactive: !!state.hideInactive,
      photographyExpanded: !!(state.photography && state.photography.expanded),
      photographyWidth: Number((state.photography && state.photography.width) || 520),
      pioEditorCollapsed: !!(state.onboarding && state.onboarding.editorCollapsed),
    };
    localStorage.setItem(APP_UI_STATE_KEY, JSON.stringify(payload));
  } catch (err) {}
}
function loadSavedUIState() {
  try {
    const raw = localStorage.getItem(APP_UI_STATE_KEY);
    return raw ? JSON.parse(raw) : null;
  } catch (err) { return null; }
}
async function restoreUIStateIfPossible() {
  const saved = loadSavedUIState();
  if (!saved) return;
  try {
    if (saved.mode) state.mode = saved.mode;
    state.hideInactive = !!saved.hideInactive;
    state.photography.expanded = !!saved.photographyExpanded;
    if (saved.photographyWidth) state.photography.width = Number(saved.photographyWidth) || state.photography.width;
    if (typeof saved.pioEditorCollapsed === 'boolean') state.onboarding.editorCollapsed = !!saved.pioEditorCollapsed;
    renderModeUI();
    if (saved.workspace === 'product_imagery_onboarding') {
      state.workspace = 'product_imagery_onboarding';
      state.onboarding.currentBoardId = '';
      state.board = null;
      state.summary = null;
      renderBrandPanel();
      renderLauncherPanel();
      renderBoard();
      await loadOnboardingBoards();
      ensureBynderCollectionsLoaded(false);
      state.collectionNotice = {kind:'notice', text:''};
  state.preflightNotices = [];
      renderCollectionStatus();
    } else if (saved.loadedCollectionOptionId) {
      launchCollection(saved.loadedCollectionOptionId, {flashReload:false, scrollTopAfter:false});
    }
  } catch (err) { console.warn(err); }
}

window.PHOTO_TO_PSA_IMAGE_TYPE_MAP = {"Detail":"Detail","Lifestyle":"Room_shot","Silo":"Silo","Styled_Silo":"Silo","Swatch":"Swatch_detail","Video_Shoot_Still":"Room_shot"};

const state = {
  collections: [],
  filteredCollections: [],
  board: null,
  summary: null,
  summaryOpen: false,
  collapsedColors: {},
  logOpen: false,
  dragging: null,
  loadedCollectionOptionId: null,
  appNotices: [],
  mode: 'positions',
  assetModeDirty: false,
  assetModeDirtyRows: {},
  hideInactive: false,
  photography: {
    expanded: false,
    color: '',
    items: [],
    width: 520,
    thumb: 170,
    activeSkuSet: [],
    selectedIds: [],
    activeId: '',
    prep: { flip: false, mode: 'original', offsetYOverrides: {}, offsetXOverrides: {}, optionsOpen: true, addingVersion: false },
    collectionLoading: false,
    collectionLoadNoticeId: '',
    previewUrl: '',
    hideFpo: false,
    hideReviewed: false,
    reviewingIds: {},
    collectionSearch: '',
    collectionOptionId: '',
    imageTypeFilter: '',
    skuFilter: '',
  },
  photoSkuOpen: {},
  photoDragId: null,
  preparedPreviewDrag: null,
  bulkFixSiloMode: false,
  bulkFixSiloRunning: false,
  setDim: {
    activeRowId: '',
    slotAssignments: [],
    scalePercents: [],
    previewUrl: '',
    loading: false,
    applying: false,
    dirty: false,
    dragSlotIdx: null,
  },
  additionalPhotoAvailabilityBySku: {},
  additionalPhotoCheckInFlight: {},
  nonCollectionSkuLoading: {},
  collectionNotice: {kind:'notice', text:'Loading Product Collection options...'},
  launchLoadingTicker: null,
  collectionSource: '',
  bynderCollections: [],
  bynderCollectionsLoading: false,
  notesOpen: false,
  notes: [
    {id:'note-1', text:''},
    {id:'note-2', text:''},
    {id:'note-3', text:''},
  ],
  game: {
    active: false,
    queueLength: 0,
    score: 0,
    username: '',
    leaderboard: [],
    leaderboardOpen: false,
    current: null,
    loading: false,
    launchOverlayOpen: false,
    lastEnsureAt: 0,
    lastIssueCount: null,
  },
  waitFlow: {
    open: false,
    baselineFingerprint: '',
    activeToken: 0,
    miniGameOpen: false,
    miniGameScore: 0,
    miniGameTimer: null,
  },
  messagePollTimer: null,
  idle: {
    thresholdMs: 30 * 60 * 1000,
    lastActivityAt: Date.now(),
    modalOpen: false,
  },

  commitInFlight: false,
  workspace: 'content_refresher',
  onboarding: {
    boards: [],
    creating: false,
    currentBoardId: '',
    pastedRows: '',
    collectionLabel: '',
    entryMode: 'start',
    recentWarning: '',
    openingBoard: false,
    busyText: '',
    editorCollapsed: false,
    busyTimer: null,
    busyStepIndex: 0,
  },
};

const PIO_STEP_HEADER_ROW = 'SKU\tProduct Name\tComponents\tProduct Color\tLength\tWidth\tHeight\tSales Channel\tFeatures';
const PIO_REQUIRED_HEADERS = ['SKU','Product Name'];
const PIO_EXPECTED_HEADERS = ['SKU','Product Name','Components','Product Color','Length','Width','Height','Sales Channel','Features'];
const PIO_WORKFLOW_STATE_OPTIONS = [
  {status:'App_Launched', sync:'Do_not_sync_to_site', label:'Board started / Do not sync to site'},
  {status:'App_Staged', sync:'Do_not_sync_to_site', label:'Staging / Do not sync to site'},
  {status:'App_Live', sync:'Do_sync_to_site', label:'Live / Do sync to site'}
];
const PIO_BYNDER_SALES_CHANNEL_VALUES = ['Full_line','Online_only','Outlet__stocked_','Outlet__online_only_'];

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
}

function boardHasSku(sku) {
  if (!sku || !state.board) return false;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      if (String(row.sku || '') === String(sku)) return true;
    }
  }
  return false;
}

function getRowById(rowId) {
  if (!state.board || !rowId) return null;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      if (String(row.row_id || '') === String(rowId) || String(row.sku || '') === String(rowId)) return row;
    }
  }
  return null;
}

function sectionRowsByColor(color) {
  if (!state.board) return [];
  for (const section of state.board.color_sections || []) {
    if (String(section.color || '') === String(color || '')) return section.rows || [];
  }
  return [];
}

function renderAdditionalPhotoAction(row) {
  const sku = String(row && row.sku || '');
  if (!sku) return '';
  if (state.additionalPhotoCheckInFlight[sku]) {
    return `<button type="button" class="btn btn-secondary photo-mini-btn photo-pull-btn photo-pull-btn-checking" disabled>Checking for additional photography</button>`;
  }
  if (state.additionalPhotoAvailabilityBySku[sku] !== true) return '';
  return `<button type="button" class="btn btn-secondary photo-mini-btn photo-pull-btn" onclick="pullAdditionalPhotographyForSku(event, '${escapeHtml(sku)}', this)">Pull additional photography for this SKU</button>`;
}

async function ensureAdditionalPhotoAvailabilityForColor(color, force=false) {
  if (!state.board || !state.loadedCollectionOptionId || !color) return;
  const rows = sectionRowsByColor(color);
  const skus = rows.map(r => String(r.sku || '')).filter(Boolean);
  const pending = skus.filter(sku => force || (!(sku in state.additionalPhotoAvailabilityBySku) && !state.additionalPhotoCheckInFlight[sku]));
  if (!pending.length) return;
  pending.forEach(sku => {
    state.additionalPhotoCheckInFlight[sku] = true;
  });
  renderBoard();
  try {
    const resp = await fetch('/api/check_additional_photography_for_skus', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({ skus: pending, existing_ids: (state.photography.items || []).map(x => x.id) })
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not check additional photography availability');
    const availability = data.availability || {};
    for (const sku of pending) {
      state.additionalPhotoAvailabilityBySku[sku] = !!availability[sku];
      delete state.additionalPhotoCheckInFlight[sku];
    }
    renderBoard();
  } catch (err) {
    for (const sku of pending) delete state.additionalPhotoCheckInFlight[sku];
    renderBoard();
    console.warn(err.message || String(err));
  }
}


function ensureNotesCapacity() {
  while ((state.notes || []).length < 3) {
    state.notes.push({id:`note-${Date.now()}-${Math.random().toString(36).slice(2,7)}`, text:''});
  }
  const last = state.notes[state.notes.length - 1];
  if (last && String(last.text || '').trim() !== '') {
    state.notes.push({id:`note-${Date.now()}-${Math.random().toString(36).slice(2,7)}`, text:''});
  }
}

function renderCollectionStatus() {
  const host = document.getElementById('collectionStatusMount');
  if (!host) return;
  if (state.workspace === 'product_imagery_onboarding') {
    if (state.board && ((state.board.workflow_statuses || []).length || (state.board.sync_states || []).length)) {
      const currentStatus = String(((state.board.workflow_statuses || [])[0] || 'App_Staged'));
      const currentSync = String(((state.board.sync_states || [])[0] || 'Do_not_sync_to_site'));
      const currentKey = `${currentStatus}||${currentSync}`;
      host.innerHTML = `<select id="pioWorkflowStateSelect" title="Workflow status and sync state for this onboarding board" class="collection-status-select pio-header-select pio-header-select-compact">${PIO_WORKFLOW_STATE_OPTIONS.map(opt => `<option value="${escapeHtml(opt.status)}||${escapeHtml(opt.sync)}" ${currentKey === `${opt.status}||${opt.sync}` ? 'selected' : ''}>${escapeHtml(opt.label)}</option>`).join('')}</select>`;
      const sel = document.getElementById('pioWorkflowStateSelect');
      if (sel) sel.addEventListener('change', updatePIOWorkflowState);
      return;
    }
    host.innerHTML = `<button type="button" class="collection-status-select pio-header-select pio-header-select-compact" disabled title="Workflow status control becomes active after a board is opened or created." style="cursor:default; opacity:1;">Staged -&gt; Live</button>`;
    return;
  }
  if (!state.collectionNotice || !state.collectionNotice.text) {
    host.innerHTML = '';
    return;
  }
  host.innerHTML = `<div class="collection-status-pill ${escapeHtml(state.collectionNotice.kind || 'notice')}">${escapeHtml(state.collectionNotice.text)}</div>`;
}


function pioWorkflowBadgeText() {
  if (!state.board || state.workspace !== 'product_imagery_onboarding') return 'Staged -> Live';
  const status = ((state.board.workflow_statuses || [])[0] || '').replaceAll('_', ' ');
  const sync = ((state.board.sync_states || [])[0] || '').replaceAll('_', ' ');
  return `${status || 'Draft'} / ${sync || 'Do not sync'}`;
}

function ensurePIOHeaderTemplate() {
  if (!String(state.onboarding.pastedRows || '').trim()) {
    state.onboarding.pastedRows = PIO_STEP_HEADER_ROW + '\n';
  }
}

function parsePIOPastedRows(rawText) {
  const text = String(rawText || '').replace(/\r\n/g, '\n').replace(/\r/g, '\n').replace(/\n+$/g, '');
  const lines = text.split('\n');
  if (!lines.length || !String(lines[0] || '').trim()) {
    throw new Error('Paste the STEP rows first.');
  }
  const headers = lines[0].split('\t').map(h => String(h || '').trim());
  const headerIndex = {};
  headers.forEach((h, i) => { if (h) headerIndex[h] = i; });
  for (const req of PIO_REQUIRED_HEADERS) {
    if (!(req in headerIndex)) throw new Error(`Missing required STEP Form column: ${req}`);
  }
  const salesIdx = headerIndex['Sales Channel'];
  const rows = [];
  const uniqueSales = [];
  const seenSales = new Set();
  for (let i = 1; i < lines.length; i += 1) {
    const parts = lines[i].split('\t');
    if (!parts.some(v => String(v || '').trim())) continue;
    const salesValue = salesIdx >= 0 && salesIdx < parts.length ? String(parts[salesIdx] || '').trim() : '';
    if (salesValue && !seenSales.has(salesValue.toLowerCase())) {
      seenSales.add(salesValue.toLowerCase());
      uniqueSales.push(salesValue);
    }
    rows.push(parts);
  }
  return {headers, rows, uniqueSales};
}

async function promptPIOSalesChannelMapping(uniqueValues) {
  const values = (uniqueValues || []).filter(v => String(v || '').trim());
  if (!values.length) return {};
  return new Promise((resolve, reject) => {
    const overlay = document.createElement('div');
    overlay.className = 'pio-modal-overlay';
    overlay.innerHTML = `
      <div class="pio-modal-card">
        <div class="pio-modal-title">Map Sales Channel values</div>
        <div class="muted" style="font-size:13px; margin-bottom:12px;">Before we commit onboarding metadata to Bynder, map each unique Sales Channel value from the pasted STEP rows to a real Bynder value.</div>
        <div class="pio-map-table">
          <div class="pio-map-head">Your value</div>
          <div class="pio-map-head">Bynder value</div>
          ${values.map((value, idx) => {
            const exact = PIO_BYNDER_SALES_CHANNEL_VALUES.find(v => v.toLowerCase() === String(value).trim().toLowerCase()) || '';
            return `
              <div class="pio-map-cell">${escapeHtml(value)}</div>
              <div class="pio-map-cell">
                <select class="pio-sales-map-select" data-source-value="${escapeHtml(value)}">
                  <option value="">Pick a Bynder value</option>
                  ${PIO_BYNDER_SALES_CHANNEL_VALUES.map(opt => `<option value="${escapeHtml(opt)}" ${exact === opt ? 'selected' : ''}>${escapeHtml(opt)}</option>`).join('')}
                </select>
              </div>
            `;
          }).join('')}
        </div>
        <div class="pio-modal-actions">
          <button type="button" class="btn btn-secondary" id="pioSalesMapCancel">Cancel</button>
          <button type="button" class="btn btn-primary" id="pioSalesMapApply">Apply mapping</button>
        </div>
      </div>
    `;
    document.body.appendChild(overlay);
    const close = () => { if (overlay && overlay.parentNode) overlay.parentNode.removeChild(overlay); };
    overlay.querySelector('#pioSalesMapCancel').addEventListener('click', () => { close(); reject(new Error('Sales Channel mapping cancelled.')); });
    overlay.addEventListener('click', (ev) => { if (ev.target === overlay) { close(); reject(new Error('Sales Channel mapping cancelled.')); } });
    overlay.querySelector('#pioSalesMapApply').addEventListener('click', () => {
      const mapping = {};
      let missing = '';
      overlay.querySelectorAll('.pio-sales-map-select').forEach(sel => {
        const source = String(sel.getAttribute('data-source-value') || '').trim();
        const target = String(sel.value || '').trim();
        if (!target && !missing) missing = source;
        if (source && target) mapping[source] = target;
      });
      if (missing) {
        alert(`Pick a Bynder Sales Channel value for: ${missing}`);
        return;
      }
      close();
      resolve(mapping);
    });
  });
}


async function updatePIOWorkflowState(event) {
  const value = String((event && event.target && event.target.value) || '').trim();
  if (!value || !state.board) return;
  const [workflow_status, sync_to_site] = value.split('||');
  const isGoingLive = workflow_status === 'App_Live' && sync_to_site === 'Do_sync_to_site';
  if (isGoingLive) {
    const okay = confirm('Are you sure you want to switch this board to App Live / Do sync to site? This means these assets will be available to be synced to the website once selected there.');
    if (!okay) { renderCollectionStatus(); return; }
  }
  try {
    const resp = await fetch('/api/onboarding/update_workflow_state', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({workflow_status, sync_to_site})});
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not update workflow state');
    applyBoardResponse(data, {keepPhotography:true, keepNotices:true});
    addAppNotice(isGoingLive ? 'This onboarding board is now marked App Live / Do sync to site.' : 'Workflow state updated for this onboarding board.', 'success');
  } catch (err) {
    alert(err.message || String(err));
    renderCollectionStatus();
  }
}


function rowCountsAsActive(row) {
  const status = String((row && row.product_status) || '').trim().toLowerCase();
  if (!status) return state.workspace === 'product_imagery_onboarding';
  return status === 'active';
}


function buildPIOPreflightNotices() {
  if (!state.board) return [];
  let firstMissingGrid = null;
  let firstMissing100 = null;
  let firstMissingSwatch = null;
  let firstMissingDimension = null;
  let firstCompilableSetDim = null;
  let firstMakeSquare = null;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      const actualAssets = (row.assets || []).filter(a => a && !a.is_marked_for_deletion && !a.is_empty_slot && !String(a.id || '').startsWith('empty::'));
      const hasGrid = actualAssets.some(a => String(a.slot_key || '') === 'SKU_grid' || String(a.current_position || '').endsWith('_grid'));
      const has100 = actualAssets.some(a => String(a.slot_key || '') === 'SKU_100' || String(a.current_position || '').endsWith('_100'));
      const hasSwatch = actualAssets.some(a => String(a.slot_key || '') === 'SKU_swatch' || String(a.current_position || '').endsWith('_swatch'));
      const hasDimension = actualAssets.some(a => String(a.slot_key || '') === 'SKU_dimension' || String(a.current_position || '').endsWith('_dimension'));
      if (!hasGrid && !firstMissingGrid) firstMissingGrid = {rowId: row.row_id, color: section.color, slot: 'SKU_grid'};
      if (!has100 && !firstMissing100) firstMissing100 = {rowId: row.row_id, color: section.color, slot: 'SKU_100'};
      if (!hasSwatch && !firstMissingSwatch) firstMissingSwatch = {rowId: row.row_id, color: section.color, slot: 'SKU_swatch'};
      if (!hasDimension && !firstMissingDimension) firstMissingDimension = {rowId: row.row_id, color: section.color, slot: 'SKU_dimension'};
      if (!hasDimension && row.set_dim_compile_ready && !firstCompilableSetDim) firstCompilableSetDim = {rowId: row.row_id, color: section.color, slot: 'SKU_dimension'};
      if (row.square_make_recommended && !firstMakeSquare) firstMakeSquare = {rowId: row.row_id, color: section.color, slot: 'SKU_square'};
    }
  }
  const notices = [];
  if (firstMissingGrid) notices.push({id:'preflight-missing-grid', kind:'error', text:'Missing grid: Jump to the first SKU missing a grid image.', rowId:firstMissingGrid.rowId, color:firstMissingGrid.color, slot:firstMissingGrid.slot});
  if (firstMissing100) notices.push({id:'preflight-missing-100', kind:'error', text:'Missing SKU_100: Jump to the first SKU missing its primary carousel image.', rowId:firstMissing100.rowId, color:firstMissing100.color, slot:firstMissing100.slot});
  if (firstMissingSwatch) notices.push({id:'preflight-missing-swatch', kind:'warning', text:'Missing swatch: Jump to the first SKU missing a swatch asset.', rowId:firstMissingSwatch.rowId, color:firstMissingSwatch.color, slot:firstMissingSwatch.slot});
  if (firstMissingDimension) notices.push({id:'preflight-missing-dimension', kind:'warning', text:'Missing dimensions: Jump to the first SKU missing a dimensions asset.', rowId:firstMissingDimension.rowId, color:firstMissingDimension.color, slot:firstMissingDimension.slot});
  if (firstCompilableSetDim) notices.push({id:'preflight-missing-set-dim', kind:'notice', text:'Set dim jumper opportunity: Jump to the first SKU where a set dim could be compiled.', rowId:firstCompilableSetDim.rowId, color:firstCompilableSetDim.color, slot:firstCompilableSetDim.slot});
  if (firstMakeSquare) notices.push({id:'preflight-make-square', kind:'notice', text:'Make square opportunity: Jump to the first SKU where a square room-shot image could probably be made.', rowId:firstMakeSquare.rowId, color:firstMakeSquare.color, slot:firstMakeSquare.slot});
  return notices;
}

function runPIOPreflightCheck() {
  if (!state.board) return;
  const notices = buildPIOPreflightNotices();
  state.preflightNotices = notices;
  if (notices.length) {
    const labels = notices.map(n => String(n.text || '').split(':')[0].trim().toLowerCase());
    addAppNotice(`Preflight check complete. ${notices.length} issue${notices.length === 1 ? '' : 's'} need attention. Review the jump notices for: ${labels.join(', ')}.`, 'warning');
  } else {
    addAppNotice('Preflight check complete. No missing critical assets or recommended square/set-dim fixes were found on this board.', 'success');
  }
  renderNotifications();
}


function clearPIOBoardView() {
  state.board = null;
  state.summary = null;
  state.loadedCollectionOptionId = '';
  state.onboarding.currentBoardId = '';
  state.onboarding.recentWarning = '';
  state.collectionNotice = {kind:'notice', text:''};
  renderLauncherPanel();
  renderBoard();
  renderCollectionStatus();
  saveUIState();
}

function renderLauncherPanel() {
  const host = document.getElementById('launcherPanelMount');
  if (!host) return;
  if (state.workspace === 'product_imagery_onboarding') {
    ensurePIOHeaderTemplate();
    const collectionOptions = (state.filteredCollections || state.collections || []).map(c => `<option value="${escapeHtml(c.label)}"></option>`).join('');
    const boardOptions = ['<option value=>Choose a board</option>'].concat((state.onboarding.boards || []).map(b => `<option value="${escapeHtml(b.label)}">${escapeHtml(b.label_display || b.label)} (${Number(b.row_count || 0)} SKUs)</option>`)).join('');
    const entryMode = state.onboarding.entryMode || 'start';
    const editorCollapsed = !!state.onboarding.editorCollapsed;
    host.innerHTML = `
      <div class="select-wrap" style="display:grid; gap:14px;">
        <div style="display:flex; align-items:center; justify-content:space-between; gap:12px; flex-wrap:wrap;">
          <div class="pio-top-actions">
            <div class="pio-mode-tabs" style="display:inline-flex; gap:0; flex-wrap:nowrap; border:1px solid var(--rf-border); border-radius:14px; overflow:hidden; background:#f6f0fb; box-shadow: inset 0 0 0 1px rgba(255,255,255,.45);">
              <button type="button" class="btn ${entryMode === 'start' ? 'btn-primary' : 'btn-secondary'}" id="pioStartModeBtn" style="border-radius:0; min-width:132px; box-shadow:none; ${entryMode === 'start' ? '' : 'background:#f6f0fb; color:var(--rf-purple);'}">Create Placeholders</button>
              <button type="button" class="btn ${entryMode === 'open' ? 'btn-primary' : 'btn-secondary'}" id="pioOpenModeBtn" style="border-radius:0; min-width:164px; box-shadow:none; border-left:1px solid var(--rf-border); ${entryMode === 'open' ? '' : 'background:#f6f0fb; color:var(--rf-purple);'}">Open Product Imagery Board</button>
            </div>
            <div class="collection-status-mount" id="collectionStatusMount" aria-label="Workflow status control"></div>
          </div>
        </div>
        ${entryMode === 'start' ? `
          <div style="display:grid; gap:12px;">
            <div style="display:flex; align-items:center; justify-content:space-between; gap:12px;">
              <div class="muted" style="font-size:13px; font-weight:700;">Board setup</div>
              <button type="button" class="btn btn-secondary btn-compact" id="pioToggleEditorBtn">${editorCollapsed ? 'Expand setup' : 'Collapse setup'}</button>
            </div>
            ${editorCollapsed ? `<div class="muted" style="font-size:13px;">Board setup is collapsed to save space. Expand it to add SKUs to a Product Collection.</div>` : `
            ${state.onboarding.creating ? `<div style="display:flex; align-items:center; gap:10px; padding:12px 14px; border-radius:14px; border:1px solid #cfe4d1; background:#eef8ef; color:#245b2f; font-weight:700; box-shadow:0 8px 18px rgba(36,91,47,.08);"><span class="spinner" style="width:18px; height:18px; border-width:2px; border-top-color:#2d8f52;"></span><span>${escapeHtml(state.onboarding.busyText || 'Working on your onboarding board...')}</span></div>` : ``}
            <div class="muted" style="font-size:13px;">Step 1: enter the Product Collection value for the new board. You can type your own value or choose from existing suggestions.</div>
            <div style="display:grid; grid-template-columns:minmax(260px, 1fr) auto; gap:12px; align-items:end;">
              <div>
                <label class="small">Product Collection</label>
                <input type="text" id="pioCollectionInput" list="pioCollectionOptions" placeholder="Type Product Collection name" value="${escapeHtml(state.onboarding.collectionLabel || '')}" />
                <datalist id="pioCollectionOptions">${collectionOptions}</datalist>
              </div>
              <div></div>
            </div>
            <div style="display:grid; gap:8px;">
              <div class="muted" style="font-size:13px;">Step 2: copy the header row into a blank Google Sheet or Excel sheet, paste your STEP data underneath it, then copy the completed rows from the sheet and paste them back into this box. Required columns: <strong>SKU</strong> and <strong>Product Name</strong>. Optional columns: Product Color, Sales Channel, Components, Length, Width, Height, and Features.</div>
              <textarea id="pioPasteInput" rows="8" style="width:100%; border:1px solid var(--rf-border); border-radius:12px; padding:10px 12px; resize:vertical; font-family:Consolas, monospace;" placeholder="Paste STEP Form rows here" ${state.onboarding.creating ? "disabled" : ""}>${escapeHtml(state.onboarding.pastedRows || '')}</textarea>
            </div>
            <div style="display:flex; align-items:center; justify-content:space-between; gap:12px; flex-wrap:wrap;">
              <div class="muted" style="font-size:12px;">Blank rows are ignored. If your Product Collection value does not exist in Bynder yet, the app will create it for you.</div>
              <button type="button" class="btn btn-primary" id="pioCreateBtn" ${state.onboarding.creating ? "disabled" : ""}>${state.onboarding.creating ? "Creating..." : "Create Placeholders"}</button>
            </div>`}
          </div>
        ` : `
          <div style="display:grid; gap:12px;">
            <div class="muted" style="font-size:13px;">Open an existing Product Imagery Onboarding board from Bynder. Draft and live boards can both be reopened here.</div>
            <div style="display:grid; grid-template-columns:minmax(280px, 1fr) auto auto; gap:12px; align-items:end;">
              <div>
                <label class="small">Existing Board</label>
                <select id="pioBoardSelect" size="1">${boardOptions}</select>
              </div>
              <button type="button" class="btn btn-primary ${state.onboarding.openingBoard ? 'btn-reload-flashing' : ''}" id="pioOpenBtn" ${state.onboarding.openingBoard ? 'disabled' : ''}>${state.onboarding.openingBoard ? 'Opening...' : 'Open Board'}</button>
              <button type="button" class="btn btn-preflight btn-compact" id="pioPreflightBtnTop" ${!state.board ? 'disabled' : ''}>Preflight Check</button>
            </div>
            <div class="muted" style="font-size:12px;">Use Preflight Check before marking a board live.</div>
          </div>
        `}
      </div>
    `;
    const startBtn = document.getElementById('pioStartModeBtn');
    const openModeBtn = document.getElementById('pioOpenModeBtn');
    if (startBtn) startBtn.addEventListener('click', () => { state.onboarding.entryMode = 'start'; renderLauncherPanel(); });
    if (openModeBtn) openModeBtn.addEventListener('click', () => { state.onboarding.entryMode = 'open'; renderLauncherPanel(); });
    const toggleEditorBtn = document.getElementById('pioToggleEditorBtn');
    if (toggleEditorBtn) toggleEditorBtn.addEventListener('click', () => { state.onboarding.editorCollapsed = !state.onboarding.editorCollapsed; renderLauncherPanel(); });
    const collectionInput = document.getElementById('pioCollectionInput');
    if (collectionInput) collectionInput.addEventListener('input', e => { state.onboarding.collectionLabel = e.target.value || ''; });
    const pasteInput = document.getElementById('pioPasteInput');
    if (pasteInput) pasteInput.addEventListener('input', e => { state.onboarding.pastedRows = e.target.value || ''; });
    const createBtn = document.getElementById('pioCreateBtn');
    if (createBtn) createBtn.addEventListener('click', createPIOBoard);
    const openBtn = document.getElementById('pioOpenBtn');
    if (openBtn) openBtn.addEventListener('click', openPIOBoard);
    const preflightBtn = document.getElementById('pioPreflightBtn');
    if (preflightBtn) preflightBtn.addEventListener('click', runPIOPreflightCheck);
    const preflightBtnTop = document.getElementById('pioPreflightBtnTop');
    if (preflightBtnTop) preflightBtnTop.addEventListener('click', runPIOPreflightCheck);
    renderCollectionStatus();
    return;
  }

  host.innerHTML = `
    <div class="select-wrap">
      <div class="inline-launch-group">
        <div class="launch-field">
          <label class="small">Search Product Collection</label>
          <input type="text" id="collectionFilter" placeholder="Type any part of the collection name" />
        </div>
        <div class="launch-field">
          <label class="small">Product Collection</label>
          <select id="collectionSelect" size="1"></select>
        </div>
        <div class="launch-button-col">
          <div class="launch-button-stack">
            <button type="button" class="btn btn-primary" id="launchBtn">Launch Collection</button>
          </div>
        </div>
      </div>
      <div class="launcher-lower-row">
        <div class="launcher-checkbox-row">
          <label class="mode-option" style="display:flex; align-items:center; gap:6px;"><input type="checkbox" id="hideInactiveToggle" /> Hide inactive SKUs</label>
        </div>
        <div class="collection-status-mount" id="collectionStatusMount"></div>
        <div class="launcher-random-row">
          <button type="button" class="btn btn-secondary btn-compact" id="launchRandomBtn">Launch Random Collection</button>
        </div>
      </div>
    </div>
  `;
  bindRegularLauncherEvents();
  renderCollectionStatus();
  renderCollectionSelect();
}

async function switchWorkspace(workspace) {
  const nextWs = workspace === 'product_imagery_onboarding' ? 'product_imagery_onboarding' : 'content_refresher';
  state.workspace = nextWs;
  renderDocumentTitle();
  state.board = null;
  state.summary = null;
  state.photography.items = [];
  state.onboarding.recentWarning = '';
  if (!state.onboarding.entryMode) state.onboarding.entryMode = 'start';
  if (!String(state.onboarding.pastedRows || '').trim()) state.onboarding.pastedRows = PIO_STEP_HEADER_ROW + '\n';
  renderBrandPanel();
  renderLauncherPanel();
  renderBoard();
  if (nextWs === 'product_imagery_onboarding') {
    state.onboarding.currentBoardId = '';
    state.loadedCollectionOptionId = '';
    await loadOnboardingBoards();
    ensureBynderCollectionsLoaded(false);
    state.collectionNotice = {kind:'notice', text:''};
    renderCollectionStatus();
  } else {
    state.collectionNotice = {kind:'notice', text:(state.collections || []).length ? `${state.collections.length.toLocaleString()} Product Collection options loaded.` : 'Loading Product Collection options...'}
    renderCollectionStatus();
  }
}

async function loadOnboardingBoards() {
  try {
    const resp = await fetch('/api/onboarding/boards');
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not load onboarding boards');
    state.onboarding.boards = data.boards || [];
  } catch (err) {
    state.onboarding.boards = [];
    addAppNotice(err.message || String(err), 'error');
  }
  renderLauncherPanel();
}

function startPIOCreateBusySequence() {
  const steps = [
    'Checking your Product Collection value and STEP rows...',
    'Mapping Sales Channel values to Bynder options...',
    'Preparing your Product Collection in Bynder...',
    'Creating placeholder grid anchors in Bynder...',
    'Waiting for placeholder metadata to settle in Bynder...',
    'Building your product imagery onboarding board...'
  ];
  clearPIOCreateBusySequence();
  state.onboarding.busyStepIndex = 0;
  state.onboarding.busyText = steps[0];
  state.collectionNotice = {kind:'notice', text: steps[0]};
  renderCollectionStatus();
  renderLauncherPanel();
  state.onboarding.busyTimer = window.setInterval(() => {
    if (!state.onboarding.creating) return;
    state.onboarding.busyStepIndex = Math.min((state.onboarding.busyStepIndex || 0) + 1, steps.length - 1);
    const nextText = steps[state.onboarding.busyStepIndex] || steps[steps.length - 1];
    state.onboarding.busyText = nextText;
    state.collectionNotice = {kind:'notice', text: nextText};
    renderCollectionStatus();
    renderLauncherPanel();
  }, 2200);
}

function clearPIOCreateBusySequence() {
  if (state.onboarding.busyTimer) {
    window.clearInterval(state.onboarding.busyTimer);
    state.onboarding.busyTimer = null;
  }
}

async function createPIOBoard() {
  const input = document.getElementById('pioCollectionInput');
  const collection_label = String((input ? input.value : state.onboarding.collectionLabel) || '').trim();
  const pasted_rows = String(state.onboarding.pastedRows || '');
  if (!collection_label) { alert('Enter a Product Collection value first.'); return; }
  if (!String(pasted_rows || '').trim()) { alert('Paste the STEP rows first.'); return; }
  try {
    if (state.board) {
      const okay = confirm('Launching a new board will remove the current board from your screen and replace it with the new one. Your Bynder assets will stay where they are. Continue?');
      if (!okay) return;
    }
    const parsed = parsePIOPastedRows(pasted_rows);
    if (!parsed.rows.length) { alert('Paste at least one STEP row under the headers.'); return; }
    const sales_channel_map = await promptPIOSalesChannelMapping(parsed.uniqueSales);
    state.onboarding.creating = true;
    startPIOCreateBusySequence();
    const resp = await fetch('/api/onboarding/create_board', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({collection_label, pasted_rows, sales_channel_map})});
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not create Product Imagery Onboarding board');
    state.workspace = 'product_imagery_onboarding';
    state.board = data.board || null;
    state.loadedCollectionOptionId = data.collection_option_id || ((data.board && (data.board.collection || {}).id) || '');
    state.onboarding.collectionLabel = collection_label;
    state.summary = data.summary || null;
    state.onboarding.currentBoardId = state.loadedCollectionOptionId || (((state.board || {}).collection || {}).id || '');
    state.onboarding.recentWarning = '';
    state.onboarding.editorCollapsed = true;
    state.collectionNotice = {kind:'success', text:`Product Imagery Onboarding board created for ${(state.board && (state.board.collection_label || ((state.board.collection || {}).label))) || 'collection'}.`};
    renderBrandPanel();
    renderLauncherPanel();
    renderBoard();
    saveUIState();
    if (Array.isArray(data.warnings) && data.warnings.length) addAppNotice(data.warnings[0], 'notice');
    await loadOnboardingBoards();
  } catch (err) {
    alert(err.message || String(err));
  } finally {
    state.onboarding.creating = false;
    clearPIOCreateBusySequence();
    state.onboarding.busyText = '';
    renderLauncherPanel();
  }
}

async function openPIOBoardById(collection_label, force_refresh=false) {
  if (!collection_label) { alert('Choose a Product Imagery Onboarding board to open.'); return; }
  try {
    state.onboarding.openingBoard = true;
    const loadingText = force_refresh ? 'Reloading Product Imagery Onboarding board from Bynder...' : 'Opening Product Imagery Onboarding board from Bynder...';
    state.collectionNotice = {kind:'notice', text:loadingText};
    addAppNotice(loadingText, 'notice');
    renderCollectionStatus();
    renderLauncherPanel();
    setReloadButtonFlashing(!!force_refresh);
    const resp = await fetch('/api/onboarding/load_board', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({collection_label, force_refresh})});
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not open Product Imagery Onboarding board');
    state.workspace = 'product_imagery_onboarding';
    state.board = data.board || null;
    state.loadedCollectionOptionId = collection_label;
    state.summary = data.summary || null;
    state.onboarding.currentBoardId = collection_label;
    state.onboarding.recentWarning = data.recent_warning || '';
    state.onboarding.editorCollapsed = true;
    state.collectionNotice = {kind:'success', text:`Opened Product Imagery Onboarding board for ${(state.board && (state.board.collection_label || ((state.board.collection || {}).label))) || 'collection'}.`};
    renderBrandPanel();
    renderLauncherPanel();
    renderBoard();
    saveUIState();
    if (state.onboarding.recentWarning) addAppNotice(state.onboarding.recentWarning, 'notice');
  } catch (err) {
    alert(err.message || String(err));
  } finally {
    state.onboarding.openingBoard = false;
    setReloadButtonFlashing(false);
    renderLauncherPanel();
  }
}

async function openPIOBoard() {
  const select = document.getElementById('pioBoardSelect');
  const collection_label = select ? select.value : '';
  return openPIOBoardById(collection_label, false);
}

async function goLivePIOBoard() {
  if (!state.board) return;
  if (!confirm('Go live? This will change Sync to Site from Do not sync to site to Do sync to site and set Workflow Status to App_Live.')) return;
  try {
    state.collectionNotice = {kind:'notice', text:'Reviewing and promoting this onboarding board to live...'};
    renderCollectionStatus();
    const resp = await fetch('/api/onboarding/go_live', {method:'POST'});
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not promote board to live');
    state.board = data.board || state.board;
    state.summary = data.summary || null;
    state.collectionNotice = {kind:'success', text:`Board is now live. Updated ${Number(data.updated_count || 0)} assets.`};
    renderLauncherPanel();
    renderBoard();
    await loadOnboardingBoards();
  } catch (err) {
    alert(err.message || String(err));
  } finally {
    state.photography.prep.addingVersion = false;
    renderPhotographyPanel();
  }
}

function renderNotesPanel() {
  const panel = document.getElementById('myNotesPanel');
  const host = document.getElementById('myNotesList');
  const btn = document.getElementById('toggleNotesBtn');
  if (!panel || !host || !btn) return;
  ensureNotesCapacity();
  panel.classList.toggle('open', !!state.notesOpen);
  btn.textContent = state.notesOpen ? 'Collapse' : 'Expand';
  host.innerHTML = (state.notes || []).map(note => `
    <div class="note-row">
      <input class="note-check" type="checkbox" title="Complete and remove note" onchange="completeNote('${escapeHtml(note.id)}')" />
      <textarea placeholder="Type a note..." oninput="updateNote('${escapeHtml(note.id)}', this.value)">${escapeHtml(note.text || '')}</textarea>
    </div>
  `).join('');
}

function updateNote(id, value) {
  const note = (state.notes || []).find(n => n.id === id);
  if (note) note.text = value || '';
  ensureNotesCapacity();
}

function completeNote(id) {
  state.notes = (state.notes || []).filter(n => n.id !== id);
  ensureNotesCapacity();
  }


function boardFingerprint(board) {
  if (!board) return '';
  const parts = [];
  for (const section of board.color_sections || []) {
    parts.push(`section:${section.color || ''}`);
    for (const row of section.rows || []) {
      parts.push(`row:${row.row_id || ''}:${row.sku || ''}`);
      for (const asset of row.assets || []) {
        parts.push([
          asset.id || '',
          asset.current_position || '',
          asset.slot_key || '',
          String(asset.deliverable_override || asset.deliverable || ''),
          asset.pending_upload ? '1' : '0',
          asset.is_marked_for_deletion ? '1' : '0'
        ].join(':'));
      }
    }
  }
  return parts.join('|');
}

function setWaitOverlay(open, statusText='', options={}) {
  state.waitFlow.open = !!open;
  const overlay = document.getElementById('waitOverlay');
  const status = document.getElementById('waitStatus');
  const titleEl = document.getElementById('waitOverlayTitle');
  const bodyEl = document.getElementById('waitOverlayBody');
  const titleText = (options && options.title) ? String(options.title) : 'Giving Bynder a moment...';
  const bodyText = (options && options.body) ? String(options.body) : 'Your updates went through. Waiting 30 seconds before checking for refreshed metadata.';
  if (overlay) overlay.classList.toggle('open', !!open);
  if (titleEl) titleEl.textContent = titleText;
  if (bodyEl) bodyEl.textContent = bodyText;
  if (status && statusText) status.textContent = statusText;
  if (open && options && options.miniGame) {
    if (!state.waitFlow.miniGameOpen) startWaitMiniGame();
  } else {
    stopWaitMiniGame();
  }
}

function setReloadButtonFlashing(isFlashing) {
  const btn = document.getElementById('reloadBtn');
  if (btn) btn.classList.toggle('btn-reload-flashing', !!isFlashing);
}

function startMessagePolling() {
  if (state.messagePollTimer) return;
  refreshMessages();
  state.messagePollTimer = setInterval(refreshMessages, 3000);
}

function stopMessagePolling() {
  if (!state.messagePollTimer) return;
  clearInterval(state.messagePollTimer);
  state.messagePollTimer = null;
}

function setIdleModalOpen(isOpen) {
  state.idle.modalOpen = !!isOpen;
  const overlay = document.getElementById('idleOverlay');
  if (overlay) overlay.classList.toggle('open', !!isOpen);
}

function resetIdleTimer() {
  state.idle.lastActivityAt = Date.now();
}

function closeIdleModal() {
  setIdleModalOpen(false);
  resetIdleTimer();
}

function maybeWarnOnIdleReturn() {
  if (!state.board || !state.loadedCollectionOptionId) {
    resetIdleTimer();
    return false;
  }
  if (state.idle.modalOpen || state.waitFlow.open) {
    return true;
  }
  const now = Date.now();
  const idleFor = now - (state.idle.lastActivityAt || 0);
  if (idleFor >= state.idle.thresholdMs) {
    setIdleModalOpen(true);
    state.idle.lastActivityAt = now;
    return true;
  }
  state.idle.lastActivityAt = now;
  return false;
}

function bindIdleActivityWatchers() {
  const handler = () => {
    maybeWarnOnIdleReturn();
  };
  ['pointerdown', 'keydown', 'input', 'change', 'drop'].forEach(evt => {
    document.addEventListener(evt, handler, true);
  });
  document.addEventListener('visibilitychange', () => {
    if (document.visibilityState === 'visible') {
      maybeWarnOnIdleReturn();
    }
  });
}

async function delay(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}


function getGameIconMarkup(ready=false, compact=false) {
  const cls = ready ? 'ready' : 'empty';
  const title = ready ? 'Cleanup Challenge candidates ready' : 'Cleanup Challenge queue is still empty';
  return `<div class="game-mode-icon ${cls}" title="${escapeHtml(title)}"><span class="tool-duo"><span class="tool hammer">🔨</span><span class="tool wrench">🔧</span></span></div>`;
}

function stopWaitMiniGame() {
  const gameEl = document.getElementById('waitMiniGame');
  if (gameEl) gameEl.classList.remove('open');
  if (state.waitFlow.miniGameTimer) {
    clearInterval(state.waitFlow.miniGameTimer);
    state.waitFlow.miniGameTimer = null;
  }
  state.waitFlow.miniGameOpen = false;
}

function moveWaitMiniBunny() {
  const board = document.getElementById('waitMiniBoard');
  const bunny = document.getElementById('waitMiniBunny');
  if (!board || !bunny) return;
  const pad = 12;
  const maxLeft = Math.max(0, board.clientWidth - bunny.offsetWidth - (pad * 2));
  const maxTop = Math.max(0, board.clientHeight - bunny.offsetHeight - (pad * 2));
  const left = Math.round(Math.random() * maxLeft) + pad;
  const top = Math.round(Math.random() * maxTop) + pad;
  bunny.style.left = `${left}px`;
  bunny.style.top = `${top}px`;
}

function startWaitMiniGame() {
  const gameEl = document.getElementById('waitMiniGame');
  const scoreEl = document.getElementById('waitMiniScore');
  const hintEl = document.getElementById('waitMiniHint');
  if (!gameEl || !scoreEl) return;
  stopWaitMiniGame();
  state.waitFlow.miniGameOpen = true;
  state.waitFlow.miniGameScore = 0;
  scoreEl.textContent = '0';
  if (hintEl) hintEl.textContent = 'Big floof on deck. Slow enough to boop. Emotionally available.';
  gameEl.classList.add('open');
  moveWaitMiniBunny();
  state.waitFlow.miniGameTimer = window.setInterval(moveWaitMiniBunny, 2400);
}

function boopWaitMiniBunny(evt) {
  if (evt) {
    evt.stopPropagation();
    evt.preventDefault();
  }
  if (!state.waitFlow.miniGameOpen) return;
  state.waitFlow.miniGameScore = Number(state.waitFlow.miniGameScore || 0) + 1;
  const scoreEl = document.getElementById('waitMiniScore');
  const hintEl = document.getElementById('waitMiniHint');
  const bunny = document.getElementById('waitMiniBunny');
  if (scoreEl) scoreEl.textContent = String(state.waitFlow.miniGameScore);
  if (bunny) bunny.style.transform = 'scale(0.92)';
  if (hintEl) {
    if (state.waitFlow.miniGameScore >= 40) hintEl.textContent = 'At this point the floof reports to you.';
    else if (state.waitFlow.miniGameScore >= 32) hintEl.textContent = 'Unhinged boop stamina. Historic work.';
    else if (state.waitFlow.miniGameScore >= 26) hintEl.textContent = 'The bunny union is drafting a strongly worded memo.';
    else if (state.waitFlow.miniGameScore >= 21) hintEl.textContent = 'This is now performance art. Very floof-forward.';
    else if (state.waitFlow.miniGameScore >= 15) hintEl.textContent = 'Legendary floof wrangler. Extremely boop-forward.';
    else if (state.waitFlow.miniGameScore >= 10) hintEl.textContent = 'Honestly? Clinical levels of boop accuracy.';
    else if (state.waitFlow.miniGameScore >= 6) hintEl.textContent = 'You are absolutely handling this floof.';
    else if (state.waitFlow.miniGameScore >= 3) hintEl.textContent = 'Nice. Very boopable.';
    else hintEl.textContent = 'Confirmed boop. Morale is excellent.';
  }
  window.setTimeout(() => {
    if (bunny) bunny.style.transform = '';
    if (state.waitFlow.miniGameOpen) moveWaitMiniBunny();
  }, 520);
}

function toggleGameLeaderboard() {
  state.game.leaderboardOpen = !state.game.leaderboardOpen;
  renderBrandPanel();
}


function renderDocumentTitle() {
  try {
    const title = state.workspace === 'product_imagery_onboarding' ? 'Product Imagery Onboarding' : 'Content Refresher';
    document.title = title;
  } catch (err) {}
}

function renderBrandPanel() {
  const panel = document.getElementById('brandPanel');
  const host = document.getElementById('brandPanelMount');
  if (!panel || !host) return;
  renderDocumentTitle();
  const g = state.game || {};
  if (!g.active) {
    panel.classList.remove('game-active');
    const workspace = state.workspace || 'content_refresher';
    const title = workspace === 'product_imagery_onboarding' ? 'Product Imagery Onboarding' : 'Content Refresher';
    const sub = workspace === 'product_imagery_onboarding'
      ? 'Draft and stage new Product Collection imagery using placeholder grid anchors and shared workflow metadata.'
      : 'Live Bynder board for Product Collection image cleanup, slotting, and safe staged updates.';
    host.innerHTML = `
      <div class="workspace-switch-row" style="position:relative;">
        <h1>${escapeHtml(title)}</h1>
        <button type="button" class="workspace-menu-btn" id="workspaceMenuBtn" aria-label="Switch workspace">▾</button>
        <div class="workspace-menu" id="workspaceMenu" style="display:none;">
          <button type="button" class="workspace-menu-item ${workspace === 'content_refresher' ? 'active' : ''}" data-workspace="content_refresher" style="color:#5a2d86 !important; background:${workspace === 'content_refresher' ? '#f4edf9' : 'transparent'};">Content Refresher</button>
          <button type="button" class="workspace-menu-item ${workspace === 'product_imagery_onboarding' ? 'active' : ''}" data-workspace="product_imagery_onboarding" style="color:#5a2d86 !important; background:${workspace === 'product_imagery_onboarding' ? '#f4edf9' : 'transparent'};">Product Imagery Onboarding</button>
        </div>
      </div>
      <div class="sub">${escapeHtml(sub)}</div>
    `;
    const menuBtn = document.getElementById('workspaceMenuBtn');
    const menu = document.getElementById('workspaceMenu');
    if (menuBtn && menu) {
      menuBtn.addEventListener('click', (ev) => {
        ev.stopPropagation();
        menu.style.display = menu.style.display === 'block' ? 'none' : 'block';
      });
      menu.querySelectorAll('[data-workspace]').forEach(btn => btn.addEventListener('click', (ev) => {
        const next = ev.currentTarget.getAttribute('data-workspace') || 'content_refresher';
        menu.style.display = 'none';
        switchWorkspace(next);
      }));
      document.addEventListener('click', () => { if (menu) menu.style.display = 'none'; }, {once:true});
    }
    return;
  }
  panel.classList.add('game-active');
  const currentLabel = escapeHtml((((g.current || {}).collection || {}).label || ''));
  const currentColor = escapeHtml((g.current || {}).color || '');
  const leaderboardRows = (g.leaderboard || []).slice(0,12).map((entry, idx) => `<div class="brand-mini-leader-row"><span>${idx + 1}. ${escapeHtml(entry.user || 'player')}</span><strong>${Number(entry.score || 0)}</strong></div>`).join('');
  const leaderboardOpen = !!g.leaderboardOpen;
  host.innerHTML = `
    <div class="brand-mini-game">
      <div class="brand-mini-top">
        ${getGameIconMarkup(Number(g.queueLength || 0) > 0)}
        <div class="brand-mini-title-wrap">
          <div class="brand-mini-kicker">Game mode</div>
          <div class="brand-mini-title">Cleanup Challenge</div>
          <div class="brand-mini-sub">Real fixes, live score, next board ready.</div>
        </div>
      </div>
      <div class="brand-mini-grid">
        <div class="brand-mini-pill"><div class="k">Player</div><div class="v">${escapeHtml(g.username || 'player')}</div></div>
        <div class="brand-mini-pill"><div class="k">Score</div><div class="v">${Number(g.score || 0)}</div></div>
        <div class="brand-mini-pill"><div class="k">Queue</div><div class="v">${Number(g.queueLength || 0)}</div></div>
        <div class="brand-mini-pill wide"><div class="k">Current challenge</div><div class="v">${currentLabel || 'Loading...'}</div><div class="s">${currentColor || 'Finding a colorway with work to tackle'}</div></div>
      </div>
      <div class="brand-mini-actions">
        <button type="button" class="game-mini-btn primary" onclick="launchCleanupChallenge()">Next</button>
        <button type="button" class="game-mini-btn pass" onclick="passCleanupChallenge()">Pass</button>
        <button type="button" class="game-mini-btn exit" onclick="exitCleanupChallenge()">Leave</button>
      </div>
      <div class="brand-mini-leader">
        <button type="button" class="brand-mini-leader-toggle" onclick="toggleGameLeaderboard()">
          <span class="brand-mini-leader-title">Workshop leaderboard</span>
          <span class="brand-mini-leader-caret">${leaderboardOpen ? '&#9662;' : '&#9656;'}</span>
        </button>
        ${leaderboardOpen ? `<div class="brand-mini-leader-rows">${leaderboardRows || `<div class="brand-mini-leader-row"><span>No scores yet</span><strong>0</strong></div>`}</div>` : ''}
      </div>
    </div>
  `;
}

function renderGameModesPanel() {
  const host = document.getElementById('gameModesPanel');
  if (!host) return;
  const g = state.game || {};
  const ready = Number(g.queueLength || 0) > 0;
  const title = g.loading ? 'Cleanup Challenge is loading' : (ready ? 'Cleanup Challenge candidates ready' : 'Cleanup Challenge is scanning for candidates');
  host.innerHTML = `
    <div class="game-mode-icon-only">
      <button type="button" onclick="launchCleanupChallenge()" title="${escapeHtml(title)}" aria-label="Launch Cleanup Challenge">
        ${getGameIconMarkup(ready)}
      </button>
    </div>
  `;
}

function syncGameState(game) {
  if (!game) return;
  state.game.active = !!game.active;
  state.game.queueLength = Number(game.queue_length || game.queueLength || 0);
  state.game.score = Number(game.score || 0);
  state.game.username = String(game.username || state.game.username || '');
  state.game.current = game.current || null;
  state.game.leaderboard = game.leaderboard || state.game.leaderboard || [];
  state.game.leaderboardOpen = !!state.game.leaderboardOpen;
  renderGameModesPanel();
  renderBrandPanel();
}

function applyBoardResponse(data, options={}) {
  state.board = data.board;
  state.summary = data.summary;
  if (data && data.workspace) state.workspace = data.workspace;
  state.collapsedColors = {};
  state.assetModeDirty = false;
  state.assetModeDirtyRows = {};
  const select = document.getElementById('collectionSelect');
  if (select && state.board && state.board.collection && state.board.collection.id) {
    select.value = state.board.collection.id;
  }
  if (!options.keepPhotography) {
    state.photography.items = [];
    state.photography.color = '';
    state.photoSkuOpen = {};
  }
  if (!options.keepNotices) state.appNotices = [];
  state.preflightNotices = [];
  if (data.game) syncGameState(data.game);
  renderBoard();
  if (!options.keepPhotography && data.photography_autoload) {
    loadPhotographyPayloadToState(data.photography_autoload, (data.random_launch || {}).color || '');
  }
  updateStickyOffsets();
  closeIdleModal();
}

async function refreshGameStatus() {
  try {
    const resp = await fetch('/api/game/status');
    const data = await resp.json();
    if (resp.ok) syncGameState(data);
  } catch (_) {}
}

function showGameCelebration(title, text) {
  const host = document.getElementById('gameCelebration');
  if (!host) return;
  host.innerHTML = `<div class="game-celebration-card"><h3>${escapeHtml(title || 'Nice work!')}</h3><p>${escapeHtml(text || '')}</p></div>`;
  host.classList.add('show');
  setTimeout(() => host.classList.remove('show'), 1400);
}

async function launchCleanupChallenge() {
  const g = state.game || {};
  if (state.workspace === 'product_imagery_onboarding') {
    await switchWorkspace('content_refresher');
  }
  if (!g.active) {
    const okay = confirm('Launch Cleanup Challenge? You will leave the regular workspace and jump into a workshop-style board with real content issues to fix, live scoring, and fresh challenge boards queued in the background.');
    if (!okay) return;
  }
  try {
    await fetch('/api/game/ensure_queue', {method:'POST'}).then(r => r.json()).then(data => { if (!data.error) syncGameState(data); });
  } catch (_) {}
  state.game.loading = true;
  renderGameModesPanel();
  renderBrandPanel();
  setWaitOverlay(true, g.active ? 'Checking this board and loading the next Cleanup Challenge...' : 'Loading your first Cleanup Challenge board...', {miniGame:true, title:'Loading Cleanup Challenge...', body: g.active ? 'First we will score this board against the latest Bynder state, then we will grab the next challenge board.' : 'Hang tight while we spin up your first Cleanup Challenge board and get it ready.'});
  try {
    if (g.active) {
      const reloadResp = await fetch('/api/game/reload_current', {method:'POST'});
      const reloadData = await reloadResp.json().catch(() => ({}));
      if (reloadResp.ok) {
        const rg = reloadData.game || {};
        if (Number(rg.resolved || 0) > 0) addAppNotice(`Nice. ${rg.resolved} issue${Number(rg.resolved) === 1 ? '' : 's'} resolved and scored before loading the next board.`, 'success');
      }
    }
    const url = g.active ? '/api/game/next' : '/api/game/launch';
    const controller = new AbortController();
    const timeoutId = window.setTimeout(() => controller.abort(), 45000);
    const resp = await fetch(url, {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({action:'launch'}), signal: controller.signal});
    window.clearTimeout(timeoutId);
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not launch Cleanup Challenge');
    applyBoardResponse(data);
    showGameCelebration('Cleanup Challenge', 'Fresh board loaded. Go score some fixes.');
    scheduleGameQueueEnsure();
  } catch (err) {
    const msg = (err && err.name === 'AbortError')
      ? 'Cleanup Challenge took too long to load. The queue may still be warming up, so please try again in a moment.'
      : (err.message || String(err));
    alert(msg);
  }
  finally {
    state.game.loading = false;
    setWaitOverlay(false);
    renderGameModesPanel();
    renderBrandPanel();
  }
}

async function passCleanupChallenge() {
  if (!state.game.active) return;
  if (!confirm('Pass on this challenge and load a new one?')) return;
  state.game.loading = true;
  renderGameModesPanel();
  renderBrandPanel();
  setWaitOverlay(true, 'Skipping this board and loading the next Cleanup Challenge...', {
    miniGame:true,
    title:'Passing this Cleanup Challenge...',
    body:'We are skipping this board, leaving your score as-is, and grabbing the next challenge.'
  });
  try {
    const resp = await fetch('/api/game/next', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({action:'pass'})});
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not load the next challenge');
    applyBoardResponse(data);
    showGameCelebration('Passed', 'Showing the next board.');
    scheduleGameQueueEnsure();
  } catch (err) { alert(err.message || String(err)); }
  finally {
    state.game.loading = false;
    setWaitOverlay(false);
    renderGameModesPanel();
    renderBrandPanel();
  }
}

async function exitCleanupChallenge() {
  if (!state.game.active) return;
  if (!confirm('Leave Cleanup Challenge and head back to the regular workspace?')) return;
  try {
    const resp = await fetch('/api/game/next', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({action:'exit'})});
    const data = await resp.json();
    if (resp.ok) syncGameState(data.game || {});
    showGameCelebration('Workshop paused', 'You are back in the regular workspace.');
  } catch (_) {}
}

function scheduleGameQueueEnsure(force=false) {
  if (!(state.game)) return;
  if (state.commitInFlight) return;
  if (state.waitFlow && state.waitFlow.activeToken) return;
  const queuedCount = Object.values(state.changeSummary || {}).reduce((acc, value) => acc + Number(value || 0), 0);
  if (!force && queuedCount > 0) return;
  const now = Date.now();
  const minGap = state.game.active ? 60000 : 12000;
  const target = state.game.active ? 2 : 1;
  if (!force && (now - Number(state.game.lastEnsureAt || 0)) < minGap) return;
  if (!force && Number(state.game.queueLength || 0) >= target) return;
  state.game.lastEnsureAt = now;
  fetch('/api/game/ensure_queue', {method:'POST'})
    .then(r => r.json())
    .then(data => { if (!data.error) syncGameState(data); })
    .catch(() => {});
}

function renderModeUI() {
  const help = document.getElementById('modeHelp');
  const modePanel = document.getElementById('modePanel');
  const commitBtn = document.getElementById('commitBtn');
  document.querySelectorAll('input[name="appMode"]').forEach(el => {
    el.checked = el.value === state.mode;
  });
  const hideInactiveToggle = document.getElementById('hideInactiveToggle');
  if (hideInactiveToggle) hideInactiveToggle.checked = !!state.hideInactive;
  if (modePanel) modePanel.classList.toggle('assets-mode', state.mode === 'assets');
  if (state.mode === 'assets') {
    help.innerHTML = 'Update assets disables reordering and lets you drop files onto slots to create new assets or upload new versions. Asset uploads happen <strong>immediately</strong> in this mode.';
    if (commitBtn) {
      commitBtn.disabled = true;
      commitBtn.title = 'Update in Bynder is only used in Update positions mode.';
      commitBtn.classList.add('btn-disabled-mode');
    }
  } else {
    help.textContent = 'Update positions stages reorder, trash, restore, and cross-SKU copy changes. File uploads are disabled in this mode.';
    if (commitBtn && !state.commitInFlight) {
      commitBtn.disabled = false;
      commitBtn.title = '';
      commitBtn.classList.remove('btn-disabled-mode');
    }
  }
}


function rowRefreshFingerprint(row) {
  if (!row) return '';
  const assets = (row.assets || []).map(asset => ({
    id: String(asset.id || ''),
    slot: String(asset.slot_key || asset.current_position || ''),
    width: Number(asset.width || 0),
    height: Number(asset.height || 0),
    modified: String(asset.dateModified || asset.dateCreated || ''),
    thumb: String(asset.transformBaseUrl || ''),
    pending: !!asset.pending_upload
  })).sort((a,b) => `${a.slot}|${a.id}`.localeCompare(`${b.slot}|${b.id}`));
  return JSON.stringify({
    row: String(row.row_id || row.sku || ''),
    assets
  });
}

function markAssetModeDirtyRows(rowIds) {
  (rowIds || []).forEach(rowId => {
    const key = String(rowId || '').trim();
    if (!key) return;
    const row = getRowById(key);
    state.assetModeDirtyRows[key] = {
      at: Date.now(),
      fingerprint: rowRefreshFingerprint(row)
    };
  });
}

async function refreshDirtyAssetRows() {
  const rowIds = Object.keys(state.assetModeDirtyRows || {}).filter(Boolean);
  if (!rowIds.length) return false;
  const baseline = {};
  rowIds.forEach(rowId => {
    const entry = state.assetModeDirtyRows[rowId] || {};
    baseline[rowId] = String(entry.fingerprint || rowRefreshFingerprint(getRowById(rowId)) || '');
  });
  const startedAt = Date.now();
  let attempts = 0;
  let lastData = null;
  while ((Date.now() - startedAt) < 15000) {
    attempts += 1;
    const resp = await fetch('/api/refresh_rows', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({row_ids: rowIds})
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Row refresh failed');
    state.board = data.board || state.board;
    state.summary = data.summary || state.summary;
    lastData = data;
    const changed = rowIds.some(rowId => rowRefreshFingerprint(getRowById(rowId)) !== String(baseline[rowId] || ''));
    if (changed || attempts >= 6) break;
    await new Promise(resolve => setTimeout(resolve, 1800));
  }
  state.assetModeDirtyRows = {};
  state.assetModeDirty = false;
  return !!lastData;
}


function scrollBoardToFirstColorTop(behavior='auto') {
  const boardMain = document.getElementById('boardMain');
  if (!boardMain) return;
  const firstSection = boardMain.querySelector('.color-section');
  const collectionBar = boardMain.querySelector('.collection-header');
  if (firstSection) {
    const offset = (collectionBar ? collectionBar.offsetHeight : 0) + 8;
    const y = Math.max(0, firstSection.offsetTop - offset);
    boardMain.scrollTo({ top: y, behavior });
    return;
  }
  boardMain.scrollTo({ top: 0, behavior });
}

async function switchMode(newMode) {
  if (newMode === state.mode) return;
  if (newMode === 'assets') {
    const queuedCount = changedAssetIds().size;
    if (queuedCount > 0) {
      const shouldCommit = confirm(`You have ${queuedCount} pending position change(s). Press OK to commit them to Bynder before switching to Update assets mode. Press Cancel to stay in Update positions mode.`);
      if (!shouldCommit) {
        renderModeUI();
        return;
      }
      const success = await commitChanges(true);
      if (!success) {
        renderModeUI();
        return;
      }
    }
    state.mode = 'assets';
    renderModeUI();
    renderBoard();
    return;
  }
  state.mode = 'positions';
  renderModeUI();
  let didFullReload = false;
  if (state.assetModeDirty && state.loadedCollectionOptionId) {
    try {
      const refreshed = await refreshDirtyAssetRows();
      if (!refreshed) {
        await launchCollection(state.loadedCollectionOptionId, {forceRefresh:true, scrollTopAfter:true});
        didFullReload = true;
      }
    } catch (err) {
      console.warn(err);
      await launchCollection(state.loadedCollectionOptionId, {forceRefresh:true, scrollTopAfter:true});
      didFullReload = true;
    }
  }
  renderBoard();
  if (didFullReload) scrollBoardToFirstColorTop('auto');
}

function getLaneMax(laneType) {
  if (!state.board) return laneType === 'core' ? 100 : 5000;
  let maxVal = laneType === 'core' ? 100 : 5000;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      for (const asset of row.assets || []) {
        if (asset.lane !== laneType) continue;
        const match = /^SKU_(\d+)$/.exec(asset.slot_key || '');
        if (!match) continue;
        const num = Number(match[1]);
        if (!Number.isFinite(num)) continue;
        if (laneType === 'core' && num === 8000) continue;
        if (num > maxVal) maxVal = num;
      }
    }
  }
  return maxVal;
}

function rowHasCore8000(row) {
  return (row.assets || []).some(asset => String(asset.lane || '') === 'core' && String(asset.slot_key || '') === 'SKU_8000' && !asset.is_marked_for_deletion);
}

function laneInfo(row, laneType) {
  if (laneType === 'core') {
    const slots = [];
    let maxVal = 0;
    for (const asset of row.assets || []) {
      if (String(asset.lane || '') !== 'core') continue;
      const match = /^SKU_(\d+)$/.exec(asset.slot_key || '');
      if (!match) continue;
      const num = Number(match[1]);
      if (!Number.isFinite(num) || num === 8000) continue;
      if (num > maxVal) maxVal = num;
    }
    if (maxVal <= 0) {
      if (state.workspace === 'product_imagery_onboarding') {
        for (let n = 100; n <= 500; n += 100) slots.push(`SKU_${n}`);
      } else {
        slots.push('SKU_100');
      }
    } else {
      const displayMax = Math.min(maxVal + 100, 4900);
      for (let n = 100; n <= displayMax; n += 100) slots.push(`SKU_${n}`);
    }
    if (rowHasCore8000(row) || rowRequiresWallArtSizing(row)) slots.push('SKU_8000');
    return slots;
  }
  if (laneType === 'swatch_detail') {
    const slots = [];
    let maxVal = 0;
    for (const asset of row.assets || []) {
      if (String(asset.lane || '') !== 'swatch_detail') continue;
      const match = /^SKU_(\d+)$/.exec(asset.slot_key || '');
      if (!match) continue;
      const num = Number(match[1]);
      if (Number.isFinite(num) && num > maxVal) maxVal = num;
    }
    if (maxVal <= 0) {
      if (state.workspace === 'product_imagery_onboarding') {
        slots.push('SKU_5000');
        slots.push('SKU_5100');
      } else {
        slots.push('SKU_5000');
      }
    } else {
      const displayMax = Math.min(maxVal + 100, 5900);
      for (let n = 5000; n <= displayMax; n += 100) slots.push(`SKU_${n}`);
    }
    return slots;
  }
  return [];
}

function changedAssetIds() {
  const changed = new Set();
  if (!state.board) return changed;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      for (const asset of row.assets || []) {
        if (asset.is_empty_slot) continue;
        const original = asset.original_state || {};
        if (asset.pending_upload || (asset.current_position || '') !== (original.position || '') || !!asset.is_marked_for_deletion !== !!original.is_marked_for_deletion || String(asset.deliverable_override || asset.deliverable || '') !== String(original.deliverable || asset.deliverable || '')) {
          changed.add(asset.id);
        }
      }
    }
  }
  return changed;
}

function bucketRow(row) {
  const buckets = {
    grid: {'SKU_grid': []},
    core: {},
    swatch_detail: {},
    special: {'SKU_dimension': [], 'SKU_swatch': [], 'SKU_square': []},
    trash: {trash: []},
    off_pattern: {off_pattern: []},
  };
  for (const slot of laneInfo(row, 'core')) buckets.core[slot] = [];
  for (const slot of laneInfo(row, 'swatch_detail')) buckets.swatch_detail[slot] = [];

  for (const asset of row.assets || []) {
    if (asset.is_empty_slot) continue;
    const lane = asset.lane;
    const pos = asset.slot_key || '';
    const rawPos = asset.last_nontrash_position || asset.current_position;
    if (lane === 'grid') buckets.grid['SKU_grid'].push(asset);
    else if (lane === 'core' && pos in buckets.core) buckets.core[pos].push(asset);
    else if (lane === 'swatch_detail' && pos in buckets.swatch_detail) buckets.swatch_detail[pos].push(asset);
    else if (lane === 'special' && pos in buckets.special) buckets.special[pos].push(asset);
    else if (lane === 'trash') buckets.trash.trash.push(asset);
    else buckets.off_pattern.off_pattern.push({...asset, raw_position: rawPos});
  }
  return buckets;
}


function assetThumbUrl(asset, forPanel=false) {
  if (!asset.transformBaseUrl) return '';
  const isSkuSwatch = (asset.slot_key || '') === 'SKU_swatch' || /_swatch$/i.test(asset.current_position || '');
  const cacheBust = encodeURIComponent(String(asset.dateModified || asset.dateCreated || `${asset.width || 0}x${asset.height || 0}` || ''));
  if (isSkuSwatch) return `${asset.transformBaseUrl}${asset.transformBaseUrl.includes('?') ? '&' : '?'}cb=${cacheBust}`;
  const width = forPanel ? 700 : 500;
  return `${asset.transformBaseUrl}?io=transform:scale,width:${width}&quality=80&cb=${cacheBust}`;
}

function shortDate(text) {
  return String(text || '').split('T')[0];
}

async function downloadAsset(event, assetId, sourceMediaId, fileName) {
  event.preventDefault();
  try {
    const targetId = sourceMediaId || assetId;
    const response = await fetch(`/api/download/${encodeURIComponent(targetId)}`);
    if (!response.ok) throw new Error(`Download failed with status ${response.status}`);
    const blob = await response.blob();
    const url = window.URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    const cd = response.headers.get('Content-Disposition') || response.headers.get('content-disposition') || '';
    const matchStar = cd.match(/filename\*=UTF-8''([^;]+)/i);
    const matchPlain = cd.match(/filename=\"?([^\";]+)/i);
    const headerName = matchStar ? decodeURIComponent(matchStar[1]) : (matchPlain ? matchPlain[1] : '');
    a.download = headerName || fileName || 'asset';
    document.body.appendChild(a);
    a.click();
    a.remove();
    window.URL.revokeObjectURL(url);
  } catch (err) {
    alert(String(err));
  }
}


function formatAssetSizeWarning(asset) {
  const text = String(asset.size_warning || '').trim();
  if (!text) return '';
  const m = text.match(/Size\s*:?\s*(\d+x\d+)\s*[;,-]?\s*expected\s*:?\s*(\d+x\d+)/i);
  if (m) {
    return `<div class="asset-size-warning">Size: ${escapeHtml(m[1])}<br>Expected: ${escapeHtml(m[2])}</div>`;
  }
  if (/needs total fill/i.test(text)) {
    return `<div class="asset-size-warning">Needs total fill<br><span style="font-weight:500;">White corners detected in this room shot.</span></div>`;
  }
  return `<div class="asset-size-warning">${escapeHtml(text)}</div>`;
}

function assetSharesSlot(asset) {
  if (!asset || !state.board) return false;
  const lane = String(asset.lane || '').trim();
  const slotKey = String(asset.slot_key || asset.current_position || '').trim();
  if (!lane || !slotKey || lane === 'off_pattern' || lane === 'trash') return false;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      const matches = (row.assets || []).filter(a => !a.pending_upload && !a.is_marked_for_deletion && String(a.lane || '').trim() === lane && String(a.slot_key || a.current_position || '').trim() === slotKey);
      if (matches.some(a => String(a.id || '') === String(asset.id || ''))) {
        return matches.length > 1;
      }
    }
  }
  return false;
}

function renderAssetCard(asset, changed) {
  if (asset && asset.is_empty_slot) return '';
  const thumb = assetThumbUrl(asset);
  const classes = ['asset-card'];
  const original = asset.original_state || {};
  if (changed) classes.push('changed');
  if (asset.lane === 'off_pattern') classes.push('offpattern');
  if (!!asset.is_marked_for_deletion && !original.is_marked_for_deletion) classes.push('deleted');
  if (!asset.is_marked_for_deletion && !!original.is_marked_for_deletion) classes.push('restored');
  if (asset.pending_upload) classes.push('pending-copy');
  if (asset.asset_mode_uploaded) classes.push('asset-uploaded');
  if (asset.size_warning) classes.push('bad-dimensions');
  if (assetIsBulkFixSiloTarget(asset)) classes.push('bulk-fix-target');
  const openLink = asset.original || asset.transformBaseUrl || '#';
  const downloadLink = asset.pending_upload ? `/api/download/${encodeURIComponent(asset.copy_source_media_id || asset.id || '')}` : `/api/download/${encodeURIComponent(asset.id || '')}`;
  let fixActions = [];
  let sizeWarningHtml = '';
  const wrongDeliverable = assetHasWrongDeliverable(asset);
  const sharedSlot = assetSharesSlot(asset);
  if (asset.size_warning) {
    const totalFillWarning = /needs total fill/i.test(String(asset.size_warning || ''));
    if (state.mode === 'assets' && !asset.pending_upload && !totalFillWarning) {
      if (asset.slot_key === 'SKU_swatch' && Number(asset.width || 0) > 0 && Number(asset.width || 0) === Number(asset.height || 0)) {
        fixActions.push(`<a href="#" class="asset-fix-action" onclick="fixAssetVersion(event, '${escapeHtml(asset.id || '')}', 'swatch')">Fix swatch</a>`);
      } else if (asset.slot_key === 'SKU_dimension') {
        fixActions.push(`<a href="#" class="asset-fix-action" onclick="fixAssetVersion(event, '${escapeHtml(asset.id || '')}', 'dim')">Fix dim</a>`);
      } else if (asset.slot_key === 'SKU_grid') {
        fixActions.push(`<a href="#" class="asset-fix-action" onclick="fixAssetVersion(event, '${escapeHtml(asset.id || '')}', 'grid')">Fix silo</a>`);
      } else if (asset.lane === 'core') {
        fixActions.push(`<a href="#" class="asset-fix-action" onclick="fixAssetVersion(event, '${escapeHtml(asset.id || '')}', 'silo')">Fix silo</a>`);
      }
    }
    sizeWarningHtml = formatAssetSizeWarning(asset);
  }
  if (state.mode === 'positions' && !asset.pending_upload && wrongDeliverable) {
    fixActions.push(`<a href="#" class="asset-fix-action" onclick="queueDeliverableFix(event, '${escapeHtml(asset.id || '')}')">Fix deliverable</a>`);
  }
  const fixHtml = fixActions.join('');
  return `
    <div class="${classes.join(' ')}" draggable="${state.mode === 'positions' ? 'true' : 'false'}" data-asset-id="${escapeHtml(asset.id)}" title="${escapeHtml(asset.size_warning || '')}">
      ${thumb ? `<img src="${escapeHtml(thumb)}" alt="" />` : `<div style="height:var(--thumb-height,84px);"></div>`}
      <div class="asset-meta">
        <div class="asset-date asset-date-row"><span class="asset-date-left">${escapeHtml(shortDate(asset.dateCreated || ''))}</span></div>
        ${asset.pending_upload ? `<div class="asset-date" style="color:#1976d2;font-weight:700;">${escapeHtml(asset.pending_message || (asset.pending_upload_kind === 'new_version' ? 'Pending new version upload' : asset.pending_upload_kind === 'new_asset' ? 'Pending new asset upload' : 'Pending copy upload'))}</div>` : ''}
        ${asset.asset_mode_uploaded ? `<div class="asset-date" style="color:#348c4b;font-weight:700;">${escapeHtml(asset.asset_mode_message || (asset.asset_mode_uploaded === 'new_version' ? 'New version uploaded to this slot. Reload to view.' : 'New asset uploaded to this slot. Reload to view.'))}</div>` : ''}
        ${sizeWarningHtml}
        ${fixHtml ? `<div class="asset-fix-pill-row">${fixHtml}</div>` : ''}
        ${asset.is_marked_for_deletion ? '<div class="asset-date" style="color:#a93d36;font-weight:700;">Marked for deletion</div>' : ''}
        ${asset.lane === 'off_pattern' ? `<div class="asset-date" style="color:#8b6b00;font-weight:700;">Off-pattern: ${escapeHtml(asset.current_position || '')}</div>` : ''}
        ${wrongDeliverable ? `<div class="asset-date" style="color:#9c4f00;font-weight:700;">Wrong deliverable for lane</div>` : ''}
        ${sharedSlot ? `<div class="asset-date" style="color:#8f2d56;font-weight:700;">Multiple assets share this slot</div>` : ''}
        ${asset.pending_upload && asset.pending_upload_kind === 'copy' ? `<button type="button" class="asset-undo-copy" onclick="undoPendingCopyClick(event, '${escapeHtml(asset.id || '')}', '${escapeHtml(asset.current_position || '')}', '${escapeHtml(asset.copy_source_media_id || '')}', '${escapeHtml(asset.sku || '')}')">No longer copy</button>` : ''}
        <div class="asset-actions">
          <a href="${escapeHtml(openLink)}" target="_blank" rel="noopener">Open</a>
          <a href="#" onclick="downloadAsset(event, '${escapeHtml(asset.id || '')}', '${escapeHtml(asset.copy_source_media_id || '')}', '${escapeHtml(asset.file_name || asset.name || 'asset')}')">Download</a>
          ${state.mode === 'assets' && !asset.pending_upload ? `<a href="#" onclick="modifyBoardAsset(event, '${escapeHtml(asset.id || '')}')">Modify</a>` : ''}
        </div>
      </div>
    </div>
  `;
}

function slotNeedsCriticalHighlight(row, slotName, items) {
  if (!row || !rowCountsAsActive(row)) return false;
  if (items && items.length) return false;
  return slotName === 'SKU_grid' || slotName === 'SKU_100';
}


function currentSetDimRow() {
  return state.setDim && state.setDim.activeRowId ? getRowById(state.setDim.activeRowId) : null;
}

function clearSetDimSelection() {
  if (state.setDim.previewUrl && String(state.setDim.previewUrl).startsWith('blob:')) {
    URL.revokeObjectURL(state.setDim.previewUrl);
  }
  state.setDim = {activeRowId:'', slotAssignments:[], scalePercents:[], previewUrl:'', loading:false, applying:false, dirty:false, dragSlotIdx:null};
  renderPhotographyPanel();
}

function currentSetDimRow() {
  return getRowById(state.setDim.activeRowId || '');
}

async function openCompileSetDim(rowId) {
  const row = getRowById(rowId);
  if (!row) return;
  state.photography.expanded = true;
  state.setDim.activeRowId = String(rowId || '');
  state.setDim.slotAssignments = (row.set_dim_components || []).map((_, idx) => idx);
  state.setDim.scalePercents = (row.set_dim_components || []).map(() => 100);
  state.setDim.dirty = false;
  state.setDim.dragSlotIdx = null;
  state.setDim.loading = true;
  renderPhotographyPanel();
  await refreshSetDimPreview();
}

async function refreshSetDimPreview() {
  const row = currentSetDimRow();
  if (!row) return;
  state.setDim.loading = true;
  renderPhotographyPanel();
  try {
    const resp = await fetch('/api/set_dim_compile_preview', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({row_id: row.row_id, slot_assignments: state.setDim.slotAssignments || [], scale_percents: state.setDim.scalePercents || []})
    });
    const blob = await resp.blob();
    if (!resp.ok) {
      let msg = 'Could not preview compiled set dim.';
      try {
        const parsed = JSON.parse(await blob.text());
        msg = parsed.error || msg;
      } catch (e) {}
      throw new Error(msg);
    }
    if (state.setDim.previewUrl && String(state.setDim.previewUrl).startsWith('blob:')) URL.revokeObjectURL(state.setDim.previewUrl);
    state.setDim.previewUrl = URL.createObjectURL(blob);
    state.setDim.dirty = false;
  } catch (err) {
    alert(err.message || String(err));
  } finally {
    state.setDim.loading = false;
    renderPhotographyPanel();
  }
}

function setDimSlotLabel(index, total) {
  if (total === 1) return 'Full canvas';
  if (total === 2) return index === 0 ? 'Upper slot' : 'Lower slot';
  if (total === 3) return ['Upper left', 'Upper right', 'Lower center'][index] || `Slot ${index + 1}`;
  if (total === 4) return ['Upper left', 'Upper right', 'Lower left', 'Lower right'][index] || `Slot ${index + 1}`;
  if (total === 5) return ['Upper left', 'Upper center', 'Upper right', 'Lower left', 'Lower right'][index] || `Slot ${index + 1}`;
  return ['Upper left', 'Upper center', 'Upper right', 'Lower left', 'Lower center', 'Lower right'][index] || `Slot ${index + 1}`;
}

function setDimComponentIndexForSlot(slotIdx) {
  const assignments = state.setDim.slotAssignments || [];
  return assignments.findIndex(val => Number(val) === Number(slotIdx));
}

function swapSetDimSlots(fromSlotIdx, toSlotIdx) {
  if (fromSlotIdx === toSlotIdx) return;
  const assignments = [...(state.setDim.slotAssignments || [])];
  const fromComponentIdx = assignments.findIndex(val => Number(val) === Number(fromSlotIdx));
  const toComponentIdx = assignments.findIndex(val => Number(val) === Number(toSlotIdx));
  if (fromComponentIdx < 0 || toComponentIdx < 0) return;
  assignments[fromComponentIdx] = Number(toSlotIdx);
  assignments[toComponentIdx] = Number(fromSlotIdx);
  state.setDim.slotAssignments = assignments;
  state.setDim.dirty = true;
  state.setDim.dragSlotIdx = null;
  renderPhotographyPanel();
}

function beginSetDimDrag(slotIdx, event) {
  state.setDim.dragSlotIdx = Number(slotIdx);
  try { event.dataTransfer.setData('text/plain', String(slotIdx)); } catch (e) {}
  try { event.dataTransfer.effectAllowed = 'move'; } catch (e) {}
}

function allowSetDimDrop(event) {
  event.preventDefault();
  try { event.dataTransfer.dropEffect = 'move'; } catch (e) {}
}

function dropSetDimSlot(slotIdx, event) {
  event.preventDefault();
  let fromSlotIdx = state.setDim.dragSlotIdx;
  try {
    const raw = event.dataTransfer.getData('text/plain');
    if (raw !== '') fromSlotIdx = Number(raw);
  } catch (e) {}
  if (fromSlotIdx === null || fromSlotIdx === undefined || Number.isNaN(Number(fromSlotIdx))) return;
  swapSetDimSlots(Number(fromSlotIdx), Number(slotIdx));
}

function endSetDimDrag() {
  state.setDim.dragSlotIdx = null;
  renderPhotographyPanel();
}

function changeSetDimScale(componentIdx, nextValue) {
  const pct = Math.max(60, Math.min(160, Number(nextValue) || 100));
  const next = [...(state.setDim.scalePercents || [])];
  next[componentIdx] = pct;
  state.setDim.scalePercents = next;
  state.setDim.dirty = true;
  renderPhotographyPanel();
}

function nudgeSetDimScale(componentIdx, delta) {
  const current = Number((state.setDim.scalePercents || [])[componentIdx] || 100);
  changeSetDimScale(componentIdx, current + delta);
}

function renderSetDimDrawer() {
  const row = currentSetDimRow();
  if (!row) return '';
  const components = row.set_dim_components || [];
  const total = components.length;
  const preview = state.setDim.loading
    ? `<div class="photo-empty">Building compiled set dim preview...</div>`
    : (state.setDim.previewUrl ? `<img src="${escapeHtml(state.setDim.previewUrl)}" alt="Compiled set dim preview" />` : `<div class="photo-empty">Preview loading...</div>`);
  return `
    <div class="set-dim-drawer">
      <div class="photo-prep-top">
        <h4>Compile set dim</h4>
        <div class="photo-prep-actions">
          <button type="button" class="btn btn-secondary photo-mini-btn" onclick="clearSetDimSelection()">Clear selection</button>
          <button type="button" class="btn btn-primary photo-mini-btn ${state.setDim.applying ? 'btn-reload-flashing' : ''}" ${state.setDim.applying ? 'disabled' : ''} onclick="applyCompiledSetDim()">${state.setDim.applying ? 'Applying...' : 'Apply as dimensions asset'}</button>
        </div>
      </div>
      <div class="photo-prep-note">Arrange the placed dims by dragging these canvas slot tiles. You can nudge each one larger or smaller, then click Re-render preview when you want to see the updated composition.</div>
      <div class="set-dim-grid">
        ${Array.from({length: total}).map((_, slotIdx) => {
          const componentIdx = setDimComponentIndexForSlot(slotIdx);
          const comp = componentIdx >= 0 ? components[componentIdx] : null;
          const scalePct = componentIdx >= 0 ? Number((state.setDim.scalePercents || [])[componentIdx] || 100) : 100;
          const thumbSrc = comp ? `/api/set_dim_component_thumb/${encodeURIComponent(comp.dim_media_id || '')}` : '';
          return `
            <div class="set-dim-item ${state.setDim.dragSlotIdx !== null && state.setDim.dragSlotIdx !== undefined && Number(state.setDim.dragSlotIdx) === slotIdx ? 'dragging' : ''}" draggable="true" ondragstart="beginSetDimDrag(${slotIdx}, event)" ondragover="allowSetDimDrop(event)" ondrop="dropSetDimSlot(${slotIdx}, event)" ondragend="endSetDimDrag()">
              <div class="set-dim-slot-title">Canvas slot - ${escapeHtml(setDimSlotLabel(slotIdx, total))}</div>
              <div class="set-dim-slot-thumb">${comp ? `<img src="${thumbSrc}" alt="Canvas slot preview" />` : `<div class="photo-empty">Empty slot</div>`}</div>
              ${comp ? `<div class="set-dim-control-label">Visual scale</div>
              <div class="set-dim-scale-row">
                <button type="button" class="btn btn-secondary photo-mini-btn" onclick="nudgeSetDimScale(${componentIdx}, -10)">-</button>
                <input type="range" min="60" max="160" step="5" value="${scalePct}" oninput="changeSetDimScale(${componentIdx}, this.value)" />
                <button type="button" class="btn btn-secondary photo-mini-btn" onclick="nudgeSetDimScale(${componentIdx}, 10)">+</button>
                <div class="set-dim-scale-value">${scalePct}%</div>
              </div>` : ''}
            </div>`;
        }).join('')}
      </div>
      <div class="set-dim-rerender-row">
        <button type="button" class="btn btn-secondary set-dim-rerender-btn ${state.setDim.loading ? 'btn-reload-flashing' : ''}" ${state.setDim.loading ? 'disabled' : ''} onclick="refreshSetDimPreview()">${state.setDim.loading ? 'Re-rendering...' : (state.setDim.dirty ? 'Re-render preview' : 'Preview is up to date')}</button>
      </div>
      <div class="set-dim-preview-wrap">${preview}</div>
    </div>
  `;
}

async function applyCompiledSetDim() {
  const row = currentSetDimRow();
  if (!row) return;
  state.setDim.applying = true;
  renderPhotographyPanel();
  try {
    const resp = await fetch('/api/set_dim_compile_apply', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({mode: state.mode, row_id: row.row_id, slot_assignments: state.setDim.slotAssignments || [], scale_percents: state.setDim.scalePercents || []})
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not apply compiled set dim.');
    state.board = data.board || state.board;
    state.summary = data.summary || state.summary;
    if (data.notice) addAppNotice(data.notice.text || 'Compiled set dim applied.', data.notice.kind || 'success', data.notice.html || '');
    if (data.asset_mode_refresh_pending) state.assetModeDirty = true;
    markAssetModeDirtyRows(data.dirty_row_ids || [row.row_id || row.id]);
    clearSetDimSelection();
    renderBoard();
  } catch (err) {
    alert(err.message || String(err));
  } finally {
    state.setDim.applying = false;
    renderPhotographyPanel();
  }
}

function renderEmptySlotActions(row, lane, slotName, items) {
  if (!row || items.length) return '';
  if (state.mode === 'assets' && lane === 'special' && slotName === 'SKU_dimension' && row.set_dim_compile_ready) {
    return `<div class="empty-slot-actions"><a href="#" class="asset-fix-action" onclick="openCompileSetDim('${escapeHtml(row.row_id || '')}'); return false;">Compile set dim</a></div>`;
  }
  if (state.mode === 'assets' && lane === 'core' && slotName === 'SKU_8000' && rowRequiresWallArtSizing(row)) {
    return `<div class="empty-slot-actions"><a href="#" class="asset-fix-action" onclick="applyWallArtSizingGuide(event, '${escapeHtml(row.row_id || '')}'); return false;">Fix wall art sizing guide</a></div>`;
  }
  return '';
}

function renderSquareOpportunityHint(row, slotName) {
  if (!row || slotName !== 'SKU_square' || !row.square_make_recommended) return '';
  const tip = row.square_make_tooltip || 'This SKU has at least one room shot. You might be able to make a nice square image out of it.';
  return `<div class="empty-slot-actions"><span class="make-square-hint" title="${escapeHtml(tip)}">Make a square</span></div>`;
}

function renderSlot(rowId, lane, slotName, items, label, changedSet, extraClass='') {
  const row = getRowById(rowId);
  const isCriticalMissing = slotNeedsCriticalHighlight(row, slotName, items);
  const needsMakeSquare = !!(row && slotName === 'SKU_square' && row.square_make_recommended);
  const emptyActions = renderEmptySlotActions(row, lane, slotName, items);
  const squareHint = renderSquareOpportunityHint(row, slotName);
  const cards = items.length
    ? `${items.map(a => renderAssetCard(a, changedSet.has(a.id))).join('')}${squareHint}`
    : `<div class="empty">${isCriticalMissing ? 'Missing required image' : 'Drop here'}</div>${emptyActions}${squareHint}`;
  return `
    <div class="slot ${extraClass} ${isCriticalMissing ? 'slot-missing-critical' : ''} ${needsMakeSquare ? 'slot-make-square' : ''}" data-row-id="${escapeHtml(rowId)}" data-lane="${escapeHtml(lane)}" data-slot="${escapeHtml(slotName)}">
      <div class="slot-label">${escapeHtml(label)}</div>
      ${cards}
    </div>
  `;
}

function renderRow(row, changedSet) {
  const buckets = bucketRow(row);
  const coreSlots = laneInfo(row, 'core');
  const swatchDetailSlots = laneInfo(row, 'swatch_detail');

  return `
    <div class="sku-row ${row.inactive ? 'inactive' : ''}" id="row-${escapeHtml(row.row_id)}">
      <div class="row-layout">
        <div class="meta-grid">
          <div class="meta-cell"><div class="k">Product Name</div><div class="v">${row.product_url ? `<a href="${escapeHtml(row.product_url)}" target="_blank" rel="noopener">${escapeHtml(row.product_name)}</a>` : escapeHtml(row.product_name)}</div></div>
          <div class="meta-cell"><div class="k">Product SKU</div><div class="v"><div class="sku-inline-top"><span class="sku-text">${escapeHtml(row.sku)}</span>${state.workspace === 'product_imagery_onboarding' ? `<button type="button" class="btn btn-secondary photo-mini-btn" onclick="focusPIOPhotographySku(event, '${escapeHtml(row.sku || '')}')">Filter</button>` : ''}</div><div class="sku-inline-actions"><a href="https://www.bynder.raymourflanigan.com/media/?resetsearch=&field=metaproperty_Product_SKU&value=${encodeURIComponent(row.sku || '')}" target="_blank" rel="noopener">Open in Bynder</a></div></div></div>
          ${state.workspace === 'product_imagery_onboarding' ? '' : `<div class="meta-cell ${row.inactive ? 'status-inactive' : ''}"><div class="k">Product Status</div><div class="v">${escapeHtml(row.product_status)}</div></div>`}
          ${row.mattress_size ? `<div class="meta-cell"><div class="k">Mattress Size</div><div class="v">${escapeHtml(row.mattress_size)}</div></div>` : ''}
          <div class="meta-cell"><div class="k">Sales Channel</div><div class="v">${escapeHtml(row.sales_channel)}</div></div>
          ${row.features ? `<div class="meta-cell"><div class="k">Features</div><div class="v">${escapeHtml(row.features)}</div></div>` : ''}
          ${row.dim_width || row.dim_length || row.dim_height ? `<div class="meta-cell meta-measure-boxes" style="grid-column:1 / -1;"><div class="measure-chip">L: ${escapeHtml(row.dim_length || '')}</div><div class="measure-chip">W: ${escapeHtml(row.dim_width || '')}</div><div class="measure-chip">H: ${escapeHtml(row.dim_height || '')}</div></div>` : ''}
          ${(row.component_display_groups && row.component_display_groups.length) || (row.component_skus && row.component_skus.length) || (row.component_warnings && row.component_warnings.length) ? `
            <div class="meta-cell components" style="grid-column:1 / -1;">
              <div class="k">Components</div>
              <div class="v component-chip-row">${(row.component_display_groups || []).map(group => group.product_name ? `<button type="button" class="component-sku-link component-chip" data-component-jump="${escapeHtml(group.sku)}" onclick="jumpToComponentSku(event, '${escapeHtml(group.sku)}')">${escapeHtml(group.sku)}${group.count > 1 ? ` x${group.count}` : ''} - ${escapeHtml(group.product_name)}</button>` : `<span class="component-chip">${escapeHtml(group.sku)}${group.count > 1 ? ` x${group.count}` : ''}</span>`).join('') || ((row.component_skus || []).map(sku => `<button type="button" class="component-sku-link" data-component-jump="${escapeHtml(sku)}" onclick="jumpToComponentSku(event, '${escapeHtml(sku)}')">${escapeHtml(sku)}</button>`).join(' '))}</div>
              ${row.component_display_groups && row.component_display_groups.length ? `<details class="component-tree"><summary><span>Components</span><span class="summary-caret">▾</span></summary><div class="component-flyout"><div class="component-visual-grid">${row.component_display_groups.map(group => `<div class="component-visual-card">${group.grid_thumb ? `<img src="${escapeHtml(group.grid_thumb)}" alt="" />` : `<div style="height:86px; border-radius:8px; background:#f5f7fa;"></div>`}<div style="margin-top:6px; font-weight:700;">${escapeHtml(group.sku)}${group.count > 1 ? ` x${group.count}` : ''}</div><div>${escapeHtml(group.product_name || 'No matching SKU row on this board')}</div></div>`).join('')}</div></div></details>` : ''}
              ${row.component_warnings && row.component_warnings.length ? `<div class="component-warning-list">${row.component_warnings.map(w => `<span class="component-warning-chip">${escapeHtml(w)}</span>`).join('')}</div>` : ''}
            </div>` : ''}
          ${state.workspace === 'product_imagery_onboarding' ? `<div class="meta-cell"><div class="k">Workflow Status</div><div class="v">${escapeHtml(String(row.workflow_status || '').replaceAll('_',' ').replace(/^App\s+/i,''))}</div></div>` : ''}
          <div class="meta-action-row">${renderAdditionalPhotoAction(row)}</div>
        </div>

        <div>
          <div class="top-slot-layout">
            <div class="lane-block compact">
              <div class="lane-title">Grid</div>
              <div class="slot-row tight" data-scroll-key="${escapeHtml(row.row_id)}::grid">
                ${renderSlot(row.row_id, 'grid', 'SKU_grid', buckets.grid['SKU_grid'], 'SKU_grid', changedSet)}
              </div>
            </div>

            <div class="lane-block compact">
              <div class="lane-title">Special Slots</div>
              <div class="slot-row tight" data-scroll-key="${escapeHtml(row.row_id)}::special">
                ${renderSlot(row.row_id, 'special', 'SKU_dimension', buckets.special['SKU_dimension'], 'SKU_dimension', changedSet, 'special')}
                ${renderSlot(row.row_id, 'special', 'SKU_swatch', buckets.special['SKU_swatch'], 'SKU_swatch', changedSet, 'special')}
                ${renderSlot(row.row_id, 'special', 'SKU_square', buckets.special['SKU_square'], 'SKU_SQUARE', changedSet, 'special')}
                ${renderSlot(row.row_id, 'off_pattern', 'off_pattern', buckets.off_pattern.off_pattern, 'Off-pattern', changedSet, 'offpattern')}
                ${renderSlot(row.row_id, 'trash', 'trash', buckets.trash.trash, 'Trash', changedSet, 'trash')}
              </div>
            </div>

            <div class="lane-block compact">
              <div class="lane-title">Swatch Detail Images</div>
              <div class="slot-row tight swatch-detail-inline" data-scroll-key="${escapeHtml(row.row_id)}::swatch_detail">
                ${swatchDetailSlots.map(slot => renderSlot(row.row_id, 'swatch_detail', slot, buckets.swatch_detail[slot] || [], slot, changedSet)).join('')}
              </div>
            </div>
          </div>

          <div class="lane-block">
            <div class="lane-title">Product Carousel Images</div>
            <div class="slot-row" data-scroll-key="${escapeHtml(row.row_id)}::core">
              ${coreSlots.map(slot => renderSlot(row.row_id, 'core', slot, buckets.core[slot] || [], slot, changedSet)).join('')}
            </div>
          </div>
        </div>
      </div>

      ${(row.overflow_warnings || []).map((w, i) => `
        <div class="warning-chip">
          <div>${escapeHtml(w)}</div>
          <button data-row-id="${escapeHtml(row.row_id)}" data-warning-index="${i}">x</button>
        </div>
      `).join('')}

      ${(row.commit_failures || []).map(f => `
        <div class="warning-chip">
          <div>${escapeHtml(f.asset_name)} failed to update: ${escapeHtml(f.error)}</div>
        </div>
      `).join('')}
    </div>
  `;
}


function panelThumbUrl(asset) {
  return assetThumbUrl(asset, true);
}

function photoMatchingSkuButtons(asset) {
  const activeSet = new Set(state.photography.activeSkuSet || []);
  return (asset.tags || []).map(tag => {
    if (activeSet.has(tag) || boardHasSku(tag)) {
      return `<button type="button" class="photo-sku-jump" onclick="jumpToComponentSku(event, '${escapeHtml(tag)}')">${escapeHtml(tag)}</button>`;
    }
    const isLoading = !!state.nonCollectionSkuLoading[tag];
    return `<button type="button" class="photo-sku-jump" ${isLoading ? 'disabled' : ''} onclick="loadNonCollectionSkuFromPhoto(event, '${escapeHtml(tag)}', this)">${isLoading ? 'Loading...' : escapeHtml(tag)}</button>`;
  }).join('');
}

function renderPhotoTile(asset) {
  const thumb = panelThumbUrl(asset);
  const isOpen = !!state.photoSkuOpen[asset.id];
  const isSelected = (state.photography.selectedIds || []).includes(asset.id);
  const isReviewing = !!((state.photography.reviewingIds || {})[asset.id]);
  return `
    <div class="photo-tile ${isSelected ? 'selected' : ''}" draggable="true" data-photo-id="${escapeHtml(asset.id)}">
      <div class="photo-image-wrap">
        ${thumb ? `<img src="${escapeHtml(thumb)}" alt="" />` : `<div style="height:var(--photo-thumb-height,170px); background:#f4f7f4;"></div>`}
        ${asset.is_final ? '' : `<div class="photo-watermark-text" aria-hidden="true"><span>NOT</span><span>FINAL</span></div>`}
        <button type="button" class="photo-select-badge" aria-label="Select photography asset" onclick="togglePhotoSelection(event, '${escapeHtml(asset.id)}')">${isSelected ? '&#10003;' : ''}</button>
      </div>
      <div class="photo-meta">
        <div class="photo-name"><a href="https://www.bynder.raymourflanigan.com/media/?mediaId=${encodeURIComponent(asset.id || '')}" target="_blank" rel="noopener">${escapeHtml(asset.name)}</a></div>
        <div class="photo-line">${escapeHtml(shortDate(asset.dateCreated || ''))}</div>
        <div class="photo-line">Source: ${escapeHtml(asset.source || '')}</div>
        ${asset.season ? `<div class="photo-line photo-season">Season: ${escapeHtml(asset.season)}</div>` : ''}
        <div class="photo-line">${escapeHtml((asset.width || 0) + 'x' + (asset.height || 0))}</div>
        <div class="photo-actions">
          <a href="${escapeHtml(asset.original || asset.transformBaseUrl || '#')}" target="_blank" rel="noopener">Open</a>
          <a href="#" onclick="downloadAsset(event, '${escapeHtml(asset.id || '')}', '${escapeHtml(asset.id || '')}', '${escapeHtml(asset.file_name || asset.name || 'asset')}')">Download</a>
        </div>
        <div class="photo-review-row">
          ${asset.reviewed_for_site ? `<div class="photo-review-status">Reviewed</div>` : `<button type="button" class="btn btn-secondary photo-mini-btn photo-review-btn" ${isReviewing ? 'disabled' : ''} onclick="markPhotoReviewed(event, '${escapeHtml(asset.id)}')">${isReviewing ? 'Saving...' : 'Mark reviewed'}</button>`}
        </div>
      </div>
      <div class="photo-skus">
        <button type="button" class="photo-skus-toggle" onclick="togglePhotoSkuDrawer('${escapeHtml(asset.id)}')">Tags</button>
        <div class="photo-skus-body ${isOpen ? 'open' : ''}">
          ${asset.sku_tags && asset.sku_tags.length ? photoMatchingSkuButtons(asset) : '<div class="photo-line">No alphanumeric 9-character tags found.</div>'}
          ${asset.extra_tags && asset.extra_tags.length ? `<div class="photo-tag-cloud">${asset.extra_tags.map(tag => `<span class="photo-tag-chip">${escapeHtml(tag)}</span>`).join('')}</div>` : ''}
        </div>
      </div>
    </div>
  `;
}

function getPhotoById(photoId) {
  return (state.photography.items || []).find(x => x.id === photoId) || null;
}

function getVisiblePhotographyItems() {
  let all = state.photography.items || [];
  if (state.photography.hideFpo) all = all.filter(x => !!x.is_final);
  if (state.photography.hideReviewed) all = all.filter(x => !x.reviewed_for_site);
  if (state.workspace === 'product_imagery_onboarding' && state.photography.imageTypeFilter) {
    all = all.filter(x => String(x.image_type || '') === String(state.photography.imageTypeFilter || ''));
  }
  if (state.workspace === 'product_imagery_onboarding' && state.photography.skuFilter) {
    all = all.filter(x => Array.isArray(x.sku_tags || x.tags) && (x.sku_tags || x.tags).map(t => String(t || '')).includes(String(state.photography.skuFilter || '')));
  }
  return all;
}

function refreshActivePhotoSelectionAfterFilter() {
  const visible = getVisiblePhotographyItems();
  if (state.photography.activeId && !visible.some(x => String(x.id) === String(state.photography.activeId))) {
    state.photography.activeId = '';
    state.photography.selectedIds = [];
    if (state.photography.previewUrl && state.photography.previewUrl.startsWith('blob:')) URL.revokeObjectURL(state.photography.previewUrl);
    state.photography.previewUrl = '';
    clearSetDimSelection();
  }
}

function setHideFpo(checked) {
  state.photography.hideFpo = !!checked;
  refreshActivePhotoSelectionAfterFilter();
  renderPhotographyPanel();
}

function setHideReviewed(checked) {
  state.photography.hideReviewed = !!checked;
  refreshActivePhotoSelectionAfterFilter();
  renderPhotographyPanel();
}

async function markPhotoReviewed(event, photoId) {
  if (event) {
    event.preventDefault();
    event.stopPropagation();
  }
  const asset = getPhotoById(photoId);
  if (!asset || asset.reviewed_for_site) return;
  const ok = confirm(
    "Before you mark this image as reviewed, please make sure you checked every product shown in it, including smaller pieces like lamps, artwork, and end tables. If everything in the image has been reviewed, go ahead. If not, give it one more pass first."
  );
  if (!ok) return;
  state.photography.reviewingIds = state.photography.reviewingIds || {};
  state.photography.reviewingIds[photoId] = true;
  renderPhotographyPanel();
  try {
    const resp = await fetch('/api/mark_photo_reviewed', {
      method: 'POST',
      headers: {'Content-Type':'application/json'},
      body: JSON.stringify({media_id: photoId})
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not mark photo as reviewed');
    asset.reviewed_for_site = true;
    asset.reviewed_for_site_values = data.reviewed_for_site_values || ['Reviewedforsite'];
    addAppNotice('Photography asset marked as reviewed for site.', 'success');
    refreshActivePhotoSelectionAfterFilter();
    renderPhotographyPanel();
  } catch (err) {
    alert(err.message || String(err));
  } finally {
    delete state.photography.reviewingIds[photoId];
    renderPhotographyPanel();
  }
}

function currentActivePhoto() {
  const id = state.photography.activeId || (state.photography.selectedIds || [])[0] || '';
  return getPhotoById(id);
}

function prepModeFromState() {
  return state.photography.prep.mode || 'original';
}

function activePhotoOffsetY(photoId) {
  const active = getPhotoById(photoId);
  if (!active) return 0;
  const overrides = state.photography.prep.offsetYOverrides || {};
  const mode = prepModeFromState();
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return 0;
  if (mode === 'pick_swatch') {
    const cropH = Math.min(163, srcH);
    const maxOff = Math.max(0, srcH - cropH);
    if (overrides[photoId] === undefined || overrides[photoId] === null) return Math.round(maxOff / 2);
    return Math.max(0, Math.min(maxOff, Number(overrides[photoId] || 0)));
  }
  if (!mode.startsWith('crop_') || mode === 'crop_square' || mode === 'crop_swatch') return 0;
  const outH = mode === 'crop_2200' ? 2200 : 1688;
  const scaledH = Math.round(srcH * (3000 / srcW));
  const maxOff = Math.max(0, scaledH - outH);
  if (overrides[photoId] === undefined || overrides[photoId] === null) return Math.round(maxOff / 2);
  return Math.max(0, Math.min(maxOff, Number(overrides[photoId] || 0)));
}

function activePhotoOffsetX(photoId) {
  const active = getPhotoById(photoId);
  if (!active) return 0;
  const overrides = state.photography.prep.offsetXOverrides || {};
  const mode = prepModeFromState();
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH || (mode !== 'crop_square' && mode !== 'crop_swatch' && mode !== 'pick_swatch')) return 0;
  if (mode === 'pick_swatch') {
    const cropW = Math.min(163, srcW);
    const maxOff = Math.max(0, srcW - cropW);
    if (overrides[photoId] === undefined || overrides[photoId] === null) return Math.round(maxOff / 2);
    return Math.max(0, Math.min(maxOff, Number(overrides[photoId] || 0)));
  }
  const side = Math.min(srcW, srcH);
  const maxOff = Math.max(0, srcW - side);
  if (overrides[photoId] === undefined || overrides[photoId] === null) return Math.round(maxOff / 2);
  return Math.max(0, Math.min(maxOff, Number(overrides[photoId] || 0)));
}


function prepModeOutputSize(mode, active=null) {
  const m = String(mode || '');
  const photo = active || currentActivePhoto();
  const srcW = Number(photo?.width || 0) || 0;
  const srcH = Number(photo?.height || 0) || 0;
  if (m === 'original') return photo ? `${photo.width || ''}x${photo.height || ''}` : 'Original';
  if (m === 'crop_2200' || m === 'pad_tb_2200') return '3000x2200';
  if (m === 'crop_square') {
    const side = Math.min(srcW || 1000, srcH || 1000) || 1000;
    const out = side < 1000 ? 1000 : side;
    return `${out}x${out}`;
  }
  if (m === 'crop_swatch' || m === 'pick_swatch') return '163x163';
  return '3000x1688';
}

function prepArrowIcon(direction, jump=false) {
  const dir = String(direction || '').toLowerCase();
  const arrows = {
    left: '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M15.5 10H5.5"></path><path d="M9 6.5L5.5 10L9 13.5"></path></svg>',
    right: '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M4.5 10H14.5"></path><path d="M11 6.5L14.5 10L11 13.5"></path></svg>',
    up: '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M10 15.5V5.5"></path><path d="M6.5 9L10 5.5L13.5 9"></path></svg>',
    down: '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M10 4.5V14.5"></path><path d="M6.5 11L10 14.5L13.5 11"></path></svg>'
  };
  const jumps = {
    left: '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M15.5 10H7"></path><path d="M10.5 6.5L7 10L10.5 13.5"></path><path d="M4.5 5.5V14.5"></path></svg>',
    right: '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M4.5 10H13"></path><path d="M9.5 6.5L13 10L9.5 13.5"></path><path d="M15.5 5.5V14.5"></path></svg>',
    up: '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M10 15.5V7"></path><path d="M6.5 10.5L10 7L13.5 10.5"></path><path d="M5.5 4.5H14.5"></path></svg>',
    down: '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M10 4.5V13"></path><path d="M6.5 9.5L10 13L13.5 9.5"></path><path d="M5.5 15.5H14.5"></path></svg>'
  };
  return jump ? (jumps[dir] || arrows[dir] || '') : (arrows[dir] || '');
}

function prepFeasibilityInfo(photo, mode) {
  const srcW = Number(photo?.width || 0) || 0;
  const srcH = Number(photo?.height || 0) || 0;
  const info = { kind:'good', title:'Ready', detail:'', badge:'Native crop', previewClass:'', icon:'OK' };
  if (!srcW || !srcH) {
    return { kind:'warn', title:'Source size unavailable', detail:'The image dimensions are missing, so crop reliability cannot be confirmed.', badge:'Check source', previewClass:'warn', icon:'!' };
  }
  if (mode === 'original') {
    return { kind:'notice', title:'Original size', detail:`Source image: ${srcW}x${srcH}. No crop, resize, or padding will be applied.`, badge:`${srcW}x${srcH}`, previewClass:'notice', icon:'i' };
  }
  if (mode === 'crop_square') {
    const side = Math.min(srcW, srcH);
    if (side < 1000) return { kind:'warn', title:'Square will upscale', detail:`Largest real square is ${side}x${side}. Output will be enlarged only to 1000x1000.`, badge:'Upscaling', previewClass:'warn', icon:'!' };
    return { ...info, detail:`Largest real square crop: ${side}x${side}. Output stays at that exact size.`, badge:`${side} square` };
  }
  if (mode === 'crop_swatch') {
    const side = Math.min(srcW, srcH);
    if (side < 163) return { kind:'warn', title:'Swatch will upscale', detail:`Largest real square is ${side}x${side}. Output will be enlarged to 163x163.`, badge:'Upscaling', previewClass:'warn', icon:'!' };
    return { ...info, detail:`Largest real square crop: ${side}x${side}; final output is 163x163.`, badge:'Native swatch' };
  }
  if (mode === 'pick_swatch') {
    const boxW = Math.min(163, srcW);
    const boxH = Math.min(163, srcH);
    if (srcW < 163 || srcH < 163) return { kind:'warn', title:'Swatch box is constrained', detail:`Only ${boxW}x${boxH} is available from this source. The output preview is enlarged to 163x163.`, badge:'Constrained', previewClass:'warn', icon:'!' };
    return { ...info, detail:'A true 163x163 movable swatch crop is available.', badge:'163x163 ready' };
  }
  if (mode === 'crop_1688') {
    const scaledH = Math.round(srcH * (3000 / Math.max(1, srcW)));
    if (srcW < 3000 || scaledH < 1688) return { kind:'warn', title:'True crop is not available', detail:`Source is ${srcW}x${srcH}. This mode has to enlarge the image to reach 3000x1688.`, badge:'Upscaling', previewClass:'warn', icon:'!' };
    return { ...info, detail:'A true 3000x1688 crop is available.', badge:'Native crop' };
  }
  if (mode === 'crop_2200') {
    const scaledH = Math.round(srcH * (3000 / Math.max(1, srcW)));
    if (srcW < 3000 || scaledH < 2200) return { kind:'warn', title:'True crop is not available', detail:`Source is ${srcW}x${srcH}. This mode has to enlarge the image to reach 3000x2200.`, badge:'Upscaling', previewClass:'warn', icon:'!' };
    return { ...info, detail:'A true 3000x2200 crop is available.', badge:'Native crop' };
  }
  if (mode === 'crop_remove_sides_1688') {
    if (srcW < 3000 || srcH < 1688) return { kind:'warn', title:'True crop is not available', detail:`Source is ${srcW}x${srcH}. This mode has to enlarge the image to reach 3000x1688.`, badge:'Upscaling', previewClass:'warn', icon:'!' };
    return { ...info, detail:'A true 3000x1688 crop is available after trimming the sides.', badge:'Native crop' };
  }
  if (mode === 'pad_lr_1688') {
    return { kind:'notice', title:'Padding mode', detail:'This mode keeps the full image and adds white sides instead of cropping.', badge:'Padding', previewClass:'notice', icon:'i' };
  }
  if (mode === 'pad_tb_2200') {
    return { kind:'notice', title:'Padding mode', detail:'This mode keeps the full image and adds white top and bottom space instead of cropping.', badge:'Padding', previewClass:'notice', icon:'i' };
  }
  return info;
}

function renderPrepFeasibility(active, mode) {
  const info = prepFeasibilityInfo(active, mode);
  return {
    info,
    header: `<div class="photo-prep-status ${info.kind}"><div class="photo-prep-status-icon">${escapeHtml(info.icon)}</div><div><div class="photo-prep-status-title">${escapeHtml(info.title)}</div><div class="photo-prep-status-detail">${escapeHtml(info.detail)}</div></div></div>`,
    badge: `<div class="photo-prep-preview-badge">${escapeHtml(info.badge)}</div>`
  };
}

function renderPhotoPrepDrawer() {
  const active = currentActivePhoto();
  if (!active) return '';
  const mode = prepModeFromState();
  const prepStatus = renderPrepFeasibility(active, mode);
  const preview = state.photography.previewUrl
    ? `<div class="photo-prep-preview-drag" draggable="${state.mode === 'assets' ? 'true' : 'false'}" ondragstart="startPreparedPreviewDrag(event)" ondragend="endPreparedPreviewDrag(event)">${prepStatus.badge}<div class="photo-prep-preview-canvas"><img src="${escapeHtml(state.photography.previewUrl)}" alt="Preview" draggable="false" /></div></div>`
    : `<div class="photo-empty">Preview loading...</div>`;
  const swatchControls = `
    <div class="photo-focus-pad photo-focus-pad-stack" aria-label="Swatch crop nudger">
      <div class="photo-focus-row">
        <button type="button" class="jump" onclick="setSwatchCropToTop()" title="Jump swatch to top">${prepArrowIcon('up', true)}</button>
        <button type="button" onclick="nudgeCropY(-1)" title="Move swatch up">${prepArrowIcon('up')}</button>
      </div>
      <div class="photo-focus-row">
        <button type="button" class="jump" onclick="setCropToLeft()" title="Jump swatch all the way left">${prepArrowIcon('left', true)}</button>
        <button type="button" onclick="nudgeCropX(-1)" title="Move swatch left">${prepArrowIcon('left')}</button>
        <button type="button" onclick="nudgeCropX(1)" title="Move swatch right">${prepArrowIcon('right')}</button>
        <button type="button" class="jump" onclick="setCropToRight()" title="Jump swatch all the way right">${prepArrowIcon('right', true)}</button>
      </div>
      <div class="photo-focus-row">
        <button type="button" onclick="nudgeCropY(1)" title="Move swatch down">${prepArrowIcon('down')}</button>
        <button type="button" class="jump" onclick="setSwatchCropToBottom()" title="Jump swatch to bottom">${prepArrowIcon('down', true)}</button>
      </div>
    </div>`;
  const squareControls = `
    <div class="photo-focus-pad" aria-label="Square crop nudger">
      <button type="button" class="jump" onclick="setCropToLeft()" title="Jump crop all the way left">${prepArrowIcon('left', true)}</button>
      <button type="button" onclick="nudgeCropX(-1)" title="Move crop left">${prepArrowIcon('left')}</button>
      <button type="button" onclick="nudgeCropX(1)" title="Move crop right">${prepArrowIcon('right')}</button>
      <button type="button" class="jump" onclick="setCropToRight()" title="Jump crop all the way right">${prepArrowIcon('right', true)}</button>
    </div>`;
  const verticalControls = `
    <div class="photo-focus-pad" aria-label="Crop nudger">
      <button type="button" class="jump" onclick="setCropToTop()" title="Jump crop to top">${prepArrowIcon('up', true)}</button>
      <button type="button" onclick="nudgeCropY(-1)" title="Move crop up">${prepArrowIcon('up')}</button>
      <button type="button" onclick="nudgeCropY(1)" title="Move crop down">${prepArrowIcon('down')}</button>
      <button type="button" class="jump" onclick="setCropToBottom()" title="Jump crop to bottom">${prepArrowIcon('down', true)}</button>
    </div>`;
  return `
    <div class="photo-prep-drawer">
      <div class="photo-prep-top">
        <h4>Prep drawer</h4>
        <div class="photo-prep-actions">
          <button type="button" class="btn btn-secondary photo-mini-btn" onclick="clearPhotoSelection()">Clear selection</button>
          <button type="button" class="btn btn-primary photo-mini-btn" onclick="downloadPreparedPhotos(false)">Download modified image</button>
          ${state.mode === 'assets' && active.from_board ? `<button type="button" class="btn btn-secondary photo-mini-btn ${state.photography.prep.addingVersion ? 'btn-reload-flashing' : ''}" ${state.photography.prep.addingVersion ? 'disabled' : ''} onclick="addPreparedAsNewVersion()">${state.photography.prep.addingVersion ? 'Adding...' : 'Add as new version'}</button>` : ''}
        </div>
      </div>
      <div class="photo-prep-controls">
        <div class="photo-prep-toolbar">
          <div class="photo-prep-note"><strong>Output size:</strong> ${escapeHtml(prepModeOutputSize(mode, active))}</div>
          <div class="photo-prep-left">
            <details class="photo-prep-details" ${state.photography.prep.optionsOpen !== false ? 'open' : ''} ontoggle="setPrepOptionsOpen(this.open)"><summary><span>Crop options</span><span class="photo-prep-summary-caret">▾</span></summary><div class="photo-prep-options">
              <label title="Mirrors the image left-to-right before any crop or padding is applied. Use this to reverse orientation while preserving scale and aspect ratio."><input type="checkbox" ${state.photography.prep.flip ? 'checked' : ''} onchange="setPrepFlip(this.checked)" /> Flip horizontally</label>
              <label title="Keeps the original image exactly as-is with no crop, resize, or padding."><input type="radio" name="prepMode" value="original" ${mode==='original'?'checked':''} onchange="setPrepMode(this.value)" /> Original size</label>
              <label title="Scales the image to cover a 3000x1688 frame and crops away excess area. No white padding is added."><input type="radio" name="prepMode" value="crop_1688" ${mode==='crop_1688'?'checked':''} onchange="setPrepMode(this.value)" /> Crop to 3000x1688</label>
              <label title="Scales the image to cover a 3000x2200 frame and crops away excess area. Good when you need a taller canvas with no padding."><input type="radio" name="prepMode" value="crop_2200" ${mode==='crop_2200'?'checked':''} onchange="setPrepMode(this.value)" /> Crop to 3000x2200</label>
              <label title="Resizes proportionally to 1688 px tall, then trims equal amounts from the left and right to land at 3000 px wide."><input type="radio" name="prepMode" value="crop_remove_sides_1688" ${mode==='crop_remove_sides_1688'?'checked':''} onchange="setPrepMode(this.value)" /> Crop to 3000x1688 and remove sides</label>
              <label title="Fits the full image inside a 3000x1688 canvas without cropping and fills the leftover side space with white."><input type="radio" name="prepMode" value="pad_lr_1688" ${mode==='pad_lr_1688'?'checked':''} onchange="setPrepMode(this.value)" /> 3000x1688 with white sides</label>
              <label title="Fits the full image inside a 3000x2200 canvas without cropping and fills the leftover top and bottom space with white."><input type="radio" name="prepMode" value="pad_tb_2200" ${mode==='pad_tb_2200'?'checked':''} onchange="setPrepMode(this.value)" /> 3000x1688 with white top/bottom</label>
              <label title="Takes the largest possible square crop from the source image and preserves only that square area."><input type="radio" name="prepMode" value="crop_square" ${mode==='crop_square'?'checked':''} onchange="setPrepMode(this.value)" /> Crop to largest square</label>
              <label title="Takes the largest possible square crop from the source image, then outputs it as a 163x163 swatch."><input type="radio" name="prepMode" value="crop_swatch" ${mode==='crop_swatch'?'checked':''} onchange="setPrepMode(this.value)" /> Crop swatch</label>
              <label title="Places a true 163x163 crop box on the source image so you can move it around and output a final 163x163 swatch."><input type="radio" name="prepMode" value="pick_swatch" ${mode==='pick_swatch'?'checked':''} onchange="setPrepMode(this.value)" /> Pick swatch</label>
            </div>
            ${((mode === 'crop_1688' || mode === 'crop_2200' || mode === 'crop_square' || mode === 'pick_swatch')) ? `<div class="photo-prep-focusbox">
              ${mode === 'crop_square' ? `${squareControls}
              <div class="photo-focus-meta">
                <span class="photo-prep-note">Use the left and right arrows to move the square crop box.</span>
                <span class="photo-prep-note">Jump buttons move it all the way left or right.</span>
                <span class="photo-prep-note">Click Add as new version to apply your modified image to this asset.</span>
              </div>` : mode === 'pick_swatch' ? `${swatchControls}
              <div class="photo-focus-meta">
                <span class="photo-prep-note">Use the arrows to move the 163x163 swatch crop box.</span>
                <span class="photo-prep-note">Top row controls vertical movement. Middle row controls horizontal movement.</span>
                <span class="photo-prep-note">Click Add as new version to apply your modified image to this asset.</span>
              </div>` : `${verticalControls}
              <div class="photo-focus-meta">
                <span class="photo-prep-note">Use the up and down arrows to move the crop box a little.</span>
                <span class="photo-prep-note">Jump buttons move it all the way to the top or bottom.</span>
                <span class="photo-prep-note">Click Add as new version to apply your modified image to this asset.</span>
              </div>` }
            </div>` : ''}
          </div>
        </div>
        <div class="photo-prep-preview-wrap">
          <div class="photo-prep-preview-meta">${prepStatus.header}</div>
          <div class="photo-prep-preview ${prepStatus.info.previewClass}">${preview}</div>
        </div>
      </div>
    </div>`;
}

async function refreshPhotoPreview() {
  const active = currentActivePhoto();
  if (!active) { state.photography.previewUrl=''; renderPhotographyPanel(); return; }
  const mode = prepModeFromState();
  const offsetY = activePhotoOffsetY(active.id);
  const offsetX = activePhotoOffsetX(active.id);
  try {
    const resp = await fetch('/api/photo_prep_preview', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({media_id: active.id, mode, flip: !!state.photography.prep.flip, offset_y: offsetY, offset_x: offsetX, apply_watermark: !active.is_final})});
    if (!resp.ok) throw new Error('Preview failed');
    const blob = await resp.blob();
    if (state.photography.previewUrl && state.photography.previewUrl.startsWith('blob:')) URL.revokeObjectURL(state.photography.previewUrl);
    state.photography.previewUrl = URL.createObjectURL(blob);
    renderPhotographyPanel();
  } catch (err) { console.error(err); }
}

function modifyBoardAsset(event, assetId) {
  if (event) {
    event.preventDefault();
    event.stopPropagation();
  }
  if (!state.board || !assetId) return;
  let found = null;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      const asset = (row.assets || []).find(a => String(a.id || '') === String(assetId || ''));
      if (asset) {
        found = {
          id: String(asset.id || ''),
          name: String(asset.name || asset.file_name || ''),
          file_name: String(asset.file_name || asset.name || 'asset.jpg'),
          dateCreated: String(asset.dateCreated || ''),
          original: String(asset.original || ''),
          transformBaseUrl: String(asset.transformBaseUrl || ''),
          width: Number(asset.width || 0),
          height: Number(asset.height || 0),
          source: 'Board Asset',
          asset_status: String(asset.asset_status || ''),
          is_final: !!asset.is_final,
          tags: [],
          matching_skus: [String(row.sku || '')],
          from_board: true,
          source_row_id: String(row.row_id || ''),
          source_lane: String(asset.lane || ''),
          source_slot: String(asset.slot_key || ''),
        };
        break;
      }
    }
    if (found) break;
  }
  if (!found) return;

  state.photography.items = [found, ...(state.photography.items || []).filter(x => String(x.id || '') !== String(found.id || ''))];
  state.photography.expanded = true;
  state.photography.selectedIds = [found.id];
  state.photography.activeId = found.id;
  if (state.photography.previewUrl && state.photography.previewUrl.startsWith('blob:')) URL.revokeObjectURL(state.photography.previewUrl);
  state.photography.previewUrl = '';
  state.photography.prep = { flip: false, mode: 'original', offsetYOverrides: {}, offsetXOverrides: {}, optionsOpen: true };
  renderPhotographyPanel();
  refreshPhotoPreview();
}


function findAssetAndRowById(assetId) {
  if (!state.board || !assetId) return {asset:null,row:null};
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      const asset = (row.assets || []).find(a => String(a.id || '') === String(assetId || ''));
      if (asset) return {asset, row};
    }
  }
  return {asset:null,row:null};
}

async function queueDeliverableFix(event, assetId) {
  if (event) { event.preventDefault(); event.stopPropagation(); }
  const found = findAssetAndRowById(assetId);
  if (!found.asset || !found.row) return;
  try {
    const resp = await fetch('/api/queue_deliverable_fix', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({asset_id: assetId || ''})
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not queue Deliverable fix');
    state.board = data.board || state.board;
    state.summary = data.summary || state.summary;
    markAssetModeDirtyRows(data.dirty_row_ids || [found.row.row_id || found.row.id]);
    renderBoard();
    if (data.notice && (data.notice.text || data.notice.html)) addAppNotice(data.notice.text || '', data.notice.kind || 'success', data.notice.html || '');
  } catch (err) {
    alert(err.message || String(err));
  }
}

function normalizePsaImageTypeChoice(value) {
  const raw = String(value || '').trim();
  if (!raw) return '';
  const lower = raw.toLowerCase();
  const match = ['Detail', 'Room_shot', 'Silo', 'Swatch_detail'].find(x => x.toLowerCase() === lower);
  return match || '';
}

function resolvePreparedPhotoPsaImageType(active) {
  if (!active || active.from_board) return '';
  const mapped = normalizePsaImageTypeChoice((window.PHOTO_TO_PSA_IMAGE_TYPE_MAP || {})[String(active.image_type || '')] || '');
  if (mapped) return mapped;
  const message = [
    'This photography asset does not have a clean Image Type to PSA Image Type match yet.',
    'Please choose the PSA Image Type for the asset you are about to upload or update.',
    '',
    'Choices: Detail, Room_shot, Silo, Swatch_detail'
  ].join('\n');
  const picked = window.prompt(message, 'Room_shot');
  const normalized = normalizePsaImageTypeChoice(picked);
  if (!normalized) {
    alert('Please enter one of these PSA Image Type values exactly: Detail, Room_shot, Silo, or Swatch_detail.');
    return null;
  }
  return normalized;
}

async function addPreparedAsNewVersion() {
  const active = currentActivePhoto();
  if (!active || !active.from_board) return;
  if (state.mode !== 'assets') {
    alert('Add as new version is only available in Update assets mode.');
    return;
  }
  state.photography.prep.addingVersion = true;
  renderPhotographyPanel();
  try {
    const resp = await fetch('/api/prepared_add_as_new_version', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({
        media_id: active.id,
        file_name: active.file_name || active.name || 'prepared_image.jpg',
        mode: state.mode,
        prep_mode: prepModeFromState(),
        flip: !!state.photography.prep.flip,
        offset_y: activePhotoOffsetY(active.id),
        offset_x: activePhotoOffsetX(active.id),
      })
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not add new version');
    state.board = data.board || state.board;
    state.summary = data.summary || state.summary;
    if (data.asset_mode_refresh_pending) state.assetModeDirty = true;
    markAssetModeDirtyRows(data.dirty_row_ids || [active.source_row_id || active.id]);
    renderBoard();
    if (data.notice && (data.notice.text || data.notice.html)) addAppNotice(data.notice.text || '', data.notice.kind || 'success', data.notice.html || '');
  } catch (err) {
    alert(err.message || String(err));
  }
}

async function pullAdditionalPhotographyForSku(event, sku, btnEl=null) {
  if (event) {
    event.preventDefault();
    event.stopPropagation();
  }
  if (!state.loadedCollectionOptionId || !sku) return;
  const prevText = btnEl ? btnEl.textContent : '';
  if (btnEl) {
    btnEl.disabled = true;
    btnEl.textContent = 'Pulling...';
  }
  try {
    const resp = await fetch('/api/pull_additional_photography_for_sku', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({
        option_id: state.loadedCollectionOptionId,
        sku,
        existing_ids: (state.photography.items || []).map(x => x.id),
      })
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not pull additional photography');
    const items = data.items || [];
    if (!items.length) {
      state.additionalPhotoAvailabilityBySku[sku] = false;
      renderBoard();
      addAppNotice(`No additional product photography was found for SKU ${sku}.`, 'notice');
      return;
    }
    state.photography.items = [...(state.photography.items || []), ...items];
    if (!state.photography.expanded) state.photography.expanded = true;
    if (!state.photography.color) state.photography.color = data.color || state.photography.color || '';
    state.additionalPhotoAvailabilityBySku[sku] = false;
    renderPhotographyPanel();
    renderBoard();
    addAppNotice(`${items.length} additional product photography asset(s) were added for SKU ${sku}.`, 'success');
  } catch (err) {
    if (btnEl) {
      btnEl.disabled = false;
      btnEl.textContent = prevText || 'Pull additional photography for this SKU';
    }
    alert(err.message || String(err));
  }
}

async function loadNonCollectionSkuFromPhoto(event, sku, btnEl=null) {
  if (event) {
    event.preventDefault();
    event.stopPropagation();
  }
  if (!state.board || !sku) return;
  if (boardHasSku(sku)) {
    jumpToComponentSku(null, sku);
    return;
  }
  state.nonCollectionSkuLoading[sku] = true;
  if (btnEl) {
    btnEl.disabled = true;
    btnEl.textContent = 'Loading...';
  }
  renderPhotographyPanel();
  try {
    const resp = await fetch('/api/load_non_collection_sku', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({ sku })
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not load SKU');
    state.board = data.board || state.board;
    state.summary = data.summary || computeClientSummary();
    state.collapsedColors['Non-Collection SKUs'] = false;
    renderBoard();
    ensureAdditionalPhotoAvailabilityForColor('Non-Collection SKUs', true);
    jumpToRow(String(sku), 'Non-Collection SKUs', '');
    addAppNotice(data.already_present ? `SKU ${sku} is already on the board.` : `SKU ${sku} was loaded into Non-Collection SKUs.`, 'success');
  } catch (err) {
    alert(err.message || String(err));
  } finally {
    delete state.nonCollectionSkuLoading[sku];
    renderPhotographyPanel();
  }
}

function togglePhotoSelection(event, photoId) {
  event.preventDefault(); event.stopPropagation();
  const isSame = state.photography.activeId === photoId && (state.photography.selectedIds || []).includes(photoId);
  if (isSame) {
    state.photography.selectedIds = [];
    state.photography.activeId = '';
    if (state.photography.previewUrl && state.photography.previewUrl.startsWith('blob:')) URL.revokeObjectURL(state.photography.previewUrl);
    state.photography.previewUrl = '';
    renderPhotographyPanel();
    return;
  }
  state.photography.selectedIds = [photoId];
  state.photography.activeId = photoId;
  renderPhotographyPanel();
  refreshPhotoPreview();
}
function setActivePhoto(photoId) { state.photography.activeId = photoId; renderPhotographyPanel(); refreshPhotoPreview(); }
function clearPhotoSelection() { state.photography.selectedIds=[]; state.photography.activeId=''; if (state.photography.previewUrl && state.photography.previewUrl.startsWith('blob:')) URL.revokeObjectURL(state.photography.previewUrl); state.photography.previewUrl=''; renderPhotographyPanel(); }
function setPrepFlip(v) { state.photography.prep.flip = !!v; refreshPhotoPreview(); }
function setPrepOptionsOpen(isOpen) {
  state.photography.prep.optionsOpen = !!isOpen;
}
function keepPrepOptionsOpen() {
  state.photography.prep.optionsOpen = true;
}
function setPrepMode(v) {
  state.photography.prep.mode = v || 'original';
  state.photography.prep.offsetYOverrides = state.photography.prep.offsetYOverrides || {};
  state.photography.prep.offsetXOverrides = state.photography.prep.offsetXOverrides || {};
  state.photography.prep.optionsOpen = false;
  renderPhotographyPanel();
  refreshPhotoPreview();
}
function cropStepYForActive() {
  const active = currentActivePhoto();
  if (!active) return 50;
  const mode = prepModeFromState();
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return 50;
  if (mode === 'pick_swatch') {
    return Math.max(8, Math.round(Math.max(0, srcH - Math.min(163, srcH)) * 0.04) || 12);
  }
  const outH = mode === 'crop_2200' ? 2200 : 1688;
  const scaledH = Math.round(srcH * (3000 / srcW));
  return Math.max(10, Math.round(Math.max(0, scaledH - outH) * 0.025) || 14);
}
function nudgeCropY(direction) {
  const active = currentActivePhoto();
  if (!active) return;
  const mode = prepModeFromState();
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return;
  if (mode === 'pick_swatch') {
    const cropH = Math.min(163, srcH);
    const maxOff = Math.max(0, srcH - cropH);
    const current = activePhotoOffsetY(active.id);
    const next = Math.max(0, Math.min(maxOff, current + (Number(direction || 0) * cropStepYForActive())));
    state.photography.prep.offsetYOverrides[active.id] = next;
  keepPrepOptionsOpen();
  renderPhotographyPanel();
  refreshPhotoPreview();
    return;
  }
  if (!(mode === 'crop_1688' || mode === 'crop_2200')) return;
  const outH = mode === 'crop_2200' ? 2200 : 1688;
  const scaledH = Math.round(srcH * (3000 / srcW));
  const maxOff = Math.max(0, scaledH - outH);
  const current = activePhotoOffsetY(active.id);
  const next = Math.max(0, Math.min(maxOff, current + (Number(direction || 0) * cropStepYForActive())));
  state.photography.prep.offsetYOverrides[active.id] = next;
  keepPrepOptionsOpen();
  renderPhotographyPanel();
  refreshPhotoPreview();
}
function setCropToTop() { const active = currentActivePhoto(); if (!active) return; state.photography.prep.offsetYOverrides[active.id] = 0; keepPrepOptionsOpen(); renderPhotographyPanel(); refreshPhotoPreview(); }
function setCropToBottom() { const active = currentActivePhoto(); if (!active) return; const mode = prepModeFromState(); const srcW = Number(active.width || 0) || 0; const srcH = Number(active.height || 0) || 0; if (!srcW || !srcH) return; if (mode === 'pick_swatch') { state.photography.prep.offsetYOverrides[active.id] = Math.max(0, srcH - Math.min(163, srcH)); keepPrepOptionsOpen(); renderPhotographyPanel(); refreshPhotoPreview(); return; } const outH = mode === 'crop_2200' ? 2200 : 1688; const scaledH = Math.round(srcH * (3000 / srcW)); state.photography.prep.offsetYOverrides[active.id] = Math.max(0, scaledH - outH); keepPrepOptionsOpen(); renderPhotographyPanel(); refreshPhotoPreview(); }
function setSwatchCropToTop() { const active = currentActivePhoto(); if (!active) return; state.photography.prep.offsetYOverrides[active.id] = 0; keepPrepOptionsOpen(); renderPhotographyPanel(); refreshPhotoPreview(); }
function setSwatchCropToBottom() { const active = currentActivePhoto(); if (!active) return; const srcH = Number(active.height || 0) || 0; if (!srcH) return; state.photography.prep.offsetYOverrides[active.id] = Math.max(0, srcH - Math.min(163, srcH)); keepPrepOptionsOpen(); renderPhotographyPanel(); refreshPhotoPreview(); }
function cropStepXForActive() {
  const active = currentActivePhoto();
  if (!active) return 50;
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return 50;
  if (prepModeFromState() === 'pick_swatch') {
    return Math.max(6, Math.round(Math.max(0, srcW - Math.min(163, srcW)) * 0.02) || 10);
  }
  const side = Math.min(srcW, srcH);
  return Math.max(10, Math.round(Math.max(0, srcW - side) * 0.025) || 14);
}
function nudgeCropX(direction) {
  const active = currentActivePhoto();
  if (!active) return;
  if (prepModeFromState() !== 'crop_square' && prepModeFromState() !== 'crop_swatch' && prepModeFromState() !== 'pick_swatch') return;
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return;
  const mode = prepModeFromState();
  const maxOff = mode === 'pick_swatch'
    ? Math.max(0, srcW - Math.min(163, srcW))
    : Math.max(0, srcW - Math.min(srcW, srcH));
  const current = activePhotoOffsetX(active.id);
  const next = Math.max(0, Math.min(maxOff, current + (Number(direction || 0) * cropStepXForActive())));
  state.photography.prep.offsetXOverrides[active.id] = next;
  keepPrepOptionsOpen();
  renderPhotographyPanel();
  refreshPhotoPreview();
}
function setCropToLeft() {
  const active = currentActivePhoto();
  if (!active) return;
  state.photography.prep.offsetXOverrides[active.id] = 0;
  keepPrepOptionsOpen();
  renderPhotographyPanel();
  refreshPhotoPreview();
}
function setCropToRight() {
  const active = currentActivePhoto();
  if (!active) return;
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return;
  const mode = prepModeFromState();
  const maxOff = mode === 'pick_swatch'
    ? Math.max(0, srcW - Math.min(163, srcW))
    : Math.max(0, srcW - Math.min(srcW, srcH));
  state.photography.prep.offsetXOverrides[active.id] = maxOff;
  refreshPhotoPreview();
}

function handlePhotoPrepArrowKeys(event) {
  if (!state.photography || !state.photography.activeId) return;
  const target = event.target;
  if (target) {
    const tag = String(target.tagName || '').toUpperCase();
    if (tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT' || target.isContentEditable) return;
  }
  const mode = prepModeFromState();
  if (!mode) return;
  if (mode === 'pick_swatch') {
    if (event.key === 'ArrowLeft') { event.preventDefault(); nudgeCropX(-1); return; }
    if (event.key === 'ArrowRight') { event.preventDefault(); nudgeCropX(1); return; }
    if (event.key === 'ArrowUp') { event.preventDefault(); nudgeCropY(-1); return; }
    if (event.key === 'ArrowDown') { event.preventDefault(); nudgeCropY(1); return; }
    return;
  }
  if (mode === 'crop_square') {
    if (event.key === 'ArrowLeft') { event.preventDefault(); nudgeCropX(-1); return; }
    if (event.key === 'ArrowRight') { event.preventDefault(); nudgeCropX(1); return; }
    return;
  }
  if (mode === 'crop_1688' || mode === 'crop_2200') {
    if (event.key === 'ArrowUp') { event.preventDefault(); nudgeCropY(-1); return; }
    if (event.key === 'ArrowDown') { event.preventDefault(); nudgeCropY(1); return; }
  }
}
function currentPreparedPreviewPayload() {
  const active = currentActivePhoto();
  if (!active) return null;
  return {
    media_id: active.id,
    source_media_id: active.id,
    prep_mode: prepModeFromState(),
    flip: !!state.photography.prep.flip,
    offset_y: activePhotoOffsetY(active.id),
    offset_x: activePhotoOffsetX(active.id),
    source_is_board_asset: !!active.from_board,
    source_photo_image_type: String(active.image_type || ''),
  };
}

function startPreparedPreviewDrag(event) {
  if (state.mode !== 'assets') {
    event.preventDefault();
    return;
  }
  const payload = currentPreparedPreviewPayload();
  if (!payload) {
    event.preventDefault();
    return;
  }
  state.preparedPreviewDrag = payload;
  const wrap = event.currentTarget;
  if (wrap) wrap.classList.add('dragging');
  try {
    const encoded = JSON.stringify(payload);
    event.dataTransfer.clearData();
    event.dataTransfer.setData('application/x-prepared-photo', encoded);
    event.dataTransfer.setData('text/plain', 'prepared-preview');
    event.dataTransfer.effectAllowed = 'copy';
    const img = wrap ? wrap.querySelector('img') : null;
    if (img) event.dataTransfer.setDragImage(img, Math.round(img.width / 2), Math.round(img.height / 2));
  } catch (err) {}
}

function endPreparedPreviewDrag(event) {
  state.preparedPreviewDrag = null;
  const wrap = event.currentTarget;
  if (wrap) wrap.classList.remove('dragging');
}

async function downloadPreparedPhotos(allSelected) {
  const active = currentActivePhoto();
  const targets = active ? [active] : [];
  if (!targets.length) return;
  const mode = prepModeFromState();
  const items = targets.map(item => ({media_id:item.id, name:item.file_name||item.name||item.id, offset_y:activePhotoOffsetY(item.id), offset_x:activePhotoOffsetX(item.id)}));
  const resp = await fetch('/api/photo_prep_download', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({items, flip:!!state.photography.prep.flip, mode})});
  if (!resp.ok) { const data=await resp.json().catch(()=>({})); alert(data.error || 'Download failed'); return; }
  const blob = await resp.blob();
  const cd = resp.headers.get('Content-Disposition') || '';
  let fname = 'photo_prep_download'; const m = /filename="?([^";]+)"?/.exec(cd); if (m) fname = m[1];
  const url = URL.createObjectURL(blob); const a=document.createElement('a'); a.href=url; a.download=fname; document.body.appendChild(a); a.click(); a.remove(); setTimeout(()=>URL.revokeObjectURL(url),1000);
}

function renderPhotographyPanel() {
  const shell = document.getElementById('photoShell');
  const body = document.getElementById('photoBody');
  const sub = document.getElementById('photoSub');
  const toggleBtn = document.getElementById('photoToggleBtn');
  const hideFpoToggle = document.getElementById('hideFpoToggle');
  const hideReviewedToggle = document.getElementById('hideReviewedToggle');
  if (!shell || !body || !sub || !toggleBtn) return;

  const photo = state.photography;
  document.documentElement.style.setProperty('--photo-panel-width', photo.expanded ? `${photo.width}px` : '56px');
  document.documentElement.style.setProperty('--photo-thumb-height', `${photo.thumb}px`);
  document.documentElement.style.setProperty('--photo-tile-min', `${Math.max(190, Math.round(photo.thumb * 1.02))}px`);

  shell.classList.toggle('collapsed', !photo.expanded);
  toggleBtn.textContent = photo.expanded ? 'Collapse' : '';
  toggleBtn.title = photo.expanded ? 'Collapse Photography panel' : 'Expand Photography panel';
  toggleBtn.setAttribute('aria-label', photo.expanded ? 'Collapse Photography panel' : 'Expand Photography panel');

  if (!photo.expanded) {
    body.innerHTML = `<div class="photo-collapsed-tease" aria-hidden="true"><div class="photo-collapsed-arrow">></div><div class="photo-collapsed-spark">ready to play</div></div>`;
    sub.textContent = photo.color ? `Loaded ${photo.color} photography.` : 'Reference panel for available product photography in the selected collection/color.';
    return;
  }

  if (hideFpoToggle) hideFpoToggle.checked = !!photo.hideFpo;
  if (hideReviewedToggle) hideReviewedToggle.checked = !!photo.hideReviewed;

  const isPIO = state.workspace === 'product_imagery_onboarding';
  const collectionOptions = (state.bynderCollections || []).map(c => `<option value="${escapeHtml(c.name)}"></option>`).join('');
  const loadedTypes = Array.from(new Set((photo.items || []).map(x => String(x.image_type || '').trim()).filter(Boolean))).sort((a,b)=>a.localeCompare(b));
  const loadedSkuOptions = Array.from(new Set((photo.items || []).flatMap(x => (x.sku_tags || x.tags || []).map(t => String(t || '').trim()).filter(Boolean)))).sort((a,b)=>a.localeCompare(b));
  const bynderCollectionInputDisabled = !!(state.bynderCollectionsLoading || !(state.bynderCollections || []).length);
  const bynderCollectionPlaceholder = state.bynderCollectionsLoading ? 'Loading Bynder collection options...' : ((state.bynderCollections || []).length ? 'Search Bynder collection' : 'Loading Bynder collection options...');
  const pioToolbar = isPIO ? `<div class="photo-pio-toolbar"><div class="photo-pio-row"><input type="text" id="pioPhotoCollectionInput" list="pioPhotoCollectionOptions" placeholder="${escapeHtml(bynderCollectionPlaceholder)}" value="${escapeHtml(photo.collectionSearch || '')}" ${bynderCollectionInputDisabled ? 'disabled' : ''} /><datalist id="pioPhotoCollectionOptions">${collectionOptions}</datalist><button type="button" id="pioLoadCollectionBtn" class="btn btn-secondary photo-mini-btn ${(photo.collectionLoading || state.bynderCollectionsLoading) ? 'btn-reload-flashing' : ''}" ${(photo.collectionLoading || state.bynderCollectionsLoading || bynderCollectionInputDisabled) ? 'disabled' : ''} onclick="loadPIOPhotographyCollection()">${(photo.collectionLoading || state.bynderCollectionsLoading) ? 'Loading Bynder collection...' : 'Load Bynder collection'}</button></div><div class="photo-pio-row filters"><label class="small-inline">Image Type</label><select id="pioPhotoImageTypeFilter" class="pio-filter-select" onchange="setPIOPhotoImageTypeFilter(this.value)"><option value="">All image types</option>${loadedTypes.map(v=>`<option value="${escapeHtml(v)}" ${String(photo.imageTypeFilter||'')===String(v)?'selected':''}>${escapeHtml(v)}</option>`).join('')}</select><label class="small-inline">SKU</label><select id="pioPhotoSkuFilter" class="pio-filter-select" onchange="setPIOPhotoSkuFilter(this.value)"><option value="">All tagged SKUs</option>${loadedSkuOptions.map(v=>`<option value="${escapeHtml(v)}" ${String(photo.skuFilter||'')===String(v)?'selected':''}>${escapeHtml(v)}</option>`).join('')}</select>${photo.skuFilter ? `<button type="button" class="btn btn-secondary photo-mini-btn" onclick="setPIOPhotoSkuFilter('')">Clear</button>` : ''}</div></div>` : '';
  if (!photo.items.length) {
    sub.textContent = isPIO ? 'Search for a Bynder collection, load it, then filter its assets by Image Type or tagged SKU.' : 'Reference panel for available product photography in the selected collection/color.';
    const standaloneDrawer = renderSetDimDrawer();
    body.innerHTML = `${pioToolbar}${standaloneDrawer || ''}${standaloneDrawer ? '' : `<div class="photo-empty">${isPIO ? 'Search for a Bynder collection and click Load collection.' : 'Pull available product photography from a color header to load this panel.'}</div>`}`;
    return;
  }

  const visibleItems = getVisiblePhotographyItems();
  if (!visibleItems.length) {
    const filterBits = [];
    if (photo.imageTypeFilter) filterBits.push(`Image Type: ${photo.imageTypeFilter}`);
    if (photo.skuFilter) filterBits.push(`SKU: ${photo.skuFilter}`);
    if (photo.hideFpo) filterBits.push('Hide FPO');
    if (photo.hideReviewed) filterBits.push('Hide reviewed');
    const filterSummary = filterBits.length ? ` Active filters: ${filterBits.join(' | ')}.` : '';
    sub.textContent = `${photo.items.length} photography asset(s) loaded. None match the active filters.${filterSummary}`;
    const standaloneDrawer = renderSetDimDrawer();
    body.innerHTML = `${pioToolbar}${standaloneDrawer || ''}<div class="photo-empty" style="border:2px dashed #c96b6b; background:#fff4f4; color:#7c2830; font-weight:700;">No loaded photography matches the current filter.${photo.skuFilter ? `<br><span style="font-weight:600;">Filtered SKU: ${escapeHtml(photo.skuFilter)}</span>` : ''}${filterBits.length ? `<br><span style="font-weight:500;">${escapeHtml(filterBits.join(' | '))}</span>` : ''}</div>`;
    return;
  }

  const hiddenCount = Math.max(0, (photo.items || []).length - visibleItems.length);
  const activeFilters = [];
  if (photo.hideFpo) activeFilters.push('Hide FPO');
  if (photo.hideReviewed) activeFilters.push('Hide reviewed');
  const photoLabel = photo.color || photo.collectionSearch || 'loaded collection';
  sub.textContent = hiddenCount ? `${visibleItems.length} photography asset(s) shown for ${photoLabel}. ${hiddenCount} hidden by ${activeFilters.join(' and ')}.` : `${visibleItems.length} photography asset(s) for ${photoLabel}.`;
  const prepDrawer = renderSetDimDrawer() || renderPhotoPrepDrawer();
  body.innerHTML = `${pioToolbar}${prepDrawer || ''}<div class="photo-grid">${visibleItems.map(renderPhotoTile).join('')}</div>`;
  bindPhotographyDnD();
}

function togglePhotoSkuDrawer(assetId) {
  state.photoSkuOpen[assetId] = !state.photoSkuOpen[assetId];
  renderPhotographyPanel();
}

function loadPhotographyPayloadToState(data, fallbackColor='') {
  const color = (data && data.color) || fallbackColor || '';
  state.photography.items = (data && data.items) || [];
  state.photography.color = color;
  state.photography.expanded = true;
  state.photography.activeSkuSet = [];
  state.photography.selectedIds = [];
  state.photography.activeId = '';
  if (state.photography.previewUrl && state.photography.previewUrl.startsWith('blob:')) URL.revokeObjectURL(state.photography.previewUrl);
  state.photography.previewUrl = '';
  state.photography.prep = { flip: false, mode: 'original', offsetYOverrides: {}, offsetXOverrides: {} };
  state.photography.hideFpo = false;
  state.photography.hideReviewed = false;
  state.photography.reviewingIds = {};
  state.photography.imageTypeFilter = '';
  state.photography.skuFilter = '';
  state.photography.collectionSearch = (data && data.collection_label) || state.photography.collectionSearch || '';
  state.additionalPhotoAvailabilityBySku = {};
  state.additionalPhotoCheckInFlight = {};
  for (const section of state.board.color_sections || []) {
    if (String(section.color) === String(color)) {
      state.photography.activeSkuSet = (section.rows || []).map(r => String(r.sku || '')).filter(Boolean);
      break;
    }
  }
  state.photoSkuOpen = {};
  renderPhotographyPanel();
  ensureAdditionalPhotoAvailabilityForColor(color, true);
}

async function pullPhotographyForColor(event, color) {
  if (event) {
    event.preventDefault();
    event.stopPropagation();
  }
  if (!state.board || !state.loadedCollectionOptionId || !color) return;
  if (state.photography.items.length && state.photography.color && state.photography.color !== color) {
    if (!confirm(`Replace the currently loaded photography for ${state.photography.color}?`)) return;
  }
  try {
    const resp = await fetch('/api/load_photography', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({option_id: state.loadedCollectionOptionId, color})
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not load photography');
    loadPhotographyPayloadToState(data, color);
  } catch (err) {
    alert(err.message || String(err));
  }
}

function clearPhotographyPanel() {
  state.photography.items = [];
  state.photography.color = '';
  state.photoSkuOpen = {};
  state.photography.selectedIds = [];
  state.photography.activeId='';
  if (state.photography.previewUrl && state.photography.previewUrl.startsWith('blob:')) URL.revokeObjectURL(state.photography.previewUrl);
  state.photography.previewUrl='';
  clearSetDimSelection();
  state.photography.prep = { flip: false, mode: 'original', offsetYOverrides: {}, offsetXOverrides: {} };
  state.photography.hideFpo = false;
  state.photography.hideReviewed = false;
  state.photography.reviewingIds = {};
  state.photography.imageTypeFilter = '';
  state.photography.skuFilter = '';
  state.additionalPhotoAvailabilityBySku = {};
  state.additionalPhotoCheckInFlight = {};
  renderPhotographyPanel();
}

async function ensureBynderCollectionsLoaded(force=false) {
  if (state.bynderCollectionsLoading) return;
  if (!force && (state.bynderCollections || []).length) return;
  state.bynderCollectionsLoading = true;
  const noticeId = 'bynder-collection-options-loading';
  upsertAppNotice(noticeId, 'Loading Bynder collection options...', 'notice', '', false);
  renderPhotographyPanel();
  try {
    const resp = await fetch('/api/bynder/collections');
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not load Bynder collections');
    state.bynderCollections = data.collections || [];
    upsertAppNotice(noticeId, `Bynder collection options loaded. (${(state.bynderCollections || []).length} collections)`, 'success', '', true);
  } catch (err) {
    console.warn(err);
    upsertAppNotice(noticeId, err.message || 'Could not load Bynder collection options.', 'error', '', true);
  } finally {
    state.bynderCollectionsLoading = false;
    renderPhotographyPanel();
  }
}

function setPIOPhotoImageTypeFilter(value) {
  state.photography.imageTypeFilter = String(value || '');
  refreshActivePhotoSelectionAfterFilter();
  renderPhotographyPanel();
}

function setPIOPhotoSkuFilter(value) {
  state.photography.skuFilter = String(value || '');
  refreshActivePhotoSelectionAfterFilter();
  renderPhotographyPanel();
}

function focusPIOPhotographySku(event, sku) {
  if (event) {
    event.preventDefault();
    event.stopPropagation();
  }
  const value = String(sku || '').trim();
  if (!value) return;
  state.photography.expanded = true;
  state.photography.skuFilter = value;
  refreshActivePhotoSelectionAfterFilter();
  renderPhotographyPanel();
}

async function loadPIOPhotographyCollection() {
  const input = document.getElementById('pioPhotoCollectionInput');
  const label = String((input && input.value) || state.photography.collectionSearch || '').trim();
  if (!label) { alert('Enter a Bynder collection name first.'); return; }
  await ensureBynderCollectionsLoaded(false);
  const options = state.bynderCollections || [];
  let match = options.find(c => String(c.name || '').toLowerCase() === label.toLowerCase());
  if (!match) {
    const matching = options.filter(c => String(c.name || '').toLowerCase().includes(label.toLowerCase()));
    if (matching.length === 1) match = matching[0];
  }
  if (!match) { alert('Could not find that Bynder collection. Choose one from the suggestions.'); return; }
  state.photography.collectionSearch = match.name || label;
  state.photography.collectionLoading = true;
  const noticeId = state.photography.collectionLoadNoticeId || `pio-collection-load-${Date.now()}`;
  state.photography.collectionLoadNoticeId = noticeId;
  upsertAppNotice(noticeId, `Bynder collection photography is loading for ${match.name || label}...`, 'notice', '', false);
  renderPhotographyPanel();
  try {
    const resp = await fetch('/api/onboarding/load_collection_photography', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({ collection_id: match.id, collection_name: match.name })
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not load collection assets');
    loadPhotographyPayloadToState(data, match.name || label);
    const itemCount = Array.isArray(data.items) ? data.items.length : 0;
    upsertAppNotice(noticeId, `Bynder collection photography loaded for ${match.name || label}. (${itemCount} asset${itemCount === 1 ? '' : 's'})`, 'success', '', true);
  } catch (err) {
    upsertAppNotice(noticeId, err.message || String(err), 'error', '', true);
    alert(err.message || String(err));
  } finally {
    state.photography.collectionLoading = false;
    renderPhotographyPanel();
  }
}

function bindPhotographyDnD() {
  document.querySelectorAll('.photo-tile').forEach(tile => {
    tile.addEventListener('dragstart', (e) => {
      state.photoDragId = tile.getAttribute('data-photo-id');
      e.dataTransfer.setData('text/plain', state.photoDragId || '');
    });
    tile.addEventListener('dragover', (e) => {
      e.preventDefault();
      tile.classList.add('dragover');
    });
    tile.addEventListener('dragleave', () => tile.classList.remove('dragover'));
    tile.addEventListener('drop', (e) => {
      e.preventDefault();
      tile.classList.remove('dragover');
      const targetId = tile.getAttribute('data-photo-id');
      const sourceId = e.dataTransfer.getData('text/plain') || state.photoDragId;
      if (!sourceId || !targetId || sourceId === targetId) return;
      const items = [...state.photography.items];
      const from = items.findIndex(i => String(i.id) === String(sourceId));
      const to = items.findIndex(i => String(i.id) === String(targetId));
      if (from < 0 || to < 0) return;
      const [moved] = items.splice(from, 1);
      items.splice(to, 0, moved);
      state.photography.items = items;
      renderPhotographyPanel();
    });
    tile.addEventListener('dragend', () => { state.photoDragId = null; document.querySelectorAll('.photo-tile.dragover').forEach(el => el.classList.remove('dragover')); });
  });
}

function snapshotLaneScrolls() {
  const out = {};
  document.querySelectorAll('.slot-row[data-scroll-key]').forEach(el => {
    out[el.getAttribute('data-scroll-key')] = el.scrollLeft || 0;
  });
  return out;
}

function restoreLaneScrolls(scrolls) {
  if (!scrolls) return;
  document.querySelectorAll('.slot-row[data-scroll-key]').forEach(el => {
    const key = el.getAttribute('data-scroll-key');
    if (Object.prototype.hasOwnProperty.call(scrolls, key)) el.scrollLeft = Number(scrolls[key] || 0);
  });
}

async function applyWallArtSizingGuide(event, rowId) {
  if (event) {
    event.preventDefault();
    event.stopPropagation();
  }
  try {
    const resp = await fetch('/api/apply_wall_art_sizing_guide', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({row_id: rowId})
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not apply wall art sizing guide');
    state.board = data.board;
    state.summary = data.summary;
    if (data.asset_mode_refresh_pending) state.assetModeDirty = true;
    markAssetModeDirtyRows(data.dirty_row_ids || [rowId]);
    renderBoard();
    if (data.notice && (data.notice.text || data.notice.html)) addAppNotice(data.notice.text || '', data.notice.kind || 'success', data.notice.html || '');
  } catch (err) {
    alert(err.message || String(err));
  }
}

function renderBoard() {
  try { saveUIState(); } catch (err) {}
  const host = document.getElementById('boardHost');
  const laneScrolls = snapshotLaneScrolls();
  const changedSet = changedAssetIds();
  const thumbValue = Number(document.getElementById('thumbSize').value || 84);
  document.documentElement.style.setProperty('--thumb-height', thumbValue + 'px');
  document.documentElement.style.setProperty('--slot-width', Math.max(118, Math.round(thumbValue * 1.28)) + 'px');

  if (!state.board) {
    host.innerHTML = '';
    document.getElementById('boardWrap').style.display = 'none';
    return;
  }

  document.getElementById('boardWrap').style.display = 'grid';
  document.getElementById('collectionTitle').textContent = state.board.collection.label;
  for (const section of state.board.color_sections || []) {
    if (!(section.color in state.collapsedColors)) state.collapsedColors[section.color] = true;
  }
  state.loadedCollectionOptionId = state.board.collection.id;
  document.getElementById('collectionMeta').textContent = `Loaded ${new Date(state.board.loaded_at).toLocaleString()}`;
  renderChallengeIssuePill();
  renderModeUI();
  renderNotifications();
  renderPhotographyPanel();
  updateBulkFixSiloControls();
  host.innerHTML = (state.board.color_sections || []).map(section => {
    const visibleRows = (section.rows || []).filter(row => !(state.hideInactive && row.inactive));
    if (!visibleRows.length) return '';
    const collapsed = !!state.collapsedColors[section.color];
    const allInactive = state.workspace === 'product_imagery_onboarding' ? false : ((section.rows || []).length > 0 && (section.rows || []).every(r => r.inactive));
    return `
    <div class="color-section" id="color-${escapeHtml(section.color).replace(/[^A-Za-z0-9_-]/g,'_')}">
      <div class="color-header" data-color-toggle="${escapeHtml(section.color)}">
        <div>${escapeHtml(section.color)} ${allInactive ? `<span class="inactive-all-badge">All products inactive</span>` : ''}</div>
        <div style="display:flex; align-items:center; gap:8px;">
          ${section.is_non_collection
            ? ''
            : Number(section.photo_available_count || 0) > 0
              ? `<button type="button" class="btn btn-secondary photo-mini-btn" onclick="pullPhotographyForColor(event, '${escapeHtml(section.color)}')">Pull available product photography</button>`
              : `<button type="button" class="btn btn-photo-none photo-mini-btn" title="No available product photography for this color.">No available product photography</button>`}
          <button type="button" class="color-toggle">${collapsed ? 'Expand' : 'Collapse'}</button>
        </div>
      </div>
      <div class="color-body ${collapsed ? 'collapsed' : ''}">
        ${visibleRows.map(row => renderRow(row, changedSet)).join('')}
      </div>
    </div>
  `}).join('');

  bindBoardDnD();
  bindWarningDismiss();
  bindColorToggles();
  bindComponentJumps();
  bindUndoCopyButtons();
  restoreLaneScrolls(laneScrolls);
  renderSummary();
  updateQueuedStatus();
}


const SWATCH_OPTIONAL_STEP_PATHS = new Set([
  'RF_Root___Home_Decor___Wall_Art',
  'RF_Root___Home_Decor___Wall_Decor',
  'RF_Root___Home_Decor___Hanging_Lights',
  'RF Root | Home Decor | Hanging Lights'
]);
const SWATCH_OPTIONAL_STEP_PATH_PREFIXES = [
  'RF_Root___Mattresses',
  'RF Root | Mattresses'
];
const WALL_ART_SIZING_STEP_PATHS = new Set([
  'RF_Root___Home_Decor___Wall_Art',
  'RF_Root___Home_Decor___Wall_Decor'
]);

function isSwatchOptionalStepPath(stepPath) {
  const clean = String(stepPath || '').trim();
  const normalized = clean.replace(/\s*\|\s*/g, '___').replace(/\s+/g, '_');
  return SWATCH_OPTIONAL_STEP_PATHS.has(clean) || SWATCH_OPTIONAL_STEP_PATHS.has(normalized) || SWATCH_OPTIONAL_STEP_PATH_PREFIXES.some(prefix => clean.startsWith(prefix) || normalized.startsWith(String(prefix || '').replace(/\s*\|\s*/g, '___').replace(/\s+/g, '_')));
}

function rowRequiresSwatch(row) {
  const stepPath = String((row && (row.step_path || row.property_STEP_Path)) || '').trim();
  return !isSwatchOptionalStepPath(stepPath);
}

function rowRequiresWallArtSizing(row) {
  const stepPath = String((row && (row.step_path || row.property_STEP_Path)) || '').trim();
  return WALL_ART_SIZING_STEP_PATHS.has(stepPath);
}

function expectedDeliverableForAsset(asset) {
  if (!asset) return '';
  const lane = String(asset.lane || '').trim();
  const slot = String(asset.slot_key || '').trim();
  if (!lane || lane === 'off_pattern' || lane === 'trash') return '';
  if (lane === 'core') return 'Product_Image_Carousel';
  if (lane === 'swatch_detail') return 'Product_Swatch_Detail_Image';
  if (lane === 'grid' && slot === 'SKU_grid') return 'Product_Grid_Image';
  if (lane === 'special' && slot === 'SKU_dimension') return 'DimensionsDiagram';
  if (lane === 'special' && slot === 'SKU_swatch') return 'Product_Swatch_Image';
  return '';
}

function assetHasWrongDeliverable(asset) {
  const expected = expectedDeliverableForAsset(asset);
  if (!expected) return false;
  const current = String(asset.deliverable_override || asset.deliverable || '').trim();
  return current !== expected;
}

function assetIsCleanupTotalFillCandidate(asset, row) {
  const warningText = String((asset && asset.size_warning) || '').trim();
  if (!/needs total fill/i.test(warningText)) return false;
  const slotKey = String((asset && (asset.slot_key || asset.current_position)) || '').trim();
  if (slotKey === 'SKU_grid' || slotKey === 'SKU_100') return true;
  if (slotKey !== 'SKU_200') return false;
  const salesChannel = String(((row && row.sales_channel) || (asset && asset.sales_channel) || '')).trim().toLowerCase();
  return salesChannel === 'full_line';
}

function computeClientChallengeIssueCount() {
  if (!state.board) return 0;
  let total = 0;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      if (!rowCountsAsActive(row)) continue;
      const liveAssets = (row.assets || []).filter(a => !a.is_marked_for_deletion && !a.is_empty_slot);
      const hasGrid = liveAssets.some(a => a.slot_key === 'SKU_grid' || String(a.current_position || '').endsWith('_grid'));
      const has100 = liveAssets.some(a => a.slot_key === 'SKU_100' || String(a.current_position || '').endsWith('_100'));
      const hasSwatch = liveAssets.some(a => a.slot_key === 'SKU_swatch' || String(a.current_position || '').endsWith('_swatch'));
      const hasDimension = liveAssets.some(a => a.slot_key === 'SKU_dimension' || String(a.current_position || '').endsWith('_dimension'));
      const has8000 = liveAssets.some(a => a.slot_key === 'SKU_8000' || String(a.current_position || '').endsWith('_8000'));
      const offPatternAssets = liveAssets.filter(a => String(a.lane || '') === 'off_pattern');
      const dupCounts = {};
      for (const asset of liveAssets) {
        const lane = String(asset.lane || '');
        if (lane === 'off_pattern' || lane === 'trash') continue;
        const key = String(asset.last_nontrash_position || asset.current_position || asset.slot_key || '');
        if (!key) continue;
        dupCounts[key] = (dupCounts[key] || 0) + 1;
      }
      const hasDuplicate = Object.values(dupCounts).some(v => Number(v || 0) > 1);
      const wrongDeliverableCount = liveAssets.filter(a => assetHasWrongDeliverable(a)).length;
      if (!hasGrid) total += 1;
      if (!has100) total += 1;
      if (rowRequiresSwatch(row) && !hasSwatch) total += 1;
      if (rowRequiresWallArtSizing(row) && !has8000) total += 1;
      if (!hasDimension && row.set_dim_compile_ready) total += 1;
      if (row.square_make_recommended) total += 1;
      if (offPatternAssets.length) total += 1;
      if (hasDuplicate) total += 1;
      total += wrongDeliverableCount;
      const sizeWarnings = (row.assets || []).filter(a => {
        if (a.is_marked_for_deletion) return false;
        const warningText = String(a.size_warning || '').trim();
        if (!a.has_size_warning && !warningText) return false;
        if (!/needs total fill/i.test(warningText)) return true;
        return assetIsCleanupTotalFillCandidate(a, row);
      }).length;
      total += sizeWarnings;
    }
  }
  return total;
}


function assetNeedsSiloFixForBulk(asset) {
  if (!asset || asset.pending_upload || asset.is_marked_for_deletion) return false;
  const psaType = String(asset.psa_image_type || '').trim().toLowerCase();
  const slotKey = String(asset.slot_key || '').trim();
  const lane = String(asset.lane || '').trim();
  const isDimensionLike = psaType === 'dimensions_diagram_image' || slotKey === 'SKU_dimension' || lane === 'special';
  const isSiloLike = psaType === 'silo' || isDimensionLike;
  if (!isSiloLike) return false;
  const warningText = String(asset.size_warning || '').trim();
  if (!warningText || /needs total fill/i.test(warningText)) return false;
  return slotKey === 'SKU_grid' || lane === 'core' || slotKey === 'SKU_dimension';
}

function assetIsBulkFixSiloTarget(asset) {
  return !!state.bulkFixSiloMode && assetNeedsSiloFixForBulk(asset);
}

function getBulkFixSiloTargets() {
  const targets = [];
  if (!state.board || state.workspace !== 'product_imagery_onboarding') return targets;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      for (const asset of row.assets || []) {
        if (assetNeedsSiloFixForBulk(asset)) {
          const slotKey = String(asset.slot_key || '');
          targets.push({
            media_id: String(asset.id || ''),
            row_id: String(row.row_id || row.sku || ''),
            fix_type: slotKey === 'SKU_grid' ? 'grid' : (slotKey === 'SKU_dimension' ? 'dim' : 'silo')
          });
        }
      }
    }
  }
  return targets.filter(t => t.media_id);
}

function updateBulkFixSiloControls() {
  const wrap = document.getElementById('bulkFixSiloWrap');
  const btn = document.getElementById('bulkFixSiloBtn');
  const goBtn = document.getElementById('bulkFixSiloGoBtn');
  if (!wrap || !btn || !goBtn) return;
  const enabled = !!state.board && state.workspace === 'product_imagery_onboarding' && state.mode === 'assets';
  const targets = getBulkFixSiloTargets();
  wrap.style.display = enabled ? 'inline-flex' : 'none';
  if (!enabled) return;
  btn.textContent = state.bulkFixSiloMode ? `Bulk fix silo (${targets.length})` : 'Bulk fix silo';
  btn.classList.toggle('is-active', !!state.bulkFixSiloMode);
  goBtn.style.display = state.bulkFixSiloMode && targets.length ? 'inline-flex' : 'none';
  goBtn.disabled = state.bulkFixSiloRunning || !targets.length;
  goBtn.classList.toggle('btn-reload-flashing', !!state.bulkFixSiloRunning);
  goBtn.textContent = state.bulkFixSiloRunning ? 'Proceeding...' : 'Proceed';
  btn.disabled = state.bulkFixSiloRunning;
}

function toggleBulkFixSiloMode() {
  state.bulkFixSiloMode = !state.bulkFixSiloMode;
  renderBoard();
}

async function runBulkFixSilo() {
  const targets = getBulkFixSiloTargets();
  if (!targets.length) {
    addAppNotice('No silo assets need bulk fixing on this board right now.', 'notice');
    state.bulkFixSiloMode = false;
    renderBoard();
    return;
  }
  state.bulkFixSiloRunning = true;
  updateBulkFixSiloControls();
  const noticeId = upsertAppNotice('bulk-fix-silo', `Bulk silo fix is running for ${targets.length} asset${targets.length === 1 ? '' : 's'}...`, 'notice', '', false);
  const dirtyRowIds = [];
  let successCount = 0;
  try {
    for (const target of targets) {
      const resp = await fetch('/api/fix_asset_version', {
        method:'POST',
        headers:{'Content-Type':'application/json'},
        body: JSON.stringify({ mode: state.mode, media_id: target.media_id, fix_type: target.fix_type })
      });
      const data = await resp.json().catch(() => ({}));
      if (!resp.ok) throw new Error(data.error || `Bulk silo fix failed for ${target.media_id}`);
      state.board = data.board || state.board;
      state.summary = data.summary || state.summary;
      if (data.asset_mode_refresh_pending) state.assetModeDirty = true;
      (data.dirty_row_ids || []).forEach(id => { if (id) dirtyRowIds.push(id); });
      successCount += 1;
      upsertAppNotice(noticeId, `Bulk silo fix is running... ${successCount}/${targets.length} complete.`, 'notice', '', false);
    }
    markAssetModeDirtyRows(dirtyRowIds);
    state.bulkFixSiloMode = false;
    upsertAppNotice(noticeId, `Bulk silo fix queued ${successCount} asset${successCount === 1 ? '' : 's'} for new versions.`, 'success', 'Click <button type="button" class="inline-link" data-reload-board>Reload</button> to see the updates.', true);
    renderBoard();
  } catch (err) {
    upsertAppNotice(noticeId, err.message || String(err), 'error', '', true);
  } finally {
    state.bulkFixSiloRunning = false;
    updateBulkFixSiloControls();
  }
}

function launchIssueZeroBurst(fromEl) {
  const host = document.getElementById('issueZeroBurst');
  if (!host || !fromEl) return;
  host.innerHTML = '';
  const rect = fromEl.getBoundingClientRect();
  const startX = rect.left + (rect.width / 2);
  const startY = rect.top + Math.min(rect.height * 0.55, 28);
  host.style.setProperty('--flash-x', `${Math.round(startX)}px`);
  host.style.setProperty('--flash-y', `${Math.round(startY)}px`);

  const banner = document.createElement('div');
  banner.className = 'issue-zero-banner';
  banner.innerHTML = `<span class="burst-emoji">🛋️</span><span>Zero issues. Very satisfying.</span><span class="burst-emoji">✨</span>`;
  host.appendChild(banner);

  const furniture = ['🛋️','🪑','🛏️','🪴','🪞','🕯️','🖼️','🪟'];
  const greenPalette = ['#62be74','#4fa85f','#7ad58c','#2f8d49','#9be7aa','#72c97d'];
  const partyPalette = ['#ffd166','#ef476f','#5ec0ff','#c77dff','#ff9f1c','#06d6a0'];
  const totalPieces = 116;
  for (let i = 0; i < totalPieces; i += 1) {
    const particle = document.createElement('span');
    const isFurniture = i >= 88;
    const isParty = !isFurniture && i >= 66;
    if (isFurniture) {
      particle.className = 'issue-zero-particle furniture';
      particle.textContent = furniture[Math.floor(Math.random() * furniture.length)];
      particle.style.setProperty('--size', `${22 + Math.round(Math.random() * 20)}px`);
    } else {
      const streamer = Math.random() < (isParty ? 0.36 : 0.16);
      particle.className = `issue-zero-particle ${streamer ? 'streamer' : 'confetti'}`;
      const colorPool = isParty ? partyPalette : greenPalette;
      particle.style.background = colorPool[Math.floor(Math.random() * colorPool.length)];
      particle.style.width = `${streamer ? 6 + Math.round(Math.random() * 4) : 8 + Math.round(Math.random() * 10)}px`;
      particle.style.height = `${streamer ? 22 + Math.round(Math.random() * 20) : 8 + Math.round(Math.random() * 12)}px`;
    }
    const spreadX = (Math.random() - 0.5) * Math.min(window.innerWidth * 0.92, 1280);
    const burstX = (Math.random() - 0.5) * 160;
    const liftY = -(70 + Math.round(Math.random() * 130));
    const midY = -80 + Math.round(Math.random() * 100);
    const startJitterX = (Math.random() - 0.5) * Math.max(rect.width * 0.7, 42);
    const startJitterY = (Math.random() - 0.5) * 12;
    particle.style.left = `${startX + startJitterX}px`;
    particle.style.top = `${startY + startJitterY}px`;
    particle.style.setProperty('--burst-x', `${burstX}px`);
    particle.style.setProperty('--lift-y', `${liftY}px`);
    particle.style.setProperty('--mid-y', `${midY}px`);
    particle.style.setProperty('--tx', `${spreadX}px`);
    particle.style.setProperty('--burst-rot', `${(Math.random() < 0.5 ? -1 : 1) * (22 + Math.round(Math.random() * 70))}deg`);
    particle.style.setProperty('--rot', `${(Math.random() < 0.5 ? -1 : 1) * (220 + Math.round(Math.random() * 520))}deg`);
    particle.style.setProperty('--delay', `${Math.random() * 0.65}s`);
    particle.style.setProperty('--dur', `${4.55 + Math.random() * 0.35}s`);
    host.appendChild(particle);
  }
  clearTimeout(host._burstTimer);
  host._burstTimer = setTimeout(() => { host.innerHTML = ''; }, 5200);
}

function renderChallengeIssuePill() {
  const pill = document.getElementById('challengeIssuePill');
  if (!pill) return;
  if (!(state.game && state.game.active && state.board)) {
    pill.style.display = 'none';
    pill.classList.remove('good');
    pill.textContent = '';
    if (state.game) state.game.lastIssueCount = null;
    return;
  }
  const clientCount = computeClientChallengeIssueCount();
  const backendCount = Number((((state.game || {}).current || {}).issue_total) || ((((state.game || {}).current || {}).issues || {}).total) || 0);
  const count = state.board ? clientCount : backendCount;
  const previousCount = Number.isFinite(Number((state.game || {}).lastIssueCount)) ? Number((state.game || {}).lastIssueCount) : null;
  pill.style.display = 'inline-flex';
  pill.classList.toggle('good', count === 0);
  pill.textContent = `${count} issue${count === 1 ? '' : 's'} remaining`;
  if (previousCount !== null && previousCount > 0 && count === 0) {
    launchIssueZeroBurst(pill);
  }
  if (state.game) state.game.lastIssueCount = count;
}


function computeMissingNotices() {
  if (!state.board) return [];

  let firstMissingGrid = null;
  let firstMissing100 = null;
  let firstMissingSwatch = null;
  let firstMissingDimension = null;
  let firstMissingWallArtSizing = null;
  let firstCompilableSetDim = null;
  let firstMakeSquare = null;
  let firstOffPattern = null;
  let firstDuplicateSlot = null;
  let firstWrongDeliverable = null;

  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      if (!rowCountsAsActive(row)) continue;

      const liveAssets = (row.assets || []).filter(a => !a.is_marked_for_deletion && !a.is_empty_slot);
      const hasGrid = liveAssets.some(a => a.slot_key === 'SKU_grid' || (a.current_position || '').endsWith('_grid'));
      const has100 = liveAssets.some(a => a.slot_key === 'SKU_100' || (a.current_position || '').endsWith('_100'));
      const hasSwatch = liveAssets.some(a => a.slot_key === 'SKU_swatch' || (a.current_position || '').endsWith('_swatch'));
      const hasDimension = liveAssets.some(a => a.slot_key === 'SKU_dimension' || (a.current_position || '').endsWith('_dimension'));
      const has8000 = liveAssets.some(a => a.slot_key === 'SKU_8000' || (a.current_position || '').endsWith('_8000'));
      const offPatternAssets = liveAssets.filter(a => (a.lane || '') === 'off_pattern');

      const dupCounts = {};
      for (const asset of liveAssets) {
        const lane = String(asset.lane || '');
        if (lane === 'off_pattern' || lane === 'trash') continue;
        const key = String(asset.last_nontrash_position || asset.current_position || asset.slot_key || '');
        if (!key) continue;
        dupCounts[key] = (dupCounts[key] || 0) + 1;
      }
      const duplicateSlotKey = Object.keys(dupCounts).find(key => dupCounts[key] > 1) || '';
      const firstWrongDeliverableAsset = liveAssets.find(a => assetHasWrongDeliverable(a));

      if (!hasGrid && !firstMissingGrid) firstMissingGrid = {rowId: row.row_id, color: section.color, slot: 'SKU_grid'};
      if (!has100 && !firstMissing100) firstMissing100 = {rowId: row.row_id, color: section.color, slot: 'SKU_100'};
      if (rowRequiresSwatch(row) && !hasSwatch && !firstMissingSwatch) firstMissingSwatch = {rowId: row.row_id, color: section.color, slot: 'SKU_swatch'};
      if (!hasDimension && !firstMissingDimension) firstMissingDimension = {rowId: row.row_id, color: section.color, slot: 'SKU_dimension'};
      if (rowRequiresWallArtSizing(row) && !has8000 && !firstMissingWallArtSizing) firstMissingWallArtSizing = {rowId: row.row_id, color: section.color, slot: 'SKU_8000'};
      if (!hasDimension && row.set_dim_compile_ready && !firstCompilableSetDim) firstCompilableSetDim = {rowId: row.row_id, color: section.color, slot: 'SKU_dimension'};
      if (row.square_make_recommended && !firstMakeSquare) firstMakeSquare = {rowId: row.row_id, color: section.color, slot: 'SKU_square'};
      if (offPatternAssets.length && !firstOffPattern) {
        firstOffPattern = {
          rowId: row.row_id,
          color: section.color,
          slot: 'off_pattern'
        };
      }
      if (duplicateSlotKey && !firstDuplicateSlot) {
        firstDuplicateSlot = {rowId: row.row_id, color: section.color, slot: normalizeJumpSlotKey(duplicateSlotKey)};
      }
      if (firstWrongDeliverableAsset && !firstWrongDeliverable) {
        firstWrongDeliverable = {rowId: row.row_id, color: section.color, slot: normalizeJumpSlotKey(firstWrongDeliverableAsset.slot_key || firstWrongDeliverableAsset.current_position || '', row.row_id)};
      }
    }
  }

  const notices = [];
  if (firstMissingGrid) notices.push({id:'missing-grid', kind:'error', text:'Missing grid: Jump to the first active SKU missing a grid image.', rowId:firstMissingGrid.rowId, color:firstMissingGrid.color, slot:firstMissingGrid.slot});
  if (firstMissing100) notices.push({id:'missing-100', kind:'error', text:'Missing SKU_100: Jump to the first active SKU missing its SKU_100 image.', rowId:firstMissing100.rowId, color:firstMissing100.color, slot:firstMissing100.slot});
  if (firstMissingSwatch) notices.push({id:'missing-swatch', kind:'notice', text:'Missing swatch: Jump to the first active SKU missing a swatch asset.', rowId:firstMissingSwatch.rowId, color:firstMissingSwatch.color, slot:firstMissingSwatch.slot});
  if (firstMissingWallArtSizing) notices.push({id:'missing-wall-art-sizing', kind:'notice', text:'Missing wall art sizing guide: Jump to the first active SKU missing its SKU_8000 wall art sizing guide.', rowId:firstMissingWallArtSizing.rowId, color:firstMissingWallArtSizing.color, slot:firstMissingWallArtSizing.slot});
  if (firstMissingDimension && !state.game.active) notices.push({id:'missing-dimension', kind:'notice', text:'Missing dimensions: Jump to the first active SKU missing a dimensions asset.', rowId:firstMissingDimension.rowId, color:firstMissingDimension.color, slot:firstMissingDimension.slot});
  if (firstCompilableSetDim) notices.push({id:'missing-set-dim', kind:'notice', text:'Missing set dim: Jump to the first active SKU where a set dim could be compiled.', rowId:firstCompilableSetDim.rowId, color:firstCompilableSetDim.color, slot:firstCompilableSetDim.slot});
  if (firstMakeSquare) notices.push({id:'make-square', kind:'notice', text:'Make a square: Jump to the first active SKU where a square room-shot image could probably be made.', rowId:firstMakeSquare.rowId, color:firstMakeSquare.color, slot:firstMakeSquare.slot});
  if (firstOffPattern) notices.push({id:'off-pattern', kind:'notice', text:'Off-pattern assets found: Jump to the first active SKU with off-pattern assets.', rowId:firstOffPattern.rowId, color:firstOffPattern.color, slot:firstOffPattern.slot});
  if (firstDuplicateSlot) notices.push({id:'duplicate-slot', kind:'notice', text:'Duplicate-slot assets found: Jump to the first active SKU with multiple assets sharing a slot.', rowId:firstDuplicateSlot.rowId, color:firstDuplicateSlot.color, slot:firstDuplicateSlot.slot});
  if (firstWrongDeliverable) notices.push({id:'wrong-deliverable', kind:'notice', text:'Wrong deliverable for lane: Jump to the first active SKU with an asset whose Deliverable does not match its lane.', rowId:firstWrongDeliverable.rowId, color:firstWrongDeliverable.color, slot:firstWrongDeliverable.slot});
  return notices;
}

function normalizeJumpSlotKey(slotKey, rowId='') {
  const key = String(slotKey || '').trim();
  if (!key) return '';
  if (key === 'off_pattern' || key === 'trash' || key === 'SKU_grid' || key === 'SKU_dimension' || key === 'SKU_swatch' || key === 'SKU_square') return key;
  if (/^SKU_\d+$/i.test(key)) return key.toUpperCase();
  const rowEl = rowId ? document.getElementById(`row-${rowId}`) : null;
  const rowSku = rowEl ? String((rowEl.querySelector('.meta-cell .v') || {}).textContent || '').trim() : '';
  const normalized = key.toLowerCase();
  if (normalized.endsWith('_grid')) return 'SKU_grid';
  if (normalized.endsWith('_dimension')) return 'SKU_dimension';
  if (normalized.endsWith('_swatch')) return 'SKU_swatch';
  if (normalized.endsWith('_square')) return 'SKU_square';
  const numMatch = normalized.match(/_(\d+)$/);
  if (numMatch) return `SKU_${numMatch[1]}`;
  return key;
}

function clearDismissibleNotifications() {
  state.appNotices = (state.appNotices || []).filter(n => !n.dismissible);
  renderNotifications();
}

function renderNotifications() {
  const host = document.getElementById('boardNotifications');
  const clearBtn = document.getElementById('clearNotificationsBtn');
  renderCollectionStatus();
  const notices = [
    ...((state.preflightNotices || []).slice()),
    ...computeMissingNotices(),
    ...((state.appNotices || []).slice().reverse())
  ];
  const dismissibleCount = (state.appNotices || []).filter(n => n.dismissible).length;
  if (clearBtn) clearBtn.disabled = !dismissibleCount;
  if (!notices.length) {
    host.innerHTML = `<div class="notifications-empty">No collection notifications.</div>`;
    bindNotificationActions();
    return;
  }
  host.innerHTML = `<div class="panel-notice-wrap">${notices.map(n => `
    <div class="notice ${escapeHtml(n.kind || 'success')} panel-notice" ${n.rowId ? `data-jump-row="${escapeHtml(n.rowId)}" data-jump-color="${escapeHtml(n.color || '')}" data-jump-slot="${escapeHtml(n.slot || '')}"` : ''}>
      <div class="text">${n.html || escapeHtml(n.text)}</div>
      ${n.dismissible ? `<button type="button" class="dismiss" data-dismiss-notice="${escapeHtml(n.id)}">x</button>` : ''}
    </div>`).join('')}</div>`;
  bindNotificationActions();
}

function bindNotificationActions() {
  const clearBtn = document.getElementById('clearNotificationsBtn');
  if (clearBtn && !clearBtn.dataset.bound) {
    clearBtn.addEventListener('click', (event) => {
      event.preventDefault();
      event.stopPropagation();
      clearDismissibleNotifications();
    });
    clearBtn.dataset.bound = '1';
  }
  document.querySelectorAll('[data-jump-row]').forEach(el => {
    el.addEventListener('click', (event) => {
      if (event.target && event.target.matches('[data-dismiss-notice]')) return;
      event.preventDefault();
      const rowId = el.getAttribute('data-jump-row');
      const colorKey = el.getAttribute('data-jump-color') || '';
      const slotKey = normalizeJumpSlotKey(el.getAttribute('data-jump-slot') || '', rowId);
      if (rowId) jumpToRow(rowId, colorKey, slotKey);
    });
  });
  document.querySelectorAll('[data-dismiss-notice]').forEach(btn => {
    btn.addEventListener('click', (event) => {
      event.preventDefault();
      event.stopPropagation();
      const id = btn.getAttribute('data-dismiss-notice');
      state.appNotices = (state.appNotices || []).filter(n => n.id !== id);
      renderNotifications();
    });
  });
  document.querySelectorAll('[data-reload-board]').forEach(btn => {
    btn.addEventListener('click', async (event) => {
      event.preventDefault();
      event.stopPropagation();
      try {
        if (state.assetModeDirty) {
          const refreshed = await refreshDirtyAssetRows();
          if (refreshed) {
            renderBoard();
            return;
          }
        }
        if (state.loadedCollectionOptionId) {
          await launchCollection(state.loadedCollectionOptionId);
          state.assetModeDirty = false;
        }
      } catch (err) {
        console.warn(err);
        if (state.loadedCollectionOptionId) {
          await launchCollection(state.loadedCollectionOptionId);
          state.assetModeDirty = false;
        }
      }
    });
  });
}

function findFirstMissingCriticalSlot(slotKey) {
  if (!state.board) return null;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      if (!rowCountsAsActive(row)) continue;
      const liveAssets = (row.assets || []).filter(a => !a.is_marked_for_deletion && !a.is_empty_slot);
      const hasSlot = slotKey === 'SKU_grid'
        ? liveAssets.some(a => a.slot_key === 'SKU_grid' || (a.current_position || '').endsWith('_grid'))
        : liveAssets.some(a => a.slot_key === slotKey || (a.current_position || '').endsWith(`_${slotKey.replace('SKU_', '')}`));
      if (!hasSlot) return {rowId: row.row_id, color: section.color, slot: slotKey};
    }
  }
  return null;
}

function jumpToFirstMissingSlot(slotKey) {
  const found = findFirstMissingCriticalSlot(slotKey);
  if (!found) {
    addAppNotice(slotKey === 'SKU_grid' ? 'No active SKUs are missing grid images.' : 'No active SKUs are missing SKU_100 images.', 'success');
    return;
  }
  jumpToRow(found.rowId, found.color, found.slot);
}

function jumpToRow(rowId, colorKey='', slotKey='') {
  if (colorKey) {
    Object.keys(state.collapsedColors || {}).forEach(key => { state.collapsedColors[key] = true; });
    state.collapsedColors[colorKey] = false;
    renderBoard();
  }

  const applyHighlight = () => {
    const rowEl = document.getElementById(`row-${rowId}`);
    if (!rowEl) return false;

    const boardMain = document.getElementById('boardMain');
    const collectionBar = boardMain ? boardMain.querySelector('.collection-header') : document.querySelector('.collection-header');
    const offset = (collectionBar ? collectionBar.offsetHeight : 0) + 12;
    if (boardMain) {
      const boardRect = boardMain.getBoundingClientRect();
      const rowRect = rowEl.getBoundingClientRect();
      const targetTop = boardMain.scrollTop + (rowRect.top - boardRect.top) - offset;
      boardMain.scrollTo({ top: Math.max(0, targetTop), behavior: 'smooth' });
    } else {
      const rowTop = rowEl.getBoundingClientRect().top + window.scrollY - offset;
      window.scrollTo({ top: Math.max(0, rowTop), behavior: 'smooth' });
    }

    rowEl.classList.add('row-highlight');
    setTimeout(() => rowEl.classList.remove('row-highlight'), 5000);

    if (slotKey) {
      const slotEl = document.getElementById(`slot-${rowId}-${slotKey}`) || rowEl.querySelector(`.slot[data-slot="${slotKey}"]`);
      if (!slotEl) return false;
      if (boardMain) {
        const boardRect2 = boardMain.getBoundingClientRect();
        const slotRect = slotEl.getBoundingClientRect();
        const slotTargetTop = boardMain.scrollTop + (slotRect.top - boardRect2.top) - offset;
        boardMain.scrollTo({ top: Math.max(0, slotTargetTop), behavior: 'smooth' });
      }
      slotEl.classList.remove('slot-highlight');
      void slotEl.offsetWidth;
      slotEl.classList.add('slot-highlight');
      slotEl.style.outline = '4px solid rgba(58,166,106,.98)';
      slotEl.style.boxShadow = '0 0 0 4px rgba(58,166,106,.98), 0 0 36px rgba(58,166,106,.78)';
      slotEl.style.background = 'rgba(58,166,106,.16)';
      setTimeout(() => {
        slotEl.classList.remove('slot-highlight');
        slotEl.style.outline = '';
        slotEl.style.boxShadow = '';
        slotEl.style.background = '';
      }, 5000);
    }
    return true;
  };

  let attempts = 0;
  const timer = setInterval(() => {
    attempts += 1;
    if (applyHighlight() || attempts >= 18) clearInterval(timer);
  }, 160);
}

function bindColorToggles() {
  document.querySelectorAll('[data-color-toggle]').forEach(el => {
    el.addEventListener('click', () => {
      const key = el.getAttribute('data-color-toggle');
      const nextCollapsed = !state.collapsedColors[key];
      state.collapsedColors[key] = nextCollapsed;
      renderBoard();
      if (!nextCollapsed) ensureAdditionalPhotoAvailabilityForColor(key);
    });
  });
}


function bindComponentJumps() {
  document.querySelectorAll('[data-component-jump]').forEach(el => {
    el.addEventListener('click', (event) => {
      const sku = el.getAttribute('data-component-jump');
      if (!sku) return;
      jumpToComponentSku(event, sku);
    });
  });
}

function jumpToComponentSku(event, sku) {
  if (event) {
    event.preventDefault();
    event.stopPropagation();
  }
  if (!sku || !state.board) return;

  let colorKey = '';
  let targetRowId = '';
  for (const section of state.board.color_sections || []) {
    const found = (section.rows || []).find(r => String(r.row_id || '') === String(sku) || String(r.sku || '') === String(sku));
    if (found) {
      colorKey = section.color;
      targetRowId = String(found.row_id || found.sku || '');
      break;
    }
  }
  if (!targetRowId) return;
  jumpToRow(targetRowId, colorKey, '');
}

async function undoPendingCopy(event, assetId, targetPos, sourceMediaId='', targetSku='') {
  event.preventDefault();
  event.stopPropagation();
  if (!confirm(`No longer copy this to ${targetPos}?`)) return;
  if (!state.board) return;
  try {
    const resp = await fetch('/api/remove_pending_copy', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({
        asset_id: assetId || '',
        target_pos: targetPos || '',
        media_id: sourceMediaId || '',
        source_media_id: sourceMediaId || '',
        target_sku: targetSku || ''
      })
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not remove pending copy');
    state.board = data.board;
    state.summary = data.summary || computeClientSummary();
    renderBoard();
    addAppNotice('Pending copy removed.', 'success');
  } catch (err) {
    addAppNotice(err.message || 'Could not find that pending copy to remove.', 'warning');
  }
}

function undoPendingCopyClick(event, assetId, targetPos, sourceMediaId='', targetSku='') {
  undoPendingCopy(event, assetId, targetPos, sourceMediaId, targetSku);
}

function bindUndoCopyButtons() {
  document.querySelectorAll('.asset-undo-copy').forEach(btn => {
    btn.addEventListener('mousedown', (event) => { event.stopPropagation(); });
  });
}

function renderSummary() {
  const body = document.getElementById('summaryBody');
  const summary = state.summary || {'Position changes': [], 'Marked for deletion': [], 'Restored from deletion': []};
  body.classList.toggle('open', state.summaryOpen);
  document.getElementById('toggleSummaryBtn').textContent = state.summaryOpen ? '▴' : '▾';
  body.innerHTML = Object.entries(summary).map(([group, items]) => `
    <div class="summary-group">
      <h4>${escapeHtml(group)} (${items.length})</h4>
      ${items.length ? items.map(item => `
        <div class="summary-item" data-jump-asset="${escapeHtml(item.asset_id)}">
          ${item.thumb ? `<img src="${escapeHtml(item.thumb + '?w=120&h=120&fit=cover')}" alt="" />` : `<div></div>`}
          <div>
            <div class="name">${escapeHtml(item.asset_name)}</div>
            <div class="desc">SKU ${escapeHtml(item.sku)} - ${escapeHtml(item.description)}</div>
          </div>
        </div>
      `).join('') : `<div class="empty">No queued changes in this group.</div>`}
    </div>
  `).join('');

  body.querySelectorAll('[data-jump-asset]').forEach(el => {
    el.addEventListener('click', () => {
      const assetId = el.getAttribute('data-jump-asset');
      const card = document.querySelector(`[data-asset-id="${CSS.escape(assetId)}"]`);
      if (card) {
        card.scrollIntoView({behavior: 'smooth', block: 'start'});
        card.animate([{transform:'scale(1)'},{transform:'scale(1.04)'},{transform:'scale(1)'}], {duration: 500});
      }
    });
  });
}

function addAppNotice(text, kind='success', html='') {
  const id = `notice-${Date.now()}-${Math.random().toString(36).slice(2,8)}`;
  state.appNotices = [{id, kind, text, html, dismissible:true}, ...(state.appNotices || [])].slice(0, 12);
  renderNotifications();
  return id;
}

function upsertAppNotice(id, text, kind='notice', html='', dismissible=false) {
  const noticeId = String(id || `notice-${Date.now()}-${Math.random().toString(36).slice(2,8)}`);
  const others = (state.appNotices || []).filter(n => String(n.id || '') !== noticeId);
  state.appNotices = [{id: noticeId, kind, text, html, dismissible: !!dismissible}, ...others].slice(0, 12);
  renderNotifications();
  return noticeId;
}

function removeAppNotice(id) {
  if (!id) return;
  state.appNotices = (state.appNotices || []).filter(n => String(n.id || '') !== String(id || ''));
  renderNotifications();
}

async function fixAssetVersion(event, assetId, fixType) {
  event.preventDefault();
  event.stopPropagation();
  try {
    const resp = await fetch('/api/fix_asset_version', {
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body: JSON.stringify({ media_id: assetId, fix_type: fixType, mode: state.mode })
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Asset fix failed');
    state.board = data.board;
    state.summary = data.summary;
    if (data.asset_mode_refresh_pending) state.assetModeDirty = true;
    markAssetModeDirtyRows(data.dirty_row_ids || []);
    renderBoard();
    if (data.notice && (data.notice.text || data.notice.html)) addAppNotice(data.notice.text || '', data.notice.kind || 'success', data.notice.html || '');
  } catch (err) {
    alert(err.message || String(err));
  }
}

function updateQueuedStatus() {
  const changed = changedAssetIds();
  const count = changed.size;
  document.getElementById('queuedCount').textContent = count ? `${count} asset(s) queued` : 'No queued changes';
  document.getElementById('commitStatus').textContent = count ? 'Review your queued changes, then commit when ready.' : 'No queued changes yet.';
}

function bindBoardDnD() {
  document.querySelectorAll('.asset-card').forEach(card => {
    card.addEventListener('dragstart', e => {
      if (state.mode !== 'positions') {
        e.preventDefault();
        return;
      }
      state.dragging = {assetId: card.getAttribute('data-asset-id')};
      e.dataTransfer.setData('text/plain', state.dragging.assetId);
    });
    card.addEventListener('dragend', () => { state.dragging = null; });
  });

  document.querySelectorAll('.slot').forEach(slot => {
    slot.addEventListener('dragover', e => {
      e.preventDefault();
      slot.classList.add('dragover');
    });
    slot.addEventListener('dragleave', () => slot.classList.remove('dragover'));
    slot.addEventListener('drop', async e => {
      e.preventDefault();
      slot.classList.remove('dragover');
      const rowId = slot.getAttribute('data-row-id');
      const targetLane = slot.getAttribute('data-lane');
      const targetSlot = slot.getAttribute('data-slot');
      const files = e.dataTransfer && e.dataTransfer.files ? Array.from(e.dataTransfer.files) : [];
      let preparedPayload = null;
      try {
        const rawPrepared = e.dataTransfer ? e.dataTransfer.getData('application/x-prepared-photo') : '';
        preparedPayload = rawPrepared ? JSON.parse(rawPrepared) : (state.preparedPreviewDrag || null);
      } catch (err) {
        preparedPayload = state.preparedPreviewDrag || null;
      }

      if (preparedPayload) {
        if (state.mode !== 'assets') {
          alert('Prepared image drops are only available in Update assets mode.');
          return;
        }
        let psaImageTypeOverride = '';
        if (!preparedPayload.source_is_board_asset) {
          const active = currentActivePhoto();
          const resolvedType = resolvePreparedPhotoPsaImageType(active);
          if (resolvedType === null) return;
          psaImageTypeOverride = resolvedType || '';
        }
        try {
          const resp = await fetch('/api/prepared_drop_upload', {
            method:'POST',
            headers:{'Content-Type':'application/json'},
            body: JSON.stringify({
              row_id: rowId || '',
              target_lane: targetLane || '',
              target_slot: targetSlot || '',
              mode: state.mode,
              psa_image_type_override: psaImageTypeOverride,
              ...preparedPayload
            })
          });
          slot.classList.add('upload-target-pending');
          const data = await resp.json();
          if (!resp.ok) throw new Error(data.error || 'Prepared image upload failed');
          state.board = data.board;
          state.summary = data.summary;
          if (data.asset_mode_refresh_pending) state.assetModeDirty = true;
          markAssetModeDirtyRows(data.dirty_row_ids || [rowId]);
          renderBoard();
          if (data.notice && (data.notice.text || data.notice.html)) addAppNotice(data.notice.text || '', data.notice.kind || 'success', data.notice.html || '');
        } catch (err) {
          alert(err.message || String(err));
        } finally {
          slot.classList.remove('upload-target-pending');
        }
        return;
      }

      const sourceId = e.dataTransfer.getData('text/plain') || state.photoDragId || (state.dragging && state.dragging.assetId);
      const sourcePhoto = getPhotoById(sourceId);
      if (sourcePhoto && state.mode !== 'assets') {
        alert('Switch to Update assets mode before dragging photography onto the board.');
        return;
      }
      if (sourcePhoto && state.mode === 'assets') {
        let psaImageTypeOverride = resolvePreparedPhotoPsaImageType(sourcePhoto);
        if (psaImageTypeOverride === null) return;
        try {
          const resp = await fetch('/api/prepared_drop_upload', {
            method:'POST',
            headers:{'Content-Type':'application/json'},
            body: JSON.stringify({
              row_id: rowId || '',
              target_lane: targetLane || '',
              target_slot: targetSlot || '',
              mode: state.mode,
              media_id: sourcePhoto.id,
              source_media_id: sourcePhoto.id,
              source_file_name: sourcePhoto.file_name || sourcePhoto.name || 'asset.jpg',
              prep_mode: 'original',
              flip: !!state.photography.prep.flip,
              offset_y: activePhotoOffsetY(sourcePhoto.id),
              offset_x: activePhotoOffsetX(sourcePhoto.id),
              source_is_board_asset: false,
              psa_image_type_override: psaImageTypeOverride || ''
            })
          });
          slot.classList.add('upload-target-pending');
          const data = await resp.json();
          if (!resp.ok) throw new Error(data.error || 'Prepared image upload failed');
          state.board = data.board;
          state.summary = data.summary;
          if (data.asset_mode_refresh_pending) state.assetModeDirty = true;
          markAssetModeDirtyRows(data.dirty_row_ids || [rowId]);
          renderBoard();
          if (data.notice && (data.notice.text || data.notice.html)) addAppNotice(data.notice.text || '', data.notice.kind || 'success', data.notice.html || '');
        } catch (err) {
          alert(err.message || String(err));
        } finally {
          slot.classList.remove('upload-target-pending');
        }
        return;
      }

      if (files.length) {
        if (state.mode !== 'assets') {
          alert('File uploads are only available in Update assets mode.');
          return;
        }
        const form = new FormData();
        form.append('file', files[0]);
        form.append('row_id', rowId || '');
        form.append('target_lane', targetLane || '');
        form.append('target_slot', targetSlot || '');
        form.append('mode', state.mode);
        try {
          const resp = await fetch('/api/file_drop_upload', {method:'POST', body: form});
          const data = await resp.json();
          if (!resp.ok) throw new Error(data.error || 'Upload failed');
          state.board = data.board;
          state.summary = data.summary;
          if (data.asset_mode_refresh_pending) state.assetModeDirty = true;
          markAssetModeDirtyRows(data.dirty_row_ids || [rowId]);
          renderBoard();
          if (data.notice && (data.notice.text || data.notice.html)) addAppNotice(data.notice.text || '', data.notice.kind || 'success', data.notice.html || '');
        } catch (err) {
          alert(err.message || String(err));
        }
        return;
      }


      if (state.mode !== 'positions') {
        alert('Asset reordering is only available in Update positions mode.');
        return;
      }
      const assetId = e.dataTransfer.getData('text/plain') || (state.dragging && state.dragging.assetId);
      if (!assetId) return;
      try {
        let resp = await fetch('/api/move', {
          method: 'POST',
          headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({row_id: rowId, asset_id: assetId, target_lane: targetLane, target_slot: targetSlot})
        });
        let data = await resp.json();
        if (!resp.ok) {
          const msg = String(data.error || 'Move failed');
          if (/Row .* not found/i.test(msg)) {
            const refreshed = await launchCollection(null, {silent:true, scrollTopAfter:false, forceRefresh:true});
            if (refreshed && state.board) {
              resp = await fetch('/api/move', {
                method: 'POST',
                headers: {'Content-Type': 'application/json'},
                body: JSON.stringify({row_id: rowId, asset_id: assetId, target_lane: targetLane, target_slot: targetSlot})
              });
              data = await resp.json();
            }
          }
        }
        if (!resp.ok) throw new Error(data.error || 'Move failed');
        state.board = data.board;
        state.summary = data.summary;
        renderBoard();
      } catch (err) {
        alert(err.message || String(err));
      }
    });
  });
}

function bindWarningDismiss() {
  document.querySelectorAll('[data-warning-index]').forEach(btn => {
    btn.addEventListener('click', () => {
      const rowId = btn.getAttribute('data-row-id');
      const idx = Number(btn.getAttribute('data-warning-index'));
      for (const section of state.board.color_sections || []) {
        for (const row of section.rows || []) {
          if (row.row_id === rowId) {
            row.overflow_warnings.splice(idx, 1);
            renderBoard();
            return;
          }
        }
      }
    });
  });
}

document.addEventListener('dragover', (e) => {
  const margin = 110;
  const step = 24;
  const panel = document.getElementById('photoBody');
  const boardMain = document.getElementById('boardMain');
  if (panel && panel.matches(':hover')) {
    const rect = panel.getBoundingClientRect();
    if (e.clientY - rect.top < margin) panel.scrollBy(0, -step);
    else if (rect.bottom - e.clientY < margin) panel.scrollBy(0, step);
    return;
  }
  if (boardMain && (state.dragging || state.photoDragId) && boardMain.matches(':hover')) {
    const rect = boardMain.getBoundingClientRect();
    if (e.clientY - rect.top < margin) boardMain.scrollBy(0, -step);
    else if (rect.bottom - e.clientY < margin) boardMain.scrollBy(0, step);
    if (e.clientX - rect.left < margin) boardMain.scrollBy(-step * 2, 0);
    else if (rect.right - e.clientX < margin) boardMain.scrollBy(step * 2, 0);
  }
});

async function loadCollections() {
  state.collectionNotice = { kind: 'notice', text: 'Loading Product Collection options...' };
  renderNotifications();
  try {
    const resp = await fetch('/api/collections');
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Could not load collections');
    state.collections = data.collections || [];
    state.filteredCollections = [...state.collections];
    state.collectionSource = data.source || 'memory';
    renderCollectionSelect();
    renderLauncherPanel();
    const sourceText = state.collectionSource === 'local_cache'
      ? 'from local cache'
      : (state.collectionSource === 'bynder' ? 'from Bynder' : '');
    state.collectionNotice = {
      kind: 'success',
      text: sourceText
        ? `${state.collections.length.toLocaleString()} Product Collection options loaded ${sourceText}.`
        : `${state.collections.length.toLocaleString()} Product Collection options loaded.`
    };
    renderNotifications();
  } catch (err) {
    state.collectionNotice = {
      kind: 'error',
      text: err.message || String(err)
    };
    renderNotifications();
  }
}

function renderCollectionSelect() {
  const select = document.getElementById('collectionSelect');
  if (select) select.innerHTML = state.filteredCollections.map(c => `<option value="${escapeHtml(c.id)}">${escapeHtml(c.label)}</option>`).join('');
  const pioSelect = document.getElementById('pioCollectionSelect');
  if (pioSelect) pioSelect.innerHTML = (state.filteredCollections || state.collections || []).map(c => `<option value="${escapeHtml(c.id)}">${escapeHtml(c.label)}</option>`).join('');
  if (state.collections.length) {
    const visible = state.filteredCollections.length;
    const sourceText = state.collectionSource === 'local_cache'
      ? 'from local cache'
      : (state.collectionSource === 'bynder' ? 'from Bynder' : '');
    state.collectionNotice = {
      kind: 'success',
      text: sourceText
        ? `${state.collections.length.toLocaleString()} Product Collection options loaded ${sourceText}. ${visible.toLocaleString()} currently shown.`
        : `${state.collections.length.toLocaleString()} Product Collection options loaded. ${visible.toLocaleString()} currently shown.`
    };
    renderNotifications();
  }
}

function filterCollections() {
  const input = document.getElementById('collectionFilter');
  const q = input ? input.value.trim().toLowerCase() : '';
  state.filteredCollections = !q ? [...state.collections] : state.collections.filter(c => c.label.toLowerCase().includes(q));
  renderCollectionSelect();
}

const launchLoadingMessages = [
  'Loading...',
  'Still working on it...',
  'Do not worry, still loading...',
  'This is a big one...',
  'Gathering the good stuff...',
  'Still stitching the board together...',
  'Almost there...',
  'Patience. Something good is coming...',
  'The board is gathering its strength...',
  'A worthy collection takes a moment...',
  'Hope is loading...',
  'The force is strong with this load...',
  'The board is awakening...',
  'A great house is assembling...',
  'Even the smallest load can take its time...',
  'The next chapter is arriving...',
  'A fellowship of assets is forming...',
  'Stand fast. The board is on its way...',
  'A long wait, but a rich reward...',
  'The banners are rising...',
  'This one has a larger destiny...',
  'The path is winding, but we are getting there...',
  'Second breakfast for the board is taking a minute...',
  'These assets are coming in hot like a pod race...',
  'The board is making itself at home in the Shire...',
  'Winter is loading, but so is your collection...',
  'This load has more layers than an onion knight...',
  'Not all those who wander are lost. Some are just loading...',
  'The board is doing a little lightsaber stretching...',
  'A wizard is never late. This load will arrive precisely when it means to...',
  'The board is forging ahead. One asset to rule them all was a bit much...',
  'This collection brought friends. We are welcoming them politely...',
  'Loading like a champion, one tile at a time...',
  'A cute little board reveal is on the way...'
];

function startLaunchLoadingTicker(buttonId='launchBtn') {
  stopLaunchLoadingTicker(buttonId);
  const btn = document.getElementById(buttonId);
  if (!btn) return;
  let idx = 0;
  btn.textContent = launchLoadingMessages[0];
  state.launchLoadingTicker = state.launchLoadingTicker || {};
  state.launchLoadingTicker[buttonId] = window.setInterval(() => {
    if (!btn.disabled) return;
    idx = (idx + 1) % launchLoadingMessages.length;
    btn.textContent = launchLoadingMessages[idx];
  }, 4500);
}

function stopLaunchLoadingTicker(buttonId='launchBtn') {
  const tickers = state.launchLoadingTicker || {};
  if (tickers[buttonId]) {
    clearInterval(tickers[buttonId]);
    delete tickers[buttonId];
  }
  state.launchLoadingTicker = tickers;
}

async function launchCollection(optionIdOverride=null, options={}) {
  if (optionIdOverride && typeof optionIdOverride === 'object' && optionIdOverride.isTrusted !== undefined) {
    optionIdOverride = null;
  }
  const opts = options || {};
  const silent = !!opts.silent;
  const flashReload = !!opts.flashReload;
  const forceRefresh = !!opts.forceRefresh || !!opts.flashReload;
  const scrollTopAfter = opts.scrollTopAfter !== false;
  const select = document.getElementById('collectionSelect');
  const optionId = optionIdOverride || select.value;
  if (!optionId) {
    alert('Please choose a Product Collection.');
    return null;
  }
  if (!silent) {
    document.getElementById('launchBtn').disabled = true;
    startLaunchLoadingTicker();
  }
  if (flashReload) setReloadButtonFlashing(true);
  try {
    const resp = await fetch('/api/load_collection', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({option_id: optionId, force_refresh: forceRefresh, game_mode: !!opts.gameMode})
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Load failed');
    if (!opts.gameMode) state.game.active = false;
    applyBoardResponse(data, {keepPhotography:false, keepNotices:false});
    if (scrollTopAfter) {
      requestAnimationFrame(() => {
        scrollBoardToFirstColorTop('auto');
      });
    }
    return data;
  } catch (err) {
    alert(err.message || String(err));
    return null;
  } finally {
    if (!silent) {
      stopLaunchLoadingTicker();
      document.getElementById('launchBtn').disabled = false;
      document.getElementById('launchBtn').textContent = 'Launch Collection';
    }
    if (flashReload) setReloadButtonFlashing(false);
  }
}


async function launchRandomCollection() {
  const launchBtn = document.getElementById('launchBtn');
  const randomBtn = document.getElementById('launchRandomBtn');
  if (launchBtn) launchBtn.disabled = true;
  if (randomBtn) {
    randomBtn.disabled = true;
    startLaunchLoadingTicker('launchRandomBtn');
  }
  try {
    const resp = await fetch('/api/launch_random_collection', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({action: 'random_launch'})
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Random launch failed');
    state.game.active = false;
    applyBoardResponse(data, {keepPhotography:false, keepNotices:false});
    const launched = data.random_launch || {};
    if (launched.collection && launched.color) {
      addAppNotice(`Random collection loaded: ${launched.collection.label} / ${launched.color}. Photography is ready in the panel. Large collections can still take longer while matching that colorway across the board.`, 'success');
    }
    requestAnimationFrame(() => {
      scrollBoardToFirstColorTop('auto');
    });
    return data;
  } catch (err) {
    alert(err.message || String(err));
    return null;
  } finally {
    stopLaunchLoadingTicker('launchRandomBtn');
    if (randomBtn) {
      randomBtn.disabled = false;
      randomBtn.textContent = 'Launch Random Collection';
    }
    if (launchBtn) launchBtn.disabled = false;
  }
}

function getSuccessfulCommitRowIds(commitSummary=null) {
  const explicit = Array.isArray(commitSummary && commitSummary.success_row_ids)
    ? commitSummary.success_row_ids.map(x => String(x || '').trim()).filter(Boolean)
    : [];
  if (explicit.length) return [...new Set(explicit)];
  const derived = Array.isArray(commitSummary && commitSummary.results)
    ? commitSummary.results
        .filter(item => item && item.success && item.row_id)
        .map(item => String(item.row_id || '').trim())
        .filter(Boolean)
    : [];
  return [...new Set(derived)];
}

async function refreshCommittedRows(rowIds) {
  const cleanRowIds = Array.isArray(rowIds) ? [...new Set(rowIds.map(x => String(x || '').trim()).filter(Boolean))] : [];
  if (!cleanRowIds.length) return null;
  const resp = await fetch('/api/refresh_rows', {
    method: 'POST',
    headers: {'Content-Type': 'application/json'},
    body: JSON.stringify({row_ids: cleanRowIds})
  });
  const data = await resp.json().catch(() => ({}));
  if (!resp.ok) throw new Error(data.error || 'Row refresh failed');
  return data;
}

async function waitThenPollForRefresh(commitSummary=null) {
  const token = Date.now();
  state.waitFlow.activeToken = token;
  const priorCollapsed = {...(state.collapsedColors || {})};
  const boardMain = document.getElementById('boardMain');
  const priorScrollTop = boardMain ? boardMain.scrollTop : 0;
  const successCount = Number((commitSummary && commitSummary.success_count) || 0);
  const failureCount = Number((commitSummary && commitSummary.failure_count) || 0);
  const successfulRowIds = getSuccessfulCommitRowIds(commitSummary);
  if (successCount <= 0 && failureCount <= 0) {
    setWaitOverlay(false, '');
    addAppNotice('No queued metadata changes were sent to Bynder.', 'notice');
    closeIdleModal();
    return false;
  }
  setWaitOverlay(true, 'Waiting 30 seconds before checking for refreshed metadata...', {miniGame:true, title:'Giving Bynder a moment...', body:'Your updates went through. Waiting 30 seconds before checking for refreshed metadata.'});
  await delay(30000);
  if (state.waitFlow.activeToken !== token) return false;

  try {
    if (successfulRowIds.length) {
      const rowWord = successfulRowIds.length === 1 ? 'row' : 'rows';
      setWaitOverlay(true, `Refreshing ${successfulRowIds.length} changed SKU ${rowWord} from Bynder...`, {miniGame:true});
      const data = await refreshCommittedRows(successfulRowIds);
      if (state.waitFlow.activeToken !== token) return false;
      setWaitOverlay(false, '');
      if (data && data.board) {
        applyBoardResponse(data, {keepPhotography:true, keepNotices:true});
        state.collapsedColors = priorCollapsed;
        renderBoard();
        requestAnimationFrame(() => {
          const boardMainNow = document.getElementById('boardMain');
          if (boardMainNow) boardMainNow.scrollTop = priorScrollTop;
        });
        addAppNotice(`Refreshed ${successfulRowIds.length} changed SKU ${rowWord} from Bynder without reloading the full board.`, 'success');
        closeIdleModal();
        return true;
      }
    }
  } catch (err) {
    console.warn('Targeted row refresh failed, falling back to full board reload.', err);
  }

  setWaitOverlay(true, 'Loading refreshed board from Bynder...', {miniGame:true});
  const resp = await fetch('/api/load_collection', {
    method: 'POST',
    headers: {'Content-Type': 'application/json'},
    body: JSON.stringify({option_id: state.loadedCollectionOptionId, force_refresh: true, game_mode: false})
  });
  const data = await resp.json().catch(() => ({}));
  if (state.waitFlow.activeToken !== token) return false;
  setWaitOverlay(false, '');
  if (resp.ok && data && data.board) {
    applyBoardResponse(data, {keepPhotography:true, keepNotices:true});
    state.collapsedColors = priorCollapsed;
    renderBoard();
    requestAnimationFrame(() => {
      const boardMainNow = document.getElementById('boardMain');
      if (boardMainNow) boardMainNow.scrollTop = priorScrollTop;
    });
    addAppNotice('Board refreshed from Bynder.', 'success');
    closeIdleModal();
    return true;
  }
  addAppNotice('Updates went through, but the refreshed board is not ready yet. Use Reload From Bynder again in a moment.', 'notice');
  closeIdleModal();
  return false;
}


async function waitThenPollForChallengeRefresh() {
  const token = Date.now();
  state.waitFlow.activeToken = token;
  const baseline = state.waitFlow.baselineFingerprint || boardFingerprint(state.board);
  setWaitOverlay(true, 'Waiting 30 seconds before checking for refreshed challenge metadata...', {miniGame:true, title:'Checking your challenge board...', body:'Your updates went through. Waiting 30 seconds before checking for refreshed challenge metadata.'});
  await delay(30000);
  if (state.waitFlow.activeToken !== token) return false;

  let attempts = 0;
  const maxAttempts = 18;
  while (attempts < maxAttempts) {
    attempts += 1;
    setWaitOverlay(true, `Checking Bynder for refreshed challenge metadata... Attempt ${attempts} of ${maxAttempts}.`, {miniGame:true});
    const resp = await fetch('/api/game/reload_current', {method:'POST'});
    const data = await resp.json().catch(() => ({}));
    if (state.waitFlow.activeToken !== token) return false;
    if (resp.ok) {
      applyBoardResponse(data, {keepPhotography:true, keepNotices:true});
      const current = boardFingerprint(state.board);
      const g = data.game || {};
      if ((current && current !== baseline) || Number(g.resolved || 0) > 0 || Number(g.remaining ?? -1) === 0) {
        setWaitOverlay(false, '');
        if (Number(g.resolved || 0) > 0) addAppNotice(`Nice. ${g.resolved} issue${Number(g.resolved) === 1 ? '' : 's'} resolved and scored.`, 'success');
        if (g.completed || Number(g.remaining ?? -1) === 0) {
          showGameCelebration('Board cleared!', `You earned ${Number(g.resolved || 0)} point${Number(g.resolved || 0) === 1 ? '' : 's'}. This board can stay open for any extra cleanup you want to do. Click Load next challenge whenever you're ready.`);
        } else {
          addAppNotice('Challenge board refreshed from Bynder.', 'success');
        }
        closeIdleModal();
        return true;
      }
    }
    await delay(5000);
  }
  setWaitOverlay(false, '');
  addAppNotice('Updates went through, but refreshed challenge metadata is still taking a while to show. Use Reload From Bynder again in a moment.', 'notice');
  return false;
}

async function discardChanges() {
  if (!state.board) return;
  if (!confirm('Discard all staged changes and go back to the last loaded version from Bynder?')) return;
  const btn = document.getElementById('discardBtn');
  const boardMain = document.getElementById('boardMain');
  const priorScrollTop = boardMain ? boardMain.scrollTop : 0;
  const priorCollapsed = {...(state.collapsedColors || {})};
  btn.disabled = true;
  btn.textContent = 'Discarding...';
  try {
    const resp = await fetch('/api/discard', {method: 'POST'});
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Discard failed');
    state.board = data.board;
    state.summary = data.summary;
    state.collapsedColors = priorCollapsed;
    renderBoard();
    requestAnimationFrame(() => {
      const boardMainNow = document.getElementById('boardMain');
      if (boardMainNow) boardMainNow.scrollTop = priorScrollTop;
    });
    closeIdleModal();
    addAppNotice('Staged changes were discarded.', 'success');
  } catch (err) {
    alert(err.message || String(err));
  } finally {
    btn.disabled = false;
    btn.textContent = 'Discard Changes';
  }
}


async function commitChanges(skipConfirm=false) {
  if (!state.board) return false;
  if (state.mode === 'assets') return false;
  if (!skipConfirm && !confirm('Are you sure you want to commit these changes to Bynder?')) return false;
  const btn = document.getElementById('commitBtn');
  btn.disabled = true;
  btn.textContent = 'Updating...';
  state.commitInFlight = true;
  setWaitOverlay(true, 'Sending updates to Bynder...', {miniGame:true});
  try {
    state.waitFlow.baselineFingerprint = boardFingerprint(state.board);
    const resp = await fetch('/api/commit', {method: 'POST'});
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Commit failed');
    const c = data.commit;
    if (c.all_succeeded) {
      if (state.game.active) {
        addAppNotice(`Beautiful. ${c.success_count} change(s) went through. Waiting a bit before checking the challenge board in Bynder. A log was saved to ${c.log_path}.`, 'success');
        await waitThenPollForChallengeRefresh();
      } else {
        addAppNotice(`Beautiful. ${c.success_count} change(s) went through. Waiting a bit before reloading from Bynder. A log was saved to ${c.log_path}.`, 'success');
        await waitThenPollForRefresh(c);
      }
      return true;
    } else {
      setWaitOverlay(false, '');
      applyBoardResponse(data, {keepPhotography:true, keepNotices:true});
      const msg = `Some changes failed. ${c.success_count} succeeded and ${c.failure_count} failed. The board was not refreshed so you can keep working. A log was saved to ${c.log_path}.`;
      addAppNotice(msg, 'error');
      return false;
    }
  } catch (err) {
    setWaitOverlay(false, '');
    alert(err.message || String(err));
    return false;
  } finally {
    state.commitInFlight = false;
    if (state.waitFlow) state.waitFlow.activeToken = null;
    btn.disabled = false;
    btn.textContent = 'Update in Bynder';
  }
}


function updateStickyOffsets() {
  const topShell = document.querySelector('.top-shell');
  const tools = document.querySelector('.sticky-board-tools');
  const root = document.documentElement;
  const topShellHeight = topShell ? Math.ceil(topShell.getBoundingClientRect().height) : 74;
  const toolsHeight = tools ? Math.ceil(tools.getBoundingClientRect().height) : 72;
  root.style.setProperty('--top-shell-height', topShellHeight + 'px');
  root.style.setProperty('--collection-tools-height', toolsHeight + 'px');
  root.style.setProperty('--photo-panel-width', state.photography && state.photography.expanded ? (state.photography.width + 'px') : '56px');
}

async function refreshMessages() {
  try {
    const resp = await fetch('/api/messages');
    const data = await resp.json();
    document.getElementById('serverLog').textContent = (data.messages || []).join('\n');
  } catch (_) {}
}


function bindRegularLauncherEvents() {
  const collectionFilter = document.getElementById('collectionFilter');
  if (collectionFilter) {
    collectionFilter.value = collectionFilter.value || '';
    collectionFilter.addEventListener('input', filterCollections);
  }
  const launchBtn = document.getElementById('launchBtn');
  if (launchBtn) launchBtn.addEventListener('click', () => launchCollection());
  const launchRandomBtn = document.getElementById('launchRandomBtn');
  if (launchRandomBtn) launchRandomBtn.addEventListener('click', () => launchRandomCollection());
  const hideInactiveToggle = document.getElementById('hideInactiveToggle');
  if (hideInactiveToggle) {
    hideInactiveToggle.checked = !!state.hideInactive;
    hideInactiveToggle.addEventListener('change', () => {
      state.hideInactive = !!hideInactiveToggle.checked;
      renderBoard();
    });
  }
}

function bindStaticUI() {
  renderLauncherPanel();
  document.getElementById('reloadBtn').addEventListener('click', async () => {
    const queuedCount = changedAssetIds().size;
    if (queuedCount > 0) {
      const shouldCommit = confirm(`You have ${queuedCount} queued change(s). Press OK to commit them to Bynder before reloading. Press Cancel to stay on this board.`);
      if (!shouldCommit) return;
      const success = await commitChanges(true);
      if (!success) return;
    }
    if (state.game && state.game.active) {
      setReloadButtonFlashing(true);
      try {
        const resp = await fetch('/api/game/reload_current', {method:'POST'});
        const data = await resp.json();
        if (!resp.ok) throw new Error(data.error || 'Reload failed');
        applyBoardResponse(data, {keepPhotography:true, keepNotices:true});
        const g = data.game || {};
        if (Number(g.resolved || 0) > 0) addAppNotice(`Nice. ${g.resolved} issue${Number(g.resolved) === 1 ? '' : 's'} resolved and scored.`, 'success');
        if (g.completed) {
          showGameCelebration('Board cleared!', `You earned ${Number(g.resolved || 0)} point${Number(g.resolved || 0) === 1 ? '' : 's'}. This board can stay open for any extra cleanup you want to do. Click Load next challenge whenever you're ready.`);
        } else {
          addAppNotice('Challenge board refreshed from Bynder.', 'success');
        }
      } catch (err) {
        alert(err.message || String(err));
      } finally {
        setReloadButtonFlashing(false);
      }
      return;
    }
    if (state.workspace === 'product_imagery_onboarding' && state.onboarding.currentBoardId) {
      saveUIState();
      addAppNotice('Reloading Product Imagery Onboarding board from Bynder...', 'notice');
      openPIOBoardById(state.onboarding.currentBoardId, true);
      return;
    }
    launchCollection(state.loadedCollectionOptionId, {flashReload:true, scrollTopAfter:true});
  });
  document.getElementById('discardBtn').addEventListener('click', discardChanges);
  document.getElementById('commitBtn').addEventListener('click', () => commitChanges());
  document.querySelectorAll('input[name="appMode"]').forEach(el => {
    el.addEventListener('change', () => switchMode(el.value));
  });
  document.getElementById('thumbSize').addEventListener('input', renderBoard);
  const bulkFixBtn = document.getElementById('bulkFixSiloBtn');
  if (bulkFixBtn) bulkFixBtn.addEventListener('click', () => toggleBulkFixSiloMode());
  const bulkFixGoBtn = document.getElementById('bulkFixSiloGoBtn');
  if (bulkFixGoBtn) bulkFixGoBtn.addEventListener('click', () => runBulkFixSilo());
  const pioClearBoardBtn = document.getElementById('pioClearBoardBtn');
  if (pioClearBoardBtn) {
    pioClearBoardBtn.addEventListener('click', async () => {
      if (state.workspace !== 'product_imagery_onboarding' || !state.board) return;
      const queuedCount = changedAssetIds().size;
      if (queuedCount > 0) {
        const shouldCommit = confirm(`You have ${queuedCount} queued change(s). Press OK to commit them to Bynder and then remove this board from the screen. Press Cancel to keep working on the board.`);
        if (!shouldCommit) return;
        const success = await commitChanges(true);
        if (!success) return;
      }
      clearPIOBoardView();
    });
  }
  document.getElementById('photoThumbSize').addEventListener('input', (e) => {
    state.photography.thumb = Number(e.target.value || 170);
    const minimum = Math.max(420, Math.round((Math.max(190, Math.round(state.photography.thumb * 1.02)) * 2) + 34));
    if (state.photography.width < minimum) state.photography.width = minimum;
    renderPhotographyPanel();
  });
  document.getElementById('photoToggleBtn').addEventListener('click', () => {
    state.photography.expanded = !state.photography.expanded;
    renderPhotographyPanel();
  });
  document.getElementById('photoClearBtn').addEventListener('click', () => {
    if (state.photography.items.length && !confirm('Clear the Photography panel?')) return;
    clearPhotographyPanel();
  });
  const resizeHandle = document.getElementById('photoResizeHandle');
  if (resizeHandle) {
    resizeHandle.addEventListener('mousedown', (ev) => {
      ev.preventDefault();
      const startX = ev.clientX;
      const startWidth = state.photography.width;
      const onMove = (moveEv) => {
        const delta = moveEv.clientX - startX;
        state.photography.width = Math.max(420, Math.min(1200, startWidth + delta));
        state.photography.expanded = true;
        renderPhotographyPanel();
      };
      const onUp = () => {
        document.removeEventListener('mousemove', onMove);
        document.removeEventListener('mouseup', onUp);
      };
      document.addEventListener('mousemove', onMove);
      document.addEventListener('mouseup', onUp);
    });
  }
  renderModeUI();
  document.getElementById('toggleSummaryBtn').addEventListener('click', () => {
    state.summaryOpen = !state.summaryOpen;
    document.getElementById('toggleSummaryBtn').textContent = state.summaryOpen ? '▴' : '▾';
    renderSummary();
  });

  document.getElementById('toggleLogBtn').addEventListener('click', () => {
    state.logOpen = !state.logOpen;
    document.getElementById('serverLog').style.display = state.logOpen ? 'block' : 'none';
    document.getElementById('toggleLogBtn').textContent = state.logOpen ? '▴' : '▾';
    if (state.logOpen) startMessagePolling();
    else stopMessagePolling();
  });
  document.getElementById('idleDismissBtn').addEventListener('click', closeIdleModal);
  document.getElementById('idleKeepWorkingBtn').addEventListener('click', closeIdleModal);
  document.getElementById('idleReloadBtn').addEventListener('click', async () => {
    closeIdleModal();
    const reloadBtn = document.getElementById('reloadBtn');
    if (reloadBtn) {
      reloadBtn.click();
    }
  });
}

bindStaticUI();
bindIdleActivityWatchers();
refreshGameStatus();
renderGameModesPanel();
setInterval(() => {
  refreshGameStatus();
  if (state.game && (Date.now() - Number(state.idle.lastActivityAt || 0)) > 12000) scheduleGameQueueEnsure(false);
}, 10000);
window.addEventListener('resize', updateStickyOffsets);
document.addEventListener('keydown', handlePhotoPrepArrowKeys);
window.addEventListener('load', updateStickyOffsets);
window.addEventListener('beforeunload', saveUIState);
loadCollections().then(()=>restoreUIStateIfPossible());
setTimeout(updateStickyOffsets, 50);
setTimeout(updateStickyOffsets, 300);
</script>
</body>
</html>
'''


# ============================================================
# LAUNCHER
# ============================================================


def open_browser_later() -> None:
    if not OPEN_BROWSER_ON_START:
        return
    def _open() -> None:
        time.sleep(1.2)
        webbrowser.open(f"http://{HOST}:{PORT}")
    threading.Thread(target=_open, daemon=True).start()


if __name__ == "__main__":
    log_message("Starting Content Refresher local server.")
    if google_scoreboard_is_configured():
        log_message(f"Google scoreboard enabled using credentials at {get_google_scoreboard_credentials_path()}")
    else:
        log_message(f"Google scoreboard disabled: credentials file not found at {get_google_scoreboard_credentials_path()}")
    start_server_side_game_queue_worker()
    maybe_start_game_queue_fill(force=True, target_count=GAME_QUEUE_PRELOAD_TARGET)
    open_browser_later()
    app.run(host=HOST, port=PORT, debug=False, threaded=True)
