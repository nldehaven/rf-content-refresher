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
from collections import defaultdict
from io import BytesIO
from zipfile import ZipFile, ZIP_DEFLATED
from concurrent.futures import ThreadPoolExecutor, as_completed
from copy import deepcopy
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import quote, unquote

import requests
from PIL import Image, ImageOps, ImageDraw, ImageFont
from flask import Flask, Response, jsonify, request, stream_with_context, send_file
from werkzeug.utils import secure_filename


# ============================================================
# USER CONFIGURATION
# ============================================================
BYNDER_BASE_URL = "https://www.bynder.raymourflanigan.com"
BYNDER_TOKEN_PATH = r"C:\bynderAPI\byndercredentials_permanenttoken.json"

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

ASSET_SUBTYPE_REQUIRED = "Product_Site_Asset"
MARKED_FOR_DELETION_VALUE_NAME = "Marked_for_Deletion"

CORE_SLOTS = [f"SKU_{n}" for n in range(100, 5000, 100)]
SWATCH_DETAIL_SLOTS = [f"SKU_{n}" for n in range(5000, 6000, 100)]
GRID_SLOT = "SKU_grid"
SPECIAL_SLOTS = ["SKU_dimension", "SKU_swatch", "SKU_square"]
ALL_KNOWN_SLOTS = [GRID_SLOT] + CORE_SLOTS + SWATCH_DETAIL_SLOTS + SPECIAL_SLOTS

DOWNLOADS_DIR = Path.home() / "Downloads"
DOWNLOADS_DIR.mkdir(parents=True, exist_ok=True)

COLLECTION_OPTIONS_CACHE_PATH = Path.home() / ".content_refresher_collection_options_cache.json"
COLLECTION_OPTIONS_CACHE_MAX_AGE_SECONDS = 24 * 60 * 60

PHOTO_WATERMARK_ALPHA = 0.46
PHOTO_WATERMARK_TEXT = ("NOT", "FINAL")
PHOTO_WATERMARK_WIDTH_RATIO = 0.86
PHOTO_WATERMARK_HEIGHT_RATIO = 0.80
PHOTO_WATERMARK_LINE_GAP_RATIO = 0.10

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
}

METAPROPERTY_DBNAME_CACHE: Dict[str, str] = {}
PROPERTY_DB_NAMES: Dict[str, str] = {
    "Product_SKU": "Product_SKU",
    "Product_SKU_Position": "Product_SKU_Position",
    "Marked_for_Deletion": "Marked_for_Deletion_from_Site",
    "Deliverable": "Deliverable",
    "Product_Color": "Product_Color",
    "Product_URL": "Product_URL",
}


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


def boolish(value: Any) -> bool:
    value_str = string_value(value).strip().lower()
    return value_str in {"true", "yes", "1"}


def parse_datetime(value: Any) -> Optional[datetime]:
    text = string_value(value)


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


def parse_target_size(size_text: str) -> tuple[int, int]:
    m = re.match(r"^(\d+)x(\d+)$", string_value(size_text))
    if not m:
        return (3000, 1688)
    return (int(m.group(1)), int(m.group(2)))


def prep_mode_to_size(mode: str) -> tuple[int, int]:
    mode = string_value(mode)
    if mode == "crop_square":
        return (2000, 2000)
    if mode in ("crop_2200", "pad_tb_2200"):
        return (3000, 2200)
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


def prepare_photo_result(image: Image.Image, mode: str, flip: bool = False, offset_y: int | float | None = None, offset_x: int | float | None = None) -> Image.Image:
    mode = string_value(mode) or "crop_1688"
    out_w, out_h = prep_mode_to_size(mode)
    im = image.convert("RGB")
    if flip:
        im = ImageOps.mirror(im)
    src_w, src_h = im.size

    if mode == "crop_square":
        bounds = get_square_crop_bounds(src_w, src_h, offset_x)
        square = im.crop(bounds)
        return square.resize((out_w, out_h), Image.LANCZOS)

    if mode in ("crop_1688", "crop_2200"):
        scaled_h = int(round(src_h * (out_w / src_w)))
        scaled = im.resize((out_w, scaled_h), Image.LANCZOS)
        max_off = max(0, scaled_h - out_h)
        off = get_default_offset_y(src_w, src_h, out_w, out_h) if offset_y is None else int(round(float(offset_y)))
        off = int(clamp(off, 0, max_off))
        return scaled.crop((0, off, out_w, off + out_h))

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
    mode = string_value(mode) or "crop_1688"
    out_w, out_h = prep_mode_to_size(mode)
    im = image.convert("RGB")
    if flip:
        im = ImageOps.mirror(im)
    src_w, src_h = im.size

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
        draw.rectangle((left + 2, top + 2, right - 3, bottom - 3), outline=(255,255,255,235), width=4)
        scale = min(preview_max_w / overlay.size[0], preview_max_h / overlay.size[1], 1.0)
        prev_size = (max(1, int(round(overlay.size[0] * scale))), max(1, int(round(overlay.size[1] * scale))))
        preview = overlay.resize(prev_size, Image.LANCZOS)
        return preview.convert("RGB")

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
        draw.rectangle((2, off + 2, out_w - 3, bottom - 3), outline=(255,255,255,235), width=4)

        scale = min(preview_max_w / overlay.size[0], preview_max_h / overlay.size[1], 1.0)
        prev_size = (max(1, int(round(overlay.size[0] * scale))), max(1, int(round(overlay.size[1] * scale))))
        preview = overlay.resize(prev_size, Image.LANCZOS)
        return preview.convert("RGB")

    final_img = prepare_photo_result(im, mode, False, offset_y, offset_x)
    scale = min(preview_max_w / final_img.size[0], preview_max_h / final_img.size[1], 1.0)
    prev_size = (max(1, int(round(final_img.size[0] * scale))), max(1, int(round(final_img.size[1] * scale))))
    return final_img.resize(prev_size, Image.LANCZOS)


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


def build_metadata_copy_fields(source_media: Dict[str, Any], metaprops_by_dbname: Dict[str, Dict[str, Any]], target_sku: str, target_position: str, target_name: str) -> List[Tuple[str, Any]]:
    fields: List[Tuple[str, Any]] = []
    skip_db_names = {"Product_SKU", "Product_SKU_Position"}
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
    fields.append(("name", target_name))
    fields.append(("tags", target_sku))
    return fields


def renamed_copy_filename(original_filename: str, source_sku: str, target_sku: str) -> str:
    original_filename = original_filename or f"{source_sku}.jpg"
    if source_sku and source_sku in original_filename:
        return original_filename.replace(source_sku, target_sku, 1)
    stem, ext = os.path.splitext(original_filename)
    return f"{target_sku}_{stem}{ext or '.jpg'}"


def create_copied_asset_for_target(session: requests.Session, source_media_id: str, source_sku: str, target_sku: str, target_position: str) -> Dict[str, Any]:
    source_media = fetch_media_by_id(session, source_media_id)
    fallback_name = string_value(source_media.get("name")) or f"{source_media_id}.jpg"
    original_name = filename_from_original(string_value(source_media.get("original")), fallback_name)
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
    fields = build_metadata_copy_fields(source_media, metaprops_by_dbname, target_sku, target_position, target_name)
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
            mark_asset_uploaded_notice(target_asset, 'new_version', 'New version uploaded to this slot. Reload to view.')
            return {"message": "Prepared image was updated. Reload to see it!", "kind": "updated"}

        exemplar = pick_left_exemplar_asset(row, target_lane, target_slot) or pick_lane_exemplar_asset(row, target_lane)
        if not exemplar:
            raise RuntimeError("Could not find a source asset in this row to borrow metadata from for the upload.")

        derived_name = derive_cru_filename(row, target_lane, exemplar, prepared_name)
        target_name = force_jpg_filename(derived_name, Path(prepared_name).stem or "prepared_image")
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
        fields = build_metadata_copy_fields(source_media, metaprops_by_dbname, sku, target_position, target_stem)
        post_media_fields(session, new_media_id, fields)
        placeholder = build_uploaded_new_asset_placeholder(exemplar, sku, target_position, target_name, target_lane, target_slot, new_media_id)
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
) -> Dict[str, Any]:
    img = open_image_from_media(session, media_id)
    result = prepare_photo_result(img, prep_mode, flip, offset_y, offset_x)
    out_w, out_h = prep_mode_to_size(prep_mode)
    with tempfile.TemporaryDirectory(prefix="content_refresher_prepped_drop_") as td:
        temp_path = Path(td) / f"prepared_{out_w}x{out_h}{'_flip' if flip else ''}.jpg"
        result = result.convert("RGB")
        result.save(temp_path, format="JPEG", quality=92, optimize=True)
        return apply_prepared_file_to_slot(session, board, row_id, target_lane, target_slot, temp_path)


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


def build_pending_new_asset(source_asset: Dict[str, Any], target_sku: str, target_position: str, staged_path: Path, target_name: str) -> Dict[str, Any]:
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


def build_uploaded_new_asset_placeholder(source_asset: Dict[str, Any], target_sku: str, target_position: str, target_name: str, target_lane: str, target_slot: str, new_media_id: str = '') -> Dict[str, Any]:
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
    clone["original_state"] = {"position": target_position, "is_marked_for_deletion": False}
    clone["dateCreated"] = datetime.now().isoformat()
    clone["transformBaseUrl"] = ""
    clone["original"] = ""
    clone["size_warning"] = ""
    clone.pop("pending_upload", None)
    clone.pop("pending_upload_kind", None)
    clone.pop("pending_message", None)
    clone.pop("staged_file_path", None)
    return clone


def apply_uploaded_file_to_slot(session: requests.Session, board: Dict[str, Any], row_id: str, target_lane: str, target_slot: str, uploaded_file_storage) -> str:
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
            mark_asset_uploaded_notice(target_asset, 'new_version', 'New version uploaded to this slot. Reload to view.')
            return {"message": "Asset was updated. Reload to see it!", "kind": "updated"}

        exemplar = pick_left_exemplar_asset(row, target_lane, target_slot) or pick_lane_exemplar_asset(row, target_lane)
        if not exemplar:
            raise RuntimeError("Could not find a source asset in this row to borrow metadata from for the upload.")

        target_name = derive_cru_filename(row, target_lane, exemplar, original_name)
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
        fields = build_metadata_copy_fields(source_media, metaprops_by_dbname, sku, target_position, target_stem)
        post_media_fields(session, new_media_id, fields)
        placeholder = build_uploaded_new_asset_placeholder(exemplar, sku, target_position, target_name, target_lane, target_slot, new_media_id)
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
    return prop(asset, "Product_SKU_Position", "Product_SKU_Position")


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
    if width <= 0 or height <= 0:
        return ""
    if slot_key == "SKU_square":
        if width == height and width >= 1000:
            return ""
        return f"Size {width}x{height}; expected square and at least 1000x1000"
    expected_w, expected_h = expected_dimensions_for_slot(slot_key)
    if width == expected_w and height == expected_h:
        return ""
    return f"Size {width}x{height}; expected {expected_w}x{expected_h}"


def refresh_row_asset_flags(row: Dict[str, Any]) -> None:
    for asset in row.get("assets", []):
        asset["size_warning"] = compute_dimension_warning(asset)


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
    if option_id in cache:
        return deepcopy(cache[option_id])
    items = fetch_all_media_for_option(session, option_id)
    cache[option_id] = deepcopy(items)
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

def photo_asset_to_client_model(asset: Dict[str, Any], matching_skus: List[str]) -> Dict[str, Any]:
    original = string_value(asset.get("original"))
    name = string_value(asset.get("name"))
    file_name = filename_from_original(original, name)
    tags = parse_photo_tags(asset)
    matching = [t for t in tags if t in set(matching_skus)]
    fp = asset.get("activeOriginalFocusPoint") or {}
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
        "asset_status": get_photography_asset_status(asset),
        "is_final": photography_asset_is_final(asset),
        "tags": tags,
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
    component_skus = get_component_skus_for_grid_asset_cached(session, newest_grid)
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
        "product_collection": prop(anchor, "Product_Collection", "Product_Collection") or collection_label,
        "dropped": prop(anchor, "Dropped", "Dropped"),
        "visible_on_website": prop(anchor, "Visible_on_Website", "Visible_on_Website"),
        "date_oldest": oldest_dt.isoformat() if oldest_dt else "",
        "date_newest": newest_dt.isoformat() if newest_dt else "",
        "inactive": status != "Active",
        "assets": client_assets,
        "overflow_warnings": [],
        "commit_failures": [],
        "is_non_collection": bool(is_non_collection),
    }
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
    elif collection_option_id in board_cache:
        return deepcopy(board_cache[collection_option_id])

    raw_collection_assets = fetch_collection_assets_cached(session, collection_option_id, force_refresh=force_refresh)

    derived_cache = STATE.setdefault("collection_derived_cache", {})
    if force_refresh:
        derived_cache.pop(collection_option_id, None)
    derived = derived_cache.get(collection_option_id)

    if derived is None:
        photo_counts_by_color = count_available_product_photography_by_color(raw_collection_assets)
        psa_assets = [a for a in raw_collection_assets if is_product_site_asset(a)]
        grid_candidates = [a for a in psa_assets if prop(a, "Deliverable", "Deliverable") == "Product_Grid_Image"]
        grid_assets_by_sku = defaultdict(list)
        for asset in grid_candidates:
            sku = prop(asset, "Product_SKU", "Product_SKU")
            if sku:
                grid_assets_by_sku[sku].append(asset)

        unique_skus = sorted(grid_assets_by_sku.keys())
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
        derived_cache[collection_option_id] = deepcopy(derived)
    else:
        photo_counts_by_color = deepcopy(derived.get("photo_counts_by_color", {}))
        unique_skus = list(derived.get("unique_skus", []))
        rows_by_sku = deepcopy(derived.get("rows_by_sku", {}))
        rows_by_color = defaultdict(list, deepcopy(derived.get("rows_by_color", {})))
        log_message(f"Using cached derived collection data for {collection_label}: {len(unique_skus)} SKUs.")

    color_sections = []
    for color in sorted(rows_by_color.keys(), key=lambda c: (c or "").lower()):
        section_rows = list(rows_by_color[color])
        section_rows.sort(key=lambda r: (bool(r.get("inactive")), (r.get("product_name") or "").lower(), r.get("sku") or ""))
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
    board_cache[collection_option_id] = deepcopy(board)
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


def sanitize_copy_warning(target_lane: str) -> bool:
    return target_lane != "swatch_detail"


def make_pending_copy_asset(source_asset: Dict[str, Any], target_sku: str) -> Dict[str, Any]:
    clone = deepcopy(source_asset)
    clone["id"] = f"pending-copy::{uuid.uuid4()}"
    clone["sku"] = target_sku
    clone["source_sku"] = source_asset.get("copy_source_sku") or source_asset.get("source_sku") or source_asset.get("sku") or ""
    clone["pending_upload"] = True
    clone["pending_upload_kind"] = "copy"
    clone["pending_message"] = "Pending copy upload"
    clone["copy_source_media_id"] = source_asset.get("copy_source_media_id") or source_asset.get("id")
    clone["copy_source_sku"] = source_asset.get("copy_source_sku") or source_asset.get("sku") or source_asset.get("source_sku") or ""
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
        asset = make_pending_copy_asset(source_asset, target_row.get("sku", ""))
        if sanitize_copy_warning(target_lane):
            target_row.setdefault("overflow_warnings", []).append(
                f"{source_asset.get('file_name') or source_asset.get('name') or source_asset.get('id')} will be copied from SKU {source_asset.get('copy_source_sku') or source_asset.get('source_sku') or source_row.get('sku')} to SKU {target_row.get('sku')}."
            )

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
                            }
                        )
                    continue

                payload = {}
                if current_position != original_position:
                    payload[f"metaproperty.{PRODUCT_SKU_POSITION_METAPROPERTY_ID}"] = current_position
                if current_deleted != original_deleted:
                    payload[f"metaproperty.{MARKED_FOR_DELETION_METAPROPERTY_ID}"] = MARKED_FOR_DELETION_OPTION_ID if current_deleted else ""

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
            response = create_copied_asset_for_target(session, job["source_media_id"], job["source_sku"], job["target_sku"], job["target_position"])
            results.append({**job, "success": True, "response": response, "job_type": "copy"})
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
                cleanup_staged_file(str(staged_path))
                results.append({**job, "success": True, "response": response})
                success_count += 1
                log_message(f"Uploaded pending new version onto {job['media_id']} ({job['asset_name']}) successfully.")
                continue
            if job.get("job_type") == "new_asset":
                staged_path = Path(job.get("staged_file_path") or "")
                source_media = fetch_media_by_id(session, job["source_media_id"])
                target_name = os.path.splitext(job["asset_name"])[0]
                new_media_id = upload_new_asset_group_upload(session, staged_path, target_name)
                metaprops_by_dbname = fetch_metaproperties_map(session)
                fields = build_metadata_copy_fields(source_media, metaprops_by_dbname, job["sku"], job["target_position"], target_name)
                post_media_fields(session, new_media_id, fields)
                cleanup_staged_file(str(staged_path))
                response = {"new_media_id": new_media_id}
                results.append({**job, "success": True, "response": response})
                success_count += 1
                log_message(f"Uploaded pending new asset for SKU {job['sku']} into {job['target_position']} successfully.")
                continue
            response = update_asset_metadata(session, job["media_id"], job["payload"])
            results.append({**job, "success": True, "response": response})
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

    return {
        "success_count": success_count,
        "failure_count": failure_count,
        "results": results,
        "log_path": log_path,
        "all_succeeded": failure_count == 0,
    }


# ============================================================
# API ROUTES
# ============================================================
@app.route("/")
def index() -> Response:
    return Response(INDEX_HTML, mimetype="text/html")


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
        STATE["board"] = board
        STATE["baseline_board"] = deepcopy(board)
        STATE["last_load"] = datetime.now().isoformat()

        return jsonify({
            "board": board,
            "summary": compute_change_summary(board),
        })
    except Exception as exc:
        log_message(f"Collection load failed: {exc}")
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
        media_id = string_value(payload.get("media_id"))
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
            media_id = string_value(item.get("media_id"))
            name = string_value(item.get("name")) or media_id
            offset_y = item.get("offset_y")
            img = open_image_from_media(session, media_id)
            result = prepare_photo_result(img, mode, flip, offset_y)
            fname = f"{Path(name).stem}_{out_w}x{out_h}{'_flip' if flip else ''}.jpg"
            return send_file(BytesIO(image_to_jpg_bytes(result)), mimetype="image/jpeg", as_attachment=True, download_name=fname)
        bio = BytesIO()
        with ZipFile(bio, 'w', ZIP_DEFLATED) as zf:
            for item in items:
                media_id = string_value(item.get("media_id"))
                name = string_value(item.get("name")) or media_id
                offset_y = item.get("offset_y")
                img = open_image_from_media(session, media_id)
                result = prepare_photo_result(img, mode, flip, offset_y)
                fname = f"{Path(name).stem}_{out_w}x{out_h}{'_flip' if flip else ''}.jpg"
                zf.writestr(fname, image_to_jpg_bytes(result))
        bio.seek(0)
        return send_file(bio, mimetype='application/zip', as_attachment=True, download_name=f"photo_prep_{mode}{'_flip' if flip else ''}.zip")
    except Exception as exc:
        log_message(f"Photo prep download failed: {exc}")
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
                upstream = requests.get(original_url, stream=False, timeout=120)
                upstream.raise_for_status()
            except Exception:
                upstream = None

        if upstream is None:
            download_url = get_media_download_url(session, source_media_id)
            upstream = request_with_retries(session, "GET", download_url, timeout=120)

        mime = upstream.headers.get("Content-Type") or mimetypes.guess_type(file_name)[0] or "application/octet-stream"
        content = upstream.content
        headers = {
            "Content-Disposition": f'attachment; filename="{file_name}"',
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
        media_id = string_value(payload.get("media_id"))
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
        media_id = string_value(payload.get("media_id"))
        prep_mode = string_value(payload.get("prep_mode") or "crop_1688")
        flip = bool(payload.get("flip"))
        offset_y = payload.get("offset_y")
        offset_x = payload.get("offset_x")
        if not media_id:
            return jsonify({"error": "media_id is required"}), 400
        token = load_bynder_token(BYNDER_TOKEN_PATH)
        session = make_session(token)
        result = apply_prepared_media_to_slot(session, board, row_id, target_lane, target_slot, media_id, prep_mode, flip, offset_y, offset_x)
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
        result = apply_uploaded_file_to_slot(session, board, row_id, target_lane, target_slot, upload)
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
            STATE.setdefault("collection_board_cache", {})[collection_id] = deepcopy(board)
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

        if result["all_succeeded"]:
            # Refresh from Bynder only if every change succeeded.
            invalidate_collection_caches(string_value(STATE["board"]["collection"].get("id")))
            board = build_board_for_collection(session, STATE["board"]["collection"], force_refresh=True)
            STATE["board"] = board
            STATE["baseline_board"] = deepcopy(board)
            return jsonify({
                "commit": result,
                "board": board,
                "summary": compute_change_summary(board),
                "refreshed": True,
            })

        return jsonify({
            "commit": result,
            "board": STATE["board"],
            "summary": compute_change_summary(STATE["board"]),
            "refreshed": False,
        })
    except Exception as exc:
        log_message(f"Commit failed: {exc}")
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
   .color-toggle {
    white-space: nowrap;
 border: 0; background: transparent; color: var(--rf-navy); font-weight: 800; cursor: pointer; }
  .top-notices { display: grid; gap: 8px; margin-bottom: 6px; min-width: 0; }
  .missing-notice { padding: 10px 12px; border-radius: 12px; background: #fff6db; border: 1px solid #ead48b; color: #6d5500; font-size: 13px; cursor: pointer; text-align: left; width: 100%; }
  .missing-notice strong { color: #523d00; }

  .mode-panel { padding: 8px 10px; }
  .mode-panel .panel-title { font-size: 12px; font-weight: 800; letter-spacing: .04em; color: var(--rf-navy); text-transform: uppercase; margin: 0 0 6px 0; }
  .mode-help { font-size: 12px; color: #6d5a77; line-height: 1.18; margin-bottom: 6px; }
  .mode-options { display: grid; gap: 6px; }
  .mode-option { display: flex; align-items: center; gap: 8px; font-weight: 700; color: var(--rf-navy); cursor: pointer; }
  .mode-option input { accent-color: var(--rf-purple); }
  .mode-banner { display:none; }
  .notifications-panel { padding: 12px; min-width: 0; }
  .notifications-panel .panel-title { font-size: 12px; font-weight: 800; letter-spacing: .04em; color: var(--rf-navy); text-transform: uppercase; margin: 0 0 8px 0; }
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
  .photo-prep-actions .photo-mini-btn { padding: 6px 8px; font-size: 11px; line-height: 1.08; border-radius: 10px; }
  .photo-pull-btn { padding: 6px 8px; font-size: 12px; line-height: 1.15; }
  .photo-pull-btn-checking { animation: photoPullCheckingPulse 1.2s ease-in-out infinite; }
  .photo-toolbar { padding: 10px 14px; border-bottom:1px solid #d8e7da; background:#f7fbf7; display:flex; justify-content:space-between; align-items:center; gap:10px; flex-wrap:wrap; }
  .photo-body { flex:1; overflow:auto; padding: 12px; }
  .photo-prep-drawer { position: sticky; top: 0; z-index: 5; border:1px solid #cddfd0; background: linear-gradient(180deg,#f8fcf8,#eef7ef); border-radius:16px; padding:10px; margin-bottom:12px; box-shadow:0 8px 18px rgba(65,98,71,.08); }
  .photo-prep-drawer h4 { margin:0 0 4px; font-size:14px; color:#2f5134; }
  .photo-prep-top { display:flex; justify-content:space-between; align-items:center; gap:12px; }
  .photo-prep-sub { font-size:12px; color:#55705a; line-height:1.35; }
  .photo-prep-controls { display:grid; gap:10px; margin-top:8px; }
  .photo-prep-row { display:flex; flex-wrap:wrap; gap:10px; align-items:center; }
  .photo-prep-row label { font-size:12px; color:#415346; display:flex; align-items:center; gap:6px; }
  .photo-prep-preview-wrap { display:grid; grid-template-columns:minmax(0,1fr); gap:10px; align-items:start; }
  .photo-prep-preview { border:1px solid #d7e6da; background:white; border-radius:14px; min-height:170px; display:flex; align-items:center; justify-content:center; overflow:hidden; }
  .photo-prep-preview img { width:100%; height:auto; display:block; max-height:270px; object-fit:contain; }
  .photo-prep-preview-drag { width:100%; display:flex; align-items:center; justify-content:center; cursor:grab; }
  .photo-prep-preview-drag.dragging { cursor:grabbing; opacity:.96; }
  .photo-prep-filmstrip { display:none; }
  .photo-prep-film-btn { display:flex; gap:8px; align-items:center; border:1px solid #d6e5d9; background:white; border-radius:12px; padding:6px; cursor:pointer; }
  .photo-prep-film-btn.active { border-color:#5ea870; box-shadow:0 0 0 2px rgba(94,168,112,.18); }
  .photo-prep-film-btn img { width:42px; height:42px; object-fit:contain; background:#f4f7f4; border-radius:8px; }
  .photo-prep-actions { display:flex; gap:8px; flex-wrap:wrap; justify-content:flex-end; align-items:center; }
  .photo-prep-toolbar { display:grid; grid-template-columns:minmax(0,1fr); gap:10px; align-items:start; }
  .photo-prep-left { display:grid; gap:8px; }
  .photo-prep-focusbox { display:flex; flex-wrap:nowrap; gap:12px; align-items:center; border:1px solid #d7e6da; background:#fff; border-radius:12px; padding:10px 12px; max-width:520px; }
  .photo-focus-pad { display:flex; flex-wrap:nowrap; gap:6px; align-items:center; justify-content:flex-start; }
  .photo-focus-pad button { width:30px; height:30px; border-radius:8px; border:1px solid #cddfd0; background:#f7fbf7; color:#315037; cursor:pointer; font-size:16px; line-height:1; }
  .photo-focus-pad .blank { display:none; }
  .photo-focus-meta { display:grid; gap:4px; font-size:12px; color:#4f6355; }
  .photo-focus-chip { display:inline-flex; align-items:center; gap:6px; padding:4px 8px; border-radius:999px; background:#eef6ef; border:1px solid #d7e6da; font-size:12px; color:#35543b; }
  .photo-prep-active { display:none; }
  .photo-prep-options { display:flex; flex-wrap:wrap; gap:12px; align-items:center; }
  .photo-prep-options label { font-size:12px; color:#415346; display:flex; align-items:center; gap:6px; }
  .photo-prep-note { font-size:11px; color:#5d7463; }
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
  .photo-grid { display:grid; gap:12px; grid-template-columns: repeat(auto-fill, minmax(var(--photo-tile-min, 220px), 1fr)); }
  .photo-tile { background:white; border:1px solid #d6e5d9; border-radius:14px; box-shadow: 0 6px 16px rgba(56,90,61,.08); overflow:hidden; display:flex; flex-direction:column; }
  .photo-tile.dragover { border-color: #56a06a; box-shadow: 0 0 0 2px rgba(86,160,106,.18); }
  .photo-tile img { width:100%; height: var(--photo-thumb-height, 170px); object-fit: contain; display:block; background:#f4f7f4; padding: 4px; }
  .photo-meta { padding: 8px 10px; display:grid; gap:4px; }
  .photo-name { font-size:12px; font-weight:700; color: var(--rf-navy); overflow-wrap:anywhere; }
  .photo-name a { color: inherit; text-decoration: underline; text-decoration-color: rgba(30, 64, 175, 0.28); }
  .photo-name a:hover { text-decoration-color: rgba(30, 64, 175, 0.62); }
  .photo-line { font-size:11px; color:#5b6a5e; }
  .photo-actions { display:flex; gap:8px; }
  .photo-actions a { font-size:11px; color: var(--rf-blue); text-decoration:none; }
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
    grid-template-columns: 126px minmax(0, 1fr);
    gap: 14px;
    align-items: start;
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
    width: 118px;
    min-width: 118px;
    max-width: 118px;
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
    grid-template-columns: auto auto minmax(220px, 1fr);
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
    height: calc(var(--thumb-height, 84px) * 0.72);
  }
  .slot.trash .asset-card {
    transform: scale(0.92);
    transform-origin: top left;
    margin-bottom: -8px;
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
  .asset-actions {
    display: flex;
    gap: 6px;
    margin-top: 0;
    line-height: 1.1;
  }
  .asset-actions a {
    font-size: 10px;
    color: var(--rf-blue);
    text-decoration: none;
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
  .summary-header {
    padding: 2px 8px;
    border-bottom: 1px solid var(--rf-border);
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: 8px;
    min-height: 24px;
    margin: 0;
  }
  .summary-header h3 {
    margin: 0;
    font-size: 12px;
    font-weight: 700;
    line-height: 1.1;
    color: var(--rf-navy);
  }
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
  .inline-launch-group { display:grid; grid-template-columns:minmax(180px,1fr) minmax(180px,1fr) 160px; gap:10px; align-items:start; }
  .inline-launch-group .btn { width:100%; white-space:normal; line-height:1.12; padding:10px 12px; min-height:48px; display:flex; align-items:center; justify-content:center; text-align:center; overflow-wrap:anywhere; }
  .launcher-lower-row { display:flex; align-items:center; gap:14px; margin-top:10px; }
  .launcher-checkbox-row { margin-top:0; flex:0 0 auto; display:flex; align-items:center; }
  .launcher-checkbox-row .mode-option { margin:0; white-space:nowrap; }
  .collection-status-mount { margin-top:0; min-height:0; flex:1 1 auto; }
  .collection-status-pill { padding:12px 14px; border-radius:14px; border:1px solid #c6d8cf; background:#d8e4dd; color:#2f6b41; font-size:13px; line-height:1.35; font-weight:500; box-shadow: inset 0 1px 0 rgba(255,255,255,.45); }
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


</style>
</head>
<body>
  <div class="shell">
    <div class="top-shell">
      <div class="panel brand-panel">
      <h1>Content Refresher</h1>
      <div class="sub">Live Bynder board for Product Collection image cleanup, slotting, and safe staged updates.</div>
    </div>

    <div class="panel launcher" id="launcherPanel">
      <div class="select-wrap">
        <div class="inline-launch-group">
          <div>
            <label class="small">Search Product Collection</label>
            <input type="text" id="collectionFilter" placeholder="Type any part of the collection name" />
          </div>
          <div>
            <label class="small">Product Collection</label>
            <select id="collectionSelect" size="1"></select>
          </div>
          <div>
            <label class="small">&nbsp;</label>
            <button type="button" class="btn btn-primary" id="launchBtn">Launch Collection</button>
          </div>
        </div>
        <div class="launcher-lower-row">
          <div class="launcher-checkbox-row">
            <label class="mode-option" style="display:flex; align-items:center; gap:6px;"><input type="checkbox" id="hideInactiveToggle" /> Hide inactive SKUs</label>
          </div>
          <div class="collection-status-mount" id="collectionStatusMount"></div>
        </div>
      </div>
    </div>

    <div class="panel mode-panel">
      <div class="panel-title">Mode</div>
      <div class="mode-help" id="modeHelp">Update positions stages reorder, trash, restore, and cross-SKU copy changes. File uploads are disabled in this mode.</div>
      <div class="mode-options">
        <label class="mode-option"><input type="radio" name="appMode" value="positions" checked /> Update positions</label>
        <label class="mode-option"><input type="radio" name="appMode" value="assets" /> Update assets</label>
      </div>

      </div>

    <div class="panel notifications-panel">
      <div class="panel-title">Notifications</div>
      <div id="boardNotifications"><div class="notifications-empty">No collection notifications yet.</div></div>
    </div>

      <div class="side">
        <div class="panel">
        <div class="summary-header">
          <h3>Queued changes</h3>
          <button type="button" class="btn btn-secondary" id="toggleSummaryBtn">Expand</button>
        </div>
        <div class="summary-body" id="summaryBody"></div>
        <div class="summary-header" style="margin-top:0;">
          <h3>Server log</h3>
          <button type="button" class="btn btn-secondary" id="toggleLogBtn">Expand</button>
        </div>
        <div class="server-log" id="serverLog" style="display:none;"></div>
        <div class="summary-header" style="margin-top:0;">
          <h3>My notes</h3>
          <button type="button" class="btn btn-secondary" id="toggleNotesBtn">Expand</button>
        </div>
        <div class="notes-panel" id="myNotesPanel">
          <div class="notes-list" id="myNotesList"></div>
        </div>
        </div>
      </div>
    </div>

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
      <h3>Giving Bynder a moment...</h3>
      <p>Your updates went through. Waiting 30 seconds before checking for refreshed metadata.</p>
      <div class="wait-status" id="waitStatus">Standing by...</div>
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
    prep: { flip: false, mode: 'crop_1688', offsetYOverrides: {} },
    previewUrl: '',
    hideFpo: false,
  },
  photoSkuOpen: {},
  photoDragId: null,
  preparedPreviewDrag: null,
  additionalPhotoAvailabilityBySku: {},
  additionalPhotoCheckInFlight: {},
  nonCollectionSkuLoading: {},
  collectionNotice: {kind:'notice', text:'Loading Product Collection options...'},
  launchLoadingTicker: null,
  collectionSource: '',
  notesOpen: false,
  notes: [
    {id:'note-1', text:''},
    {id:'note-2', text:''},
    {id:'note-3', text:''},
  ],
  waitFlow: {
    open: false,
    baselineFingerprint: '',
    activeToken: 0,
  },
  messagePollTimer: null,
  idle: {
    thresholdMs: 30 * 60 * 1000,
    lastActivityAt: Date.now(),
    modalOpen: false,
  },
};

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
  if (!state.collectionNotice || !state.collectionNotice.text) {
    host.innerHTML = '';
    return;
  }
  host.innerHTML = `<div class="collection-status-pill ${escapeHtml(state.collectionNotice.kind || 'notice')}">${escapeHtml(state.collectionNotice.text)}</div>`;
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
  renderNotesPanel();
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
          asset.pending_upload ? '1' : '0',
          asset.is_marked_for_deletion ? '1' : '0'
        ].join(':'));
      }
    }
  }
  return parts.join('|');
}

function setWaitOverlay(open, statusText='') {
  state.waitFlow.open = !!open;
  const overlay = document.getElementById('waitOverlay');
  const status = document.getElementById('waitStatus');
  if (overlay) overlay.classList.toggle('open', !!open);
  if (status && statusText) status.textContent = statusText;
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

function renderModeUI() {
  const help = document.getElementById('modeHelp');
  document.querySelectorAll('input[name="appMode"]').forEach(el => {
    el.checked = el.value === state.mode;
  });
  const hideInactiveToggle = document.getElementById('hideInactiveToggle');
  if (hideInactiveToggle) hideInactiveToggle.checked = !!state.hideInactive;
  if (state.mode === 'assets') {
    help.textContent = 'Update assets disables reordering and lets you drop files onto slots to create new assets or upload new versions. Asset uploads happen immediately in this mode.';
  } else {
    help.textContent = 'Update positions stages reorder, trash, restore, and cross-SKU copy changes. File uploads are disabled in this mode.';
  }
}


function markAssetModeDirtyRows(rowIds) {
  (rowIds || []).forEach(rowId => {
    const key = String(rowId || '').trim();
    if (key) state.assetModeDirtyRows[key] = true;
  });
}

async function refreshDirtyAssetRows() {
  const rowIds = Object.keys(state.assetModeDirtyRows || {}).filter(Boolean);
  if (!rowIds.length) return false;
  const resp = await fetch('/api/refresh_rows', {
    method: 'POST',
    headers: {'Content-Type': 'application/json'},
    body: JSON.stringify({row_ids: rowIds})
  });
  const data = await resp.json();
  if (!resp.ok) throw new Error(data.error || 'Row refresh failed');
  state.board = data.board || state.board;
  state.summary = data.summary || state.summary;
  state.assetModeDirtyRows = {};
  state.assetModeDirty = false;
  return true;
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
  if (state.assetModeDirty && state.loadedCollectionOptionId) {
    try {
      const refreshed = await refreshDirtyAssetRows();
      if (!refreshed) {
        await launchCollection(state.loadedCollectionOptionId, {forceRefresh:true});
      }
    } catch (err) {
      console.warn(err);
      await launchCollection(state.loadedCollectionOptionId, {forceRefresh:true});
    }
  }
  renderBoard();
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
        if (Number.isFinite(num) && num > maxVal) maxVal = num;
      }
    }
  }
  return maxVal;
}

function laneInfo(row, laneType) {
  if (laneType === 'core') {
    const slots = [];
    const maxVal = getLaneMax('core');
    for (let n = 100; n <= maxVal; n += 100) slots.push(`SKU_${n}`);
    return slots;
  }
  if (laneType === 'swatch_detail') {
    const slots = [];
    const maxVal = getLaneMax('swatch_detail');
    for (let n = 5000; n <= maxVal; n += 100) slots.push(`SKU_${n}`);
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
        const original = asset.original_state || {};
        if (asset.pending_upload || (asset.current_position || '') !== (original.position || '') || !!asset.is_marked_for_deletion !== !!original.is_marked_for_deletion) {
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
  if (isSkuSwatch) return asset.transformBaseUrl;
  const width = forPanel ? 700 : 500;
  return `${asset.transformBaseUrl}?io=transform:scale,width:${width}&quality=80`;
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
    a.download = fileName || 'asset';
    document.body.appendChild(a);
    a.click();
    a.remove();
    window.URL.revokeObjectURL(url);
  } catch (err) {
    alert(String(err));
  }
}

function renderAssetCard(asset, changed) {
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
  const openLink = asset.original || asset.transformBaseUrl || '#';
  const downloadLink = asset.pending_upload ? `/api/download/${encodeURIComponent(asset.copy_source_media_id || asset.id || '')}` : `/api/download/${encodeURIComponent(asset.id || '')}`;
  return `
    <div class="${classes.join(' ')}" draggable="${state.mode === 'positions' ? 'true' : 'false'}" data-asset-id="${escapeHtml(asset.id)}" title="${escapeHtml(asset.size_warning || '')}">
      ${thumb ? `<img src="${escapeHtml(thumb)}" alt="" />` : `<div style="height:var(--thumb-height,84px);"></div>`}
      <div class="asset-meta">
        <div class="asset-date">${escapeHtml(shortDate(asset.dateCreated || ''))}</div>
        ${asset.pending_upload ? `<div class="asset-date" style="color:#1976d2;font-weight:700;">${escapeHtml(asset.pending_message || (asset.pending_upload_kind === 'new_version' ? 'Pending new version upload' : asset.pending_upload_kind === 'new_asset' ? 'Pending new asset upload' : 'Pending copy upload'))}</div>` : ''}
        ${asset.asset_mode_uploaded ? `<div class="asset-date" style="color:#348c4b;font-weight:700;">${escapeHtml(asset.asset_mode_message || (asset.asset_mode_uploaded === 'new_version' ? 'New version uploaded to this slot. Reload to view.' : 'New asset uploaded to this slot. Reload to view.'))}</div>` : ''}
        ${asset.size_warning ? `<div class="asset-date" style="color:#a93d36;font-weight:700;">${escapeHtml(asset.size_warning)}</div>` : ''}
        ${asset.is_marked_for_deletion ? '<div class="asset-date" style="color:#a93d36;font-weight:700;">Marked for deletion</div>' : ''}
        ${asset.lane === 'off_pattern' ? `<div class="asset-date" style="color:#8b6b00;font-weight:700;">Off-pattern: ${escapeHtml(asset.current_position || '')}</div>` : ''}
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

function renderSlot(rowId, lane, slotName, items, label, changedSet, extraClass='') {
  const cards = items.length ? items.map(a => renderAssetCard(a, changedSet.has(a.id))).join('') : '<div class="empty">Drop here</div>';
  return `
    <div class="slot ${extraClass}" data-row-id="${escapeHtml(rowId)}" data-lane="${escapeHtml(lane)}" data-slot="${escapeHtml(slotName)}">
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
          <div class="meta-cell"><div class="k">Product SKU</div><div class="v">${escapeHtml(row.sku)}<div style="margin-top:4px;"><a href="https://www.bynder.raymourflanigan.com/media/?resetsearch=&field=metaproperty_Product_SKU&value=${encodeURIComponent(row.sku || '')}" target="_blank" rel="noopener">Open Product Site Assets in Bynder</a></div></div></div>
          <div class="meta-cell ${row.inactive ? 'status-inactive' : ''}"><div class="k">Product Status</div><div class="v">${escapeHtml(row.product_status)}</div></div>
          ${row.mattress_size ? `<div class="meta-cell"><div class="k">Mattress Size</div><div class="v">${escapeHtml(row.mattress_size)}</div></div>` : ''}
          <div class="meta-cell"><div class="k">Sales Channel</div><div class="v">${escapeHtml(row.sales_channel)}</div></div>
          ${row.component_skus && row.component_skus.length ? `<div class="meta-cell components"><div class="k">Component SKUs</div><div class="v">${row.component_skus.map(sku => `<button type="button" class="component-sku-link" data-component-jump="${escapeHtml(sku)}" onclick="jumpToComponentSku(event, '${escapeHtml(sku)}')">${escapeHtml(sku)}</button>`).join(' ')}</div></div>` : ''}
          <div class="meta-action-row">${renderAdditionalPhotoAction(row)}</div>
        </div>

        <div>
          <div class="top-slot-layout">
            <div class="lane-block compact">
              <div class="lane-title">Grid</div>
              <div class="slot-row tight">
                ${renderSlot(row.row_id, 'grid', 'SKU_grid', buckets.grid['SKU_grid'], 'SKU_grid', changedSet)}
              </div>
            </div>

            <div class="lane-block compact">
              <div class="lane-title">Special Slots</div>
              <div class="slot-row tight">
                ${renderSlot(row.row_id, 'special', 'SKU_dimension', buckets.special['SKU_dimension'], 'SKU_dimension', changedSet, 'special')}
                ${renderSlot(row.row_id, 'special', 'SKU_swatch', buckets.special['SKU_swatch'], 'SKU_swatch', changedSet, 'special')}
                ${renderSlot(row.row_id, 'special', 'SKU_square', buckets.special['SKU_square'], 'SKU_SQUARE', changedSet, 'special')}
                ${renderSlot(row.row_id, 'off_pattern', 'off_pattern', buckets.off_pattern.off_pattern, 'Off-pattern', changedSet, 'offpattern')}
                ${renderSlot(row.row_id, 'trash', 'trash', buckets.trash.trash, 'Trash', changedSet, 'trash')}
              </div>
            </div>

            <div class="lane-block compact">
              <div class="lane-title">Swatch Detail Images</div>
              <div class="slot-row tight swatch-detail-inline">
                ${swatchDetailSlots.map(slot => renderSlot(row.row_id, 'swatch_detail', slot, buckets.swatch_detail[slot] || [], slot, changedSet)).join('')}
              </div>
            </div>
          </div>

          <div class="lane-block">
            <div class="lane-title">Product Carousel Images</div>
            <div class="slot-row">
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
        <div class="photo-line">${escapeHtml((asset.width || 0) + 'x' + (asset.height || 0))}</div>
        <div class="photo-actions">
          <a href="${escapeHtml(asset.original || asset.transformBaseUrl || '#')}" target="_blank" rel="noopener">Open</a>
          <a href="#" onclick="downloadAsset(event, '${escapeHtml(asset.id || '')}', '${escapeHtml(asset.id || '')}', '${escapeHtml(asset.file_name || asset.name || 'asset')}')">Download</a>
        </div>
      </div>
      <div class="photo-skus">
        <button type="button" class="photo-skus-toggle" onclick="togglePhotoSkuDrawer('${escapeHtml(asset.id)}')">SKUs</button>
        <div class="photo-skus-body ${isOpen ? 'open' : ''}">
          ${asset.tags && asset.tags.length ? photoMatchingSkuButtons(asset) : '<div class="photo-line">No alphanumeric 9-character tags found.</div>'}
        </div>
      </div>
    </div>
  `;
}

function getPhotoById(photoId) {
  return (state.photography.items || []).find(x => x.id === photoId) || null;
}

function getVisiblePhotographyItems() {
  const all = state.photography.items || [];
  if (!state.photography.hideFpo) return all;
  return all.filter(x => !!x.is_final);
}

function setHideFpo(checked) {
  state.photography.hideFpo = !!checked;
  const visible = getVisiblePhotographyItems();
  if (state.photography.activeId && !visible.some(x => String(x.id) === String(state.photography.activeId))) {
    state.photography.activeId = '';
    state.photography.selectedIds = [];
    if (state.photography.previewUrl && state.photography.previewUrl.startsWith('blob:')) URL.revokeObjectURL(state.photography.previewUrl);
    state.photography.previewUrl = '';
  }
  renderPhotographyPanel();
}

function currentActivePhoto() {
  const id = state.photography.activeId || (state.photography.selectedIds || [])[0] || '';
  return getPhotoById(id);
}

function prepModeFromState() {
  return state.photography.prep.mode || 'crop_1688';
}

function activePhotoOffsetY(photoId) {
  const active = getPhotoById(photoId);
  if (!active) return 0;
  const overrides = state.photography.prep.offsetYOverrides || {};
  const mode = prepModeFromState();
  const outH = mode === 'crop_2200' ? 2200 : 1688;
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH || !mode.startsWith('crop_') || mode === 'crop_square') return 0;
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
  if (!srcW || !srcH || mode !== 'crop_square') return 0;
  const side = Math.min(srcW, srcH);
  const maxOff = Math.max(0, srcW - side);
  if (overrides[photoId] === undefined || overrides[photoId] === null) return Math.round(maxOff / 2);
  return Math.max(0, Math.min(maxOff, Number(overrides[photoId] || 0)));
}

function renderPhotoPrepDrawer() {
  const active = currentActivePhoto();
  if (!active) return '';
  const mode = prepModeFromState();
  const preview = state.photography.previewUrl
    ? `<div class="photo-prep-preview-drag" draggable="${state.mode === 'assets' ? 'true' : 'false'}" ondragstart="startPreparedPreviewDrag(event)" ondragend="endPreparedPreviewDrag(event)"><img src="${escapeHtml(state.photography.previewUrl)}" alt="Preview" draggable="false" /></div>`
    : `<div class="photo-empty">Preview loading...</div>`;
  return `
    <div class="photo-prep-drawer">
      <div class="photo-prep-top">
        <h4>Prep drawer</h4>
        <div class="photo-prep-actions">
          <button type="button" class="btn btn-secondary photo-mini-btn" onclick="clearPhotoSelection()">Clear selection</button>
          <button type="button" class="btn btn-primary photo-mini-btn" onclick="downloadPreparedPhotos(false)">Download modified image</button>
          ${state.mode === 'assets' && active.from_board ? `<button type="button" class="btn btn-secondary photo-mini-btn" onclick="addPreparedAsNewVersion()">Add as new version</button>` : ''}
        </div>
      </div>
      <div class="photo-prep-controls">
        <div class="photo-prep-toolbar">
          <div class="photo-prep-left">
            <div class="photo-prep-options">
              <label><input type="checkbox" ${state.photography.prep.flip ? 'checked' : ''} onchange="setPrepFlip(this.checked)" /> Flip horizontally</label>
              <label><input type="radio" name="prepMode" value="crop_1688" ${mode==='crop_1688'?'checked':''} onchange="setPrepMode(this.value)" /> Crop to 3000x1688</label>
              <label><input type="radio" name="prepMode" value="crop_2200" ${mode==='crop_2200'?'checked':''} onchange="setPrepMode(this.value)" /> Crop to 3000x2200</label>
              <label><input type="radio" name="prepMode" value="pad_lr_1688" ${mode==='pad_lr_1688'?'checked':''} onchange="setPrepMode(this.value)" /> 3000x1688 with white sides</label>
              <label><input type="radio" name="prepMode" value="pad_tb_2200" ${mode==='pad_tb_2200'?'checked':''} onchange="setPrepMode(this.value)" /> 3000x1688 with white top/bottom</label>
              <label><input type="radio" name="prepMode" value="crop_square" ${mode==='crop_square'?'checked':''} onchange="setPrepMode(this.value)" /> Crop to largest square</label>
            </div>
            ${(mode.startsWith('crop_') || mode === 'crop_square') ? `<div class="photo-prep-focusbox">
              ${mode === 'crop_square' ? `<div class="photo-focus-pad" aria-label="Square crop nudger">
                <button type="button" onclick="setCropToLeft()" title="Jump crop all the way left">&#8678;</button>
                <button type="button" onclick="nudgeCropX(-1)" title="Move crop left">&#11164;</button>
                <button type="button" onclick="nudgeCropX(1)" title="Move crop right">&#11166;</button>
                <button type="button" onclick="setCropToRight()" title="Jump crop all the way right">&#8680;</button>
              </div>
              <div class="photo-focus-meta">
                <span class="photo-prep-note">Use the left and right arrows to move the square crop box.</span>
                <span class="photo-prep-note">Jump buttons move it all the way left or right.</span>
                <span class="photo-prep-note">Click Add as new version to apply your modified image to this asset.</span>
              </div>` : `<div class="photo-focus-pad" aria-label="Crop nudger">
                <button type="button" onclick="setCropToTop()" title="Jump crop to top">&#8679;</button>
                <button type="button" onclick="nudgeCropY(-1)" title="Move crop up">&#8593;</button>
                <button type="button" onclick="nudgeCropY(1)" title="Move crop down">&#8595;</button>
                <button type="button" onclick="setCropToBottom()" title="Jump crop to bottom">&#8681;</button>
              </div>
              <div class="photo-focus-meta">
                <span class="photo-prep-note">Use the up and down arrows to move the crop box a little.</span>
                <span class="photo-prep-note">Jump buttons move it all the way to the top or bottom.</span>
                <span class="photo-prep-note">Click Add as new version to apply your modified image to this asset.</span>
              </div>` }
            </div>` : ''}
          </div>
        </div>
        <div class="photo-prep-preview-wrap">
          <div class="photo-prep-preview">${preview}</div>
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
  state.photography.prep = { flip: false, mode: 'crop_1688', offsetYOverrides: {}, offsetXOverrides: {} };
  renderPhotographyPanel();
  refreshPhotoPreview();
}

async function addPreparedAsNewVersion() {
  const active = currentActivePhoto();
  if (!active || !active.from_board) return;
  if (state.mode !== 'assets') {
    alert('Add as new version is only available in Update assets mode.');
    return;
  }
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
function setPrepMode(v) {
  state.photography.prep.mode = v || 'crop_1688';
  state.photography.prep.offsetYOverrides = state.photography.prep.offsetYOverrides || {};
  state.photography.prep.offsetXOverrides = state.photography.prep.offsetXOverrides || {};
  refreshPhotoPreview();
}
function cropStepYForActive() {
  const active = currentActivePhoto();
  if (!active) return 100;
  const mode = prepModeFromState();
  const outH = mode === 'crop_2200' ? 2200 : 1688;
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return 100;
  const scaledH = Math.round(srcH * (3000 / srcW));
  return Math.max(40, Math.round(Math.max(0, scaledH - outH) * 0.1) || 80);
}
function nudgeCropY(direction) {
  const active = currentActivePhoto();
  if (!active) return;
  const mode = prepModeFromState();
  if (!mode.startsWith('crop_')) return;
  const outH = mode === 'crop_2200' ? 2200 : 1688;
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return;
  const scaledH = Math.round(srcH * (3000 / srcW));
  const maxOff = Math.max(0, scaledH - outH);
  const current = activePhotoOffsetY(active.id);
  const next = Math.max(0, Math.min(maxOff, current + (Number(direction || 0) * cropStepYForActive())));
  state.photography.prep.offsetYOverrides[active.id] = next;
  refreshPhotoPreview();
}
function setCropToTop() { const active = currentActivePhoto(); if (!active) return; state.photography.prep.offsetYOverrides[active.id] = 0; refreshPhotoPreview(); }
function setCropToBottom() { const active = currentActivePhoto(); if (!active) return; const mode = prepModeFromState(); const outH = mode === 'crop_2200' ? 2200 : 1688; const srcW = Number(active.width || 0) || 0; const srcH = Number(active.height || 0) || 0; if (!srcW || !srcH) return; const scaledH = Math.round(srcH * (3000 / srcW)); state.photography.prep.offsetYOverrides[active.id] = Math.max(0, scaledH - outH); refreshPhotoPreview(); }
function cropStepXForActive() {
  const active = currentActivePhoto();
  if (!active) return 100;
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return 100;
  const side = Math.min(srcW, srcH);
  return Math.max(40, Math.round(Math.max(0, srcW - side) * 0.1) || 80);
}
function nudgeCropX(direction) {
  const active = currentActivePhoto();
  if (!active) return;
  if (prepModeFromState() !== 'crop_square') return;
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return;
  const side = Math.min(srcW, srcH);
  const maxOff = Math.max(0, srcW - side);
  const current = activePhotoOffsetX(active.id);
  const next = Math.max(0, Math.min(maxOff, current + (Number(direction || 0) * cropStepXForActive())));
  state.photography.prep.offsetXOverrides[active.id] = next;
  refreshPhotoPreview();
}
function setCropToLeft() {
  const active = currentActivePhoto();
  if (!active) return;
  state.photography.prep.offsetXOverrides[active.id] = 0;
  refreshPhotoPreview();
}
function setCropToRight() {
  const active = currentActivePhoto();
  if (!active) return;
  const srcW = Number(active.width || 0) || 0;
  const srcH = Number(active.height || 0) || 0;
  if (!srcW || !srcH) return;
  const side = Math.min(srcW, srcH);
  state.photography.prep.offsetXOverrides[active.id] = Math.max(0, srcW - side);
  refreshPhotoPreview();
}
function currentPreparedPreviewPayload() {
  const active = currentActivePhoto();
  if (!active) return null;
  return {
    media_id: active.id,
    prep_mode: prepModeFromState(),
    flip: !!state.photography.prep.flip,
    offset_y: activePhotoOffsetY(active.id),
    offset_x: activePhotoOffsetX(active.id),
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

  if (!photo.items.length) {
    sub.textContent = 'Reference panel for available product photography in the selected collection/color.';
    body.innerHTML = `<div class="photo-empty">Pull available product photography from a color header to load this panel.</div>`;
    return;
  }

  const visibleItems = getVisiblePhotographyItems();
  if (!visibleItems.length) {
    sub.textContent = `${photo.items.length} photography asset(s) for ${photo.color}.`;
    body.innerHTML = `<div class="photo-empty">All loaded photography is currently hidden by Hide FPO.</div>`;
    return;
  }

  const hiddenCount = Math.max(0, (photo.items || []).length - visibleItems.length);
  sub.textContent = hiddenCount ? `${visibleItems.length} photography asset(s) shown for ${photo.color}. ${hiddenCount} hidden by Hide FPO.` : `${visibleItems.length} photography asset(s) for ${photo.color}.`;
  const prepDrawer = renderPhotoPrepDrawer();
  body.innerHTML = `${prepDrawer || ''}<div class="photo-grid">${visibleItems.map(renderPhotoTile).join('')}</div>`;
  bindPhotographyDnD();
}

function togglePhotoSkuDrawer(assetId) {
  state.photoSkuOpen[assetId] = !state.photoSkuOpen[assetId];
  renderPhotographyPanel();
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
    state.photography.items = data.items || [];
    state.photography.color = data.color || color;
    state.photography.expanded = true;
    state.photography.activeSkuSet = [];
    state.photography.selectedIds = [];
    state.photography.activeId = '';
    state.photography.previewUrl = '';
    state.photography.prep = { flip: false, mode: 'crop_1688', offsetYOverrides: {}, offsetXOverrides: {} };
    state.photography.hideFpo = false;
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
  state.photography.prep = { flip: false, mode: 'crop_1688', offsetYOverrides: {}, offsetXOverrides: {} };
  state.additionalPhotoAvailabilityBySku = {};
  state.additionalPhotoCheckInFlight = {};
  renderPhotographyPanel();
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

function renderBoard() {
  const host = document.getElementById('boardHost');
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
  renderModeUI();
  renderNotifications();
  renderPhotographyPanel();
  host.innerHTML = (state.board.color_sections || []).map(section => {
    const visibleRows = (section.rows || []).filter(row => !(state.hideInactive && row.inactive));
    if (!visibleRows.length) return '';
    const collapsed = !!state.collapsedColors[section.color];
    const allInactive = (section.rows || []).length > 0 && (section.rows || []).every(r => r.inactive);
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
  renderSummary();
  updateQueuedStatus();
}


function computeMissingNotices() {
  if (!state.board) return [];

  let firstMissingGrid = null;
  let firstMissing100 = null;
  let firstMissingSwatch = null;
  let firstMissingDimension = null;
  let firstOffPattern = null;
  let firstDuplicateSlot = null;

  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      if ((row.product_status || '').toLowerCase() !== 'active') continue;

      const liveAssets = (row.assets || []).filter(a => !a.is_marked_for_deletion);
      const hasGrid = liveAssets.some(a => a.slot_key === 'SKU_grid' || (a.current_position || '').endsWith('_grid'));
      const has100 = liveAssets.some(a => a.slot_key === 'SKU_100' || (a.current_position || '').endsWith('_100'));
      const hasSwatch = liveAssets.some(a => a.slot_key === 'SKU_swatch' || (a.current_position || '').endsWith('_swatch'));
      const hasDimension = liveAssets.some(a => a.slot_key === 'SKU_dimension' || (a.current_position || '').endsWith('_dimension'));
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

      if (!hasGrid && !firstMissingGrid) firstMissingGrid = {rowId: row.row_id, color: section.color, slot: 'SKU_grid'};
      if (!has100 && !firstMissing100) firstMissing100 = {rowId: row.row_id, color: section.color, slot: 'SKU_100'};
      if (!hasSwatch && !firstMissingSwatch) firstMissingSwatch = {rowId: row.row_id, color: section.color, slot: 'SKU_swatch'};
      if (!hasDimension && !firstMissingDimension) firstMissingDimension = {rowId: row.row_id, color: section.color, slot: 'SKU_dimension'};
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
    }
  }

  const notices = [];
  if (firstMissingGrid) notices.push({id:'missing-grid', kind:'error', text:'Missing grid: Jump to the first active SKU missing a grid image.', rowId:firstMissingGrid.rowId, color:firstMissingGrid.color, slot:firstMissingGrid.slot});
  if (firstMissing100) notices.push({id:'missing-100', kind:'error', text:'Missing SKU_100: Jump to the first active SKU missing its SKU_100 image.', rowId:firstMissing100.rowId, color:firstMissing100.color, slot:firstMissing100.slot});
  if (firstMissingSwatch) notices.push({id:'missing-swatch', kind:'notice', text:'Missing swatch: Jump to the first active SKU missing a swatch asset.', rowId:firstMissingSwatch.rowId, color:firstMissingSwatch.color, slot:firstMissingSwatch.slot});
  if (firstMissingDimension) notices.push({id:'missing-dimension', kind:'notice', text:'Missing dimensions: Jump to the first active SKU missing a dimensions asset.', rowId:firstMissingDimension.rowId, color:firstMissingDimension.color, slot:firstMissingDimension.slot});
  if (firstOffPattern) notices.push({id:'off-pattern', kind:'notice', text:'Off-pattern assets found: Jump to the first active SKU with off-pattern assets.', rowId:firstOffPattern.rowId, color:firstOffPattern.color, slot:firstOffPattern.slot});
  if (firstDuplicateSlot) notices.push({id:'duplicate-slot', kind:'notice', text:'Duplicate-slot assets found: Jump to the first active SKU with multiple assets sharing a slot.', rowId:firstDuplicateSlot.rowId, color:firstDuplicateSlot.color, slot:firstDuplicateSlot.slot});
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

function renderNotifications() {
  const host = document.getElementById('boardNotifications');
  renderCollectionStatus();
  const notices = [
    ...computeMissingNotices(),
    ...((state.appNotices || []).slice().reverse())
  ];
  if (!notices.length) {
    host.innerHTML = `<div class="notifications-empty">No collection notifications.</div>`;
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
      if (state.loadedCollectionOptionId) {
        await launchCollection(state.loadedCollectionOptionId);
        state.assetModeDirty = false;
      }
    });
  });
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
    const offset = (collectionBar ? collectionBar.offsetHeight : 0) + 8;
    const y = rowEl.offsetTop - offset;
    if (boardMain) boardMain.scrollTo({ top: Math.max(0, y), behavior: 'smooth' });
    else window.scrollTo({ top: Math.max(0, y), behavior: 'smooth' });

    rowEl.classList.add('row-highlight');
    setTimeout(() => rowEl.classList.remove('row-highlight'), 5000);

    if (slotKey) {
      const slotEl = document.getElementById(`slot-${rowId}-${slotKey}`) || rowEl.querySelector(`.slot[data-slot="${slotKey}"]`);
      if (!slotEl) return false;
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

function undoPendingCopy(event, assetId, targetPos, sourceMediaId='', targetSku='') {
  event.preventDefault();
  event.stopPropagation();
  if (!confirm(`No longer copy this to ${targetPos}?`)) return;
  if (!state.board) return;
  let removed = false;
  for (const section of state.board.color_sections || []) {
    for (const row of section.rows || []) {
      row.assets = (row.assets || []).filter(a => {
        const sameId = String(a.id || '') === String(assetId || '');
        const samePendingCopy = Boolean(a.pending_upload) && String(a.pending_upload_kind || '') === 'copy';
        const samePos = String(a.current_position || '') === String(targetPos || '');
        const sameSku = !targetSku || String(a.sku || '') === String(targetSku || '');
        const sameSource = !sourceMediaId || String(a.copy_source_media_id || '') === String(sourceMediaId || '');
        const match = sameId || (samePendingCopy && samePos && sameSku && sameSource);
        if (match) removed = true;
        return !match;
      });
    }
  }
  if (removed) {
    state.summary = computeClientSummary();
    renderBoard();
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
  document.getElementById('toggleSummaryBtn').textContent = state.summaryOpen ? 'Collapse' : 'Expand';
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
        card.scrollIntoView({behavior: 'smooth', block: 'center'});
        card.animate([{transform:'scale(1)'},{transform:'scale(1.04)'},{transform:'scale(1)'}], {duration: 500});
      }
    });
  });
}

function addAppNotice(text, kind='success', html='') {
  const id = `notice-${Date.now()}-${Math.random().toString(36).slice(2,8)}`;
  state.appNotices = [{id, kind, text, html, dismissible:true}, ...(state.appNotices || [])].slice(0, 12);
  renderNotifications();
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
        try {
          const resp = await fetch('/api/prepared_drop_upload', {
            method:'POST',
            headers:{'Content-Type':'application/json'},
            body: JSON.stringify({
              row_id: rowId || '',
              target_lane: targetLane || '',
              target_slot: targetSlot || '',
              mode: state.mode,
              ...preparedPayload
            })
          });
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
  select.innerHTML = state.filteredCollections.map(c => `<option value="${escapeHtml(c.id)}">${escapeHtml(c.label)}</option>`).join('');
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
  const q = document.getElementById('collectionFilter').value.trim().toLowerCase();
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
  'Almost there...'
];

function startLaunchLoadingTicker() {
  stopLaunchLoadingTicker();
  const btn = document.getElementById('launchBtn');
  if (!btn) return;
  let idx = 0;
  btn.textContent = launchLoadingMessages[0];
  state.launchLoadingTicker = window.setInterval(() => {
    if (!btn.disabled) return;
    idx = (idx + 1) % launchLoadingMessages.length;
    btn.textContent = launchLoadingMessages[idx];
  }, 4500);
}

function stopLaunchLoadingTicker() {
  if (state.launchLoadingTicker) {
    clearInterval(state.launchLoadingTicker);
    state.launchLoadingTicker = null;
  }
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
      body: JSON.stringify({option_id: optionId, force_refresh: forceRefresh})
    });
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Load failed');
    state.board = data.board;
    state.summary = data.summary;
    state.collapsedColors = {};
    if (!silent) {
      state.appNotices = [];
      state.photography.items = [];
      state.photography.color = '';
      state.photoSkuOpen = {};
    }
    state.assetModeDirty = false;
    state.assetModeDirtyRows = {};
    renderBoard();
    updateStickyOffsets();
    closeIdleModal();
    if (scrollTopAfter) {
      const boardMain = document.getElementById('boardMain');
      if (boardMain) boardMain.scrollTop = 0;
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


async function waitThenPollForRefresh() {
  const token = Date.now();
  state.waitFlow.activeToken = token;
  const baseline = state.waitFlow.baselineFingerprint || boardFingerprint(state.board);
  setWaitOverlay(true, 'Waiting 30 seconds before checking for refreshed metadata...');
  await delay(30000);
  if (state.waitFlow.activeToken !== token) return false;

  let attempts = 0;
  const maxAttempts = 18; // about 90 seconds at 5-second intervals
  while (attempts < maxAttempts) {
    attempts += 1;
    setWaitOverlay(true, `Checking Bynder for refreshed metadata... Attempt ${attempts} of ${maxAttempts}.`);
    const result = await launchCollection(state.loadedCollectionOptionId, {
      silent: true,
      flashReload: true,
      scrollTopAfter: true,
    });
    if (state.waitFlow.activeToken !== token) return false;
    const current = boardFingerprint(state.board);
    if (current && current !== baseline) {
      setWaitOverlay(false, '');
      addAppNotice('Board refreshed from Bynder.', 'success');
      closeIdleModal();
      return true;
    }
    await delay(5000);
  }
  setWaitOverlay(false, '');
  addAppNotice('Updates went through, but refreshed metadata is still taking a while to show. Use Reload From Bynder again in a moment.', 'notice');
  return false;
}

async function discardChanges() {
  if (!state.board) return;
  if (!confirm('Discard all staged changes and go back to the last loaded version from Bynder?')) return;
  const btn = document.getElementById('discardBtn');
  btn.disabled = true;
  btn.textContent = 'Discarding...';
  try {
    const resp = await fetch('/api/discard', {method: 'POST'});
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Discard failed');
    state.board = data.board;
    state.summary = data.summary;
    state.collapsedColors = {};
    renderBoard();
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
  if (!skipConfirm && !confirm('Are you sure you want to commit these changes to Bynder?')) return false;
  const btn = document.getElementById('commitBtn');
  btn.disabled = true;
  btn.textContent = 'Updating...';
  try {
    state.waitFlow.baselineFingerprint = boardFingerprint(state.board);
    const resp = await fetch('/api/commit', {method: 'POST'});
    const data = await resp.json();
    if (!resp.ok) throw new Error(data.error || 'Commit failed');
    const c = data.commit;
    if (c.all_succeeded) {
      addAppNotice(`Beautiful. ${c.success_count} change(s) went through. Waiting a bit before reloading from Bynder. A log was saved to ${c.log_path}.`, 'success');
      await waitThenPollForRefresh();
      return true;
    } else {
      state.board = data.board;
      state.summary = data.summary;
      state.collapsedColors = {};
      renderBoard();
      const msg = `Some changes failed. ${c.success_count} succeeded and ${c.failure_count} failed. The board was not refreshed so you can keep working. A log was saved to ${c.log_path}.`;
      addAppNotice(msg, 'error');
      return false;
    }
  } catch (err) {
    alert(err.message || String(err));
    return false;
  } finally {
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

function bindStaticUI() {
  document.getElementById('collectionFilter').addEventListener('input', filterCollections);
  document.getElementById('launchBtn').addEventListener('click', () => launchCollection());
  document.getElementById('reloadBtn').addEventListener('click', () => launchCollection(state.loadedCollectionOptionId, {flashReload:true, scrollTopAfter:true}));
  document.getElementById('discardBtn').addEventListener('click', discardChanges);
  document.getElementById('commitBtn').addEventListener('click', () => commitChanges());
  document.querySelectorAll('input[name="appMode"]').forEach(el => {
    el.addEventListener('change', () => switchMode(el.value));
  });
  const hideInactiveToggle = document.getElementById('hideInactiveToggle');
  if (hideInactiveToggle) {
    hideInactiveToggle.addEventListener('change', () => {
      state.hideInactive = !!hideInactiveToggle.checked;
      renderBoard();
    });
  }
  document.getElementById('thumbSize').addEventListener('input', renderBoard);
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
    document.getElementById('toggleSummaryBtn').textContent = state.summaryOpen ? 'Collapse' : 'Expand';
    renderSummary();
  });

  document.getElementById('toggleLogBtn').addEventListener('click', () => {
    state.logOpen = !state.logOpen;
    document.getElementById('serverLog').style.display = state.logOpen ? 'block' : 'none';
    document.getElementById('toggleLogBtn').textContent = state.logOpen ? 'Collapse' : 'Expand';
    if (state.logOpen) startMessagePolling();
    else stopMessagePolling();
  });
  document.getElementById('idleDismissBtn').addEventListener('click', closeIdleModal);
  document.getElementById('idleKeepWorkingBtn').addEventListener('click', closeIdleModal);
  document.getElementById('idleReloadBtn').addEventListener('click', async () => {
    closeIdleModal();
    if (state.loadedCollectionOptionId) {
      await launchCollection(state.loadedCollectionOptionId, {flashReload:true, scrollTopAfter:true});
    }
  });
  document.getElementById('toggleNotesBtn').addEventListener('click', () => {
    state.notesOpen = !state.notesOpen;
    renderNotesPanel();
  });
}

bindStaticUI();
bindIdleActivityWatchers();
renderNotesPanel();
window.addEventListener('resize', updateStickyOffsets);
window.addEventListener('load', updateStickyOffsets);
loadCollections();
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
    open_browser_later()
    app.run(host=HOST, port=PORT, debug=False, threaded=True)
