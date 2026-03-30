import json
import os
import shutil
import subprocess
import sys
import urllib.request
from pathlib import Path

REPO_OWNER = "nldehaven"
REPO_NAME = "rf-content-refresher"
BRANCH = "main"

RAW_BASE = f"https://raw.githubusercontent.com/{REPO_OWNER}/{REPO_NAME}/{BRANCH}"

APP_ROOT_NAME = "content_refresher_app"
CURRENT_DIR_NAME = "current"
PREVIOUS_DIR_NAME = "previous"
LOGS_DIR_NAME = "logs"
VENV_DIR_NAME = ".venv"
CONFIG_FILENAME = "config.json"

STABLE_FILES = [
    "content_refresher_app.py",
    "requirements.txt",
    "version.json",
]

def log(message: str) -> None:
    print(f"[Content Refresher Bootstrap] {message}")

def get_scripts_root() -> Path:
    return Path(__file__).resolve().parent

def get_app_root() -> Path:
    return get_scripts_root() / APP_ROOT_NAME

def get_current_dir() -> Path:
    return get_app_root() / CURRENT_DIR_NAME

def get_previous_dir() -> Path:
    return get_app_root() / PREVIOUS_DIR_NAME

def get_logs_dir() -> Path:
    return get_app_root() / LOGS_DIR_NAME

def get_venv_dir() -> Path:
    return get_app_root() / VENV_DIR_NAME

def get_config_path() -> Path:
    return get_app_root() / CONFIG_FILENAME

def ensure_dirs() -> None:
    get_app_root().mkdir(parents=True, exist_ok=True)
    get_current_dir().mkdir(parents=True, exist_ok=True)
    get_previous_dir().mkdir(parents=True, exist_ok=True)
    get_logs_dir().mkdir(parents=True, exist_ok=True)

def load_config() -> dict:
    path = get_config_path()
    if path.exists():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            pass
    return {}

def save_config(config: dict) -> None:
    get_config_path().write_text(json.dumps(config, indent=2), encoding="utf-8")

def find_credentials_files() -> list[Path]:
    scripts_root = get_scripts_root()
    return sorted(scripts_root.glob("byndercredentials_permanenttoken_*.json"))

def choose_credentials_file() -> Path:
    config = load_config()
    saved_path = config.get("credentials_path")
    if saved_path:
        saved = Path(saved_path)
        if saved.exists():
            return saved

    matches = find_credentials_files()
    if len(matches) == 1:
        chosen = matches[0]
        config["credentials_path"] = str(chosen)
        save_config(config)
        return chosen

    if not matches:
        raise FileNotFoundError(
            "No credentials file found. Put a file named like "
            "'byndercredentials_permanenttoken_EL.json' in your Scripts folder."
        )

    raise RuntimeError(
        "Multiple credentials files found. For now, keep only one credentials file in the Scripts folder."
    )

def download_text(url: str) -> str:
    with urllib.request.urlopen(url) as response:
        return response.read().decode("utf-8")

def download_file(url: str, destination: Path) -> None:
    with urllib.request.urlopen(url) as response:
        data = response.read()
    destination.write_bytes(data)

def get_remote_version() -> dict:
    url = f"{RAW_BASE}/stable/version.json"
    return json.loads(download_text(url))

def get_local_version() -> dict:
    path = get_current_dir() / "version.json"
    if path.exists():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            return {}
    return {}

def replace_current_with_download(download_dir: Path) -> None:
    current_dir = get_current_dir()
    previous_dir = get_previous_dir()

    if previous_dir.exists():
        shutil.rmtree(previous_dir)

    if current_dir.exists():
        shutil.move(str(current_dir), str(previous_dir))

    shutil.move(str(download_dir), str(current_dir))

def update_stable_files_if_needed() -> None:
    remote_version = get_remote_version()
    local_version = get_local_version()

    if remote_version.get("version") == local_version.get("version"):
        log(f"Already on latest stable version: {remote_version.get('version')}")
        return

    log(
        f"Updating Content Refresher from "
        f"{local_version.get('version', 'none')} to {remote_version.get('version')}"
    )

    temp_dir = get_app_root() / "_download_tmp"
    if temp_dir.exists():
        shutil.rmtree(temp_dir)
    temp_dir.mkdir(parents=True, exist_ok=True)

    for filename in STABLE_FILES:
        url = f"{RAW_BASE}/stable/{filename}"
        destination = temp_dir / filename
        log(f"Downloading {filename}")
        download_file(url, destination)

    replace_current_with_download(temp_dir)
    log("Stable files updated successfully.")

def get_venv_python() -> Path:
    if os.name == "nt":
        return get_venv_dir() / "Scripts" / "python.exe"
    return get_venv_dir() / "bin" / "python"

def ensure_venv() -> None:
    venv_python = get_venv_python()
    if venv_python.exists():
        return
    log("Creating virtual environment...")
    subprocess.run([sys.executable, "-m", "venv", str(get_venv_dir())], check=True)

def install_requirements() -> None:
    requirements = get_current_dir() / "requirements.txt"
    if not requirements.exists():
        raise FileNotFoundError("requirements.txt is missing from current app payload.")

    venv_python = get_venv_python()
    log("Installing/updating required Python modules...")
    subprocess.run(
        [str(venv_python), "-m", "pip", "install", "--upgrade", "pip"],
        check=True,
    )
    subprocess.run(
        [str(venv_python), "-m", "pip", "install", "-r", str(requirements)],
        check=True,
    )

def launch_app() -> None:
    app_script = get_current_dir() / "content_refresher_app.py"
    if not app_script.exists():
        raise FileNotFoundError("content_refresher_app.py is missing from current app payload.")

    credentials_path = choose_credentials_file()
    venv_python = get_venv_python()

    env = os.environ.copy()
    env["CONTENT_REFRESHER_CREDENTIALS_PATH"] = str(credentials_path)

    log(f"Launching app with credentials file: {credentials_path.name}")
    subprocess.Popen([str(venv_python), str(app_script)], env=env)

def main() -> None:
    ensure_dirs()
    update_stable_files_if_needed()
    ensure_venv()
    install_requirements()
    launch_app()

if __name__ == "__main__":
    main()