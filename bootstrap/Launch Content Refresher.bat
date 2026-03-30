@echo off
setlocal

set SCRIPT_DIR=%~dp0

where python >nul 2>nul
if %errorlevel% neq 0 (
    echo Python was not found on this machine.
    echo Please install Python and then try again.
    pause
    exit /b 1
)

python "%SCRIPT_DIR%content_refresher_bootstrap.py"

if %errorlevel% neq 0 (
    echo.
    echo Content Refresher failed to launch.
    echo Please review the message above.
    pause
)