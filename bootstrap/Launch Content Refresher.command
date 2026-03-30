#!/bin/bash

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

if command -v python3 >/dev/null 2>&1; then
    PYTHON_CMD="python3"
elif command -v python >/dev/null 2>&1; then
    PYTHON_CMD="python"
else
    echo "Python was not found on this machine."
    echo "Please install Python and then try again."
    read -n 1 -s -r -p "Press any key to continue..."
    echo
    exit 1
fi

"$PYTHON_CMD" "$SCRIPT_DIR/content_refresher_bootstrap.py"

if [ $? -ne 0 ]; then
    echo
    echo "Content Refresher failed to launch."
    echo "Please review the message above."
    read -n 1 -s -r -p "Press any key to continue..."
    echo
fi