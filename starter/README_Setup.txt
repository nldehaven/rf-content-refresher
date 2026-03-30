Content Refresher Setup

1. Put these files into your Scripts folder:
   - Launch Content Refresher.bat
   - content_refresher_bootstrap.py

2. Put your assigned Bynder credentials file into the same Scripts folder.
   The credentials file will be named like:
   byndercredentials_permanenttoken_EL.json

3. Double-click:
   Launch Content Refresher.bat

What happens on first launch:
- Content Refresher creates its local app folder
- installs any missing required Python modules
- downloads the latest approved stable app files from GitHub
- launches the app locally

If setup fails:
- make sure Python is installed
- make sure your credentials file is in the Scripts folder
- try launching again

Notes:
- The app runs locally on your machine
- Future approved updates are pulled automatically on launch