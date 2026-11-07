#!/usr/bin/env python3
"""Check that materialized Git dependencies match the committed lock file."""
import json
import re
import subprocess
from pathlib import Path

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / "lake-manifest.json").read_text())
for package in manifest["packages"]:
    revision = package["rev"]
    if package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise SystemExit(f"Unpinned dependency: {package['name']}")
    directory = root / manifest["packagesDir"] / package["name"]
    actual = subprocess.check_output(
        ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
    if actual != revision:
        raise SystemExit(f"Dependency revision mismatch: {package['name']}")
    dirty = subprocess.check_output(
        ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"],
        text=True).strip()
    if dirty:
        raise SystemExit(f"Tracked dependency sources have local changes: {package['name']}")
print(f"PASS: all {len(manifest['packages'])} dependency revisions match the lock file.")
