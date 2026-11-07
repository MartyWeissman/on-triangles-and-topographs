#!/usr/bin/env python3
"""Count first-party Lean sources without requiring development Git history."""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
library = [root / "ArithmeticTriangles.lean", *sorted((root / "ArithmeticTriangles").glob("*.lean"))]
lessons = [root / "Learning.lean", root / "Check.lean"]
print("# Source statistics\n")
print("Physical lines include comments and blank lines. Dependencies, generated files,\n"
      "documentation outside Lean files, and research archives are excluded. These\n"
      "counts measure source size, not mathematical novelty or difficulty.\n")
print("| Scope | Files | Lines |\n|---|---:|---:|")
for name, paths in [("Library", library), ("Lessons and audit", lessons), ("Total", library + lessons)]:
    print(f"| {name} | {len(paths)} | {sum(len(p.read_text().splitlines()) for p in paths)} |")
print("\nRegenerate with `python3 scripts/source_stats.py > docs/SourceStatistics.md`.\n")
print("| File | Lines |\n|---|---:|")
for path in library + lessons:
    name = path.relative_to(root)
    print(f"| [{name}](../{name}) | {len(path.read_text().splitlines())} |")
