#!/usr/bin/env bash
# Reproduce the library build, lessons, and selected-declaration axiom audit.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p work
./lakew build 2>&1 | tee work/build.log
python3 scripts/check_dependencies.py
./lakew env lean Learning.lean 2>&1 | tee work/lessons.log
./lakew env lean Check.lean 2>&1 | tee work/axioms-current.txt
python3 scripts/audit_axioms.py work/axioms-current.txt
python3 -m unittest discover -s tests -v
