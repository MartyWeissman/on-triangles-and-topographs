#!/usr/bin/env python3
"""Validate the named-declaration audit; this does not replace Lean's kernel."""
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED = {
    "ArithmeticTriangles.classification",
    "ArithmeticTriangles.initial_pair_arithmetic_iff",
    "ArithmeticTriangles.final_pair_arithmetic_iff",
    "ArithmeticTriangles.Triangle.not_arithmeticHyperbolic_of_scalene",
}


def validate(check_source, output):
    requested = re.findall(r"^#print axioms (\S+)\s*$", check_source, re.M)
    if not requested or len(requested) != len(set(requested)):
        raise ValueError("Audit requests are empty or duplicated")
    if not REQUIRED <= set(requested):
        raise ValueError("The audit omits a required classification theorem")
    if re.search(r"\berror:|\bsorryAx\b", output):
        raise ValueError("Lean reported an error or a proof placeholder")
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
    reports += [(name, "") for name in re.findall(
        r"'([^']+)' does not depend on any axioms", output)]
    names = [name for name, _ in reports]
    if len(names) != len(set(names)) or set(names) != set(requested):
        raise ValueError("Audit output is incomplete, duplicated, or unexpected")
    for name, axioms in reports:
        unexpected = {a.strip() for a in axioms.split(",") if a.strip()} - ALLOWED
        if unexpected:
            raise ValueError(f"Unexpected axioms for {name}: {sorted(unexpected)}")
    return len(requested)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    args = parser.parse_args()
    try:
        count = validate((ROOT / "Check.lean").read_text(), args.report.read_text())
    except (ValueError, OSError) as exc:
        parser.exit(1, f"Axiom audit failed: {exc}\n")
    print(f"PASS: all {count} requested declarations use only the allowed foundations.")


if __name__ == "__main__":
    main()
