"""Regression tests for rejecting incomplete or unsafe verification reports."""
import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("audit", ROOT / "scripts/audit_axioms.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AuditTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / "Check.lean").read_text()
        self.report = (ROOT / "verification/axioms.txt").read_text()

    def test_recorded_report(self):
        self.assertEqual(audit.validate(self.source, self.report), 238)

    def test_truncated_report_rejected(self):
        with self.assertRaises(ValueError):
            audit.validate(self.source, self.report[:len(self.report)//2])

    def test_extra_axiom_rejected(self):
        with self.assertRaises(ValueError):
            audit.validate(self.source, self.report.replace("propext", "untrustedAxiom", 1))

    def test_placeholder_rejected(self):
        with self.assertRaises(ValueError):
            audit.validate(self.source, self.report.replace("propext", "sorryAx", 1))

    def test_duplicate_report_rejected(self):
        with self.assertRaises(ValueError):
            audit.validate(self.source, self.report + self.report.splitlines()[0])

    def test_required_theorem_cannot_be_removed(self):
        name = "ArithmeticTriangles.classification"
        source = self.source.replace(f"#print axioms {name}\n", "")
        report = "\n".join(s for s in self.report.splitlines()
                           if not s.startswith(f"'{name}' "))
        with self.assertRaises(ValueError):
            audit.validate(source, report)

    def test_lean_error_rejected(self):
        with self.assertRaises(ValueError):
            audit.validate(self.source, self.report + "\nCheck.lean:1:1: error: failed\n")


if __name__ == "__main__":
    unittest.main()
