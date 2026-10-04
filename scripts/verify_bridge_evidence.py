"""Check the saved Azure evidence and exact source hashes; does not run Lean."""
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "evidence"
build = json.loads((EVIDENCE / "algorithm-bridge-build.json").read_text())
negative = json.loads((EVIDENCE / "algorithm-bridge-negative.json").read_text())
report = json.loads((EVIDENCE / "algorithm-bridge-audit.json").read_text())
cleanup = json.loads((EVIDENCE / "algorithm-bridge-cleanup.json").read_text())
expected_modules = {p.stem for p in (ROOT / "formal").glob("*.lean")}
assert len(expected_modules) == 11
assert build["status"] == "PASS"
assert {r["module"] for r in build["records"]} == expected_modules
assert len(build["records"]) == len(expected_modules)
assert all(r["exit_code"] == 0 for r in build["records"])
for p in (ROOT / "formal").glob("*.lean"):
    assert hashlib.sha256(p.read_bytes()).hexdigest() == build["source_sha256"][p.name], p.name
    assert not re.search(r"\b(sorry|admit|native_decide|unsafe|axiom)\b", p.read_text()), p.name
result_log = next(r["log"] for r in build["records"] if r["module"] == "Result")
assert result_log == (EVIDENCE / "algorithm-bridge-Result.log").read_text()
axioms = dict((name, terms.split(", ")) for name, terms in
              re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]", result_log))
assert len(axioms) == 24
for terms in axioms.values():
    assert set(terms) <= {"propext", "Classical.choice", "Quot.sound"}
assert axioms == report["target_axioms"]
assert negative["source_sha256"] == build["source_sha256"]
assert len(negative["records"]) == 1
control = negative["records"][0]
assert control["module"] == "InvalidControl" and control["exit_code"] == 1
assert "is false" in control["log"]
assert hashlib.sha256((EVIDENCE / "algorithm-bridge-InvalidControl.lean").read_bytes()).hexdigest() == negative["source_sha256"]["InvalidControl.lean"]
assert cleanup["all_deleted"] is True
assert report["worker_exit_code"] == 0
assert report["lean_build_passed"] and report["negative_control_rejected"]
print("PASS: 11 source hashes, 24 axiom lists, rejected control, Azure cleanup.")
print("This verifies recorded evidence integrity; it does not rebuild Lean.")
