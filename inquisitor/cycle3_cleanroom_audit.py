from __future__ import annotations

"""Cycle 3B Final Isolated `/tmp` Clean-Room Gate & Dossier Completeness Audit (SPEC.md §5).

100% pure Python 3.9+ stdlib (`from __future__ import annotations`), zero `float`, zero `Fraction`,
zero `isinstance`, zero `ast.Div` (`/`), zero hardcoded host paths (`Path(__file__).resolve()`),
enforcing `signal.alarm(20)` per audit stage.

Executes:
1. Stage 1 (`workspace_ast_and_json_firewall`): Scans every `.py` and `artifacts/*.json` file in the
   workspace via `inquisitor.ast_scanner` (`0` external imports, `0` floats, `0` inner-loop `Fraction`,
   `0` `isinstance` bypasses, `0` hardcoded host paths, `0` SVGs).
2. Stage 2 (`tmp_cleanroom_isolated_verify_all`): Copies source code (`SPEC.md`, `verify_all.py`,
   `PROOF_DOSSIER_v1.md`, `failure_log_v1.md`, `architect/`, `formalist/`, `simulator/`, `inquisitor/`,
   strictly excluding `__pycache__` and all stale `artifacts/*.json`) into a fresh `tempfile.TemporaryDirectory`
   in `/tmp`, executes `/usr/bin/python3 -I verify_all.py` with a scrubbed environment (`< 30s` gate),
   verifies fresh `artifacts/theorem_ledger_v1.json` creation, 100% machine-checked certificate coverage,
   and `0` JSON float tokens inside `/tmp`, then cleans up `/tmp` completely.
3. Stage 3 (`dossier_and_ledger_completeness`): Verifies `PROOF_DOSSIER_v1.md`, `failure_log_v1.md`,
   `simulator/cycle_benchmarks.md`, and `artifacts/theorem_ledger_v1.json` (100% certificate coverage
   across Gate 0 + Tracks A, B, C, D, E and honest 3-valued epistemic tags).
"""

import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from typing import Any, Callable

WORKSPACE_ROOT = str(Path(__file__).resolve().parent.parent)
if WORKSPACE_ROOT not in sys.path:
    sys.path.insert(0, WORKSPACE_ROOT)

from inquisitor import ast_scanner, cycle2_adversarial_probes


class _CleanroomTimeoutError(RuntimeError):
    pass


def _alarm_handler(signum: int, frame: object) -> None:
    _ = (signum, frame)
    raise _CleanroomTimeoutError("Cycle 3B audit stage exceeded 20-second wall-clock timeout")


def _run_stage_with_alarm(name: str, fn: Callable[[], dict[str, Any]]) -> dict[str, Any]:
    prev = signal.signal(signal.SIGALRM, _alarm_handler)
    signal.alarm(20)
    t0_ns = time.perf_counter_ns()
    try:
        res = fn()
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, prev)
    elapsed_ms = (time.perf_counter_ns() - t0_ns) // 1_000_000
    out = dict(res)
    out["stage"] = name
    out["elapsed_ms"] = elapsed_ms
    return out


def _verify_100pct_ledger_certificates(ledger_path: str) -> dict[str, Any]:
    """Verify every claim in `theorem_ledger_v1.json` has a valid epistemic tag AND an explicit certificate object."""
    base_audit = cycle2_adversarial_probes.audit_epistemic_ledger(ledger_path)
    findings = list(base_audit["findings"])
    if not base_audit["present"]:
        findings.append({
            "severity": "CRITICAL",
            "rule": "MISSING_THEOREM_LEDGER",
            "detail": f"Expected ledger at {ledger_path}",
        })
        return {"status": "FAIL", "claim_count": 0, "certified_entries": 0, "findings": findings}

    with open(ledger_path, "r", encoding="utf-8") as fh:
        doc = json.load(fh)

    theorems = doc.get("theorems", []) if type(doc) is dict else []
    certified_entries = 0
    missing_cert_ids: list[str] = []
    for entry in theorems:
        if type(entry) is not dict:
            continue
        cid = str(entry.get("id", "<unknown>"))
        cert_obj = entry.get("certificate")
        if type(cert_obj) is dict and len(cert_obj) > 0:
            certified_entries += 1
        elif type(cert_obj) is list and len(cert_obj) > 0:
            certified_entries += 1
        else:
            missing_cert_ids.append(cid)

    if missing_cert_ids:
        findings.append({
            "severity": "HIGH",
            "rule": "INCOMPLETE_LEDGER_CERTIFICATE_COVERAGE",
            "detail": f"{len(missing_cert_ids)} ledger claim(s) lack explicit `certificate` objects: {missing_cert_ids}",
        })

    return {
        "status": "PASS" if len(findings) == 0 else "FAIL",
        "claim_count": len(theorems),
        "certified_entries": certified_entries,
        "missing_certificate_ids": missing_cert_ids,
        "tag_counts": doc.get("tag_counts", {}) if type(doc) is dict else {},
        "findings": findings,
    }


def _copy_clean_source_tree(src_root: str, dst_root: str) -> dict[str, int]:
    """Copy source files into isolated `dst_root`, excluding `__pycache__`, `.pyc`, and `artifacts/`."""
    copied_files = 0
    top_files = ("SPEC.md", "verify_all.py", "PROOF_DOSSIER_v1.md", "failure_log_v1.md")
    for fname in top_files:
        s_file = os.path.join(src_root, fname)
        if os.path.isfile(s_file):
            shutil.copy2(s_file, os.path.join(dst_root, fname))
            copied_files += 1

    pkg_dirs = ("architect", "formalist", "simulator", "inquisitor")
    for pkg in pkg_dirs:
        src_pkg = os.path.join(src_root, pkg)
        if not os.path.isdir(src_pkg):
            continue
        for dirpath, dirnames, filenames in os.walk(src_pkg):
            dirnames[:] = [
                d for d in dirnames if d not in ("__pycache__", ".pytest_cache", ".mypy_cache", ".git")
            ]
            rel_dir = os.path.relpath(dirpath, src_root)
            target_dir = os.path.join(dst_root, rel_dir)
            os.makedirs(target_dir, exist_ok=True)
            for fn in filenames:
                if fn.endswith((".pyc", ".pyo")) or fn == ".DS_Store":
                    continue
                shutil.copy2(os.path.join(dirpath, fn), os.path.join(target_dir, fn))
                copied_files += 1

    return {"copied_files": copied_files}


def run_tmp_cleanroom_gate(root_path: str = WORKSPACE_ROOT) -> dict[str, Any]:
    """Copy workspace code to `/tmp`, run `/usr/bin/python3 -I verify_all.py` in a scrubbed env, and verify fresh outputs."""
    findings: list[dict[str, str]] = []
    tmp_parent = "/tmp"
    with tempfile.TemporaryDirectory(dir=tmp_parent, prefix="itst_wave1_cleanroom_") as tmp_dir:
        copy_stats = _copy_clean_source_tree(root_path, tmp_dir)

        # Confirm `artifacts/` does NOT exist prior to clean-room execution!
        tmp_artifacts = os.path.join(tmp_dir, "artifacts")
        if os.path.exists(tmp_artifacts):
            raise AssertionError("Clean-room `/tmp` directory unexpectedly contained pre-existing `artifacts/`")

        scrubbed_env = {
            "PATH": "/usr/bin:/bin",
            "HOME": tmp_dir,
            "TMPDIR": tmp_dir,
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PYTHONDONTWRITEBYTECODE": "1",
        }

        t0_ns = time.perf_counter_ns()
        proc = subprocess.run(
            ["/usr/bin/python3", "-I", "verify_all.py"],
            cwd=tmp_dir,
            env=scrubbed_env,
            capture_output=True,
            text=True,
            timeout=29,
        )
        verify_elapsed_ms = (time.perf_counter_ns() - t0_ns) // 1_000_000

        if proc.returncode != 0:
            findings.append({
                "severity": "CRITICAL",
                "rule": "CLEANROOM_VERIFY_ALL_NONZERO_EXIT",
                "detail": f"`/usr/bin/python3 -I verify_all.py` in `/tmp` exited with {proc.returncode}: {proc.stderr[-600:]}",
            })

        if verify_elapsed_ms >= 30_000:
            findings.append({
                "severity": "CRITICAL",
                "rule": "CLEANROOM_RUNTIME_BUDGET_EXCEEDED",
                "detail": f"`verify_all.py` took {verify_elapsed_ms} ms >= 30,000 ms budget.",
            })

        tmp_ledger = os.path.join(tmp_artifacts, "theorem_ledger_v1.json")
        fresh_ledger_created = os.path.isfile(tmp_ledger)
        if not fresh_ledger_created:
            findings.append({
                "severity": "CRITICAL",
                "rule": "CLEANROOM_LEDGER_NOT_GENERATED",
                "detail": "`verify_all.py` did not generate fresh `artifacts/theorem_ledger_v1.json` in `/tmp`.",
            })
            ledger_check: dict[str, Any] = {"status": "FAIL", "claim_count": 0, "certified_entries": 0}
        else:
            ledger_check = _verify_100pct_ledger_certificates(tmp_ledger)
            findings.extend(ledger_check["findings"])

        tmp_ast = ast_scanner.scan_workspace(tmp_dir)
        if tmp_ast["status"] != "PASS":
            findings.append({
                "severity": "CRITICAL",
                "rule": "CLEANROOM_AST_OR_JSON_FLOAT_VIOLATION",
                "detail": f"Clean-room `/tmp` AST/JSON scan reported {tmp_ast['total_violations']} violation(s).",
            })

        stdout_lines = [ln.strip() for ln in proc.stdout.strip().splitlines() if ln.strip()]
        cleaned_dir_ref = os.path.basename(tmp_dir)

    # Confirm TemporaryDirectory removed `/tmp/itst_wave1_cleanroom_*` cleanly
    tmp_cleaned_up = not os.path.exists(os.path.join(tmp_parent, cleaned_dir_ref))
    if not tmp_cleaned_up:
        findings.append({
            "severity": "HIGH",
            "rule": "TMP_CLEANUP_INCOMPLETE",
            "detail": f"Temporary directory {cleaned_dir_ref} was not removed.",
        })

    return {
        "status": "PASS" if len(findings) == 0 else "FAIL",
        "copied_source_files": copy_stats["copied_files"],
        "isolated_python_cmd": "/usr/bin/python3 -I verify_all.py",
        "exit_code": proc.returncode,
        "verify_all_elapsed_ms": verify_elapsed_ms,
        "within_30s_budget": verify_elapsed_ms < 30_000,
        "fresh_ledger_generated": fresh_ledger_created,
        "ledger_claim_count": ledger_check["claim_count"],
        "ledger_certified_entries": ledger_check["certified_entries"],
        "tmp_directory_cleaned_up": tmp_cleaned_up,
        "stdout_tail": stdout_lines[-12:],
        "findings": findings,
    }


def audit_dossier_and_documents(root_path: str = WORKSPACE_ROOT) -> dict[str, Any]:
    """Verify presence, non-SVG purity, and section coverage of `PROOF_DOSSIER_v1.md`,
    `failure_log_v1.md`, `simulator/cycle_benchmarks.md`, and workspace `artifacts/theorem_ledger_v1.json`."""
    findings: list[dict[str, str]] = []
    required_docs = {
        "proof_dossier": "PROOF_DOSSIER_v1.md",
        "failure_log": "failure_log_v1.md",
        "simulator_benchmarks": os.path.join("simulator", "cycle_benchmarks.md"),
    }
    doc_stats: dict[str, Any] = {}
    svg_tok = "<" + "svg"

    for key, rel in required_docs.items():
        fpath = os.path.join(root_path, rel)
        exists = os.path.isfile(fpath)
        if not exists:
            doc_stats[key] = {"path": rel, "present": False, "size_bytes": 0}
            findings.append({
                "severity": "HIGH",
                "rule": "MISSING_REQUIRED_DOCUMENT",
                "detail": f"Required Wave I deliverable `{rel}` is not yet present.",
            })
            continue
        with open(fpath, "r", encoding="utf-8") as fh:
            text = fh.read()
        doc_stats[key] = {"path": rel, "present": True, "size_bytes": len(text.encode("utf-8"))}
        if len(text.strip()) < 200:
            findings.append({
                "severity": "HIGH",
                "rule": "TRUNCATED_DOCUMENT",
                "detail": f"Document `{rel}` is unexpectedly short ({len(text)} chars).",
            })
        if svg_tok in text.lower():
            findings.append({
                "severity": "CRITICAL",
                "rule": "WAVE1_SVG_IN_MARKDOWN",
                "detail": f"Document `{rel}` contains inline SVG markup (strictly deferred to Wave II per SPEC.md §0.3).",
            })

        if key == "proof_dossier":
            up = text.upper()
            required_markers = ("B1", "B2", "C1", "C2", "E0", "E1", "E2", "A1", "MAX_6", "A3", "D1", "D2", "D3", "WAVE II")
            missing_m = [m for m in required_markers if m not in up]
            doc_stats[key]["missing_markers"] = missing_m
            if missing_m:
                findings.append({
                    "severity": "HIGH",
                    "rule": "INCOMPLETE_PROOF_DOSSIER_COVERAGE",
                    "detail": f"`PROOF_DOSSIER_v1.md` is missing coverage markers: {missing_m}",
                })

    ws_ledger_path = os.path.join(root_path, "artifacts", "theorem_ledger_v1.json")
    ws_ledger_audit = _verify_100pct_ledger_certificates(ws_ledger_path)
    findings.extend(ws_ledger_audit["findings"])

    return {
        "status": "PASS" if len(findings) == 0 else "FAIL",
        "documents": doc_stats,
        "workspace_theorem_ledger": ws_ledger_audit,
        "findings": findings,
    }


def run_full_cycle3_cleanroom_audit(root_path: str = WORKSPACE_ROOT) -> dict[str, Any]:
    t0_ns = time.perf_counter_ns()

    def _stage1() -> dict[str, Any]:
        self_tests = ast_scanner.run_scanner_self_tests()
        ws_scan = ast_scanner.scan_workspace(root_path)
        return {
            "status": "PASS" if (self_tests["status"] == "PASS" and ws_scan["status"] == "PASS") else "FAIL",
            "self_tests": self_tests["passed_cases"],
            "scanned_python_files": ws_scan["scanned_python_files"],
            "total_violations": ws_scan["total_violations"],
            "total_advisories": ws_scan["total_advisories"],
            "violations": ws_scan["violations"],
            "advisories": ws_scan["advisories"],
        }

    st1 = _run_stage_with_alarm("stage1_workspace_ast_and_json_firewall", _stage1)
    st2 = _run_stage_with_alarm("stage2_tmp_cleanroom_isolated_verify_all", lambda: run_tmp_cleanroom_gate(root_path))
    st3 = _run_stage_with_alarm("stage3_dossier_and_ledger_completeness", lambda: audit_dossier_and_documents(root_path))

    total_ms = (time.perf_counter_ns() - t0_ns) // 1_000_000
    overall_ok = st1["status"] == "PASS" and st2["status"] == "PASS" and st3["status"] == "PASS"

    payload = {
        "cycle": "3B",
        "agent": "inquisitor",
        "overall_status": "PASS" if overall_ok else "FINDINGS_DETECTED",
        "total_elapsed_ms": total_ms,
        "stage1_ast_and_json_firewall": st1,
        "stage2_tmp_cleanroom_gate": st2,
        "stage3_dossier_and_ledger": st3,
    }

    out_path = os.path.join(root_path, "artifacts", "cycle3_inquisitor_cleanroom.json")
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2)

    json_float_errs = ast_scanner.scan_json_artifacts_for_floats(root_path)
    if json_float_errs:
        raise AssertionError(f"Float token detected in JSON artifacts after Cycle 3B flush: {json_float_errs}")

    return payload


def main() -> int:
    res = run_full_cycle3_cleanroom_audit(WORKSPACE_ROOT)
    print(
        json.dumps(
            {
                "overall_status": res["overall_status"],
                "total_elapsed_ms": res["total_elapsed_ms"],
                "ast_status": res["stage1_ast_and_json_firewall"]["status"],
                "scanned_python_files": res["stage1_ast_and_json_firewall"]["scanned_python_files"],
                "ast_violations": res["stage1_ast_and_json_firewall"]["total_violations"],
                "cleanroom_status": res["stage2_tmp_cleanroom_gate"]["status"],
                "cleanroom_verify_all_ms": res["stage2_tmp_cleanroom_gate"]["verify_all_elapsed_ms"],
                "dossier_and_ledger_status": res["stage3_dossier_and_ledger"]["status"],
            },
            indent=2,
        )
    )
    return 0 if res["overall_status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
