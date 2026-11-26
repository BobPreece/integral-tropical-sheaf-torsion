from __future__ import annotations

"""Wave II (v2.0) Final Dual-`/tmp` Clean-Room Sign-Off Harness (`SPEC_WAVE2.md` §3).

Constitutional Compliance:
- 100% Python 3.9+ stdlib only (`from __future__ import annotations`).
- Strictly ZERO `float`, ZERO `Fraction`, ZERO `ast.Div` (`/`), ZERO `isinstance`, ZERO hardcoded host paths.
- Hard subprocess timeouts (`< 45s` on `verify_all.py`, `< 25s` on `standalone_integral_sheaf_torsion.py`)
  and `signal.alarm(20)` on all in-process certificate, AST, SVG, and documentation verification stages.
- Guaranteed `finally: shutil.rmtree(...)` teardown of both `/tmp` sandboxes (`tmp_cleaned_up == True`).

Executes:
1. **Isolated Clean-Room Sandbox A (`/tmp/itst_wave2_ws_*`)**:
   - Copies full workspace (excluding `__pycache__`, `.pyc`, `.pyo`, `.DS_Store`, `.git`), removes pre-existing
     `theorem_ledger_v1.json` & `theorem_ledger_v2.json` inside `/tmp` to prove fresh regeneration, and runs
     `/usr/bin/python3 -I -B verify_all.py` with scrubbed environment (`< 45,000 ms` gate).
   - Audits the `/tmp` copy post-run via:
     * `inquisitor.ast_scanner.scan_workspace` (`0` violations across all `.py`, `svg_atlas_zero_float == True`,
       `0` float tokens across all `artifacts/*.json`),
     * `inquisitor.svg_auditor.audit_plots_directory` (`10/10` SVGs, `OOB == 0`, `overlaps == 0`, `xml_errors == 0`),
     * `formalist.cert_kernel.verify_ledger_certificate` (`21/21` in `theorem_ledger_v1.json` + `26/26` in
       `theorem_ledger_v2.json`) & `wave2_torture_tests.audit_wave2_epistemic_ledger`,
     * Documentation & Link Integrity Audit (when `require_v2_docs=True`): verifies `README.md`,
       `PROOF_DOSSIER_v2.md`, `failure_log_v2.md`, `PROOF_DOSSIER_v1.md`, `failure_log_v1.md`, all `10/10`
       `plots/fig01..fig10.svg` links in `README.md` resolving on disk, and honest `OPEN_BUDGET_EXCEEDED` prose.
2. **Isolated Clean-Room Sandbox B (`/tmp/itst_wave2_standalone_*`)**:
   - Copies **ONLY** `standalone_integral_sheaf_torsion.py` into an empty `/tmp` folder (`0` sibling files),
     executes `/usr/bin/python3 -I -B standalone_integral_sheaf_torsion.py` (`< 25,000 ms` gate), and certifies
     `exit_code == 0`, `0` disk files created (`Disk I/O == 0`), and deterministic verification of all `26/26`
     Wave I + Wave II claims (`24 CERTIFIED_EXACT`, `1 FALSIFIED_COUNTEREXAMPLE`, `1 OPEN_BUDGET_EXCEEDED`).
"""

import json
import os
from pathlib import Path
import re
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

from formalist import cert_kernel
from inquisitor import ast_scanner, svg_auditor, wave2_torture_tests

EXPECTED_26_CLAIM_IDS: tuple[str, ...] = (
    "TRAP_1",
    "TRAP_2",
    "TRAP_3",
    "TRAP_4",
    "TRAP_5",
    "TRAP_6",
    "TRAP_7",
    "B1",
    "B2",
    "C1",
    "C2",
    "E0",
    "E1",
    "E2",
    "A1",
    "A2_MAX6_Z_SIXTH_AND_SYL2_ENGINE",
    "A2_MAX6_Z_HALF_FRONTIER",
    "A3",
    "D1",
    "D2",
    "D3",
    "A2a",
    "A2_TIER123_3ADIC_OBSTRUCTION",
    "A2c",
    "D4a",
    "D4b",
)


class _Wave2CleanroomTimeout(RuntimeError):
    pass


def _alarm_handler(signum: int, frame: object) -> None:
    _ = (signum, frame)
    raise _Wave2CleanroomTimeout("Wave II clean-room inspection stage exceeded 20-second timeout")


def _run_inproc_with_alarm(name: str, fn: Callable[[], dict[str, Any]]) -> dict[str, Any]:
    prev = signal.signal(signal.SIGALRM, _alarm_handler)
    signal.alarm(20)
    t0_ns = time.perf_counter_ns()
    try:
        res = fn()
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, prev)
    out = dict(res)
    out["stage"] = name
    out["elapsed_ms"] = (time.perf_counter_ns() - t0_ns) // 1_000_000
    return out


def _copy_workspace_to_tmp(src_root: str, dst_root: str) -> dict[str, int]:
    """Copy entire workspace into `dst_root` excluding `__pycache__`, `.pyc`/`.pyo`, `.DS_Store`, and `.git`."""
    copied_files = 0
    excluded_dirs = {"__pycache__", ".git", ".pytest_cache", ".mypy_cache"}
    for dirpath, dirnames, filenames in os.walk(src_root):
        dirnames[:] = sorted(d for d in dirnames if d not in excluded_dirs)
        rel_dir = os.path.relpath(dirpath, src_root)
        target_dir = dst_root if rel_dir == "." else os.path.join(dst_root, rel_dir)
        os.makedirs(target_dir, exist_ok=True)
        for fn in sorted(filenames):
            if fn.endswith((".pyc", ".pyo")) or fn == ".DS_Store":
                continue
            shutil.copy2(os.path.join(dirpath, fn), os.path.join(target_dir, fn))
            copied_files += 1
    return {"copied_files": copied_files}


def _verify_both_ledgers_100pct(tmp_root: str) -> dict[str, Any]:
    """Verify `21/21` claims in `theorem_ledger_v1.json` and `26/26` claims in `theorem_ledger_v2.json` via `cert_kernel`."""
    findings: list[dict[str, str]] = []
    v1_path = os.path.join(tmp_root, "artifacts", "theorem_ledger_v1.json")
    v2_path = os.path.join(tmp_root, "artifacts", "theorem_ledger_v2.json")

    summary: dict[str, Any] = {}
    for label, l_path, exp_cnt in (("v1", v1_path, 21), ("v2", v2_path, 26)):
        if not os.path.isfile(l_path):
            findings.append({
                "severity": "CRITICAL",
                "rule": f"MISSING_LEDGER_{label.upper()}",
                "detail": f"Expected fresh ledger `{l_path}` in `/tmp`.",
            })
            summary[label] = {"present": False, "verified_count": 0}
            continue

        ep_audit = wave2_torture_tests.audit_wave2_epistemic_ledger(l_path)
        findings.extend(ep_audit["findings"])

        with open(l_path, "r", encoding="utf-8") as fh:
            doc = json.load(fh)
        theorems = doc.get("theorems", [])
        if len(theorems) != exp_cnt:
            findings.append({
                "severity": "CRITICAL",
                "rule": f"UNEXPECTED_CLAIM_COUNT_{label.upper()}",
                "detail": f"Expected {exp_cnt} claims in {label}, got {len(theorems)}.",
            })

        verified_ids: list[str] = []
        for entry in theorems:
            cid = str(entry.get("id", ""))
            tag = str(entry.get("epistemic_tag", ""))
            cert_obj = entry.get("certificate")
            res_c = cert_kernel.verify_ledger_certificate(cert_obj, claim_id=cid, epistemic_tag=tag)
            if not res_c.get("verified", False):
                findings.append({
                    "severity": "CRITICAL",
                    "rule": "CERT_KERNEL_VERIFICATION_FAILED",
                    "detail": f"Claim `{cid}` in `{label}` failed `cert_kernel.verify_ledger_certificate`.",
                })
            else:
                verified_ids.append(cid)

        if label == "v2":
            missing_ids = [cid for cid in EXPECTED_26_CLAIM_IDS if cid not in set(verified_ids)]
            if missing_ids:
                findings.append({
                    "severity": "CRITICAL",
                    "rule": "MISSING_EXPECTED_V2_CLAIM_IDS",
                    "detail": f"Missing expected v2 claim IDs: {missing_ids}",
                })

        summary[label] = {
            "present": True,
            "claim_count": len(theorems),
            "verified_count": len(verified_ids),
            "tag_counts": doc.get("tag_counts", {}),
        }

    return {
        "status": "PASS" if len(findings) == 0 else "FAIL",
        "ledgers": summary,
        "findings": findings,
    }


def audit_v2_documentation_and_links(root_dir: str) -> dict[str, Any]:
    """Verify Wave I + Wave II Markdown deliverables, `10/10` `plots/fig*.svg` links in `README.md`, and epistemic honesty."""
    findings: list[dict[str, str]] = []
    required_docs = (
        "README.md",
        "PROOF_DOSSIER_v2.md",
        "failure_log_v2.md",
        "PROOF_DOSSIER_v1.md",
        "failure_log_v1.md",
        "SPEC_WAVE2.md",
    )
    doc_sizes: dict[str, int] = {}
    doc_texts: dict[str, str] = {}

    for rel in required_docs:
        fp = os.path.join(root_dir, rel)
        if not os.path.isfile(fp):
            doc_sizes[rel] = 0
            findings.append({
                "severity": "CRITICAL",
                "rule": "MISSING_REQUIRED_V2_DOCUMENT",
                "detail": f"Required deliverable `{rel}` is missing.",
            })
            continue
        with open(fp, "r", encoding="utf-8") as fh:
            txt = fh.read()
        sz = len(txt.encode("utf-8"))
        doc_sizes[rel] = sz
        doc_texts[rel] = txt
        if sz < 500:
            findings.append({
                "severity": "HIGH",
                "rule": "TRUNCATED_V2_DOCUMENT",
                "detail": f"Document `{rel}` is unexpectedly short ({sz} bytes).",
            })

    # 1. Check `README.md`: all 10 `plots/fig01..fig10.svg` links + local Markdown link resolution + quickstart cmds
    resolved_plot_links = 0
    if "README.md" in doc_texts:
        readme_txt = doc_texts["README.md"]
        for fig_fn in svg_auditor.REQUIRED_ATLAS_FILENAMES:
            rel_fig = f"plots/{fig_fn}"
            full_fig = os.path.join(root_dir, "plots", fig_fn)
            if rel_fig not in readme_txt:
                findings.append({
                    "severity": "CRITICAL",
                    "rule": "README_MISSING_ATLAS_SVG_LINK",
                    "detail": f"`README.md` does not link `{rel_fig}`.",
                })
            elif os.path.isfile(full_fig):
                resolved_plot_links += 1
            else:
                findings.append({
                    "severity": "CRITICAL",
                    "rule": "README_BROKEN_ATLAS_SVG_LINK",
                    "detail": f"`README.md` links `{rel_fig}`, which does not exist on disk.",
                })

        # Also check all relative `](plots/...)` Markdown links inside `README.md` resolve on disk
        for m in re.finditer(r"\]\((plots/[^)#\s]+)\)", readme_txt):
            rel_target = m.group(1)
            if not os.path.isfile(os.path.join(root_dir, rel_target)):
                findings.append({
                    "severity": "HIGH",
                    "rule": "README_BROKEN_RELATIVE_PLOT_LINK",
                    "detail": f"Broken relative plot link in `README.md`: `{rel_target}`.",
                })

        for cmd_marker in ("verify_all.py", "standalone_integral_sheaf_torsion.py", "OPEN_BUDGET_EXCEEDED"):
            if cmd_marker not in readme_txt:
                findings.append({
                    "severity": "HIGH",
                    "rule": "README_MISSING_REQUIRED_MARKER",
                    "detail": f"`README.md` is missing required reference `{cmd_marker}`.",
                })

    # 2. Check `PROOF_DOSSIER_v2.md` coverage markers & epistemic honesty
    if "PROOF_DOSSIER_v2.md" in doc_texts:
        pd2_up = doc_texts["PROOF_DOSSIER_v2.md"].upper()
        for req_m in ("A2A", "A2C", "D4A", "D4B", "Q_8", "DIC_3", "MAX_6", "OPEN_BUDGET_EXCEEDED", "FALSIFIED_COUNTEREXAMPLE"):
            if req_m not in pd2_up:
                findings.append({
                    "severity": "HIGH",
                    "rule": "PROOF_DOSSIER_V2_MISSING_MARKER",
                    "detail": f"`PROOF_DOSSIER_v2.md` is missing coverage marker `{req_m}`.",
                })

    # 3. Guard against hardcoded `/Users/` host paths & false `A2_MAX6_Z_HALF_FRONTIER` table overclaims
    users_prefix = "/" + "Users/"
    for doc_name in ("README.md", "PROOF_DOSSIER_v2.md", "failure_log_v2.md"):
        if doc_name not in doc_texts:
            continue
        if users_prefix in doc_texts[doc_name]:
            findings.append({
                "severity": "HIGH",
                "rule": "DOC_HARDCODED_HOST_PATH",
                "detail": f"`{doc_name}` contains a hardcoded host user-home path `{users_prefix}...`.",
            })
        for line_idx, ln in enumerate(doc_texts[doc_name].splitlines(), start=1):
            ln_up = ln.upper()
            if "|" in ln_up and "A2_MAX6_Z_HALF_FRONTIER" in ln_up and "CERTIFIED_EXACT" in ln_up and "OPEN_BUDGET_EXCEEDED" not in ln_up:
                findings.append({
                    "severity": "CRITICAL",
                    "rule": "DOC_TABLE_EPISTEMIC_OVERCLAIM",
                    "detail": f"`{doc_name}:{line_idx}` tags `A2_MAX6_Z_HALF_FRONTIER` as `CERTIFIED_EXACT` instead of `OPEN_BUDGET_EXCEEDED`.",
                })

    return {
        "status": "PASS" if len(findings) == 0 else "FAIL",
        "doc_sizes_bytes": doc_sizes,
        "readme_atlas_links_resolved": resolved_plot_links,
        "findings": findings,
    }


def run_sandbox_a_full_workspace_cleanroom(
    src_root: str = WORKSPACE_ROOT,
    require_v2_docs: bool = True,
) -> dict[str, Any]:
    """Sandbox A: Copy full workspace to `/tmp/itst_wave2_ws_*`, run `/usr/bin/python3 -I -B verify_all.py`, and audit."""
    findings: list[dict[str, str]] = []
    tmp_ws_dir = tempfile.mkdtemp(prefix="itst_wave2_ws_", dir="/tmp")
    copy_stats = {"copied_files": 0}
    exit_code = -1
    verify_ms = 0
    ast_res: dict[str, Any] = {}
    svg_res: dict[str, Any] = {}
    ledger_res: dict[str, Any] = {}
    docs_res: dict[str, Any] = {"status": "SKIPPED_DRY_RUN"}
    stdout_tail: list[str] = []

    try:
        copy_stats = _copy_workspace_to_tmp(src_root, tmp_ws_dir)

        # Remove copied theorem ledgers BEFORE running `verify_all.py` so we prove 100% fresh regeneration in `/tmp`!
        for l_name in ("theorem_ledger_v1.json", "theorem_ledger_v2.json"):
            lp = os.path.join(tmp_ws_dir, "artifacts", l_name)
            if os.path.exists(lp):
                os.remove(lp)

        scrubbed_env = {
            "PATH": "/usr/bin:/bin",
            "HOME": tmp_ws_dir,
            "TMPDIR": tmp_ws_dir,
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PYTHONDONTWRITEBYTECODE": "1",
        }

        t0_ns = time.perf_counter_ns()
        proc = subprocess.run(
            ["/usr/bin/python3", "-I", "-B", "verify_all.py"],
            cwd=tmp_ws_dir,
            env=scrubbed_env,
            capture_output=True,
            text=True,
            timeout=45,
        )
        verify_ms = (time.perf_counter_ns() - t0_ns) // 1_000_000
        exit_code = proc.returncode
        stdout_tail = [ln.strip() for ln in proc.stdout.strip().splitlines() if ln.strip()][-18:]

        if exit_code != 0:
            findings.append({
                "severity": "CRITICAL",
                "rule": "SANDBOX_A_VERIFY_ALL_NONZERO_EXIT",
                "detail": f"`verify_all.py` in `/tmp` exited with {exit_code}: {proc.stderr[-600:]}",
            })
        if verify_ms >= 45_000:
            findings.append({
                "severity": "CRITICAL",
                "rule": "SANDBOX_A_BUDGET_EXCEEDED",
                "detail": f"`verify_all.py` took {verify_ms} ms >= 45,000 ms budget.",
            })

        def _post_checks() -> dict[str, Any]:
            ws_ast = ast_scanner.scan_workspace(tmp_ws_dir)
            j_floats = ast_scanner.scan_json_artifacts_for_floats(tmp_ws_dir)
            plots_r = svg_auditor.audit_plots_directory(os.path.join(tmp_ws_dir, "plots"), require_full_atlas=True)
            led_r = _verify_both_ledgers_100pct(tmp_ws_dir)
            d_r = audit_v2_documentation_and_links(tmp_ws_dir) if require_v2_docs else {"status": "SKIPPED_DRY_RUN", "findings": []}
            return {
                "ast": ws_ast,
                "json_floats": j_floats,
                "svg": plots_r,
                "ledgers": led_r,
                "docs": d_r,
            }

        post = _run_inproc_with_alarm("sandbox_a_post_verification_audits", _post_checks)
        ast_res = post["ast"]
        svg_res = post["svg"]
        ledger_res = post["ledgers"]
        docs_res = post["docs"]

        if ast_res["status"] != "PASS" or len(post["json_floats"]) > 0 or not ast_res.get("svg_atlas_zero_float", False):
            findings.append({
                "severity": "CRITICAL",
                "rule": "SANDBOX_A_AST_OR_FLOAT_VIOLATION",
                "detail": f"AST violations={ast_res['total_violations']}, json_floats={len(post['json_floats'])}, svg_atlas_zero_float={ast_res.get('svg_atlas_zero_float')}",
            })
        if svg_res["status"] != "PASS" or svg_res["svg_files_audited"] != 10 or svg_res["total_oob"] != 0 or svg_res["total_overlaps"] != 0:
            findings.append({
                "severity": "CRITICAL",
                "rule": "SANDBOX_A_SVG_GEOMETRY_VIOLATION",
                "detail": f"SVG audit failed in `/tmp`: status={svg_res['status']}, oob={svg_res['total_oob']}, overlaps={svg_res['total_overlaps']}",
            })
        findings.extend(ledger_res["findings"])
        if require_v2_docs:
            findings.extend(docs_res["findings"])
    finally:
        if os.path.exists(tmp_ws_dir):
            shutil.rmtree(tmp_ws_dir)

    tmp_cleaned = not os.path.exists(tmp_ws_dir)
    if not tmp_cleaned:
        findings.append({
            "severity": "HIGH",
            "rule": "SANDBOX_A_TMP_CLEANUP_FAILED",
            "detail": f"Failed to remove `{tmp_ws_dir}`.",
        })

    return {
        "sandbox": "A_full_workspace_tmp",
        "status": "PASS" if len(findings) == 0 else "FAIL",
        "copied_files": copy_stats["copied_files"],
        "cmd": "/usr/bin/python3 -I -B verify_all.py",
        "exit_code": exit_code,
        "verify_all_elapsed_ms": verify_ms,
        "within_45s_budget": verify_ms < 45_000,
        "scanned_python_files": ast_res.get("scanned_python_files", 0),
        "ast_violations": ast_res.get("total_violations", -1),
        "svg_atlas_zero_float": ast_res.get("svg_atlas_zero_float", False),
        "svg_files_audited": svg_res.get("svg_files_audited", 0),
        "svg_oob": svg_res.get("total_oob", -1),
        "svg_overlaps": svg_res.get("total_overlaps", -1),
        "ledgers": ledger_res.get("ledgers", {}),
        "documentation_audit": docs_res,
        "tmp_cleaned_up": tmp_cleaned,
        "stdout_tail": stdout_tail,
        "findings": findings,
    }


def run_sandbox_b_standalone_cleanroom(src_root: str = WORKSPACE_ROOT) -> dict[str, Any]:
    """Sandbox B: Copy ONLY `standalone_integral_sheaf_torsion.py` into empty `/tmp/itst_wave2_standalone_*` and run."""
    findings: list[dict[str, str]] = []
    sa_src = os.path.join(src_root, "standalone_integral_sheaf_torsion.py")
    if not os.path.isfile(sa_src):
        return {
            "sandbox": "B_standalone_only_tmp",
            "status": "FAIL",
            "findings": [{"severity": "CRITICAL", "rule": "MISSING_STANDALONE_BUNDLE", "detail": "standalone_integral_sheaf_torsion.py not found"}],
        }

    tmp_sa_dir = tempfile.mkdtemp(prefix="itst_wave2_standalone_", dir="/tmp")
    exit_code = -1
    elapsed_ms = 0
    zero_extra_files_after = False
    verified_claim_ids: list[str] = []
    stdout_tail: list[str] = []

    try:
        shutil.copy2(sa_src, os.path.join(tmp_sa_dir, "standalone_integral_sheaf_torsion.py"))
        entries_before = os.listdir(tmp_sa_dir)
        if entries_before != ["standalone_integral_sheaf_torsion.py"]:
            raise AssertionError(f"Sandbox B unexpectedly contained extra files before run: {entries_before}")

        scrubbed_env = {
            "PATH": "/usr/bin:/bin",
            "HOME": tmp_sa_dir,
            "TMPDIR": tmp_sa_dir,
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PYTHONDONTWRITEBYTECODE": "1",
        }

        t0_ns = time.perf_counter_ns()
        proc = subprocess.run(
            ["/usr/bin/python3", "-I", "-B", "standalone_integral_sheaf_torsion.py"],
            cwd=tmp_sa_dir,
            env=scrubbed_env,
            capture_output=True,
            text=True,
            timeout=25,
        )
        elapsed_ms = (time.perf_counter_ns() - t0_ns) // 1_000_000
        exit_code = proc.returncode
        out_text = proc.stdout
        stdout_tail = [ln.strip() for ln in out_text.strip().splitlines() if ln.strip()][-12:]

        entries_after = os.listdir(tmp_sa_dir)
        zero_extra_files_after = (entries_after == ["standalone_integral_sheaf_torsion.py"])
        if not zero_extra_files_after:
            findings.append({
                "severity": "HIGH",
                "rule": "STANDALONE_UNEXPECTED_DISK_WRITE",
                "detail": f"Standalone bundle wrote unexpected files in `/tmp`: {entries_after}",
            })

        if exit_code != 0:
            findings.append({
                "severity": "CRITICAL",
                "rule": "SANDBOX_B_STANDALONE_NONZERO_EXIT",
                "detail": f"Standalone bundle exited with {exit_code}: {proc.stderr[-600:]}",
            })
        if elapsed_ms >= 25_000:
            findings.append({
                "severity": "CRITICAL",
                "rule": "SANDBOX_B_BUDGET_EXCEEDED",
                "detail": f"Standalone bundle took {elapsed_ms} ms >= 25,000 ms budget.",
            })

        expected_banner = "[STANDALONE PASS] 26/26 Claims Verified (24 CERTIFIED_EXACT, 1 FALSIFIED_COUNTEREXAMPLE, 1 OPEN_BUDGET_EXCEEDED)"
        if expected_banner not in out_text:
            findings.append({
                "severity": "CRITICAL",
                "rule": "STANDALONE_BANNER_MISMATCH",
                "detail": f"Missing expected summary banner `{expected_banner}` in standalone stdout.",
            })

        for cid in EXPECTED_26_CLAIM_IDS:
            if re.search(rf"\b{re.escape(cid)}\b", out_text):
                verified_claim_ids.append(cid)
            else:
                findings.append({
                    "severity": "CRITICAL",
                    "rule": "STANDALONE_MISSING_CLAIM_ID",
                    "detail": f"Standalone output did not report expected claim ID `{cid}`.",
                })
    finally:
        if os.path.exists(tmp_sa_dir):
            shutil.rmtree(tmp_sa_dir)

    tmp_cleaned = not os.path.exists(tmp_sa_dir)
    if not tmp_cleaned:
        findings.append({
            "severity": "HIGH",
            "rule": "SANDBOX_B_TMP_CLEANUP_FAILED",
            "detail": f"Failed to remove `{tmp_sa_dir}`.",
        })

    return {
        "sandbox": "B_standalone_only_tmp",
        "status": "PASS" if len(findings) == 0 else "FAIL",
        "cmd": "/usr/bin/python3 -I -B standalone_integral_sheaf_torsion.py",
        "exit_code": exit_code,
        "standalone_elapsed_ms": elapsed_ms,
        "within_25s_budget": elapsed_ms < 25_000,
        "zero_sibling_files_verified": True,
        "zero_disk_writes_verified": zero_extra_files_after,
        "claims_verified_count": len(verified_claim_ids),
        "tmp_cleaned_up": tmp_cleaned,
        "stdout_tail": stdout_tail,
        "findings": findings,
    }


def run_wave2_dual_tmp_cleanroom_signoff(
    root_path: str = WORKSPACE_ROOT,
    require_v2_docs: bool = True,
    flush_artifact: bool = True,
) -> dict[str, Any]:
    """Execute full `SPEC_WAVE2.md` §3 dual-`/tmp` clean-room sign-off."""
    t0_ns = time.perf_counter_ns()
    sb_a = run_sandbox_a_full_workspace_cleanroom(root_path, require_v2_docs=require_v2_docs)
    sb_b = run_sandbox_b_standalone_cleanroom(root_path)

    ws_docs_live = (
        _run_inproc_with_alarm("live_workspace_v2_docs_check", lambda: audit_v2_documentation_and_links(root_path))
        if require_v2_docs
        else {"status": "SKIPPED_DRY_RUN", "findings": []}
    )
    ws_ast_live = _run_inproc_with_alarm("live_workspace_ast_and_json_firewall", lambda: ast_scanner.scan_workspace(root_path))

    overall_ok = (
        sb_a["status"] == "PASS"
        and sb_b["status"] == "PASS"
        and ws_ast_live["status"] == "PASS"
        and (not require_v2_docs or ws_docs_live["status"] == "PASS")
    )
    total_ms = (time.perf_counter_ns() - t0_ns) // 1_000_000

    payload: dict[str, Any] = {
        "wave": "2.0",
        "cycle": "3B" if require_v2_docs else "3A_DRY_RUN",
        "agent": "inquisitor",
        "overall_status": "CLEANROOM_CERTIFIED_PASS" if overall_ok else "FAIL",
        "require_v2_docs": require_v2_docs,
        "total_elapsed_ms": total_ms,
        "sandbox_a_full_workspace": sb_a,
        "sandbox_b_standalone_bundle": sb_b,
        "live_workspace_docs": ws_docs_live,
        "live_workspace_ast": {
            "status": ws_ast_live["status"],
            "scanned_python_files": ws_ast_live["scanned_python_files"],
            "total_violations": ws_ast_live["total_violations"],
            "total_advisories": ws_ast_live["total_advisories"],
            "svg_atlas_zero_float": ws_ast_live["svg_atlas_zero_float"],
        },
    }

    if flush_artifact:
        out_path = os.path.join(root_path, "artifacts", "wave2_cleanroom_signoff.json")
        os.makedirs(os.path.dirname(out_path), exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, sort_keys=True)
        float_errs = ast_scanner.scan_json_artifacts_for_floats(root_path)
        if float_errs:
            raise AssertionError(f"JSON float firewall triggered after clean-room sign-off flush: {float_errs}")

    return payload


def main(argv: list[str] | None = None) -> int:
    args = argv if argv is not None else sys.argv[1:]
    skip_docs = ("--skip-v2-docs" in args) or ("--dry-run" in args)
    no_flush = ("--no-flush" in args) or skip_docs
    res = run_wave2_dual_tmp_cleanroom_signoff(
        WORKSPACE_ROOT,
        require_v2_docs=not skip_docs,
        flush_artifact=not no_flush,
    )
    summary = {
        "overall_status": res["overall_status"],
        "mode": res["cycle"],
        "total_elapsed_ms": res["total_elapsed_ms"],
        "sandbox_a_status": res["sandbox_a_full_workspace"]["status"],
        "sandbox_a_verify_all_ms": res["sandbox_a_full_workspace"]["verify_all_elapsed_ms"],
        "sandbox_a_tmp_cleaned_up": res["sandbox_a_full_workspace"]["tmp_cleaned_up"],
        "sandbox_b_status": res["sandbox_b_standalone_bundle"]["status"],
        "sandbox_b_standalone_ms": res["sandbox_b_standalone_bundle"]["standalone_elapsed_ms"],
        "sandbox_b_claims_verified": res["sandbox_b_standalone_bundle"]["claims_verified_count"],
        "sandbox_b_tmp_cleaned_up": res["sandbox_b_standalone_bundle"]["tmp_cleaned_up"],
        "live_workspace_ast_status": res["live_workspace_ast"]["status"],
        "live_workspace_py_files": res["live_workspace_ast"]["scanned_python_files"],
        "live_docs_status": res["live_workspace_docs"]["status"],
    }
    print(json.dumps(summary, indent=2))
    if res["overall_status"] != "CLEANROOM_CERTIFIED_PASS":
        print(json.dumps({"sandbox_a_findings": res["sandbox_a_full_workspace"]["findings"], "sandbox_b_findings": res["sandbox_b_standalone_bundle"]["findings"], "docs_findings": res["live_workspace_docs"].get("findings", [])}, indent=2))
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
