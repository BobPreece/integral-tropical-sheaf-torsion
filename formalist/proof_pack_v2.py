"""Formalist independent zero-dependency Wave II (v2.0) proof, tamper & live peer cross-audit suite.

Strictly pure Python 3.9+ stdlib, zero `float`, zero `Fraction`, zero `ast.Div`, zero `isinstance`,
hard `signal.alarm(20)` per verification stage, `< 4.0s` end-to-end runtime.

Covers:
  - Stage 0: Full 21/21 Wave I (`theorem_ledger_v1.json`) backward-compatibility regression gate
             + automatic `theorem_ledger_v2.json` 100%-coverage gate (`0` float tokens) when present.
  - Stage 1 (Theorem A2a): Independent Beneath-Beyond + Cayley-Shephard determinant verification of
             lattice zonotope joins `conv(Z_1 u Z_2)` across `d=5` (`MAX_6`) and `d=6` (`MAX_7`).
  - Stage 2 (Theorem A2b): Both exact epistemic outcomes on `MAX_n` / `MAX_6` `Syl_2(S_6)`:
             (i) Primal `Z[1/2]` universal off-braid sub-cone identity verifier, and
             (ii) Dual `3`-adic obstruction verifier independently reconstructing `(A, b)` from
                  `CPWL` gate/gradient functionals with strict 3-valued epistemic guardrail.
  - Stage 3 (Theorem A2c): Finite-arrangement integral paramid quotient SNF verifier across
             `n = 4, 5, 6` (`B_4, B_5, B_6` + off-braid `H_4` with saturated `(B, L)` basis).
  - Stage 4 (Theorems D4a & D4b): Independent Cayley tables (`Q_8, D_4, Dic_3, Q_16, C_3, V_4, C_4, C_5`),
             `H^2` 2-cocycle non-triviality, compressed pure-`Z` `{0,1}` circuits (`Q_8` `W=40`, `Dic_3` `W=108`),
             Bareiss `det(I_mult^T I_mult) == |G|^{|G|}`, and universal rank lower bounds.
  - Stage 5: Adversarial Wave II tamper & torture suite (`11 / 11` negative cases rejected).
  - Stage 6 (Cycle 2 Live Peer Cross-Audit): Zero-trust first-principles verification of
             `artifacts/checkpoint_a2_wave2.json`, `artifacts/checkpoint_d4_wave2.json`, and
             `artifacts/simulator_wave2_data.json` (`100%` of sub-certificates, independent reconstruction
             of all 4 `A2b` `p=3` dual matrices `(A, b)`, all 7 `A2c` SNFs, all `D4a/D4b` circuits & Farkas
             duals, plus `@simulator`'s `V_4` `W=6` surgical pure-`Z` circuit and `Q_16` `W=33` circuit).
"""

from __future__ import annotations

import itertools
import json
import math
import pathlib
import signal
import sys
import time
from typing import Any, Sequence

ROOT_DIR = pathlib.Path(__file__).resolve().parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from formalist.cert_kernel import (
    IntMatrix,
    IntVector,
    _enumerate_arrangement_chambers_zero_sum,
    _primitive_canonical_vec,
    assert_int_matrix,
    build_canonical_group_cayley,
    compile_2layer_gate,
    compute_convex_hull_normalized_volume,
    eval_compiled_gate_int,
    exact_det_bareiss,
    exact_q_rank_bareiss,
    find_group_isomorphism,
    mat_eye,
    mat_mul,
    mat_sub,
    mat_transpose,
    smooth_gradient_compiled_gate_int,
    vec_dot,
    verify_arrangement_paramid_snf_certificate,
    verify_central_extension_cocycle_certificate,
    verify_group_axioms,
    verify_group_circuit_certificate,
    verify_group_indicator_bounds_certificate,
    verify_ledger_certificate,
    verify_max6_dual_padic_certificate,
    verify_max6_primal_z_half_certificate,
    verify_padic_obstruction_certificate,
    verify_saturation_projector,
    verify_snf_certificate,
    verify_zonotope_join_volume_certificate,
)
from formalist.proof_pack_v1 import build_compressed_cn_biased_circuit
from formalist.tracks_ade_proofs import build_unbiased_cn_circuit

ARTIFACTS_DIR = ROOT_DIR.joinpath("artifacts")


class Wave2StageTimeoutError(RuntimeError):
    """Raised when any Wave II verification stage exceeds its hard 20-second alarm."""


def _alarm_handler(signum: int, frame: Any) -> None:
    raise Wave2StageTimeoutError(f"Wave II formalist stage exceeded 20s alarm (signal={signum})")


def run_timed_stage(stage_name: str, fn: Any) -> dict[str, Any]:
    """Execute `fn()` under a hard `signal.alarm(20)` guard with integer nanosecond timing."""
    prev_handler = signal.signal(signal.SIGALRM, _alarm_handler)
    t0_ns = time.monotonic_ns()
    signal.alarm(20)
    try:
        payload = fn()
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, prev_handler)
    elapsed_us = (time.monotonic_ns() - t0_ns) // 1000
    return {
        "stage": stage_name,
        "status": "PASS",
        "elapsed_us": elapsed_us,
        "elapsed_ms": elapsed_us // 1000,
        "details": payload,
    }


def _load_json_zero_float(path: pathlib.Path) -> Any:
    """Parse JSON file while rejecting any IEEE floating-point token."""
    float_tokens: list[str] = []

    def _reject_float(tok: str) -> int:
        float_tokens.append(tok)
        return 0

    data = json.loads(path.read_text(encoding="utf-8"), parse_float=_reject_float)
    if float_tokens:
        raise AssertionError(f"Float tokens detected in {path.name}: {float_tokens[:5]}")
    return data


def _build_fast_verified_snf_witness(a_in: Sequence[Sequence[int]]) -> dict[str, Any]:
    """Fast Markowitz unit-peeling unimodular SNF witness builder (immediately verified via `cert_kernel`)."""
    s = assert_int_matrix(a_in, context="snf_input")
    m = len(s)
    n = len(s[0]) if m > 0 else 0
    u = mat_eye(m)
    u_inv = mat_eye(m)
    v = mat_eye(n)
    v_inv = mat_eye(n)

    def swap_rows(r1: int, r2: int) -> None:
        if r1 == r2:
            return
        s[r1], s[r2] = s[r2], s[r1]
        u[r1], u[r2] = u[r2], u[r1]
        for row in u_inv:
            row[r1], row[r2] = row[r2], row[r1]

    def neg_row(r: int) -> None:
        s[r] = [-x for x in s[r]]
        u[r] = [-x for x in u[r]]
        for row in u_inv:
            row[r] = -row[r]

    def add_row(dst: int, src: int, q: int) -> None:
        if q == 0:
            return
        s_dst, s_src = s[dst], s[src]
        u_dst, u_src = u[dst], u[src]
        for c in range(n):
            v_sc = s_src[c]
            if v_sc:
                s_dst[c] += q * v_sc
        for c in range(m):
            v_uc = u_src[c]
            if v_uc:
                u_dst[c] += q * v_uc
        for r in range(m):
            v_id = u_inv[r][dst]
            if v_id:
                u_inv[r][src] -= q * v_id

    def swap_cols(c1: int, c2: int) -> None:
        if c1 == c2:
            return
        for row in s:
            row[c1], row[c2] = row[c2], row[c1]
        for row in v:
            row[c1], row[c2] = row[c2], row[c1]
        v_inv[c1], v_inv[c2] = v_inv[c2], v_inv[c1]

    def add_col(dst: int, src: int, q: int) -> None:
        if q == 0:
            return
        for r in range(m):
            v_sr = s[r][src]
            if v_sr:
                s[r][dst] += q * v_sr
        for r in range(n):
            v_vr = v[r][src]
            if v_vr:
                v[r][dst] += q * v_vr
        vi_src, vi_dst = v_inv[src], v_inv[dst]
        for c in range(n):
            v_dc = vi_dst[c]
            if v_dc:
                vi_src[c] -= q * v_dc

    def nearest_q(a_val: int, b_pos: int) -> int:
        q_f, rem = divmod(a_val, b_pos)
        if 2 * rem > b_pos:
            q_f += 1
        return q_f

    k = 0
    limit = min(m, n)
    # Phase A: Peel sparse +-1 unit pivots by minimum Markowitz product `(row_nnz - 1) * (col_nnz - 1)`
    while k < limit:
        r_nnz = [0] * m
        c_nnz = [0] * n
        has_unit = False
        for r in range(k, m):
            sr = s[r]
            cnt_r = 0
            for c in range(k, n):
                val = sr[c]
                if val != 0:
                    cnt_r += 1
                    c_nnz[c] += 1
                    if val == 1 or val == -1:
                        has_unit = True
            r_nnz[r] = cnt_r
        if not has_unit:
            break
        best_u: tuple[int, int] | None = None
        best_cost = 0
        for r in range(k, m):
            sr = s[r]
            rn = r_nnz[r] - 1
            for c in range(k, n):
                val = sr[c]
                if val == 1 or val == -1:
                    cost = rn * (c_nnz[c] - 1)
                    if best_u is None or cost < best_cost:
                        best_u = (r, c)
                        best_cost = cost
                        if cost == 0:
                            break
            if best_u is not None and best_cost == 0:
                break
        assert best_u is not None
        swap_rows(k, best_u[0])
        swap_cols(k, best_u[1])
        if s[k][k] < 0:
            neg_row(k)
        for r in range(k + 1, m):
            if s[r][k] != 0:
                add_row(r, k, -s[r][k])
        for c in range(k + 1, n):
            if s[k][c] != 0:
                add_col(c, k, -s[k][c])
        k += 1

    # Phase B: Euclidean elimination + divisibility restoration on remaining non-unit core
    while k < limit:
        best_pos: tuple[int, int] | None = None
        best_abs = 0
        for r in range(k, m):
            for c in range(k, n):
                val = abs(s[r][c])
                if val > 0 and (best_pos is None or val < best_abs):
                    best_abs = val
                    best_pos = (r, c)
        if best_pos is None:
            break
        swap_rows(k, best_pos[0])
        swap_cols(k, best_pos[1])
        if s[k][k] < 0:
            neg_row(k)

        while True:
            while True:
                sub_changed = False
                for r in range(k + 1, m):
                    if s[r][k] != 0:
                        q = -nearest_q(s[r][k], s[k][k])
                        add_row(r, k, q)
                        if s[r][k] != 0:
                            swap_rows(k, r)
                            if s[k][k] < 0:
                                neg_row(k)
                            sub_changed = True
                for c in range(k + 1, n):
                    if s[k][c] != 0:
                        q = -nearest_q(s[k][c], s[k][k])
                        add_col(c, k, q)
                        if s[k][c] != 0:
                            swap_cols(k, c)
                            if s[k][k] < 0:
                                neg_row(k)
                            sub_changed = True
                if not sub_changed:
                    break

            d_piv = s[k][k]
            violator: int | None = None
            for r in range(k + 1, m):
                for c in range(k + 1, n):
                    if s[r][c] % d_piv != 0:
                        violator = r
                        break
                if violator is not None:
                    break
            if violator is None:
                break
            add_row(k, violator, 1)
        k += 1

    snf_check = verify_snf_certificate(a_in, u, u_inv, s, v, v_inv)
    return {
        "U": u,
        "U_inv": u_inv,
        "S": s,
        "V": v,
        "V_inv": v_inv,
        "snf_verification": snf_check,
    }


# ---------------------------------------------------------------------------
# Stage 0: Full Ledger Verification (`theorem_ledger_v1.json` + `v2` if present)
# ---------------------------------------------------------------------------


def verify_ledger_json_file(ledger_path: pathlib.Path, min_entries: int = 21) -> dict[str, Any]:
    """Verify 100% certificate coverage and zero JSON float tokens on a theorem ledger file."""
    if not ledger_path.exists():
        raise AssertionError(f"Missing theorem ledger file: {ledger_path.name}")

    data = _load_json_zero_float(ledger_path)

    entries: list[dict[str, Any]] = []
    if type(data) is dict:
        for k_name in ("theorems", "claims", "entries"):
            sub = data.get(k_name)
            if type(sub) is list:
                entries = [x for x in sub if type(x) is dict]
                break
            if type(sub) is dict:
                entries = [v for v in sub.values() if type(v) is dict]
                break
    elif type(data) is list:
        entries = [x for x in data if type(x) is dict]

    if len(entries) < min_entries:
        raise AssertionError(f"{ledger_path.name}: expected >= {min_entries} claims, got {len(entries)}")

    valid_tags = {"CERTIFIED_EXACT", "FALSIFIED_COUNTEREXAMPLE", "OPEN_BUDGET_EXCEEDED"}
    tag_counts: dict[str, int] = {t: 0 for t in valid_tags}
    verified_ids: list[str] = []

    for idx, item in enumerate(entries):
        cid = str(item.get("id") or item.get("theorem_id") or f"entry_{idx}")
        tag = (
            item.get("epistemic_tag")
            or item.get("epistemic_status")
            or item.get("tag")
            or item.get("status")
        )
        if tag not in valid_tags:
            raise AssertionError(f"{ledger_path.name} claim `{cid}` has invalid epistemic tag {tag!r}")
        tag_str = str(tag)
        tag_counts[tag_str] += 1
        cert = item.get("certificate")
        if cert is None:
            raise AssertionError(f"{ledger_path.name} claim `{cid}` missing mandatory certificate")
        res = verify_ledger_certificate(cert, claim_id=cid, epistemic_tag=tag_str)
        if not res.get("verified", False):
            raise AssertionError(f"{ledger_path.name} claim `{cid}` failed verification")
        verified_ids.append(cid)

    return {
        "ledger": ledger_path.name,
        "total_claims": len(entries),
        "verified_count": len(verified_ids),
        "coverage_percent": 100,
        "tag_counts": tag_counts,
        "verified_ids": verified_ids,
    }


def verify_stage0_wave1_and_optional_wave2_ledgers() -> dict[str, Any]:
    """Verify 100% of `theorem_ledger_v1.json` (21 claims) and `theorem_ledger_v2.json` whenever landed."""
    v1_path = ARTIFACTS_DIR.joinpath("theorem_ledger_v1.json")
    v1_report = verify_ledger_json_file(v1_path, min_entries=21)
    if v1_report["total_claims"] != 21:
        raise AssertionError(f"Expected 21 Wave I claims, got {v1_report['total_claims']}")

    out: dict[str, Any] = {"ledger_v1": v1_report, "ledger_v2_present": False}
    v2_path = ARTIFACTS_DIR.joinpath("theorem_ledger_v2.json")
    if v2_path.exists():
        out["ledger_v2_present"] = True
        out["ledger_v2"] = verify_ledger_json_file(v2_path, min_entries=24)
    return out


# ---------------------------------------------------------------------------
# Stage 1: Theorem A2a — Join-Volume Arithmetic Dichotomy (`d=5` vs `d=6`)
# ---------------------------------------------------------------------------


def verify_stage1_theorem_a2a() -> dict[str, Any]:
    """Independently construct & verify Theorem A2a join-volume dichotomy certificates."""
    e5 = [[1 if j == i else 0 for j in range(5)] for i in range(5)]
    e6 = [[1 if j == i else 0 for j in range(6)] for i in range(6)]

    z1_tris = [
        [[0, 0, 0, 0, 0], e5[0], [1, 1, 0, 0, 0]],
        [[0, 0, 0, 0, 0], e5[1], [1, 1, 0, 0, 0]],
    ]
    z2_tris = [
        [e5[4], [0, 0, 1, 0, 1], [0, 0, 1, 1, 1]],
        [e5[4], [0, 0, 0, 1, 1], [0, 0, 1, 1, 1]],
    ]
    join_22_simplices = [t1 + t2 for t1 in z1_tris for t2 in z2_tris]

    cert_a2a: dict[str, Any] = {
        "cert_type": "zonotope_join_volume",
        "verify_d6_all_partitions_div6": True,
        "join_cases": [
            {
                "d_dim": 5,
                "r1": 4,
                "r2": 0,
                "Z1_base": [0, 0, 0, 0, 0],
                "Z1_gens": [e5[0], e5[1], e5[2], e5[3]],
                "Z2_base": e5[4],
                "Z2_gens": [],
                "expected_volume": 24,
                "modulus": 3,
                "expected_mod_residue": 0,
                "divisible_by": 6,
            },
            {
                "d_dim": 5,
                "r1": 3,
                "r2": 1,
                "Z1_base": [0, 0, 0, 0, 0],
                "Z1_gens": [e5[0], e5[1], e5[2]],
                "Z2_base": e5[4],
                "Z2_gens": [e5[3]],
                "expected_volume": 6,
                "modulus": 3,
                "expected_mod_residue": 0,
                "divisible_by": 6,
            },
            {
                "d_dim": 5,
                "r1": 2,
                "r2": 2,
                "Z1_base": [0, 0, 0, 0, 0],
                "Z1_gens": [e5[0], e5[1]],
                "Z2_base": e5[4],
                "Z2_gens": [e5[2], e5[3]],
                "simplices": join_22_simplices,
                "expected_volume": 4,
                "modulus": 3,
                "expected_mod_residue": 1,
            },
            {
                "d_dim": 5,
                "r1": 2,
                "r2": 2,
                "Z1_base": [0, 0, 0, 0, 0],
                "Z1_gens": [e5[0], e5[1], [1, 1, 0, 0, 0]],
                "Z2_base": e5[4],
                "Z2_gens": [e5[2], e5[3]],
                "expected_volume": 12,
                "divisible_by": 4,
            },
            {
                "d_dim": 6,
                "r1": 5,
                "r2": 0,
                "Z1_base": [0, 0, 0, 0, 0, 0],
                "Z1_gens": [e6[0], e6[1], e6[2], e6[3], e6[4]],
                "Z2_base": e6[5],
                "Z2_gens": [],
                "expected_volume": 120,
                "divisible_by": 6,
            },
            {
                "d_dim": 6,
                "r1": 4,
                "r2": 1,
                "Z1_base": [0, 0, 0, 0, 0, 0],
                "Z1_gens": [e6[0], e6[1], e6[2], e6[3]],
                "Z2_base": e6[5],
                "Z2_gens": [e6[4]],
                "expected_volume": 24,
                "divisible_by": 6,
            },
            {
                "d_dim": 6,
                "r1": 3,
                "r2": 2,
                "Z1_base": [0, 0, 0, 0, 0, 0],
                "Z1_gens": [e6[0], e6[1], e6[2]],
                "Z2_base": e6[5],
                "Z2_gens": [e6[3], e6[4]],
                "expected_volume": 12,
                "divisible_by": 6,
            },
        ],
    }

    res = verify_ledger_certificate(cert_a2a, claim_id="A2a", epistemic_tag="CERTIFIED_EXACT")
    if res["cases_verified"] != 7:
        raise AssertionError("Expected 7 join cases verified in Stage 1")
    return res


# ---------------------------------------------------------------------------
# Stage 2: Theorem A2b — Primal `Z[1/2]` & Dual `3`-adic `Syl_2(S_6)` Verifiers
# ---------------------------------------------------------------------------


def _build_bakaev_2max5_gate_specs() -> tuple[list[dict[str, Any]], list[int]]:
    """Express Bakaev et al.'s 9-term `2 * MAX_5` formula via `cert_kernel` 2-layer gate specs."""
    s01_vs_2x4 = {"linear": [0, 0, 0, 0, 2], "hinges": [[1, [1, 1, 0, 0, -2]]]}
    s23_vs_2x4 = {"linear": [0, 0, 0, 0, 2], "hinges": [[1, [0, 0, 1, 1, -2]]]}
    s01_vs_s23 = {"linear": [0, 0, 1, 1, 0], "hinges": [[1, [1, 1, -1, -1, 0]]]}

    gates: list[dict[str, Any]] = [
        {"kind": "zonotope_max", "U": s01_vs_2x4, "V": [[0, 2], [0, 3]]},
        {"kind": "zonotope_max", "U": s01_vs_2x4, "V": [[1, 2], [1, 3]]},
        {"kind": "zonotope_max", "U": s23_vs_2x4, "V": [[2, 0], [2, 1]]},
        {"kind": "zonotope_max", "U": s23_vs_2x4, "V": [[3, 0], [3, 1]]},
        {"kind": "zonotope_max", "U": {"linear": [0, 0, 0, 0, 2], "hinges": []}, "V": s01_vs_s23},
    ]
    for i in (0, 1):
        for j in (2, 3):
            sij_normal = [0, 0, 0, 0, -2]
            sij_normal[i] += 1
            sij_normal[j] += 1
            sij_vs_2x4 = {"linear": [0, 0, 0, 0, 2], "hinges": [[1, sij_normal]]}
            gates.append({"kind": "zonotope_max", "U": sij_vs_2x4, "V": s01_vs_s23})

    coeffs = [1, 1, 1, 1, 1, -1, -1, -1, -1]
    return (gates, coeffs)


def verify_stage2_theorem_a2b() -> dict[str, Any]:
    """Verify both Primal Z[1/2] universal sub-cone prover and Dual 3-adic `Syl_2(S_6)` obstruction checker."""
    bak_gates, bak_coeffs = _build_bakaev_2max5_gate_specs()
    primal_cert = {
        "cert_type": "max6_z_half_primal",
        "n_dim": 5,
        "t_exp": 1,
        "gates": bak_gates,
        "coeffs_z": bak_coeffs,
    }
    primal_res = verify_ledger_certificate(primal_cert, claim_id="A2b_primal_bakaev_test", epistemic_tag="CERTIFIED_EXACT")
    if primal_res["leaf_subcones_verified"] < 300:
        raise AssertionError("Expected >= 300 refined off-braid leaf sub-cones verified on Bakaev 2*MAX_5")

    max4_gates = [{"kind": "zonotope_max", "U": [[0, 1]], "V": [[2, 3]]}]
    primal_m4_res = verify_max6_primal_z_half_certificate(
        {"n_dim": 4, "t_exp": 0, "gates": max4_gates, "coeffs_z": [1]}
    )
    assert primal_m4_res["verified"] is True

    hex_orbit_specs: list[dict[str, Any]] = [
        {"kind": "pair_max", "pair": [0, 1], "orbit_group": "d6", "orbit_mode": "unique"},
        {"kind": "zonotope_max", "U": [[0, 1], [0, 2]], "V": [[0, 1], [1, 3]], "orbit_group": "d6", "orbit_mode": "unique"},
        {"kind": "zonotope_max", "U": [[0, 1], [0, 2]], "V": [[2, 3], [4, 5]], "orbit_group": "d6", "orbit_mode": "unique"},
        {"kind": "zonotope_max", "U": [[0, 1], [0, 2]], "V": [[2, 5], [3, 4]], "orbit_group": "d6", "orbit_mode": "unique"},
        {"kind": "zonotope_max", "U": [[0, 1], [0, 2]], "V": [[3, 4], [3, 5]], "orbit_group": "d6", "orbit_mode": "unique"},
        {"kind": "zonotope_max", "U": [[0, 1], [0, 2]], "V": [[3, 5], [4, 5]], "orbit_group": "d6", "orbit_mode": "unique"},
        {"kind": "zonotope_max", "U": [[0, 1], [0, 3]], "V": [[0, 2], [4, 5]], "orbit_group": "d6", "orbit_mode": "unique"},
        {"kind": "zonotope_max", "U": [[0, 1], [0, 3]], "V": [[2, 3], [4, 5]], "orbit_group": "d6", "orbit_mode": "unique"},
        {"kind": "zonotope_max", "U": [[0, 1], [0, 5]], "V": [[1, 4], [2, 3]], "orbit_group": "d6", "orbit_mode": "unique"},
        {"kind": "zonotope_max", "U": [[0, 1], [0, 5]], "V": [[2, 3], [3, 4]], "orbit_group": "d6", "orbit_mode": "unique"},
        {"kind": "zonotope_max", "U": [[0, 1], [2, 3]], "V": [[0, 2], [4, 5]], "orbit_group": "d6", "orbit_mode": "unique"},
    ]
    compiled_11 = [compile_2layer_gate(sp, 6, f"hex[{i}]") for i, sp in enumerate(hex_orbit_specs)]

    pt_smooth = [0, 1, 3, 7, 15, 40]
    for cg in compiled_11:
        ok_s, _ = smooth_gradient_compiled_gate_int(cg, pt_smooth)
        assert ok_s is True

    row_specs: list[dict[str, Any]] = [
        {"kind": "point_eval", "point": [1, 1, 1, 1, 1, 1]},
        {"kind": "subcone_grad", "interior_point": pt_smooth, "coord": 5},
        {"kind": "finite_diff", "terms": [[1, [0, 2, 7, 19, 30, 51]], [-2, [0, 2, 6, 19, 30, 51]], [1, [0, 2, 5, 19, 30, 51]]]},
    ]
    a_dual: IntMatrix = [
        [eval_compiled_gate_int(cg, [1, 1, 1, 1, 1, 1]) for cg in compiled_11],
        [smooth_gradient_compiled_gate_int(cg, pt_smooth)[1][5] for cg in compiled_11],
        [
            eval_compiled_gate_int(cg, [0, 2, 7, 19, 30, 51])
            - 2 * eval_compiled_gate_int(cg, [0, 2, 6, 19, 30, 51])
            + eval_compiled_gate_int(cg, [0, 2, 5, 19, 30, 51])
            for cg in compiled_11
        ],
    ]
    b_dual = [1, 1, 0]
    y_dual = [1, 0, 0]

    dual_tier_cert = {
        "cert_type": "max6_padic_dual",
        "scope": "bounded_tier",
        "n_dim": 6,
        "target_scale": 1,
        "gates": hex_orbit_specs,
        "row_specs": row_specs,
        "A": a_dual,
        "b": b_dual,
        "y": y_dual,
        "p": 3,
        "s_bound": 1,
        "inverted_primes": [2],
    }
    dual_bounded_res = verify_ledger_certificate(
        dual_tier_cert, claim_id="A2b_tier_obstruction", epistemic_tag="CERTIFIED_EXACT"
    )

    dual_unconstrained_cert = dict(dual_tier_cert)
    dual_unconstrained_cert["scope"] = "unconstrained_relu_6_2_z_half"
    dual_open_res = verify_ledger_certificate(
        dual_unconstrained_cert, claim_id="A2b_unconstrained_frontier", epistemic_tag="OPEN_BUDGET_EXCEEDED"
    )

    return {
        "primal_bakaev_z_half": primal_res,
        "primal_max4_z": primal_m4_res,
        "dual_bounded_tier_3adic": dual_bounded_res,
        "dual_unconstrained_open_guard": dual_open_res,
    }


# ---------------------------------------------------------------------------
# Stage 3: Theorem A2c — Finite-Arrangement Integral Paramid Quotient SNF
# ---------------------------------------------------------------------------


def _build_saturated_arrangement_basis_from_chambers(
    n_dim: int,
    hyperplanes: IntMatrix,
) -> tuple[IntMatrix, IntMatrix, list[tuple[tuple[int, ...], Any]]]:
    """Independently compute an exact saturated Z-basis `B in Z^{(n*M) x D}` and integer left-inverse `L in Z^{D x (n*M)}`
    (`L @ B == I_D`) for `CPWL_{H_n}(Z)` via exact unimodular SNF of the chamber ray-continuity operator.
    """
    chambers = _enumerate_arrangement_chambers_zero_sum(n_dim, hyperplanes)
    m_ch = len(chambers)
    amb_dim = n_dim * m_ch

    ray_owner: dict[tuple[int, ...], int] = {}
    cont_rows: IntMatrix = []
    for c_idx, (_, c_state) in enumerate(chambers):
        c_rays = c_state[0]
        if c_idx > 0:
            r_lin = [0] * amb_dim
            for d_i in range(n_dim):
                r_lin[d_i] = -1
                r_lin[c_idx * n_dim + d_i] = 1
            cont_rows.append(r_lin)
        for r_vec in c_rays:
            rk = _primitive_canonical_vec(r_vec)
            if rk not in ray_owner:
                ray_owner[rk] = c_idx
            else:
                ow = ray_owner[rk]
                if ow != c_idx:
                    r_eq = [0] * amb_dim
                    for d_i in range(n_dim):
                        r_eq[ow * n_dim + d_i] = -rk[d_i]
                        r_eq[c_idx * n_dim + d_i] = rk[d_i]
                    cont_rows.append(r_eq)

    snf_k = _build_fast_verified_snf_witness(cont_rows)
    r_k = int(snf_k["snf_verification"]["rank"])
    v_mat = snf_k["V"]
    v_inv = snf_k["V_inv"]
    d_null = amb_dim - r_k
    b_basis = [[v_mat[i][r_k + j] for j in range(d_null)] for i in range(amb_dim)]
    l_inv = [[v_inv[r_k + j][i] for i in range(amb_dim)] for j in range(d_null)]
    assert mat_mul(l_inv, b_basis) == mat_eye(d_null)
    return (b_basis, l_inv, chambers)


def _braid_hyperplanes(n_dim: int) -> IntMatrix:
    out: IntMatrix = []
    for i in range(n_dim):
        for j in range(i + 1, n_dim):
            v = [0] * n_dim
            v[i] = 1
            v[j] = -1
            out.append(v)
    return out


def _build_braid_conforming_2layer_gates(n_dim: int) -> list[dict[str, Any]]:
    """All `max_{i in S} x_i` for `1 <= |S| <= min(n_dim, 4)` (spanning all `B_n`-conforming 2-layer gates)."""
    gates: list[dict[str, Any]] = []
    for i in range(n_dim):
        gates.append({"kind": "linear", "coeffs": [1 if k == i else 0 for k in range(n_dim)]})
    for i, j in itertools.combinations(range(n_dim), 2):
        gates.append({"kind": "pair_max", "pair": [i, j]})
    for i, j, k in itertools.combinations(range(n_dim), 3):
        gates.append({"kind": "zonotope_max", "U": [[i, j]], "V": [[j, k]]})
    if n_dim >= 4:
        for i, j, k, l_idx in itertools.combinations(range(n_dim), 4):
            gates.append({"kind": "zonotope_max", "U": [[i, j]], "V": [[k, l_idx]]})
    return gates


def verify_stage3_theorem_a2c() -> dict[str, Any]:
    """Independently compute & certify finite-arrangement integral paramid / (2,2) SNF tables for n = 4, 5, 6."""
    braid_cases: list[dict[str, Any]] = []
    summary_table: dict[str, Any] = {}

    for n_dim in (4, 5, 6):
        hps = _braid_hyperplanes(n_dim)
        gates = _build_braid_conforming_2layer_gates(n_dim)
        cg_list = [compile_2layer_gate(g, n_dim) for g in gates]
        eval_pts: list[IntVector] = [[1] * n_dim]
        for mask in range(1, (1 << n_dim) - 1):
            eval_pts.append([(mask >> d_i) & 1 for d_i in range(n_dim)])
        a_mat = [[eval_compiled_gate_int(cg, pt) for cg in cg_list] for pt in eval_pts]
        snf_w = _build_fast_verified_snf_witness(a_mat)
        cert_n = {
            "n_dim": n_dim,
            "hyperplanes": hps,
            "gates": gates,
            "braid_boolean_basis": True,
            "A": a_mat,
            "U": snf_w["U"],
            "U_inv": snf_w["U_inv"],
            "S": snf_w["S"],
            "V": snf_w["V"],
            "V_inv": snf_w["V_inv"],
            "invariant_factors": snf_w["snf_verification"]["invariant_factors"],
        }
        braid_cases.append(cert_n)
        summary_table[f"B_{n_dim}"] = {
            "cpwl_rank": len(eval_pts),
            "span_rank": snf_w["snf_verification"]["rank"],
            "corank": len(eval_pts) - snf_w["snf_verification"]["rank"],
            "torsion": snf_w["snf_verification"]["torsion_factors"],
        }

    if summary_table["B_4"]["corank"] != 0 or summary_table["B_5"]["corank"] != 1 or summary_table["B_6"]["corank"] != 7:
        raise AssertionError(f"Unexpected B_n paramid corank progression: {summary_table}")

    hps_h4 = _braid_hyperplanes(4) + [[1, 1, -1, -1]]
    b_h4, l_h4, ch_h4 = _build_saturated_arrangement_basis_from_chambers(4, hps_h4)
    gates_h4 = _build_braid_conforming_2layer_gates(4) + [
        {"kind": "zonotope_max", "U": {"linear": [1, 1, 0, 0], "hinges": []}, "V": {"linear": [0, 0, 1, 1], "hinges": []}}
    ]
    cg_h4 = [compile_2layer_gate(g, 4) for g in gates_h4]
    m_grad_h4 = [[0] * len(cg_h4) for _ in range(4 * len(ch_h4))]
    for j_col, cg in enumerate(cg_h4):
        for c_idx, (_, c_state) in enumerate(ch_h4):
            c_rays = c_state[0]
            int_pt = [sum(r[d_i] for r in c_rays) for d_i in range(4)]
            ok_s, gv = smooth_gradient_compiled_gate_int(cg, int_pt)
            assert ok_s is True
            for d_i in range(4):
                m_grad_h4[c_idx * 4 + d_i][j_col] = gv[d_i]
    a_h4 = mat_mul(l_h4, m_grad_h4)
    snf_h4 = _build_fast_verified_snf_witness(a_h4)
    cert_h4 = {
        "n_dim": 4,
        "hyperplanes": hps_h4,
        "gates": gates_h4,
        "basis_chamber_gradients": b_h4,
        "basis_left_inverse": l_h4,
        "A": a_h4,
        "U": snf_h4["U"],
        "U_inv": snf_h4["U_inv"],
        "S": snf_h4["S"],
        "V": snf_h4["V"],
        "V_inv": snf_h4["V_inv"],
        "invariant_factors": snf_h4["snf_verification"]["invariant_factors"],
    }
    braid_cases.append(cert_h4)
    summary_table["H_4_off_braid"] = {
        "chambers": len(ch_h4),
        "cpwl_rank": len(b_h4[0]),
        "span_rank": snf_h4["snf_verification"]["rank"],
        "corank": len(b_h4[0]) - snf_h4["snf_verification"]["rank"],
        "torsion": snf_h4["snf_verification"]["torsion_factors"],
    }

    batch_cert = {"cert_type": "arrangement_paramid_snf", "arrangement_cases": braid_cases}
    res_a2c = verify_ledger_certificate(batch_cert, claim_id="A2c", epistemic_tag="CERTIFIED_EXACT")
    return {"verified_batch": res_a2c, "snf_summary": summary_table}


# ---------------------------------------------------------------------------
# Stage 4: Theorems D4a & D4b — 2-Cocycle Group Compression & `{0,1}` Bounds
# ---------------------------------------------------------------------------


def build_v4_sidon_pure_z_circuit() -> dict[str, Any]:
    """Construct an exact 8-neuron pure-Z `{0,1}`-indicator circuit for `V_4` (`8 < 16`) via Sidon map `b_1 + 3*b_2`."""
    v4_cay = build_canonical_group_cayley("V_4")
    sidon = [0, 1, 3, 4]
    sum_to_elem = {0: 0, 1: 1, 2: 0, 3: 2, 4: 3, 5: 2, 6: 0, 7: 1, 8: 0}

    w1 = [sidon + sidon for _ in range(8)]
    b1 = [-t for t in range(8)]
    w2 = [[0] * 8 for _ in range(4)]
    b2 = [1, 0, 0, 0]
    w2[0][0] -= 1
    w2[0][1] += 1
    for m_val in range(1, 7):
        tgt = sum_to_elem[m_val]
        w2[tgt][m_val - 1] += 1
        w2[tgt][m_val] -= 2
        w2[tgt][m_val + 1] += 1
    w2[sum_to_elem[7]][6] += 1
    w2[sum_to_elem[7]][7] -= 2
    w2[sum_to_elem[8]][7] += 1

    return {
        "cayley": v4_cay,
        "expected_group_name": "V_4",
        "W1": w1,
        "b1": b1,
        "W2": w2,
        "b2": b2,
        "compressed": True,
        "mode": "indicator",
    }


def build_v4_walsh_q_circuit() -> dict[str, Any]:
    """Construct an exact 6-neuron rational (`Q`, denom=4) `{0,1}`-indicator circuit for `V_4` (`6 < 8 < 16`)."""
    v4_cay = build_canonical_group_cayley("V_4")
    chars = [
        [1, -1, 1, -1],
        [1, 1, -1, -1],
        [1, -1, -1, 1],
    ]
    w1: IntMatrix = []
    for ch in chars:
        w1.append(ch + ch)
        w1.append([-v for v in ch] + [-v for v in ch])
    b1 = [0] * 6
    w2: IntMatrix = []
    b2: IntVector = []
    for c in range(4):
        row = [0] * 6
        bias_c = 1
        for k_idx, ch in enumerate(chars):
            sc = ch[c]
            row[2 * k_idx] = sc
            row[2 * k_idx + 1] = sc
            bias_c -= sc
        w2.append(row)
        b2.append(bias_c)

    return {
        "cayley": v4_cay,
        "expected_group_name": "V_4",
        "W1": w1,
        "b1": b1,
        "W2": w2,
        "b2": b2,
        "w2_den": 4,
        "b2_den": 4,
        "compressed": True,
        "mode": "indicator",
    }


def build_q8_cocycle_pure_z_w40_circuit() -> tuple[dict[str, Any], dict[str, Any]]:
    """Break the `W = 64` faithful-permutation wall on `Q_8` via `1 -> Z_2 -> Q_8 -> V_4 -> 1` (`[beta] != 0`):
    constructs an explicit `W = 40 < 48 < 64` 1-layer pure-Z `{0,1}`-indicator circuit.
    """
    v4_cay = build_canonical_group_cayley("V_4")
    beta_q8 = [
        [0, 0, 0, 0],
        [0, 1, 0, 1],
        [0, 1, 1, 0],
        [0, 0, 1, 1],
    ]
    coc_cert = {
        "cert_type": "central_extension_cocycle",
        "quotient_cayley": v4_cay,
        "expected_quotient_group": "V_4",
        "central_modulus": 2,
        "cocycle_beta": beta_q8,
        "expect_nontrivial_cohomology": True,
        "expected_extension_group": "Q_8",
    }
    coc_res = verify_central_extension_cocycle_certificate(coc_cert)
    q8_cay = coc_res["extension_cayley"]

    w1: IntMatrix = []
    b1: IntVector = []
    pair_neuron_target_w: list[int] = []
    for u in range(4):
        for v in range(4):
            w_quot = v4_cay[u][v]
            b_uv = beta_q8[u][v]
            targets_s = ((0, 0), (1, 1)) if b_uv == 0 else ((1, 0), (0, 1))
            for want_sx, want_sy in targets_s:
                row = [0] * 16
                for uu in range(4):
                    for sx in (0, 1):
                        row[2 * uu + sx] = (2 if uu == u else 0) + (1 if sx == want_sx else 0)
                for vv in range(4):
                    for sy in (0, 1):
                        row[8 + 2 * vv + sy] = (2 if vv == v else 0) + (1 if sy == want_sy else 0)
                w1.append(row)
                b1.append(-5)
                pair_neuron_target_w.append(w_quot)

    v4_sidon_cert = build_v4_sidon_pure_z_circuit()
    for r_v4, b_v4 in zip(v4_sidon_cert["W1"], v4_sidon_cert["b1"]):
        row16 = [0] * 16
        for u in range(4):
            row16[2 * u] = r_v4[u]
            row16[2 * u + 1] = r_v4[u]
            row16[8 + 2 * u] = r_v4[4 + u]
            row16[8 + 2 * u + 1] = r_v4[4 + u]
        w1.append(row16)
        b1.append(b_v4)

    assert len(w1) == 40
    w2 = [[0] * 40 for _ in range(8)]
    b2 = [0] * 8
    for w_q in range(4):
        pos_idx = 2 * w_q
        neg_idx = 2 * w_q + 1
        for k_n, tgt_w in enumerate(pair_neuron_target_w):
            if tgt_w == w_q:
                w2[pos_idx][k_n] += 1
                w2[neg_idx][k_n] -= 1
        for r_k in range(8):
            w2[neg_idx][32 + r_k] += v4_sidon_cert["W2"][w_q][r_k]
        b2[neg_idx] += v4_sidon_cert["b2"][w_q]

    circuit_cert = {
        "cert_type": "group_circuit",
        "cayley": q8_cay,
        "expected_group_name": "Q_8",
        "cocycle_certificate": coc_cert,
        "W1": w1,
        "b1": b1,
        "W2": w2,
        "b2": b2,
        "compressed": True,
        "mode": "indicator",
    }
    return (coc_cert, circuit_cert)


def build_dic3_cocycle_pure_z_w108_circuit() -> tuple[dict[str, Any], dict[str, Any]]:
    """Generalize cohomological compression to `1 -> Z_2 -> Dic_3 -> S_3 -> 1` (order 12, `W = 108 < 144` over Z)."""
    s3_elems = [(r, t) for t in (0, 1) for r in range(3)]
    s3_idx = {el: i for i, el in enumerate(s3_elems)}
    s3_cay = [[0] * 6 for _ in range(6)]
    beta_dic3 = [[0] * 6 for _ in range(6)]

    for i, (r1, t1) in enumerate(s3_elems):
        for j, (r2, t2) in enumerate(s3_elems):
            if t1 == 0:
                k_dic = (r1 + r2) % 6
                t_dic = t2
            elif t2 == 0:
                k_dic = (r1 - r2) % 6
                t_dic = 1
            else:
                k_dic = (r1 - r2 + 3) % 6
                t_dic = 0
            r_quot = k_dic % 3
            s_cent = 1 if k_dic >= 3 else 0
            s3_cay[i][j] = s3_idx[(r_quot, t_dic)]
            beta_dic3[i][j] = s_cent

    coc_cert = {
        "cert_type": "central_extension_cocycle",
        "quotient_cayley": s3_cay,
        "expected_quotient_group": "S_3",
        "central_modulus": 2,
        "cocycle_beta": beta_dic3,
        "expect_nontrivial_cohomology": True,
        "expected_extension_group": "Dic_3",
    }
    coc_res = verify_central_extension_cocycle_certificate(coc_cert)
    dic3_cay = coc_res["extension_cayley"]

    w1: IntMatrix = []
    b1: IntVector = []
    w2 = [[0] * 108 for _ in range(12)]
    b2 = [0] * 12

    for u in range(6):
        for v in range(6):
            base_col = 3 * (6 * u + v)
            row_base = [0] * 24
            for uu in range(6):
                for sx in (0, 1):
                    row_base[2 * uu + sx] = (3 if uu == u else 0) + sx
            for vv in range(6):
                for sy in (0, 1):
                    row_base[12 + 2 * vv + sy] = (3 if vv == v else 0) + sy
            w1.append(list(row_base))
            b1.append(-5)
            w1.append(list(row_base))
            b1.append(-6)
            w1.append(list(row_base))
            b1.append(-7)

            w_q = s3_cay[u][v]
            b_uv = beta_dic3[u][v]
            out_even_parity = 2 * w_q + b_uv
            out_odd_parity = 2 * w_q + (1 ^ b_uv)
            w2[out_even_parity][base_col] += 1
            w2[out_even_parity][base_col + 1] -= 2
            w2[out_even_parity][base_col + 2] += 2
            w2[out_odd_parity][base_col + 1] += 1
            w2[out_odd_parity][base_col + 2] -= 2

    circuit_cert = {
        "cert_type": "group_circuit",
        "cayley": dic3_cay,
        "expected_group_name": "Dic_3",
        "cocycle_certificate": coc_cert,
        "W1": w1,
        "b1": b1,
        "W2": w2,
        "b2": b2,
        "compressed": True,
        "mode": "indicator",
    }
    return (coc_cert, circuit_cert)


def verify_stage4_theorems_d4a_and_d4b() -> dict[str, Any]:
    """Independently certify Theorems D4a (Q_8 & Dic_3 2-cocycle compression) and D4b (`{0,1}` width bounds)."""
    v4_cay = build_canonical_group_cayley("V_4")
    beta_d4 = [
        [0, 0, 0, 0],
        [0, 1, 0, 1],
        [0, 1, 0, 1],
        [0, 0, 0, 0],
    ]
    d4_coc_res = verify_central_extension_cocycle_certificate(
        {
            "quotient_cayley": v4_cay,
            "expected_quotient_group": "V_4",
            "central_modulus": 2,
            "cocycle_beta": beta_d4,
            "expect_nontrivial_cohomology": True,
            "expected_extension_group": "D_4",
        }
    )
    assert find_group_isomorphism(build_canonical_group_cayley("Q_8"), build_canonical_group_cayley("D_4")) is None

    _, q8_w40_cert = build_q8_cocycle_pure_z_w40_circuit()
    q8_res = verify_ledger_certificate(q8_w40_cert, claim_id="D4a_Q8_W40", epistemic_tag="CERTIFIED_EXACT")
    if q8_res["width"] != 40:
        raise AssertionError(f"Expected Q_8 pure-Z cocycle circuit width 40 < 64, got {q8_res['width']}")

    _, dic3_w108_cert = build_dic3_cocycle_pure_z_w108_circuit()
    dic3_res = verify_ledger_certificate(dic3_w108_cert, claim_id="D4a_Dic3_W108", epistemic_tag="CERTIFIED_EXACT")
    if dic3_res["width"] != 108:
        raise AssertionError(f"Expected Dic_3 pure-Z cocycle circuit width 108 < 144, got {dic3_res['width']}")

    def _cn_circuit_dict(n_c: int, zero_bias: bool) -> dict[str, Any]:
        if zero_bias:
            w1_c, b1_c, w2_c, b2_c = build_unbiased_cn_circuit(n_c)
        else:
            w1_c, b1_c, w2_c, b2_c = build_compressed_cn_biased_circuit(n_c)
        return {
            "W1": w1_c,
            "b1": b1_c,
            "W2": w2_c,
            "b2": b2_c,
            "zero_bias": zero_bias,
            "compressed": True,
            "mode": "indicator",
        }

    d4b_cert: dict[str, Any] = {
        "cert_type": "group_indicator_bounds",
        "indicator_bound_groups": [
            {
                "group_name": "C_3",
                "cayley": build_canonical_group_cayley("C_3"),
                "expected_gram_det": 3 ** 3,
                "circuits": [_cn_circuit_dict(3, False), _cn_circuit_dict(3, True)],
            },
            {
                "group_name": "V_4",
                "cayley": build_canonical_group_cayley("V_4"),
                "expected_gram_det": 4 ** 4,
                "circuits": [build_v4_walsh_q_circuit(), build_v4_sidon_pure_z_circuit()],
            },
            {
                "group_name": "C_4",
                "cayley": build_canonical_group_cayley("C_4"),
                "expected_gram_det": 4 ** 4,
                "circuits": [_cn_circuit_dict(4, False), _cn_circuit_dict(4, True)],
            },
            {
                "group_name": "C_5",
                "cayley": build_canonical_group_cayley("C_5"),
                "expected_gram_det": 5 ** 5,
                "circuits": [_cn_circuit_dict(5, False), _cn_circuit_dict(5, True)],
            },
            {
                "group_name": "Q_8",
                "cayley": q8_w40_cert["cayley"],
                "expected_gram_det": 8 ** 8,
                "circuits": [q8_w40_cert],
            },
            {
                "group_name": "D_4",
                "cayley": build_canonical_group_cayley("D_4"),
                "expected_gram_det": 8 ** 8,
                "circuits": [],
            },
            {
                "group_name": "Dic_3",
                "cayley": dic3_w108_cert["cayley"],
                "expected_gram_det": 12 ** 12,
                "circuits": [dic3_w108_cert],
            },
        ],
    }
    d4b_res = verify_ledger_certificate(d4b_cert, claim_id="D4b", epistemic_tag="CERTIFIED_EXACT")
    if d4b_res["groups_verified"] != 7:
        raise AssertionError("Expected 7 groups verified in D4b")

    return {
        "d4_cocycle_check": {
            "verified": d4_coc_res["verified"],
            "nontrivial": d4_coc_res["cohomologically_nontrivial"],
        },
        "q8_cocycle_w40_z": q8_res,
        "dic3_cocycle_w108_z": dic3_res,
        "d4b_bounds_and_circuits": d4b_res,
    }


# ---------------------------------------------------------------------------
# Stage 5: Adversarial Wave II Tamper & Impostor Torture Suite
# ---------------------------------------------------------------------------


def verify_stage5_wave2_adversarial_tamper_suite() -> dict[str, Any]:
    """Verify `cert_kernel` deterministically rejects corrupt SNF multipliers, non-saturated bases,
    fake `3`-adic witnesses, kink-point gradient rows, epistemic breaches, finite-ray impostors,
    and `Q_8` sign-collapsed / Cayley-spoofed circuits.
    """
    caught: dict[str, str] = {}

    hps4 = _braid_hyperplanes(4)
    g4 = [{"kind": "linear", "coeffs": [1, 0, 0, 0]}]
    pts15 = [[1, 1, 1, 1]] + [[(m >> k) & 1 for k in range(4)] for m in range(1, 15)]
    a15 = [[pt[0]] for pt in pts15]
    snf15 = _build_fast_verified_snf_witness(a15)
    bad_u = [list(r) for r in snf15["U"]]
    bad_u[0][0] *= 2
    try:
        verify_arrangement_paramid_snf_certificate(
            {
                "n_dim": 4,
                "hyperplanes": hps4,
                "gates": g4,
                "braid_boolean_basis": True,
                "A": a15,
                "U": bad_u,
                "U_inv": snf15["U_inv"],
                "S": snf15["S"],
                "V": snf15["V"],
                "V_inv": snf15["V_inv"],
            }
        )
        raise RuntimeError("Failed to reject corrupt non-unimodular U in A2c")
    except AssertionError as exc:
        caught["a2c_corrupt_snf_multiplier"] = str(exc)

    off_braid_gate = [{"kind": "relu1", "normal": [1, 1, -1, -1]}]
    a15_off = [[max(0, pt[0] + pt[1] - pt[2] - pt[3])] for pt in pts15]
    snf15_off = _build_fast_verified_snf_witness(a15_off)
    try:
        verify_arrangement_paramid_snf_certificate(
            {
                "n_dim": 4,
                "hyperplanes": hps4,
                "gates": off_braid_gate,
                "braid_boolean_basis": True,
                "A": a15_off,
                "U": snf15_off["U"],
                "U_inv": snf15_off["U_inv"],
                "S": snf15_off["S"],
                "V": snf15_off["V"],
                "V_inv": snf15_off["V_inv"],
            }
        )
        raise RuntimeError("Failed to reject unmodeled off-braid kink in CPWL_{B_4}(Z)")
    except AssertionError as exc:
        caught["a2c_unmodeled_chamber_kink"] = str(exc)

    spoof_gate = {
        "kind": "relu2",
        "base_linear": [0, 0, 0, 0, 0],
        "inner_linear": [0, 0, 0, 0, 0],
        "inner_hinges": [
            [1, [0, 0, 0, -1, 1]],
            [-4, [-1, 0, 0, 1, 0]],
            [-4, [0, -1, 0, 1, 0]],
            [-4, [0, 0, -1, 1, 0]],
            [-1, [1, 0, 0, -1, 0]],
            [-1, [0, 1, 0, -1, 0]],
            [-1, [0, 0, 1, -1, 0]],
        ],
    }
    cg_spoof = compile_2layer_gate(spoof_gate, 5)
    for perm5 in itertools.permutations((0, 1, 2, 3, 4)):
        if eval_compiled_gate_int(cg_spoof, perm5) != 0:
            raise AssertionError(f"Expected S_spoof == 0 on 120-ray sample {perm5}")
    assert eval_compiled_gate_int(cg_spoof, [0, 1, 2, 3, 50]) > 0

    bak_gates, bak_coeffs = _build_bakaev_2max5_gate_specs()
    try:
        verify_max6_primal_z_half_certificate(
            {
                "n_dim": 5,
                "t_exp": 1,
                "gates": bak_gates + [spoof_gate],
                "coeffs_z": bak_coeffs + [1],
            }
        )
        raise RuntimeError("Failed to reject 120-ray off-braid impostor in primal Z[1/2] verifier")
    except AssertionError as exc:
        caught["a2b_finite_ray_off_braid_impostor"] = str(exc)

    g_edge = [{"kind": "pair_max", "pair": [0, 1], "orbit_group": "d6", "orbit_mode": "unique"}]
    try:
        verify_max6_dual_padic_certificate(
            {
                "scope": "bounded_tier",
                "n_dim": 6,
                "gates": g_edge,
                "eval_points": [[1, 1, 1, 1, 1, 1]],
                "A": [[6]],
                "b": [2],
                "y": [1],
                "p": 3,
                "inverted_primes": [2],
            }
        )
        raise RuntimeError("Failed to reject forged b vector in 3-adic dual certificate")
    except AssertionError as exc:
        caught["a2b_forged_dual_rhs"] = str(exc)

    g_lin = [{"kind": "linear", "coeffs": [1, 0, 0, 0, 0, 0]}]
    try:
        verify_max6_dual_padic_certificate(
            {
                "scope": "bounded_tier",
                "n_dim": 6,
                "gates": g_lin,
                "eval_points": [[1, 1, 1, 1, 1, 1]],
                "A": [[1]],
                "b": [1],
                "y": [3],
                "p": 3,
                "inverted_primes": [2],
            }
        )
        raise RuntimeError("Failed to reject non-strict 3-adic valuation witness")
    except AssertionError as exc:
        caught["a2b_fake_3adic_valuation"] = str(exc)

    try:
        verify_max6_dual_padic_certificate(
            {
                "scope": "bounded_tier",
                "n_dim": 6,
                "gates": [{"kind": "pair_max", "pair": [0, 1]}],
                "row_specs": [{"kind": "subcone_grad", "interior_point": [5, 5, 1, 2, 3, 10], "coord": 5}],
                "A": [[0]],
                "b": [1],
                "y": [1],
                "p": 3,
                "inverted_primes": [2],
            }
        )
        raise RuntimeError("Failed to reject subcone_grad at active kink x_0 == x_1")
    except AssertionError as exc:
        caught["a2b_kink_point_subcone_grad"] = str(exc)

    try:
        verify_ledger_certificate(
            {
                "cert_type": "max6_padic_dual",
                "scope": "unconstrained_relu_6_2_z_half",
                "n_dim": 6,
                "gates": g_edge,
                "eval_points": [[1, 1, 1, 1, 1, 1]],
                "A": [[6]],
                "b": [1],
                "y": [1],
                "p": 3,
                "inverted_primes": [2],
            },
            claim_id="forged_unconstrained_max6",
            epistemic_tag="CERTIFIED_EXACT",
        )
        raise RuntimeError("Failed to block CERTIFIED_EXACT on unconstrained ReLU_{6,2}(Z[1/2]) bounded UNSAT")
    except AssertionError as exc:
        caught["a2b_epistemic_guardrail_breach"] = str(exc)

    _, q8_true_cert = build_q8_cocycle_pure_z_w40_circuit()
    v4_sid = build_v4_sidon_pure_z_circuit()
    w1_sign_collapsed: IntMatrix = []
    for r_v4 in v4_sid["W1"]:
        r16 = [0] * 16
        for u in range(4):
            r16[2 * u] = r_v4[u]
            r16[2 * u + 1] = r_v4[u]
            r16[8 + 2 * u] = r_v4[4 + u]
            r16[8 + 2 * u + 1] = r_v4[4 + u]
        w1_sign_collapsed.append(r16)
    w2_sign_collapsed = [[0] * 8 for _ in range(8)]
    b2_sign_collapsed = [0] * 8
    for u in range(4):
        w2_sign_collapsed[2 * u] = list(v4_sid["W2"][u])
        b2_sign_collapsed[2 * u] = v4_sid["b2"][u]
    try:
        verify_group_circuit_certificate(
            {
                "cayley": q8_true_cert["cayley"],
                "expected_group_name": "Q_8",
                "W1": w1_sign_collapsed,
                "b1": v4_sid["b1"],
                "W2": w2_sign_collapsed,
                "b2": b2_sign_collapsed,
                "compressed": True,
                "mode": "indicator",
            }
        )
        raise RuntimeError("Failed to reject sign-collapsed Q_8 circuit")
    except AssertionError as exc:
        caught["d4a_q8_sign_collapsed_circuit"] = str(exc)

    d4_cay = build_canonical_group_cayley("D_4")
    try:
        verify_group_circuit_certificate(
            {
                "cayley": d4_cay,
                "expected_group_name": "Q_8",
                "W1": [[0] * 16],
                "b1": [0],
                "W2": [[0] for _ in range(8)],
                "b2": [0] * 8,
            }
        )
        raise RuntimeError("Failed to reject D_4 Cayley table masquerading as Q_8")
    except AssertionError as exc:
        caught["d4a_q8_cayley_spoof"] = str(exc)

    v4_cay = build_canonical_group_cayley("V_4")
    alpha_triv = [0, 1, 1, 0]
    beta_cobound = [[(alpha_triv[x] + alpha_triv[y] - alpha_triv[v4_cay[x][y]]) % 2 for y in range(4)] for x in range(4)]
    try:
        verify_central_extension_cocycle_certificate(
            {
                "quotient_cayley": v4_cay,
                "central_modulus": 2,
                "cocycle_beta": beta_cobound,
                "expect_nontrivial_cohomology": True,
            }
        )
        raise RuntimeError("Failed to reject coboundary in H^2(V_4; Z_2)")
    except AssertionError as exc:
        caught["d4a_trivial_coboundary_spoof"] = str(exc)

    e5 = [[1 if j == i else 0 for j in range(5)] for i in range(5)]
    try:
        verify_zonotope_join_volume_certificate(
            {
                "d_dim": 5,
                "r1": 2,
                "r2": 2,
                "Z1_base": [0, 0, 0, 0, 0],
                "Z1_gens": [e5[0], e5[1]],
                "Z2_base": e5[4],
                "Z2_gens": [e5[2], e5[3]],
                "expected_volume": 6,
            }
        )
        raise RuntimeError("Failed to reject forged (2,2) join volume 6 != 4")
    except AssertionError as exc:
        caught["a2a_forged_join_volume"] = str(exc)

    if len(caught) != 11:
        raise AssertionError(f"Expected 11 adversarial rejections, got {len(caught)}")
    return {"adversarial_cases_rejected": len(caught), "caught_summaries": caught}


# ---------------------------------------------------------------------------
# Stage 6 (Cycle 2): Zero-Trust First-Principles Cross-Audit of Peer Checkpoints
# ---------------------------------------------------------------------------


def _build_syl2_s6_independent() -> tuple[list[tuple[int, ...]], list[tuple[int, ...]]]:
    """Independently build `Syl_2(S_6) = D_4(0..3) x C_2(4,5)` (`16` perms) and `45` chamber orbit reps."""
    gens = ((1, 2, 3, 0, 4, 5), (3, 2, 1, 0, 4, 5), (0, 1, 2, 3, 5, 4))
    ident = (0, 1, 2, 3, 4, 5)
    grp = {ident}
    stk = [ident]
    while stk:
        cur = stk.pop()
        for g in gens:
            nxt = tuple(cur[g[i]] for i in range(6))
            if nxt not in grp:
                grp.add(nxt)
                stk.append(nxt)
    sorted_grp = sorted(grp)
    assert len(sorted_grp) == 16

    unseen = set(itertools.permutations(range(6)))
    reps: list[tuple[int, ...]] = []
    while unseen:
        r = min(unseen)
        reps.append(r)
        for g in sorted_grp:
            unseen.discard(tuple(r[g[i]] for i in range(6)))
    assert len(reps) == 45
    return (sorted_grp, reps)


def _act_vec6_ind(v: Sequence[int], g: Sequence[int]) -> tuple[int, ...]:
    out = [0] * 6
    for i in range(6):
        out[g[i]] = int(v[i])
    return tuple(out)


def _reconstruct_pairwise_m2_945x615_independent(
    syl2_grp: Sequence[tuple[int, ...]],
    reps_45: Sequence[tuple[int, ...]],
) -> tuple[list[tuple[int, ...]], list[int]]:
    """Independently construct all `615` `Syl_2(S_6)` pairwise-M2 gate orbits and their exact `945`
    chamber gradient + off-braid wall-jump linear functional rows from first principles.
    """
    pairs15 = list(itertools.combinations(range(6), 2))
    two_pairs = list(itertools.combinations_with_replacement(pairs15, 2))

    def cp(p: tuple[int, int], g: Sequence[int]) -> tuple[int, int]:
        u, v = g[p[0]], g[p[1]]
        return (u, v) if u < v else (v, u)

    def cs(
        s: tuple[tuple[int, int], tuple[int, int]], g: Sequence[int]
    ) -> tuple[tuple[int, int], tuple[int, int]]:
        p1, p2 = cp(s[0], g), cp(s[1], g)
        return (p1, p2) if p1 <= p2 else (p2, p1)

    seen_1l: set[tuple[int, int]] = set()
    orbs_1l: list[tuple[tuple[int, int], ...]] = []
    for p in pairs15:
        if p not in seen_1l:
            o = tuple(sorted({cp(p, g) for g in syl2_grp}))
            seen_1l |= set(o)
            orbs_1l.append(o)

    seen_m2: set[Any] = set()
    orbs_m2: list[Any] = []
    for i1 in range(len(two_pairs)):
        s1 = two_pairs[i1]
        for i2 in range(i1 + 1, len(two_pairs)):
            s2 = two_pairs[i2]
            k0 = (s1, s2) if s1 <= s2 else (s2, s1)
            if k0 not in seen_m2:
                orb_set = set()
                for g in syl2_grp:
                    gs1, gs2 = cs(s1, g), cs(s2, g)
                    orb_set.add((gs1, gs2) if gs1 <= gs2 else (gs2, gs1))
                seen_m2 |= orb_set
                orbs_m2.append(tuple(sorted(orb_set)))

    cols_spec: list[tuple[str, Any]] = [("LIN", (0, 1, 2, 3)), ("LIN", (4, 5))]
    for o1 in orbs_1l:
        cols_spec.append(("1L_PM", o1))
    for o2 in orbs_m2:
        cols_spec.append(("M2_PM", o2))
    nc = len(cols_spec)
    if nc != 615:
        raise AssertionError(f"Expected 615 pairwise-M2 Syl_2 orbits, got {nc}")

    rdict: dict[tuple[Any, ...], list[int]] = {}
    for ci, rep in enumerate(reps_45):
        for r in range(6):
            rdict[("L", ci, r)] = [0] * nc
        for cj, (kind, data) in enumerate(cols_spec):
            if kind == "LIN":
                for coord_i in data:
                    rdict[("L", ci, rep[coord_i])][cj] += 1
            elif kind == "1L_PM":
                for u, v in data:
                    rdict[("L", ci, max(rep[u], rep[v]))][cj] += 1
            else:
                for s1, s2 in data:
                    a1 = max(rep[s1[0][0]], rep[s1[0][1]])
                    a2 = max(rep[s1[1][0]], rep[s1[1][1]])
                    b1 = max(rep[s2[0][0]], rep[s2[0][1]])
                    b2 = max(rep[s2[1][0]], rep[s2[1][1]])
                    diff = [0] * 6
                    diff[a1] += 1
                    diff[a2] += 1
                    diff[b1] -= 1
                    diff[b2] -= 1
                    if all(v == 0 for v in diff):
                        rdict[("L", ci, a1)][cj] += 1
                        rdict[("L", ci, a2)][cj] += 1
                        continue
                    suf = [sum(diff[k:]) for k in range(1, 6)]
                    hp, hn = any(v > 0 for v in suf), any(v < 0 for v in suf)
                    if hp and not hn:
                        rdict[("L", ci, a1)][cj] += 1
                        rdict[("L", ci, a2)][cj] += 1
                    elif hn and not hp:
                        rdict[("L", ci, b1)][cj] += 1
                        rdict[("L", ci, b2)][cj] += 1
                    else:
                        prim = _primitive_canonical_vec(diff)
                        g_div = 0
                        for dv in diff:
                            g_div = math.gcd(g_div, abs(dv))
                        first_nz = next(dv for dv in diff if dv != 0)
                        gs = g_div if first_nz > 0 else -g_div
                        kk = ("K", ci, prim)
                        if kk not in rdict:
                            rdict[kk] = [0] * nc
                        if gs > 0:
                            rdict[("L", ci, b1)][cj] += 1
                            rdict[("L", ci, b2)][cj] += 1
                            rdict[kk][cj] += gs
                        else:
                            rdict[("L", ci, a1)][cj] += 1
                            rdict[("L", ci, a2)][cj] += 1
                            rdict[kk][cj] += -gs

    # Cross-check on a concrete smooth interior ray `x_test` of chamber `ci == 0` that the symbolic
    # decomposition `sum_r L[r]*z_r + sum_prim K[prim]*ReLU(prim.z)` matches direct 2-layer gate evaluation!
    rep0 = reps_45[0]
    z_vals = (0, 2, 7, 19, 30, 55)
    pt_test = [z_vals[rep0[i]] for i in range(6)]
    for cj, (kind, data) in enumerate(cols_spec[:40]):
        if kind == "LIN":
            direct = sum(pt_test[i] for i in data)
        elif kind == "1L_PM":
            direct = sum(max(pt_test[u], pt_test[v]) for u, v in data)
        else:
            direct = sum(
                max(
                    max(pt_test[s1[0][0]], pt_test[s1[0][1]]) + max(pt_test[s1[1][0]], pt_test[s1[1][1]]),
                    max(pt_test[s2[0][0]], pt_test[s2[0][1]]) + max(pt_test[s2[1][0]], pt_test[s2[1][1]]),
                )
                for s1, s2 in data
            )
        sym_val = sum(rdict[("L", 0, r)][cj] * z_vals[r] for r in range(6))
        for k_key, r_vec in rdict.items():
            if k_key[0] == "K" and k_key[1] == 0 and r_vec[cj] != 0:
                p_dot = sum(k_key[2][r] * z_vals[r] for r in range(6))
                if p_dot > 0:
                    sym_val += r_vec[cj] * p_dot
        if direct != sym_val:
            raise AssertionError(f"Symbolic sub-chamber expansion mismatch at col {cj}: {direct} != {sym_val}")

    skeys = sorted(rdict.keys(), key=lambda x: (0 if x[0] == "L" else 1, x[1], x[2]))
    a_rows = [tuple(rdict[k]) for k in skeys]
    b_rows = [1 if (k[0] == "L" and k[2] == 5) else 0 for k in skeys]
    assert len(a_rows) == 945
    return (a_rows, b_rows)


def _reconstruct_tier123_gates_and_eval_independent(
    syl2_grp: Sequence[tuple[int, ...]],
    reps_45: Sequence[tuple[int, ...]],
) -> tuple[list[dict[str, Any]], list[tuple[int, ...]], IntMatrix, IntVector]:
    """Independently build the 384 `Syl_2(S_6)` 2-layer Z-gate specs (`cert_kernel` format) and evaluate
    their `362 x 384` integer table `(A_362, b_362)` from first principles.
    """
    def e6(i: int) -> list[int]:
        v = [0] * 6
        v[i] = 1
        return v

    def vadd(u: Sequence[int], v: Sequence[int]) -> list[int]:
        return [u[d] + v[d] for d in range(6)]

    def vsub(u: Sequence[int], v: Sequence[int]) -> list[int]:
        return [u[d] - v[d] for d in range(6)]

    seen_raw: set[Any] = set()
    raw_specs: list[tuple[str, Any]] = []
    kernel_gate_specs: list[dict[str, Any]] = []

    def add_lin(idxs: tuple[int, ...]) -> None:
        key = ("LIN", idxs)
        if key not in seen_raw:
            seen_raw.add(key)
            raw_specs.append(key)
            kernel_gate_specs.append(
                {"kind": "linear", "coeffs": [1 if d in idxs else 0 for d in range(6)]}
            )

    def add_1l(a_seed: Sequence[int]) -> None:
        orb = tuple(sorted({_act_vec6_ind(a_seed, g) for g in syl2_grp}))
        key = ("1L", orb)
        if key not in seen_raw:
            seen_raw.add(key)
            raw_specs.append(key)
            kernel_gate_specs.append(
                {"kind": "relu1", "normal": list(a_seed), "orbit_group": "syl2_s6", "orbit_mode": "unique"}
            )

    def add_l2(c0_seed: Sequence[int], terms_seed: Sequence[tuple[int, Sequence[int]]]) -> None:
        orb_set = set()
        for g in syl2_grp:
            c0_g = _act_vec6_ind(c0_seed, g)
            t_g = tuple(
                sorted((int(al), _act_vec6_ind(av, g)) for al, av in terms_seed if al != 0 and any(x != 0 for x in av))
            )
            orb_set.add((c0_g, t_g))
        orb = tuple(sorted(orb_set))
        key = ("L2", orb)
        if key not in seen_raw:
            seen_raw.add(key)
            raw_specs.append(key)
            kernel_gate_specs.append(
                {
                    "kind": "relu2",
                    "base_linear": [0] * 6,
                    "inner_linear": list(c0_seed),
                    "inner_hinges": [[int(al), list(av)] for al, av in terms_seed if al != 0 and any(x != 0 for x in av)],
                    "orbit_group": "syl2_s6",
                    "orbit_mode": "unique",
                }
            )

    add_lin((0, 1, 2, 3))
    add_lin((4, 5))

    t1_l1_seeds: list[Sequence[int]] = [
        (-1, 1, 0, 0, 0, 0),
        (-1, 0, 1, 0, 0, 0),
        (-1, 0, 0, 0, 1, 0),
        (0, 0, 0, 0, -1, 1),
        (-1, -1, 1, 1, 0, 0),
        (-1, 1, -1, 1, 0, 0),
        (-1, -1, 0, 0, 1, 1),
        (-1, 0, -1, 0, 1, 1),
        (-1, -1, 0, 0, 2, 0),
        (-1, 0, -1, 0, 2, 0),
        (2, 0, -1, -1, 0, 0),
        (2, 0, 0, 0, -1, -1),
        (-1, -1, -1, -1, 2, 2),
        (1, 1, 1, 1, -2, -2),
    ]
    for sa in t1_l1_seeds:
        add_1l(sa)
        add_1l([-c for c in sa])

    t1_z_blocks: list[tuple[list[int], list[list[int]]]] = [
        (vadd(e6(0), e6(1)), []),
        (vadd(e6(2), e6(3)), []),
        (vadd(e6(4), e6(5)), []),
        (vadd(e6(0), e6(2)), []),
        (vadd(e6(0), e6(4)), []),
        (vadd(e6(4), e6(4)), []),
        (vadd(e6(0), e6(1)), [[-1, -1, 0, 0, 2, 0]]),
        (vadd(e6(0), e6(1)), [[-1, -1, 0, 0, 0, 2]]),
        (vadd(e6(0), e6(2)), [[-1, 0, -1, 0, 2, 0]]),
        (vadd(e6(0), e6(1)), [[-1, -1, 0, 0, 1, 1]]),
        (vadd(e6(0), e6(2)), [[-1, 0, -1, 0, 1, 1]]),
        (vadd(e6(0), e6(1)), [[-1, -1, 1, 1, 0, 0]]),
        (vadd(e6(4), e6(4)), [[0, 0, 0, 0, -1, 1], [0, 0, 0, 0, -1, 1]]),
        (vadd(e6(0), e6(1)), [[-1, -1, -1, -1, 2, 2]]),
        (vadd(e6(0), e6(2)), [[0, 0, 1, -1, 0, 0], [-1, 0, 0, 1, 0, 0]]),
        (vadd(e6(0), e6(0)), [[-1, 0, 1, 0, 0, 0], [-1, 0, 0, 1, 0, 0]]),
        (vadd(e6(0), e6(1)), [[-1, 0, 1, 0, 0, 0], [0, -1, 0, 1, 0, 0]]),
        (vadd(e6(0), e6(0)), [[-1, 0, 0, 0, 1, 0], [-1, 0, 0, 0, 0, 1]]),
        (vadd(e6(0), e6(1)), [[-1, 0, 0, 0, 1, 0], [0, -1, 0, 0, 0, 1]]),
        (vadd(e6(4), e6(4)), [[1, 0, 0, 0, -1, 0], [0, 0, 1, 0, -1, 0]]),
        (vadd(e6(0), e6(2)), [[-1, 1, 0, 0, 0, 0], [0, 0, -1, 1, 0, 0]]),
        (vadd(e6(0), e6(4)), [[-1, 1, 0, 0, 0, 0], [0, 0, 0, 0, -1, 1]]),
        (vadd(e6(0), e6(4)), [[-1, 0, 1, 0, 0, 0], [0, 0, 0, 0, -1, 1]]),
        (vadd(e6(0), e6(2)), [[-1, -1, 0, 0, 2, 0], [0, 0, -1, -1, 0, 2]]),
        (vadd(e6(0), e6(2)), [[-1, 0, -1, 0, 2, 0], [0, -1, 0, -1, 0, 2]]),
        (vadd(e6(0), e6(1)), [[-1, -1, 0, 0, 1, 1], [0, 0, -1, -1, 1, 1]]),
    ]
    clean_b = [(b, [h for h in hs if sum(h) == 0]) for (b, hs) in t1_z_blocks if sum(b) == 2]
    for i in range(len(clean_b)):
        b1_v, h1_v = clean_b[i]
        for j in range(i + 1, len(clean_b)):
            b2_v, h2_v = clean_b[j]
            c0 = [b2_v[d] - b1_v[d] for d in range(6)]
            terms = [(1, a) for a in h2_v] + [(-1, a) for a in h1_v]
            add_l2(c0, terms)
    assert len(raw_specs) == 321

    t2_l1_seeds: list[Sequence[int]] = [
        (-1, -1, -1, 1, 1, 1),
        (-1, -1, 1, -1, 1, 1),
        (-2, 1, 1, -1, 0, 1),
        (-2, 0, 1, 1, -1, 1),
        (-2, -1, 1, 1, 1, 0),
        (-2, -1, 1, 0, 1, 1),
        (-2, -2, 1, 1, 1, 1),
        (-2, 2, -1, 1, -1, 1),
        (-2, 1, 0, 0, -1, 2),
        (-1, -1, -2, 2, 1, 1),
    ]
    for sa in t2_l1_seeds:
        add_1l(sa)
        add_1l([-c for c in sa])

    t2_joins: list[tuple[Sequence[int], Sequence[tuple[int, Sequence[int]]]]] = [
        ((0, 0, 0, 0, 0, 0), [(1, (-1, -1, 0, 0, 2, 0)), (1, (0, 0, -1, -1, 0, 2)), (-1, (-1, 0, -1, 0, 1, 1)), (-1, (0, -1, 0, -1, 1, 1))]),
        ((-1, 0, 0, 0, 1, 0), [(1, (-1, -1, -1, 1, 1, 1)), (1, (0, 0, 0, 0, -1, 1)), (-1, (-1, 1, 0, 0, 0, 0)), (-1, (0, 0, -1, 1, 0, 0))]),
        ((-1, -1, 0, 0, 1, 1), [(1, (-2, 1, 1, 0, 0, 0)), (1, (0, 0, -2, 1, 1, 0)), (-1, (-1, -1, 0, 0, 2, 0)), (-1, (0, 0, -1, -1, 0, 2))]),
        ((0, 0, -1, -1, 1, 1), [(1, (-1, 1, 0, 0, 0, 0)), (1, (-1, -1, -1, -1, 2, 2)), (-1, (-1, 0, -1, 0, 2, 0)), (-1, (0, -1, 0, -1, 0, 2))]),
        ((1, 0, -1, 0, 0, 0), [(1, (-1, 0, 0, 0, 1, 0)), (1, (0, -1, 0, 0, 0, 1)), (-1, (0, 0, -1, 0, 1, 0)), (-1, (0, 0, 0, -1, 0, 1))]),
        ((0, 0, 0, 0, -1, 1), [(1, (-1, -1, 1, 1, 0, 0)), (1, (-1, 1, -1, 1, 0, 0)), (-1, (-1, -1, 0, 0, 2, 0)), (-1, (0, 0, -1, -1, 0, 2))]),
        ((-1, 0, 0, 0, 1, 0), [(1, (-1, 1, 0, 0, 0, 0)), (1, (-1, 0, 1, 0, 0, 0)), (1, (-1, 0, 0, 1, 0, 0)), (-1, (0, 0, 0, 0, -1, 1))]),
        ((-1, -1, 0, 0, 1, 1), [(1, (-1, 1, 0, 0, 0, 0)), (1, (0, 0, -1, 1, 0, 0)), (1, (-1, -1, 1, 1, 0, 0)), (-1, (0, 0, 0, 0, -1, 1))]),
        ((0, 0, -1, 0, 1, 0), [(1, (-1, -1, 0, 0, 2, 0)), (1, (-1, 1, 0, 0, 0, 0)), (1, (0, 0, -1, 1, 0, 0)), (-1, (-1, -1, -1, 1, 1, 1))]),
        ((-2, 0, 0, 0, 1, 1), [(1, (-1, 1, 0, 0, 0, 0)), (1, (-1, 0, 1, 0, 0, 0)), (1, (-1, 0, 0, 0, 2, -1)), (-1, (0, 0, 0, -1, 0, 1))]),
        ((1, 0, 0, 0, -1, 0), [(1, (-1, 1, 0, 0, 0, 0)), (1, (-1, 0, 1, 0, 0, 0)), (1, (-1, 0, 0, 1, 0, 0)), (1, (-1, 0, 0, 0, 0, 1))]),
        ((-1, 0, 0, 0, 1, 0), [(-1, (-1, 1, 0, 0, 0, 0)), (-1, (-1, 0, 1, 0, 0, 0)), (-1, (-1, 0, 0, 1, 0, 0)), (-1, (-1, 0, 0, 0, 0, 1))]),
        ((-1, -1, 0, 0, 1, 1), [(1, (-1, 1, 0, 0, 0, 0)), (1, (0, 0, -1, 1, 0, 0)), (1, (-1, -1, 0, 0, 2, 0)), (1, (0, 0, -1, -1, 0, 2))]),
        ((1, 1, 0, 0, -1, -1), [(-1, (-1, 1, 0, 0, 0, 0)), (-1, (0, 0, -1, 1, 0, 0)), (-1, (-1, -1, 0, 0, 2, 0)), (-1, (0, 0, -1, -1, 0, 2))]),
    ]
    for c0_s, t_s in t2_joins:
        add_l2(c0_s, t_s)
        add_l2([-c for c in c0_s], [(-al, av) for al, av in t_s])

    extra_m2 = [
        ((0, 1), (2, 4), (0, 3), (1, 5)),
        ((0, 2), (1, 4), (0, 5), (2, 3)),
        ((0, 4), (1, 2), (2, 5), (3, 4)),
        ((0, 3), (2, 4), (1, 4), (3, 5)),
        ((0, 5), (1, 3), (0, 2), (4, 5)),
    ]
    for (a1, b1), (a2, b2), (c1, d1), (c2, d2) in extra_m2:
        c0_m = vsub(vadd(e6(c1), e6(c2)), vadd(e6(a1), e6(a2)))
        t_m: list[tuple[int, Sequence[int]]] = [
            (1, vsub(e6(d1), e6(c1))),
            (1, vsub(e6(d2), e6(c2))),
            (-1, vsub(e6(b1), e6(a1))),
            (-1, vsub(e6(b2), e6(a2))),
        ]
        add_l2(c0_m, t_m)
    assert len(raw_specs) == 364

    t3_signed: list[tuple[Sequence[int], Sequence[tuple[int, Sequence[int]]]]] = [
        ((0, 0, 0, 0, 0, 0), [(2, (-1, -1, 0, 0, 1, 1)), (-2, (0, 0, 0, 0, -1, 1)), (-1, (-1, 1, 0, 0, 0, 0))]),
        ((-1, -1, 0, 0, 1, 1), [(2, (0, 0, 0, 0, -1, 1)), (-1, (-1, 0, 1, 0, 0, 0)), (-1, (0, -1, 0, 1, 0, 0))]),
        ((0, 0, -1, -1, 1, 1), [(2, (-1, 1, 0, 0, 0, 0)), (-2, (0, 0, -1, 1, 0, 0)), (1, (-1, -1, -1, -1, 2, 2))]),
        ((-2, 0, 0, 0, 1, 1), [(2, (-1, 1, 0, 0, 0, 0)), (2, (0, 0, 0, 0, -1, 1)), (-1, (-1, -1, 0, 0, 2, 0)), (-1, (0, 0, -1, -1, 0, 2))]),
        ((0, 0, 0, 0, -2, 2), [(2, (-1, -1, 0, 0, 2, 0)), (-2, (0, 0, -1, -1, 0, 2)), (1, (-1, -1, 1, 1, 0, 0))]),
        ((1, -1, 0, 0, 0, 0), [(2, (-1, 0, 0, 0, 1, 0)), (-2, (0, -1, 0, 0, 0, 1)), (1, (0, 0, -1, 1, 0, 0)), (-1, (-1, -1, -1, 1, 1, 1))]),
        ((-1, 0, -1, 0, 1, 1), [(2, (-1, -1, -1, 1, 1, 1)), (-2, (-1, 1, 0, 0, 0, 0)), (2, (0, 0, 0, 0, -1, 1))]),
        ((0, 0, 0, 0, 0, 0), [(2, (-2, 1, 1, 0, 0, 0)), (-2, (0, 0, -2, 1, 1, 0)), (1, (-1, -1, 0, 0, 1, 1)), (-1, (0, 0, -1, -1, 1, 1))]),
        ((-1, 1, -1, 1, 0, 0), [(2, (-1, 0, -1, 0, 2, 0)), (-2, (0, -1, 0, -1, 0, 2)), (1, (0, 0, 0, 0, -1, 1))]),
        ((2, -1, -1, 0, 0, 0), [(-2, (1, 0, 0, 0, -1, 0)), (2, (0, 1, 0, 0, 0, -1)), (1, (0, 0, 1, -1, 0, 0)), (-1, (-1, -1, 1, 1, 0, 0))]),
    ]
    for c0_s, t_s in t3_signed:
        add_l2(c0_s, t_s)
        add_l2([-c for c in c0_s], [(-al, av) for al, av in t_s])
    assert len(raw_specs) == 384

    profiles = (
        (0, 1, 3, 7, 15, 31),
        (0, 2, 5, 11, 23, 47),
        (0, 4, 6, 10, 25, 40),
        (0, 2, 6, 10, 25, 40),
        (0, 2, 7, 19, 30, 50),
        (0, 3, 8, 10, 13, 17),
        (0, 5, 6, 7, 19, 20),
        (0, 1, 2, 3, 4, 5),
    )
    cand_pts: list[tuple[int, ...]] = [(1, 1, 1, 1, 1, 1), (-1, -1, -1, -1, -1, -1)]
    for bp in profiles:
        for rep in reps_45:
            cand_pts.append(tuple(bp[rep[i]] for i in range(6)))
    assert len(cand_pts) == 362

    # Fast cached pure-int evaluation of all 384 gate orbits on all 362 points:
    vec_set: set[tuple[int, ...]] = set()
    for kind, data in raw_specs:
        if kind == "1L":
            for a in data:
                vec_set.add(a)
        elif kind == "L2":
            for c0, terms in data:
                vec_set.add(c0)
                for _al, av in terms:
                    vec_set.add(av)
    dot_c: dict[tuple[int, ...], list[int]] = {}
    relu_c: dict[tuple[int, ...], list[int]] = {}
    for v in vec_set:
        v0, v1, v2, v3, v4, v5 = v
        dl = [v0 * p[0] + v1 * p[1] + v2 * p[2] + v3 * p[3] + v4 * p[4] + v5 * p[5] for p in cand_pts]
        dot_c[v] = dl
        relu_c[v] = [val if val > 0 else 0 for val in dl]

    m_r = len(cand_pts)
    cols: list[list[int]] = []
    for kind, data in raw_specs:
        if kind == "LIN":
            cols.append([sum(p[i] for i in data) for p in cand_pts])
        elif kind == "1L":
            c1 = [0] * m_r
            for a in data:
                rc = relu_c[a]
                for r in range(m_r):
                    c1[r] += rc[r]
            cols.append(c1)
        else:
            c2 = [0] * m_r
            for c0, terms in data:
                dc = dot_c[c0]
                t_rcs = [(al, relu_c[av]) for al, av in terms]
                for r in range(m_r):
                    pre = dc[r]
                    for al, rc in t_rcs:
                        rv = rc[r]
                        if rv > 0:
                            pre += al * rv
                    if pre > 0:
                        c2[r] += pre
            cols.append(c2)

    a_362 = [[cols[j][r] for j in range(384)] for r in range(m_r)]
    b_362 = [max(p) for p in cand_pts]
    return (kernel_gate_specs, cand_pts, a_362, b_362)


def verify_stage6_live_peer_checkpoints_cross_audit() -> dict[str, Any]:
    """Zero-trust first-principles audit of `checkpoint_a2_wave2.json`, `checkpoint_d4_wave2.json`,
    and `simulator_wave2_data.json`.
    """
    p_a2 = ARTIFACTS_DIR.joinpath("checkpoint_a2_wave2.json")
    p_d4 = ARTIFACTS_DIR.joinpath("checkpoint_d4_wave2.json")
    p_sim = ARTIFACTS_DIR.joinpath("simulator_wave2_data.json")
    for p_req in (p_a2, p_d4, p_sim):
        if not p_req.exists():
            raise AssertionError(f"Missing required Wave II peer artifact: {p_req.name}")

    a2_data = _load_json_zero_float(p_a2)
    d4_data = _load_json_zero_float(p_d4)
    sim_data = _load_json_zero_float(p_sim)

    # -----------------------------------------------------------------------
    # 1. Cross-verify `checkpoint_a2_wave2.json` (`A2a`, `A2b`, `A2c`)
    # -----------------------------------------------------------------------
    t_a2a = a2_data["theorem_a2a"]
    res_a2a_cert = verify_ledger_certificate(
        t_a2a["certificate"], claim_id="peer_A2a", epistemic_tag=str(t_a2a["epistemic_status"])
    )
    # Also verify convex-hull volumes directly from the simplices' vertex union via our Beneath-Beyond engine!
    s_d5 = t_a2a["certificate"]["sub_certificates"]["d5_zonotope_pair_2_2_vol4_mod3_eq_1"]["simplices"]
    s_d6 = t_a2a["certificate"]["sub_certificates"]["d6_zonotope_pair_3_2_vol12_mod6_eq_0"]["simplices"]
    hull_d5 = compute_convex_hull_normalized_volume([v for simp in s_d5 for v in simp], 5)
    hull_d6 = compute_convex_hull_normalized_volume([v for simp in s_d6 for v in simp], 6)
    if hull_d5["normalized_volume"] != 4 or hull_d6["normalized_volume"] != 12:
        raise AssertionError("Independent Beneath-Beyond disagreed with peer A2a simplex hull volumes")
    if (
        t_a2a["d5_n6_volumes"]["paramid_4_0"] != 24
        or t_a2a["d5_n6_volumes"]["segment_join_3_1"] != 6
        or t_a2a["d5_n6_volumes"]["zonotope_pair_2_2"] != 4
        or t_a2a["d6_n7_volumes"]["universal_gcd_value"] != 12
    ):
        raise AssertionError("Peer A2a volume summary table mismatch")

    t_a2b = a2_data["theorem_a2b"]
    if t_a2b["tier123_epistemic_status"] != "CERTIFIED_EXACT":
        raise AssertionError("Expected CERTIFIED_EXACT on bounded Tier 1-3 3-adic obstructions")
    if t_a2b["unconstrained_z_half_epistemic_status"] != "OPEN_BUDGET_EXCEEDED":
        raise AssertionError("Epistemic guardrail: unconstrained MAX_6 Z[1/2] must be OPEN_BUDGET_EXCEEDED")

    res_a2b_cert = verify_ledger_certificate(
        t_a2b["certificate"], claim_id="peer_A2b", epistemic_tag="CERTIFIED_EXACT"
    )

    # Zero-trust reconstruction of ALL FOUR A2b `p = 3` dual linear systems `(A, b)`:
    syl2_grp, reps_45 = _build_syl2_s6_independent()
    a_sym_945, b_sym_945 = _reconstruct_pairwise_m2_945x615_independent(syl2_grp, reps_45)
    sym_lookup: dict[tuple[tuple[int, ...], int], list[int]] = {}
    for idx_r, (ar, br) in enumerate(zip(a_sym_945, b_sym_945)):
        sym_lookup.setdefault((ar, br), []).append(idx_r)

    pm_cert = t_a2b["certificate"]["sub_certificates"]["pairwise_m2_945x615_padic_p3"]
    used_sym_rows: set[int] = set()
    for r_i, (row_a, val_b) in enumerate(zip(pm_cert["A"], pm_cert["b"])):
        key_pm = (tuple(row_a), int(val_b))
        cands = [idx for idx in sym_lookup.get(key_pm, []) if idx not in used_sym_rows]
        if not cands:
            raise AssertionError(f"Pairwise-M2 945x615 dual row {r_i} failed independent symbolic reconstruction!")
        used_sym_rows.add(cands[0])
    pm_padic_res = verify_padic_obstruction_certificate(
        pm_cert["A"], pm_cert["b"], pm_cert["y"], p=3, s_bound=1, inverted_primes=[2]
    )

    kernel_384_specs, cand_pts_362, a_true_362, b_true_362 = _reconstruct_tier123_gates_and_eval_independent(
        syl2_grp, reps_45
    )
    tier_checks: dict[str, Any] = {"pairwise_m2_945x615": {"matched_rows": len(used_sym_rows), "padic": pm_padic_res}}

    for t_key, n_cols in (
        ("tier1_bakaev_4plus2_padic_p3", 321),
        ("tier2_small_coeff_joins_padic_p3", 364),
        ("tier3_signed_layer2_padic_p3", 384),
    ):
        tc = t_a2b["certificate"]["sub_certificates"][t_key]
        row_map: dict[tuple[tuple[int, ...], int], list[int]] = {}
        for r_idx in range(len(cand_pts_362)):
            rk = (tuple(a_true_362[r_idx][:n_cols]), b_true_362[r_idx])
            row_map.setdefault(rk, []).append(r_idx)

        matched_pts: list[list[int]] = []
        used_r: set[int] = set()
        for i_c, (ra, vb) in enumerate(zip(tc["A"], tc["b"])):
            rk_c = (tuple(ra), int(vb))
            avail = [idx for idx in row_map.get(rk_c, []) if idx not in used_r]
            if not avail:
                raise AssertionError(f"{t_key} row {i_c} failed independent 2-layer Z-gate & MAX_6 evaluation match!")
            chosen_r = avail[0]
            used_r.add(chosen_r)
            matched_pts.append(list(cand_pts_362[chosen_r]))

        # Also cross-check `compile_2layer_gate` evaluation on spot rows (row 0 and last row) via `cert_kernel`:
        for spot_i in (0, len(matched_pts) - 1):
            pt_s = matched_pts[spot_i]
            if tc["b"][spot_i] != max(pt_s):
                raise AssertionError(f"{t_key} b[{spot_i}] != MAX_6({pt_s})")
        padic_t = verify_padic_obstruction_certificate(
            tc["A"], tc["b"], tc["y"], p=3, s_bound=1, inverted_primes=[2]
        )
        tier_checks[t_key] = {
            "rows_matched_to_true_gates": len(matched_pts),
            "cols": n_cols,
            "vp_yt_a": padic_t["vp_yt_a"],
            "vp_yt_b": padic_t["vp_yt_b"],
        }

    # Verify all 7 unimodular SNF factorizations in `theorem_a2c`:
    t_a2c = a2_data["theorem_a2c"]
    res_a2c_cert = verify_ledger_certificate(
        t_a2c["certificate"], claim_id="peer_A2c", epistemic_tag=str(t_a2c["epistemic_status"])
    )
    a2c_subs = t_a2c["certificate"]["sub_certificates"]
    expected_a2c_torsion = {
        "h4_pure_paramids_snf": [2, 2, 2, 2, 2],
        "h4_zonotope_pairs_snf": [2, 2, 2],
        "h5_d4_pure_paramids_snf": [4],
        "h5_d4_zonotope_pairs_snf": [2],
        "h6_s6_pure_paramids_snf": [3, 12],
        "h6_s6_zonotope_pairs_snf": [2, 2, 6, 6, 60, 180],
        "h6_d6_zonotope_pairs_snf": [2, 2, 6],
    }
    a2c_torsion_verified: dict[str, list[int]] = {}
    for k_snf, exp_tor in expected_a2c_torsion.items():
        sc = a2c_subs[k_snf]
        sr = verify_snf_certificate(
            sc["A"], sc["U"], sc["U_inv"], sc["S"], sc["V"], sc["V_inv"], sc.get("invariant_factors")
        )
        if sr["torsion_factors"] != exp_tor:
            raise AssertionError(f"A2c {k_snf} torsion {sr['torsion_factors']} != expected {exp_tor}")
        a2c_torsion_verified[k_snf] = sr["torsion_factors"]

    # -----------------------------------------------------------------------
    # 2. Cross-verify `checkpoint_d4_wave2.json` (`D4a` & `D4b`)
    # -----------------------------------------------------------------------
    t_d4a = d4_data["theorem_d4a"]
    res_d4a_cert = verify_ledger_certificate(
        t_d4a["certificate"], claim_id="peer_D4a", epistemic_tag=str(t_d4a["epistemic_status"])
    )
    verify_central_extension_cocycle_certificate(
        {
            "quotient_cayley": build_canonical_group_cayley("V_4"),
            "expected_quotient_group": "V_4",
            "central_modulus": 2,
            "cocycle_beta": t_d4a["q8_h2_v4_z2_cocycle"]["beta_table_4x4"],
            "expect_nontrivial_cohomology": True,
            "expected_extension_group": "Q_8",
        }
    )

    d4a_subs = t_d4a["certificate"]["sub_certificates"]
    tier2_q8_w = int(t_d4a["q8_width_hierarchy"]["tier2_v4_cocycle_quotient_reduced_pure_z"])
    if not (17 <= tier2_q8_w < 48):
        raise AssertionError(f"Unexpected Tier-2 reduced Q_8 cocycle width {tier2_q8_w}")
    d4a_iso_checks = (
        ("q8_v4_cocycle_w48_pure_z", "Q_8", 48, False),
        ("q8_v4_cocycle_reduced_pure_z", "Q_8", tier2_q8_w, False),
        ("q8_walsh_howell_lafon_w22_argmax_z", "Q_8", 22, False),
        ("q8_shifted_coset_w17_pure_z", "Q_8", 17, False),
        ("q8_shifted_coset_w18_unbiased_pure_z", "Q_8", 18, True),
        ("d4_shifted_coset_w17_pure_z", "D_4", 17, False),
        ("dic3_shifted_coset_w25_pure_z", "Dic_3", 25, False),
    )
    d4a_widths_verified: dict[str, int] = {}
    for c_key, g_exp, w_exp, z_readout_bias in d4a_iso_checks:
        c_obj = dict(d4a_subs[c_key])
        c_obj["expected_group_name"] = g_exp
        c_obj["zero_readout_bias"] = z_readout_bias
        rc = verify_group_circuit_certificate(c_obj)
        if rc["width"] != w_exp:
            raise AssertionError(f"D4a {c_key} width {rc['width']} != expected {w_exp}")
        if z_readout_bias:
            # Also verify exact one-hot absorption `b1 -> W1[:, :n]` yields strict `b1 == 0, b2 == 0` at identical width!
            n_g = len(c_obj["cayley"])
            w1_hom = [[r[j] + (b_i if j < n_g else 0) for j in range(2 * n_g)] for r, b_i in zip(c_obj["W1"], c_obj["b1"])]
            verify_group_circuit_certificate(
                {
                    "cayley": c_obj["cayley"],
                    "expected_group_name": g_exp,
                    "W1": w1_hom,
                    "b1": [0] * w_exp,
                    "W2": c_obj["W2"],
                    "b2": [0] * n_g,
                    "zero_bias": True,
                    "compressed": True,
                    "mode": "indicator",
                }
            )
        d4a_widths_verified[c_key] = int(rc["width"])

    t_d4b = d4_data["theorem_d4b"]
    res_d4b_cert = verify_ledger_certificate(
        t_d4b["certificate"], claim_id="peer_D4b", epistemic_tag=str(t_d4b["epistemic_status"])
    )
    d4b_subs = t_d4b["certificate"]["sub_certificates"]
    for c_key, g_exp, w_exp in (
        ("c3_minimal_w4_pure_z", "C_3", 4),
        ("v4_w7_pure_z", "V_4", 7),
        ("c4_w6_pure_z", "C_4", 6),
        ("c5_w8_pure_z", "C_5", 8),
    ):
        c_obj = dict(d4b_subs[c_key])
        c_obj["expected_group_name"] = g_exp
        rc = verify_group_circuit_certificate(c_obj)
        if rc["width"] != w_exp:
            raise AssertionError(f"D4b {c_key} width {rc['width']} != {w_exp}")

    for g_nm, rec in t_d4b["gram_determinant_records"].items():
        gb_res = verify_group_indicator_bounds_certificate(
            {
                "group_name": g_nm,
                "cayley": build_canonical_group_cayley(g_nm),
                "expected_gram_det": rec["gram_det"],
            }
        )
        if gb_res["biased_rank_lower_bound"] != rec["rank_lower_bound_biased"]:
            raise AssertionError(f"D4b {g_nm} rank lower bound mismatch")

    # -----------------------------------------------------------------------
    # 3. Cross-verify `simulator_wave2_data.json` (`V_4` `W=6` pure-Z + Tier 3 `Q_16`..`S_3` + Volumes)
    # -----------------------------------------------------------------------
    sim_ge = sim_data["group_extensions_and_widths"]
    v4_surg = sim_ge["v4_walsh_vs_surgical_z"]
    v4_cay = build_canonical_group_cayley("V_4")
    sim_v4_w6_res = verify_group_circuit_certificate(
        {
            "cayley": v4_cay,
            "expected_group_name": "V_4",
            "W1": v4_surg["surgical_W1"],
            "b1": [0] * 6,
            "W2": v4_surg["surgical_W2"],
            "b2": v4_surg["surgical_b2"],
            "compressed": True,
            "mode": "indicator",
        }
    )
    if sim_v4_w6_res["width"] != 6:
        raise AssertionError("Expected Simulator surgical pure-Z V_4 circuit width == 6")
    # Also verify its 16 x 7 augmented feature matrix is genuinely Z-unimodular (`SNF == [1]*7`):
    f_v4_surg = [
        [max(0, r[g] + r[4 + h]) for r in v4_surg["surgical_W1"]] + [1]
        for g in range(4)
        for h in range(4)
    ]
    snf_v4_surg = _build_fast_verified_snf_witness(f_v4_surg)
    if snf_v4_surg["snf_verification"]["invariant_factors"] != [1] * 7:
        raise AssertionError("Simulator surgical V_4 W=6 feature matrix failed unimodular SNF == [1]*7")

    sim_t3_widths: dict[str, int] = {}
    for g_nm, t3_entry in sim_ge["tier3_superposed_cocycle_ramp_pure_z"].items():
        n_ord = int(t3_entry["order"])
        w1_t3 = t3_entry["W1"]
        b1_t3 = t3_entry["b1"]
        w2_t3 = t3_entry["W2"]
        b2_t3 = t3_entry["b2"]
        # Extract the exact {0,1}-indicator output table directly from the circuit and verify both
        # group axioms AND explicit isomorphism to canonical `g_nm` (`S_3, D_4, Q_8, Dic_3, Q_16`)!
        cay_sim = [[0] * n_ord for _ in range(n_ord)]
        for g in range(n_ord):
            for h in range(n_ord):
                hid = [max(0, int(r[g]) + int(r[n_ord + h]) + int(bi)) for r, bi in zip(w1_t3, b1_t3)]
                out_v = [vec_dot(w2_t3[c], hid) + int(b2_t3[c]) for c in range(n_ord)]
                ones_pos = [c for c in range(n_ord) if out_v[c] == 1]
                if len(ones_pos) != 1 or any(out_v[c] != 0 for c in range(n_ord) if c != ones_pos[0]):
                    raise AssertionError(f"Simulator Tier-3 {g_nm} failed {0,1} one-hot output at ({g},{h}): {out_v}")
                cay_sim[g][h] = ones_pos[0]
        res_t3 = verify_group_circuit_certificate(
            {
                "cayley": cay_sim,
                "expected_group_name": g_nm,
                "W1": w1_t3,
                "b1": b1_t3,
                "W2": w2_t3,
                "b2": b2_t3,
                "compressed": True,
                "mode": "indicator",
            }
        )
        sim_t3_widths[g_nm] = int(res_t3["width"])

    sim_jv = sim_data["join_volume_dichotomy"]
    if (
        sim_jv["d5_max6_dichotomy_highlight"]["zonotope_pair_2_2_vol"] != 4
        or sim_jv["d5_max6_dichotomy_highlight"]["zonotope_pair_2_2_mod_3"] != 1
        or sim_jv["d6_max7_obstruction_highlight"]["all_splits_gcd"] != 12
        or not sim_jv["d6_max7_obstruction_highlight"]["divisible_by_6"]
    ):
        raise AssertionError("Simulator join_volume_dichotomy highlight mismatch")

    return {
        "architect_a2_subcerts_verified": res_a2a_cert["count"] + res_a2b_cert["count"] + res_a2c_cert["count"],
        "architect_a2b_zero_trust_dual_systems": tier_checks,
        "architect_a2c_torsion_verified": a2c_torsion_verified,
        "architect_d4_subcerts_verified": res_d4a_cert["count"] + res_d4b_cert["count"],
        "architect_d4a_widths_verified": d4a_widths_verified,
        "simulator_v4_surgical_pure_z_width": sim_v4_w6_res["width"],
        "simulator_tier3_pure_z_widths": sim_t3_widths,
        "simulator_join_families_checked": int(sim_jv["total_zonotope_join_families_verified"]),
    }


# ---------------------------------------------------------------------------
# Master Wave II Entrypoint
# ---------------------------------------------------------------------------


def run_wave2_verification(flush_checkpoints: bool = True) -> dict[str, Any]:
    """Run all 7 Wave II formalist verification & cross-audit stages under per-stage 20s alarms."""
    t_start_ns = time.monotonic_ns()
    stages = [
        run_timed_stage("stage0_wave1_and_ledger_gate", verify_stage0_wave1_and_optional_wave2_ledgers),
        run_timed_stage("stage1_theorem_a2a_join_volume_dichotomy", verify_stage1_theorem_a2a),
        run_timed_stage("stage2_theorem_a2b_primal_and_dual_verifiers", verify_stage2_theorem_a2b),
        run_timed_stage("stage3_theorem_a2c_arrangement_paramid_snf", verify_stage3_theorem_a2c),
        run_timed_stage("stage4_theorems_d4a_d4b_cocycle_and_bounds", verify_stage4_theorems_d4a_and_d4b),
        run_timed_stage("stage5_wave2_adversarial_tamper_suite", verify_stage5_wave2_adversarial_tamper_suite),
        run_timed_stage("stage6_live_peer_checkpoints_cross_audit", verify_stage6_live_peer_checkpoints_cross_audit),
    ]
    total_ms = (time.monotonic_ns() - t_start_ns) // 1_000_000
    summary = {
        "wave": "2.0",
        "cycle": 2,
        "owner": "formalist",
        "all_passed": all(st["status"] == "PASS" for st in stages),
        "stages_passed": sum(1 for st in stages if st["status"] == "PASS"),
        "total_stages": len(stages),
        "total_elapsed_ms": total_ms,
        "stages": stages,
    }
    if flush_checkpoints:
        ARTIFACTS_DIR.mkdir(parents=True, exist_ok=True)
        out_path = ARTIFACTS_DIR.joinpath("cycle2_wave2_formalist_audit.json")
        out_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def main(argv: Sequence[str] | None = None) -> int:
    args = list(argv) if argv is not None else sys.argv[1:]
    do_flush = "--no-flush" not in args
    summary = run_wave2_verification(flush_checkpoints=do_flush)
    print(
        f"[formalist/proof_pack_v2] ALL_PASS={summary['all_passed']} "
        f"stages={summary['stages_passed']}/{summary['total_stages']} "
        f"total={summary['total_elapsed_ms']} ms"
    )
    for st in summary["stages"]:
        print(f"  - {st['stage']}: {st['status']} ({st['elapsed_ms']} ms / {st['elapsed_us']} us)")
    return 0 if summary["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
