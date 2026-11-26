from __future__ import annotations

"""Wave I + Wave II (v2.0) Master Clean-Room Verification Gate (`verify_all.py`).

Executes end-to-end in `< 45 seconds` under `/usr/bin/python3 -I verify_all.py` with:
- 0 external dependencies (`from __future__ import annotations` + Python 3.9+ stdlib only)
- 0 hardcoded workspace paths (100% portable to `/tmp` clean-room execution)
- Hard `signal.alarm(20)` per verification stage
- 0 `float` outside `simulator/svg_atlas.py`, 0 inner-loop `Fraction`, 0 `ast.Div`, 0 `isinstance`, 0 JSON float tokens
- Runs:
  1. Gate 0: All 7 Repaired Wave-1 Adversarial Sanity Traps (`architect/test_wave1_traps.py`)
  2. Architect Wave I Tracks A, B, C, D, E + Wave II Tracks A2 & D4 (`track_a_wave2_max6.py`, `track_d_wave2_extensions.py`)
  3. Emits & verifies 100% of `artifacts/theorem_ledger_v1.json` (21 claims) AND `artifacts/theorem_ledger_v2.json` (26 claims)
     via `formalist.cert_kernel.verify_ledger_certificate`
  4. Simulator parameterized sweeps + deterministic zero-overlap vector atlas (`simulator/svg_atlas.py` -> `plots/`)
  5. Formalist Independent Zero-Dependency Proof Packs (`formalist/proof_pack_v1.py` & `formalist/proof_pack_v2.py`)
  6. Inquisitor SVG Geometry Auditor (`inquisitor/svg_auditor.py`), Wave II Torture Suite (`inquisitor/wave2_torture_tests.py`),
     Scope-Aware AST Contraband & JSON Float Firewall (`inquisitor/ast_scanner.py`), and Cycle 1 & Cycle 2 Adversarial Probes
"""

import importlib
import itertools
import json
import os
import signal
import sys
import time
from typing import Callable, Sequence

_ROOT = os.path.dirname(os.path.abspath(__file__))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from architect.core import (
    SNFResult,
    dot_int,
    primitive_direction,
    smith_normal_form,
    solve_lp,
    solve_s_integral,
)
from architect.test_wave1_traps import (
    MAX4_W1,
    MAX4_W2,
    MAX4_W3,
    build_forward_invariant_octagonal_annulus,
    eval_bakaev_2max5_terms,
    run_all_wave1_traps_and_flush,
)
from architect.track_a_foundations import run_track_a
from architect.track_a_wave2_max6 import run_track_a2_wave2
from architect.track_b_decomp_splines import run_track_b
from architect.track_c_airy_cosheaf import (
    _make_desargues_prism,
    _make_primitive_twisted_wheel,
    _make_spiderweb,
    build_airy_cosheaf_complex,
    run_track_c,
)
from architect.track_d_group_circuits import (
    _build_nontrivial_coset_feature_matrix,
    make_q8_group,
    make_s3_group,
    run_track_d,
)
from architect.track_d_wave2_extensions import run_track_d4_wave2
from architect.track_e_cpa_torsors import (
    _build_square_annulus_8tri,
    _rat_str,
    _rot90_ccw,
    _trace_straight_ray_to_line,
    run_track_e,
)


class _MasterTimeoutError(RuntimeError):
    pass


def _alarm_handler(signum: int, frame: object) -> None:
    _ = (signum, frame)
    raise _MasterTimeoutError("verify_all.py stage exceeded 20s wall-clock alarm")


def _run_stage(name: str, fn: Callable[[], dict[str, object]]) -> dict[str, object]:
    prev = signal.signal(signal.SIGALRM, _alarm_handler)
    signal.alarm(20)
    t0 = time.monotonic_ns()
    try:
        res = fn()
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, prev)
    elapsed_ms = (time.monotonic_ns() - t0) // 1_000_000
    return {"stage": name, "status": "PASS", "elapsed_ms": elapsed_ms, "payload": res}


def _snf_cert(mat: Sequence[Sequence[int]], snf: SNFResult | None = None) -> dict[str, object]:
    a_clean = [[int(v) for v in row] for row in mat]
    res = snf if snf is not None else smith_normal_form(a_clean)
    return {
        "A": a_clean,
        "U": res.U,
        "U_inv": res.U_inv,
        "S": res.S,
        "V": res.V,
        "V_inv": res.V_inv,
        "invariant_factors": list(res.invariant_factors),
    }


def _build_gate0_certificates(gate0: dict[str, object]) -> dict[str, dict[str, object]]:
    """Construct 100% machine-verifiable `CERTIFICATE_SCHEMA_V1` objects for Traps 1..7."""
    traps = gate0["traps"]  # type: ignore[index]

    # Trap 1: Strict 9-neuron MAX_4 over Z + Vol_4(Delta_4) mod 2 + 240-chamber Bakaev Z[1/2] realization
    bakaev_names = ("P1", "P2", "P3", "P4", "Q", "R13", "R14", "R23", "R24")
    pts_240: list[tuple[int, ...]] = []
    for prof in ((2, 5, 9, 14, 20), (2, 5, 13, 15, 18)):
        for perm in itertools.permutations(range(5)):
            pts_240.append(tuple(prof[perm[i]] for i in range(5)))
    m_bakaev_240 = [[eval_bakaev_2max5_terms(pt)[nm] for nm in bakaev_names] for pt in pts_240]
    b_max5_240 = [max(pt) for pt in pts_240]
    cert_trap1: dict[str, object] = {
        "sub_certificates": {
            "max4_strict_9neuron_z_network": {
                "W1": [list(r) for r in MAX4_W1],
                "W2": [list(r) for r in MAX4_W2],
                "w_out": list(MAX4_W3),
                "out_denom": 1,
                "n_dim": 4,
                "target_scale": 1,
            },
            "delta4_vol4_mod2": {
                "simplices": [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]],
                "expected_volume": 1,
                "modulus": 2,
                "expected_mod_residue": 1,
            },
            "bakaev_2max5_z_half_realization": {
                "A": m_bakaev_240,
                "b": b_max5_240,
                "c_num": [1, 1, 1, 1, 1, -1, -1, -1, -1],
                "c_den": 2,
            },
        }
    }

    # Trap 2: Odd denominator clearing M = 27 == 1 (mod 2) -> Vol_4(27 * Delta_4) = 27^4 = 531441 == 1 (mod 2)
    cert_trap2: dict[str, object] = {
        "simplices": [[[27, 0, 0, 0], [0, 27, 0, 0], [0, 0, 27, 0], [0, 0, 0, 27]]],
        "expected_volume": 531441,
        "modulus": 2,
        "expected_mod_residue": 1,
    }

    # Trap 3: Exact signed Farkas obstruction y_signed^T A_eq == 0, y_signed^T b_eq != 0 across all <=4-var B_5 atoms on {0,1}^5
    pts_01 = [[(mask >> i) & 1 for i in range(5)] for mask in range(32)]
    cols_b5 = [[1] * 32]
    for r_sz in range(1, 5):
        for comb in itertools.combinations(range(5), r_sz):
            cols_b5.append([max(pt[i] for i in comb) for pt in pts_01])
    a_eq_b5 = [[cols_b5[c][r] for c in range(len(cols_b5))] for r in range(32)]
    b_eq_max5 = [0 if mask == 0 else 1 for mask in range(32)]
    cube32_y = [int(v) for v in traps["trap_3_mandatory_off_braid_spurious_hinges"]["farkas_witness_cube32"]]
    cert_trap3: dict[str, object] = {
        "A_eq": a_eq_b5,
        "b_eq": b_eq_max5,
        "y_signed": cube32_y,
    }

    # Trap 4: A_1 singular cone SNF [1,2] + Reeve T_5 primal [1,1,5] & polar [1,5,5] unimodular SNFs
    cert_trap4: dict[str, object] = {
        "sub_certificates": {
            "a1_singular_cone_snf": _snf_cert([[1, 0], [-1, 2]]),
            "reeve_T5_primal_snf": _snf_cert([[1, 0, 0], [0, 1, 0], [1, 1, 5]]),
            "reeve_T5_polar_snf": _snf_cert([[0, 0, 1], [0, -5, 1], [5, 0, -1]]),
        }
    }

    # Trap 5: Exact W = |C_5|^2 = 25 1-layer pure-Z {0,1}-indicator lookup realization
    c5_cayley = [[(g + h) % 5 for h in range(5)] for g in range(5)]
    w1_triv_25: list[list[int]] = []
    for g in range(5):
        for h in range(5):
            row10 = [0] * 10
            row10[g] = 1
            row10[5 + h] = 1
            w1_triv_25.append(row10)
    w2_triv_25 = [[1 if (g + h) % 5 == c else 0 for g in range(5) for h in range(5)] for c in range(5)]
    cert_trap5: dict[str, object] = {
        "cayley": c5_cayley,
        "W1": w1_triv_25,
        "b1": [-1] * 25,
        "W2": w2_triv_25,
        "b2": [0] * 5,
        "mode": "indicator",
    }

    # Trap 6: Spiderweb m=2 unclamped nodal SNF [1,2,2,2] + 6-triangle annulus rank-3 monodromy SNF [1,1,2]
    ann_verts = ((1, 0), (0, 1), (-1, -1), (2, 0), (0, 2), (-2, -2))
    int_edges = ((0, 4), (1, 4), (1, 5), (2, 5), (2, 3), (0, 3))
    j_mono_3x6 = [[0] * 6 for _ in range(3)]
    for k, (ia, ib) in enumerate(int_edges):
        px, py = ann_verts[ia]
        qx, qy = ann_verts[ib]
        (nx, ny), _ = primitive_direction((-(qy - py), qx - px))
        j_mono_3x6[0][k] = nx
        j_mono_3x6[1][k] = ny
        j_mono_3x6[2][k] = -(nx * px + ny * py)
    cert_trap6: dict[str, object] = {
        "sub_certificates": {
            "spiderweb_m2_nodal_snf": _snf_cert([[1, 0, 0, 0], [1, 2, 0, 0], [1, 0, 2, 0], [1, 0, -2, -2]]),
            "annulus_6tri_monodromy_snf": _snf_cert(j_mono_3x6),
        }
    }

    # Trap 7: Forward-invariant 16-triangle octagonal annulus global vertex-LP Farkas witness + closed 1-cocycle d^1 eta == 0
    oct_ann = build_forward_invariant_octagonal_annulus()
    o_verts: list[tuple[int, int]] = oct_ann["verts"]  # type: ignore[assignment]
    o_fverts: list[tuple[int, int]] = oct_ann["f_verts"]  # type: ignore[assignment]
    o_tris: list[tuple[int, int, int]] = oct_ann["tris"]  # type: ignore[assignment]
    edge_set = {(min(u, w), max(u, w)) for (a, b, c) in o_tris for (u, w) in ((a, b), (b, c), (a, c))}
    edges_sorted = sorted(edge_set)
    e_idx = {e: idx for idx, e in enumerate(edges_sorted)}

    a_glob: list[list[int]] = []
    b_glob: list[int] = []
    a_eq_coc: list[list[int]] = []
    b_eq_coc: list[int] = []
    a_ub_coc: list[list[int]] = []
    b_ub_coc: list[int] = []
    for a, b, c in o_tris:
        s_ab, c_ab = (1, e_idx[(a, b)]) if a < b else (-1, e_idx[(b, a)])
        s_bc, c_bc = (1, e_idx[(b, c)]) if b < c else (-1, e_idx[(c, b)])
        s_ac, c_ac = (1, e_idx[(a, c)]) if a < c else (-1, e_idx[(c, a)])
        eq_r = [0] * len(edges_sorted)
        eq_r[c_ab] += s_ab
        eq_r[c_bc] += s_bc
        eq_r[c_ac] -= s_ac
        a_eq_coc.append(eq_r)
        b_eq_coc.append(0)

        xa, ya = o_verts[a]
        xb, yb = o_verts[b]
        xc, yc = o_verts[c]
        dx_b, dy_b = xb - xa, yb - ya
        dx_c, dy_c = xc - xa, yc - ya
        area2 = dx_b * dy_c - dy_b * dx_c
        for vp in (a, b, c):
            fx, fy = o_fverts[vp]
            cab = dy_c * fx - dx_c * fy
            cac = -dy_b * fx + dx_b * fy
            rv = [0] * len(o_verts)
            rv[a] -= cab + cac
            rv[b] += cab
            rv[c] += cac
            a_glob.append(rv)
            b_glob.append(-area2)
            ru = [0] * len(edges_sorted)
            ru[c_ab] += cab * s_ab
            ru[c_ac] += cac * s_ac
            a_ub_coc.append(ru)
            b_ub_coc.append(-area2)

    lp_g7 = solve_lp(A_ub=a_glob, b_ub=b_glob)
    lp_c7 = solve_lp(A_ub=a_ub_coc, b_ub=b_ub_coc, c_max=None, A_eq=a_eq_coc, b_eq=b_eq_coc)
    assert lp_g7.farkas_y is not None and lp_c7.primal_num is not None
    cert_trap7: dict[str, object] = {
        "sub_certificates": {
            "global_vertex_lp_farkas": {
                "A_ub": a_glob,
                "b_ub": b_glob,
                "y": list(lp_g7.farkas_y),
            },
            "closed_1cocycle_coboundary_zero": {
                "A": a_eq_coc,
                "b": b_eq_coc,
                "c_num": list(lp_c7.primal_num),
                "c_den": lp_c7.primal_den,
            },
        }
    }

    return {
        "TRAP_1": cert_trap1,
        "TRAP_2": cert_trap2,
        "TRAP_3": cert_trap3,
        "TRAP_4": cert_trap4,
        "TRAP_5": cert_trap5,
        "TRAP_6": cert_trap6,
        "TRAP_7": cert_trap7,
    }


def _build_track_certificates(
    track_a: dict[str, object],
    track_b: dict[str, object],
    track_c: dict[str, object],
    track_d: dict[str, object],
    track_e: dict[str, object],
) -> dict[str, dict[str, object]]:
    """Construct 100% machine-verifiable `CERTIFICATE_SCHEMA_V1` objects for all 14 Track A-E claims."""
    a2 = track_a["max6_and_syl2"]  # type: ignore[index]
    b1 = track_b["theorem_b1"]  # type: ignore[index]
    c2 = track_c["theorem_c2"]  # type: ignore[index]
    d2 = track_d["theorem_d2"]  # type: ignore[index]
    e1 = track_e["theorem_e1"]  # type: ignore[index]
    e2 = track_e["theorem_e2"]  # type: ignore[index]

    # B1: Reeve T_2, T_5, T_12 primal & polar unimodular SNF certificates
    cert_b1: dict[str, object] = {"sub_certificates": b1["unimodular_snf_certificates"]}

    # B2: Exact Chvatal-Gomory multiplier cuts + Klein sail vertices {(2,1), (2,2), (3,1)} on Sigma_*^(1)
    cert_b2: dict[str, object] = {
        "A_ge": [[-1, 3], [1, 0], [0, 2], [2, -1]],
        "b_ge": [0, 1, 0, 2],
        "cuts": [
            {"lam_num": [2, 0, 0, 1], "lam_den": 5, "cut_lhs": [0, 1], "cut_rhs": 1},
            {"lam_num": [1, 0, 0, 3], "lam_den": 5, "cut_lhs": [1, 0], "cut_rhs": 2},
        ],
        "hull_vertices": [[2, 1], [2, 2], [3, 1]],
    }

    # C1: Unimodular SNF certificates of unclamped nodal evaluation maps on spiderweb m=2, twisted wheel m=4, Desargues m=3
    ops_sw2 = build_airy_cosheaf_complex(_make_spiderweb(2))
    ops_tw4 = build_airy_cosheaf_complex(_make_primitive_twisted_wheel(4))
    ops_des3 = build_airy_cosheaf_complex(_make_desargues_prism(3))
    cert_c1: dict[str, object] = {
        "sub_certificates": {
            "spiderweb_m2_nodal_snf": _snf_cert(ops_sw2["ev_nodal"], ops_sw2["snf_ev"]),  # type: ignore[arg-type]
            "twisted_wheel_m4_nodal_snf": _snf_cert(ops_tw4["ev_nodal"], ops_tw4["snf_ev"]),  # type: ignore[arg-type]
            "desargues_m3_nodal_snf": _snf_cert(ops_des3["ev_nodal"], ops_des3["snf_ev"]),  # type: ignore[arg-type]
        }
    }

    # C2: Global Z-saturation projector idempotent certificate on subdivided annulus b=2
    cert_c2: dict[str, object] = c2["annulus_b2_saturation_certificate"]  # type: ignore[assignment]

    # E0: Exact 0/1-error outward-spiraling Poincare trajectory segments + cell/Clarke negative dots
    ann_e0 = _build_square_annulus_8tri(r_in=1, r_out=2)
    grads_e0: list[tuple[int, int]] = ann_e0["grads"]  # type: ignore[assignment]
    f_e0: list[tuple[int, int]] = []
    for k in range(4):
        fk = _rot90_ccw((1, 20), k)
        f_e0.extend([fk, fk])
    dots_e0: list[int] = [dot_int(grads_e0[t], f_e0[t]) for t in range(8)]
    for k in range(4):
        kn = (k + 1) % 4
        for ta, tb in ((2 * k, 2 * k + 1), (2 * k + 1, 2 * kn)):
            for gs in (grads_e0[ta], grads_e0[tb]):
                for fs in (f_e0[ta], f_e0[tb]):
                    dots_e0.append(dot_int(gs, fs))
    corner_lines = [(1, -1, 0), (1, 1, 0), (1, -1, 0), (1, 1, 0)]
    cur_e0: tuple[tuple[int, int], tuple[int, int]] = ((1, 1), (-1, 1))
    segs_e0: list[dict[str, object]] = []
    for k in range(4):
        vel = f_e0[2 * k]
        dt, nxt_e0 = _trace_straight_ray_to_line(cur_e0, vel, corner_lines[k])
        segs_e0.append({
            "p_start": [_rat_str(*cur_e0[0]), _rat_str(*cur_e0[1])],
            "velocity": [vel[0], vel[1]],
            "dt": _rat_str(*dt),
            "p_end": [_rat_str(*nxt_e0[0]), _rat_str(*nxt_e0[1])],
        })
        cur_e0 = nxt_e0
    cert_e0: dict[str, object] = {
        "mode": "outward_counterexample",
        "segments": segs_e0,
        "cell_and_crease_dots": dots_e0,
    }

    # E1: Global CPA Farkas witness + exact 8-segment Poincare contraction trajectories from r=2 and r=6 toward r*=10/3
    ann_e1 = _build_square_annulus_8tri(r_in=2, r_out=6)
    grads_e1: list[tuple[int, int]] = ann_e1["grads"]  # type: ignore[assignment]
    f_e1: list[tuple[int, int]] = []
    for k in range(4):
        f_e1.append(_rot90_ccw((-1, 10), k))
        f_e1.append(_rot90_ccw((1, 10), k))
    dots_e1: list[int] = [dot_int(grads_e1[t], f_e1[t]) for t in range(8)]
    for k in range(4):
        kn = (k + 1) % 4
        for ta, tb in ((2 * k, 2 * k + 1), (2 * k + 1, 2 * kn)):
            for gs in (grads_e1[ta], grads_e1[tb]):
                for fs in (f_e1[ta], f_e1[tb]):
                    dots_e1.append(dot_int(gs, fs))
    diag_lines_e1 = [(*_rot90_ccw((2, -1), k), 6) for k in range(4)]

    def _trace_e1_lap(r0: int) -> list[dict[str, object]]:
        pt: tuple[tuple[int, int], tuple[int, int]] = ((r0, 1), (-r0, 1))
        segs: list[dict[str, object]] = []
        for k in range(4):
            v_out = f_e1[2 * k]
            dt1, pm = _trace_straight_ray_to_line(pt, v_out, diag_lines_e1[k])
            if dt1[0] > 0:
                segs.append({
                    "p_start": [_rat_str(*pt[0]), _rat_str(*pt[1])],
                    "velocity": [v_out[0], v_out[1]],
                    "dt": _rat_str(*dt1),
                    "p_end": [_rat_str(*pm[0]), _rat_str(*pm[1])],
                })
            v_in = f_e1[2 * k + 1]
            dt2, pq = _trace_straight_ray_to_line(pm, v_in, corner_lines[k])
            if dt2[0] > 0:
                segs.append({
                    "p_start": [_rat_str(*pm[0]), _rat_str(*pm[1])],
                    "velocity": [v_in[0], v_in[1]],
                    "dt": _rat_str(*dt2),
                    "p_end": [_rat_str(*pq[0]), _rat_str(*pq[1])],
                })
            pt = pq
        return segs

    cert_e1: dict[str, object] = {
        "sub_certificates": {
            "global_cpa_farkas": e1["global_cpa_farkas_witness"],
            "poincare_inner_rim_r2_contraction": {
                "mode": "contraction",
                "r_star": "10/3",
                "segments": _trace_e1_lap(2),
                "cell_and_crease_dots": dots_e1,
            },
            "poincare_outer_rim_r6_contraction": {
                "mode": "contraction",
                "r_star": "10/3",
                "segments": _trace_e1_lap(6),
                "cell_and_crease_dots": dots_e1,
            },
        }
    }

    # E2: Twisted Mobius M_3 Z_{-1} coboundary unimodular SNF certificate [1,1,1,1,1,2]
    cert_e2: dict[str, object] = e2["primary_M3_snf_certificate"]  # type: ignore[assignment]

    # A1: Explicit 10 unimodular staircase 5-simplices of Delta_2 x Delta_3 -> Vol_5 == 10 == 1 (mod 3)
    d2_v = [[0, 0], [1, 0], [0, 1]]
    d3_v = [[0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 0, 1]]
    staircase_10: list[list[list[int]]] = []
    for east_steps in itertools.combinations(range(5), 2):
        east_set = set(east_steps)
        ic, jc = 0, 0
        simp5: list[list[int]] = []
        for s_idx in range(5):
            if s_idx in east_set:
                ic += 1
            else:
                jc += 1
            simp5.append(d2_v[ic] + d3_v[jc])
        staircase_10.append(simp5)
    cert_a1: dict[str, object] = {
        "simplices": staircase_10,
        "expected_volume": 10,
        "modulus": 3,
        "expected_mod_residue": 1,
    }

    # A2 (CERTIFIED_EXACT): Pure-Z 6*MAX_6 & Z[1/6] MAX_6 linear realizations on 92 x 11 Syl_2(S_6) system
    m_syl2: list[list[int]] = a2["fixed_dict_mod3_witness"]["A"]  # type: ignore[index]
    b_syl2: list[int] = a2["fixed_dict_mod3_witness"]["b"]  # type: ignore[index]
    sol_6x = solve_s_integral(m_syl2, [6 * v for v in b_syl2], inverted_primes=(), run_f3_prescreen=True)
    sol_1x_z6 = solve_s_integral(m_syl2, b_syl2, inverted_primes=(2, 3), run_f3_prescreen=False)
    assert sol_6x.c_num is not None and sol_1x_z6.c_num is not None
    cert_a2_sat: dict[str, object] = {
        "sub_certificates": {
            "pure_z_6max6_syl2": {
                "A": m_syl2,
                "b": [6 * v for v in b_syl2],
                "c_num": list(sol_6x.c_num),
                "c_den": sol_6x.c_den,
            },
            "z_sixth_max6_syl2": {
                "A": m_syl2,
                "b": b_syl2,
                "c_num": list(sol_1x_z6.c_num),
                "c_den": sol_1x_z6.c_den,
            },
        }
    }

    # A2 (OPEN_BUDGET_EXCEEDED): p=3 valuation obstruction on fixed 11-orbit D_6 dictionary over Z[1/2]
    cert_a2_open: dict[str, object] = a2["fixed_dict_mod3_witness"]  # type: ignore[assignment]

    # A3: Vol_4(Delta_4) = 1 == 1 (mod 2) Z-obstruction + 9-block Z[1/2] realization across all 120 signed 4D cones
    bakaev_names = ("P1", "P2", "P3", "P4", "Q", "R13", "R14", "R23", "R24")
    m_d4_120: list[list[int]] = []
    b_d4_120: list[int] = []
    for p5 in itertools.permutations((-13, -5, 2, 7, 19)):
        sh = p5[4]
        y4 = [p5[i] - sh for i in range(4)]
        ev = eval_bakaev_2max5_terms([y4[0], y4[1], y4[2], y4[3], 0])
        m_d4_120.append([ev[nm] for nm in bakaev_names])
        b_d4_120.append(max(0, y4[0], y4[1], y4[2], y4[3]))
    cert_a3: dict[str, object] = {
        "sub_certificates": {
            "delta4_vol4_mod2_unsat_z": {
                "simplices": [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]],
                "expected_volume": 1,
                "modulus": 2,
                "expected_mod_residue": 1,
            },
            "delta4_9block_z_half_sat": {
                "A": m_d4_120,
                "b": b_d4_120,
                "c_num": [1, 1, 1, 1, 1, -1, -1, -1, -1],
                "c_den": 2,
            },
        }
    }

    # D1: Explicit compressed pure-Z C_5 indicator circuit (W=8 < 25) + zero-bias S_3 permutation circuit (W=9 < 36)
    c5_cay = [[(g + h) % 5 for h in range(5)] for g in range(5)]
    w1_c5_8 = [[0, 1, 2, 3, 4, 0, 1, 2, 3, 4] for _ in range(8)]
    b1_c5_8 = [-t for t in range(8)]
    w2_c5_8 = [[0] * 8 for _ in range(5)]
    b2_c5_8 = [1, 0, 0, 0, 0]
    w2_c5_8[0][0] -= 1
    w2_c5_8[0][1] += 1
    for m_val in range(1, 7):
        tgt = m_val % 5
        w2_c5_8[tgt][m_val - 1] += 1
        w2_c5_8[tgt][m_val] -= 2
        w2_c5_8[tgt][m_val + 1] += 1
    w2_c5_8[7 % 5][6] += 1
    w2_c5_8[7 % 5][7] -= 2
    w2_c5_8[8 % 5][7] += 1

    s3_grp = make_s3_group()
    s3_perms = s3_grp.perm_images
    s3_pa: list[list[int]] = []
    for g in range(6):
        vec3 = [0, 0, 0]
        for k_idx in range(3):
            vec3[s3_perms[g][k_idx]] = k_idx + 1
        s3_pa.append(vec3)
    w1_s3_9: list[list[int]] = []
    for i_out in range(3):
        for k_in in range(3):
            r12 = [0] * 12
            for g in range(6):
                r12[g] = 0 if s3_perms[g][k_in] == i_out else -3
            for h in range(6):
                r12[6 + h] = s3_pa[h][k_in]
            w1_s3_9.append(r12)
    w2_s3_9 = [[s3_pa[c][i_out] for i_out in range(3) for _ in range(3)] for c in range(6)]

    cert_d1: dict[str, object] = {
        "sub_certificates": {
            "c5_biased_w8_indicator_z": {
                "cayley": c5_cay,
                "W1": w1_c5_8,
                "b1": b1_c5_8,
                "W2": w2_c5_8,
                "b2": b2_c5_8,
                "compressed": True,
                "mode": "indicator",
            },
            "s3_biequivariant_w9_argmax_z": {
                "cayley": [list(r) for r in s3_grp.cayley],
                "W1": w1_s3_9,
                "b1": [0] * 9,
                "W2": w2_s3_9,
                "b2": [0] * 6,
                "compressed": True,
                "mode": "strict_argmax",
            },
        }
    }

    # D2: V_4 Hadamard [1,2,2,4] + S_3 proper-coset [1,1,1,1,1,3] + Q_8 rank-4 proper-coset SNFs
    c_s3 = _build_nontrivial_coset_feature_matrix(make_s3_group())
    c_q8 = _build_nontrivial_coset_feature_matrix(make_q8_group())
    cert_d2: dict[str, object] = {
        "sub_certificates": {
            "v4_hadamard_snf": d2["v4_hadamard_snf_certificate"],
            "s3_proper_coset_snf": _snf_cert(c_s3),
            "q8_proper_coset_rank4_snf": _snf_cert(c_q8),
        }
    }

    # D3: 100-row short-orbit strict-argmax Farkas Dual + Eisenstein p=5 on Phi_5(y+1) = 5 + 10y + 10y^2 + 5y^3 + y^4
    a_d3_ub: list[list[int]] = []
    b_d3_ub: list[int] = []
    for g in range(5):
        for h in range(5):
            t_out = (g + h) % 5
            for k_other in range(5):
                if k_other == t_out:
                    continue
                row50 = [0] * 50
                row50[5 * k_other + g] += 1
                row50[25 + 5 * k_other + h] += 1
                row50[5 * t_out + g] -= 1
                row50[25 + 5 * t_out + h] -= 1
                a_d3_ub.append(row50)
                b_d3_ub.append(-1)
    lp_d3 = solve_lp(a_d3_ub, b_d3_ub)
    assert lp_d3.farkas_y is not None
    cert_d3: dict[str, object] = {
        "sub_certificates": {
            "c5_short_orbit_strict_argmax_farkas": {
                "A_ub": a_d3_ub,
                "b_ub": b_d3_ub,
                "y": list(lp_d3.farkas_y),
            },
            "phi5_shifted_eisenstein_p5": {
                "poly_coeffs_low_to_high": [5, 10, 10, 5, 1],
                "prime": 5,
            },
        }
    }

    return {
        "B1": cert_b1,
        "B2": cert_b2,
        "C1": cert_c1,
        "C2": cert_c2,
        "E0": cert_e0,
        "E1": cert_e1,
        "E2": cert_e2,
        "A1": cert_a1,
        "A2_MAX6_Z_SIXTH_AND_SYL2_ENGINE": cert_a2_sat,
        "A2_MAX6_Z_HALF_FRONTIER": cert_a2_open,
        "A3": cert_a3,
        "D1": cert_d1,
        "D2": cert_d2,
        "D3": cert_d3,
    }


def build_theorem_ledger_v1(
    gate0: dict[str, object],
    track_a: dict[str, object],
    track_b: dict[str, object],
    track_c: dict[str, object],
    track_d: dict[str, object],
    track_e: dict[str, object],
) -> dict[str, object]:
    """Assemble the 100%-certified 3-valued Brave & Humble Epistemic Ledger (`artifacts/theorem_ledger_v1.json`)."""
    g0_traps = gate0["traps"]  # type: ignore[index]
    g0_certs = _build_gate0_certificates(gate0)
    tr_certs = _build_track_certificates(track_a, track_b, track_c, track_d, track_e)

    a1 = track_a["theorem_a1"]  # type: ignore[index]
    a2 = track_a["max6_and_syl2"]  # type: ignore[index]
    a3 = track_a["theorem_a3"]  # type: ignore[index]
    b1 = track_b["theorem_b1"]  # type: ignore[index]
    b2 = track_b["theorem_b2"]  # type: ignore[index]
    c1 = track_c["theorem_c1"]  # type: ignore[index]
    c2 = track_c["theorem_c2"]  # type: ignore[index]
    d1 = track_d["theorem_d1"]  # type: ignore[index]
    d2 = track_d["theorem_d2"]  # type: ignore[index]
    d3 = track_d["theorem_d3"]  # type: ignore[index]
    e0 = track_e["counterexample_e0"]  # type: ignore[index]
    e1 = track_e["theorem_e1"]  # type: ignore[index]
    e2 = track_e["theorem_e2"]  # type: ignore[index]

    theorems: list[dict[str, object]] = [
        {
            "id": "TRAP_1",
            "track": "Gate_Zero",
            "title": "Gate 0 Trap 1: Strict 9-Neuron MAX_4 over Z vs MAX_5 Parity Obstruction & Bakaev Z[1/2] Identity",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": g0_traps["trap_1_max4_z_vs_max5_z_and_z_half"]["elapsed_us"],
            "certificate": g0_certs["TRAP_1"],
            "witness_summary": {"max4_neurons": [6, 3], "vol4_delta4": 1, "bakaev_terms": 9},
        },
        {
            "id": "TRAP_2",
            "track": "Gate_Zero",
            "title": "Gate 0 Trap 2: Asymptotic Recession + Vol_4 mod 2 Modular Refuter for Rational-Bias Z_(2) Networks",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "simplex_triangulation_volume",
            "elapsed_us": g0_traps["trap_2_unrestricted_rational_biases_refuter"]["elapsed_us"],
            "certificate": g0_certs["TRAP_2"],
            "witness_summary": g0_traps["trap_2_unrestricted_rational_biases_refuter"]["candidate_1_refutation"],
        },
        {
            "id": "TRAP_3",
            "track": "Gate_Zero",
            "title": "Gate 0 Trap 3: Mandatory Off-Braid Spurious Hinges (B_5-Conforming Farkas Obstruction)",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "farkas_eq",
            "elapsed_us": g0_traps["trap_3_mandatory_off_braid_spurious_hinges"]["elapsed_us"],
            "certificate": g0_certs["TRAP_3"],
            "witness_summary": {
                "b5_unsat_over_q": True,
                "z_half_augmented_den": g0_traps["trap_3_mandatory_off_braid_spurious_hinges"]["z_half_augmented_den"],
            },
        },
        {
            "id": "TRAP_4",
            "track": "Gate_Zero",
            "title": "Gate 0 Trap 4: Primitive Dual-Lattice Normals & Lineality Quotient in D_Sigma(f)",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": g0_traps["trap_4_primitive_normals_weil_cartier"]["elapsed_us"],
            "certificate": g0_certs["TRAP_4"],
            "witness_summary": {"a1_torsion": [2], "reeve_T5_polar_snf": [1, 5, 5]},
        },
        {
            "id": "TRAP_5",
            "track": "Gate_Zero",
            "title": "Gate 0 Trap 5: Trivial W = |G|^2 Realization & Mandatory Compression Width Guard",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "group_circuit",
            "elapsed_us": g0_traps["trap_5_trivial_w_g2_group_circuit_guard"]["elapsed_us"],
            "certificate": g0_certs["TRAP_5"],
            "witness_summary": g0_traps["trap_5_trivial_w_g2_group_circuit_guard"]["guard_rejections_verified"],
        },
        {
            "id": "TRAP_6",
            "track": "Gate_Zero",
            "title": "Gate 0 Trap 6: Spiderweb Cokernel Torsion & Repaired 6-Triangle Annular Monodromy",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": g0_traps["trap_6_spiderweb_torsion_and_annular_monodromy"]["elapsed_us"],
            "certificate": g0_certs["TRAP_6"],
            "witness_summary": {
                "wheel_unclamped_nodal_snf": [1, 2, 2, 2],
                "annulus_free_monodromy_rank": 3,
            },
        },
        {
            "id": "TRAP_7",
            "track": "Gate_Zero",
            "title": "Gate 0 Trap 7: Annular CPA Torsor LOCAL_SAT vs Global Vertex-LP INFEASIBLE",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": g0_traps["trap_7_annular_cpa_torsor_vs_global_lp"]["elapsed_us"],
            "certificate": g0_certs["TRAP_7"],
            "witness_summary": {
                "global_vertex_lp_status": "INFEASIBLE",
                "torsor_cocycle_status": "LOCAL_SAT",
                "torsor_period_H1_Q": g0_traps["trap_7_annular_cpa_torsor_vs_global_lp"]["torsor_period_H1_Q"],
            },
        },
        {
            "id": "B1",
            "track": "B",
            "title": "Weil vs. Cartier, Reeve Polar Torsion & Integral BSS Degree-1 Splines",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": b1["elapsed_us"],
            "certificate": tr_certs["B1"],
            "witness_summary": {
                "reeve_r_range": [2, 12],
                "primal_snf_template": ["1", "1", "r"],
                "polar_snf_template": ["1", "r", "r"],
                "three_ray_dim_B": 1,
            },
        },
        {
            "id": "B2",
            "track": "B",
            "title": "Fractional Vertices, Klein Sail & Chvatal-Gomory Rank Split Inside Cart(Sigma)",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "cg_cuts",
            "elapsed_us": b2["elapsed_us"],
            "certificate": tr_certs["B2"],
            "witness_summary": {
                "sigma_star_k1_lp_vertex": b2["sigma_star_k1_highlight"]["lp_vertex_ut"],
                "sigma_star_k1_sequential_gomory_rank": 2,
                "four_ray_simultaneous_chvatal_rank_k1_to_10": 1,
                "five_ray_simultaneous_chvatal_ranks_k1_to_3": [3, 5, 7],
                "klein_sail_k1": b2["sigma_star_k1_highlight"]["klein_sail_vertices"],
            },
        },
        {
            "id": "C1",
            "track": "C",
            "title": "Saturated Integral Airy Sequence & Non-Primitive Geometric Force Torsion",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": c1["elapsed_us"],
            "certificate": tr_certs["C1"],
            "witness_summary": {
                "spiderwebs_verified": [2, 3, 4, 6],
                "spiderweb_m2_nodal_snf": [1, 2, 2, 2],
                "annulus_b2_monodromy_rank": 3,
                "double_punctured_b3_monodromy_rank": 6,
            },
        },
        {
            "id": "C2",
            "track": "C",
            "title": "2D Precision-Bockstein Digit-SNF Dictionary & Global Z-Saturation Idempotents",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "saturation_projector",
            "elapsed_us": c2["elapsed_us"],
            "certificate": tr_certs["C2"],
            "witness_summary": {
                "primes_tested": [2, 3],
                "scales_tested": [1, 2, 3],
                "desargues_h1_torsion": c2["complex_dictionaries"]["desargues_prism_m3"]["h1_torsion_factors"],
            },
        },
        {
            "id": "E0",
            "track": "E",
            "title": "Counterexample E0: The Outward-Spiraling Escher Waterfall",
            "epistemic_tag": "FALSIFIED_COUNTEREXAMPLE",
            "status": "FALSIFIED_COUNTEREXAMPLE",
            "certificate_kind": "poincare_trajectory",
            "elapsed_us": e0["elapsed_us"],
            "certificate": tr_certs["E0"],
            "witness_summary": {
                "claim_refuted": e0["claim_refuted"],
                "torsor_period_H1": e0["torsor_period_H1"],
                "max_cell_and_filippov_derivative": e0["max_cell_and_filippov_derivative"],
                "initial_point_x0": e0["initial_point_x0"],
                "return_point_P_x0": e0["return_point_P_x0"],
                "exact_1_lap_expansion_ratio": e0["exact_1_lap_expansion_ratio"],
                "evaluation_error": "0/1",
            },
        },
        {
            "id": "E1",
            "track": "E",
            "title": "Orientable Annulus Torsor Transit + Pinned-Torsor Poincare Contraction",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": e1["elapsed_us"],
            "certificate": tr_certs["E1"],
            "witness_summary": {
                "torsor_period_H1": e1["torsor_period_H1"],
                "limit_cycle_r_star": e1["limit_cycle_cut_radius_r_star"],
                "poincare_1_lap_contraction_factor": e1["poincare_contraction_factor"],
            },
        },
        {
            "id": "E2",
            "track": "E",
            "title": "Non-Orientable Mobius Quotient — Genuine Z/2Z Sheaf Torsion",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "snf_unimodular",
            "elapsed_us": e2["elapsed_us"],
            "certificate": tr_certs["E2"],
            "witness_summary": {
                "M3_snf_delta0": [1, 1, 1, 1, 1, 2],
                "H1_Z_minus1": "Z/2Z",
                "H1_Q_minus1": "0",
            },
        },
        {
            "id": "A1",
            "track": "A",
            "title": "Minkowski & Valuation Functors and Vol_5(Delta_2 x Delta_3) = 10 == 1 (mod 3) Refutation",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "simplex_triangulation_volume",
            "elapsed_us": a1["elapsed_us"],
            "certificate": tr_certs["A1"],
            "witness_summary": {
                "minimal_annihilators": a1["minimal_annihilators"],
                "vol5_delta2_x_delta3": a1["vol5_beneath_beyond"],
                "vol5_mod_3": a1["vol5_mod_3"],
                "prime_power_d9_binom_gcd": a1["prime_power_d9_binom_gcd"],
            },
        },
        {
            "id": "A2_MAX6_Z_SIXTH_AND_SYL2_ENGINE",
            "track": "A",
            "title": "D_6-Equivariant 15-Pair Hexagon Realization of 6*MAX_6 over Z and <200ms Syl_2(S_6) Engine",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": a2["elapsed_us"],
            "certificate": tr_certs["A2_MAX6_Z_SIXTH_AND_SYL2_ENGINE"],
            "witness_summary": {
                "d6_orbit_count": a2["d6_orbit_count"],
                "total_expanded_gates": a2["total_expanded_gates"],
                "syl2_order": a2["syl2_order"],
                "syl2_braid_chamber_orbits": a2["syl2_braid_chamber_orbits"],
                "syl2_engine_elapsed_ms": a2["syl2_engine_elapsed_ms"],
            },
        },
        {
            "id": "A2_MAX6_Z_HALF_FRONTIER",
            "track": "A",
            "title": "Unrestricted MAX_6 in ReLU_{6,2}(Z[1/2]) Frontier Probe (Bounded D_6 Hexagon Dictionary UNSAT)",
            "epistemic_tag": "OPEN_BUDGET_EXCEEDED",
            "status": "OPEN_BUDGET_EXCEEDED",
            "certificate_kind": "padic_obstruction",
            "elapsed_us": a2["elapsed_us"],
            "certificate": tr_certs["A2_MAX6_Z_HALF_FRONTIER"],
            "finite_search_bounds": {
                "dictionary": "Fixed 11-orbit (105-gate) D_6-equivariant 15-pair hexagon gate dictionary",
                "fixed_dictionary_result": a2["fixed_dict_zhalf_probe_status"],
                "unrestricted_off_braid_arrangement_status": "OPEN_FOR_WAVE_II",
            },
        },
        {
            "id": "A3",
            "track": "A",
            "title": "Virtual Zonotope-Hull Complexity Separation vrc_{2,Z}(Delta_4) = +inf vs vrc_{2,Z[1/2]}(Delta_4) <= 9",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": a3["elapsed_us"],
            "certificate": tr_certs["A3"],
            "witness_summary": {
                "vrc_2_Z_delta4": "+infinity",
                "vrc_2_Z_half_delta4_upper_bound": 9,
                "signed_4d_cones_verified": 120,
            },
        },
        {
            "id": "D1",
            "track": "D",
            "title": "Strict-Argmax LCM Collapse, C_n Width 2n-2/2n-1 Pure-Z Circuits & W=m^2 Permutation Compression",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": d1["elapsed_us"],
            "certificate": tr_certs["D1"],
            "witness_summary": {
                "c5_biased_width": 8,
                "c5_unbiased_width": 9,
                "compressed_m2_widths": {"S_3": 9, "D_4": 16, "D_5": 25, "A_4": 16, "S_4": 16},
                "q8_w64_guard_triggered": True,
            },
        },
        {
            "id": "D2",
            "track": "D",
            "title": "Character & Proper-Coset Readout SNF Torsion Trichotomy (V_4, S_3, D_4, Q_8, S_4)",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": d2["elapsed_us"],
            "certificate": tr_certs["D2"],
            "witness_summary": {
                "v4_hadamard_snf": d2["v4_hadamard_snf"],
                "q8_coset_q_rank": 4,
                "s4_coset_torsion": [],
            },
        },
        {
            "id": "D3",
            "track": "D",
            "title": "C_5 Strict Equivariance Barrier (W >= 25 over R) vs Phi_5 Linear Bottleneck (2 vs 4)",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": d3["elapsed_us"],
            "certificate": tr_certs["D3"],
            "witness_summary": {
                "strict_equivariant_min_width_R": 25,
                "short_orbit_feature_rank": 9,
                "phi5_eisenstein_shifted_coeffs": d3["phi5_shifted_eisenstein_coeffs"],
                "d_emb_R": 2,
                "d_emb_Q": 4,
                "d_emb_Z": 4,
            },
        },
    ]

    counts = {
        "CERTIFIED_EXACT": sum(1 for t in theorems if t["epistemic_tag"] == "CERTIFIED_EXACT"),
        "FALSIFIED_COUNTEREXAMPLE": sum(1 for t in theorems if t["epistemic_tag"] == "FALSIFIED_COUNTEREXAMPLE"),
        "OPEN_BUDGET_EXCEEDED": sum(1 for t in theorems if t["epistemic_tag"] == "OPEN_BUDGET_EXCEEDED"),
    }
    return {
        "project": "Integral Tropical-Sheaf Torsion (Wave I v1.0)",
        "schema_version": "1.0",
        "total_claims": len(theorems),
        "certified_coverage_percent": 100,
        "tag_counts": counts,
        "theorems": theorems,
    }


def build_theorem_ledger_v2(
    v1_doc: dict[str, object],
    track_a2: dict[str, object],
    track_d4: dict[str, object],
) -> dict[str, object]:
    """Assemble Wave II `theorem_ledger_v2.json`: all 21 Wave I claims + 5 Wave II frontier claims (26 total)."""
    a2a: dict[str, object] = track_a2["theorem_a2a"]  # type: ignore[assignment]
    a2b: dict[str, object] = track_a2["theorem_a2b"]  # type: ignore[assignment]
    a2c: dict[str, object] = track_a2["theorem_a2c"]  # type: ignore[assignment]
    d4a: dict[str, object] = track_d4["theorem_d4a"]  # type: ignore[assignment]
    d4b: dict[str, object] = track_d4["theorem_d4b"]  # type: ignore[assignment]

    theorems_v2: list[dict[str, object]] = []
    for entry in v1_doc["theorems"]:  # type: ignore[attr-defined]
        item = dict(entry)
        if item.get("id") == "A2_MAX6_Z_HALF_FRONTIER":
            item["title"] = "Unconstrained ReLU_{6,2}(Z[1/2]) Open Frontier for MAX_6"
            item["epistemic_tag"] = "OPEN_BUDGET_EXCEEDED"
            item["status"] = "OPEN_BUDGET_EXCEEDED"
            item["finite_search_bounds"] = {
                "wave1_dictionary": "11-orbit (105-gate) D_6-equivariant 15-pair hexagon dictionary (UNSAT_MOD3)",
                "wave2_dictionaries": (
                    "615-orbit Syl_2(S_6) pairwise-M2 symbolic sub-chamber system (945x615, UNSAT_MOD3) "
                    "and nested Syl_2(S_6) Tiers 1 (321 orbits), 2 (364 orbits), and 3 (384 orbits, signed Layer-2) (all UNSAT_MOD3)"
                ),
                "unconstrained_arbitrary_off_braid_status": "OPEN_BUDGET_EXCEEDED",
            }
        theorems_v2.append(item)

    wave2_claims: list[dict[str, object]] = [
        {
            "id": "A2a",
            "track": "A2_Wave2",
            "title": "Join-Volume Arithmetic Dichotomy: (r_1! r_2!) | Vol_d(conv(Z_1 u Z_2)) and d=5 vs d=6 Prime-3 Threshold",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": a2a["elapsed_us"],
            "certificate": a2a["certificate"],
            "witness_summary": {
                "dimension_staircase": a2a["dimension_staircase"],
                "d5_22_zonotope_pair_vol": 4,
                "d5_22_mod_3": 1,
                "d6_32_zonotope_pair_vol": 12,
                "d6_all_convex_joins_divisible_by_6": True,
            },
        },
        {
            "id": "A2_TIER123_3ADIC_OBSTRUCTION",
            "track": "A2_Wave2",
            "title": "Syl_2(S_6) Tier 1-3 Bounded Zonotope-Pair Dictionary 3-Adic Valuation Obstruction",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": a2b["elapsed_us"],
            "certificate": a2b["certificate"],
            "witness_summary": {
                "syl2_order": a2b["syl2_order"],
                "syl2_chamber_orbits": a2b["syl2_chamber_orbits"],
                "pairwise_m2_symbolic_rows": 945,
                "pairwise_m2_orbits": 615,
                "finite_47ray_impostor_refuted": True,
                "tier_orbits": {"Tier_1": 321, "Tier_2": 364, "Tier_3": 384},
                "obstruction_prime": 3,
            },
        },
        {
            "id": "A2c",
            "track": "A2_Wave2",
            "title": "Finite-Arrangement Integral Paramid vs Zonotope-Pair Quotient SNF Tables (H_4, H_5, H_6)",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": a2c["elapsed_us"],
            "certificate": a2c["certificate"],
            "witness_summary": {
                "H4_paramids_max4_den": 2,
                "H4_zonotope22_max4_den": 1,
                "H5_D4_zonotope22_max5_den": 2,
                "H6_D6_zonotope22_max6_den": 6,
            },
        },
        {
            "id": "D4a",
            "track": "D4_Wave2",
            "title": "H^2(V_4; Z_2) 2-Cocycle & Shifted-Coset Cohomological Extension Compression (Q_8 W=17, Dic_3 W=25)",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": d4a["elapsed_us"],
            "certificate": d4a["certificate"],
            "witness_summary": {
                "q8_width_hierarchy": d4a["q8_width_hierarchy"],
                "d4_vs_q8_comparison": d4a["d4_vs_q8_comparison"],
                "dic3_extension_compression": d4a["dic3_extension_compression"],
            },
        },
        {
            "id": "D4b",
            "track": "D4_Wave2",
            "title": "Universal {0,1}-Indicator Gram Determinant |G|^{|G|}, W >= |G| Farkas Lower Bound & V_4 W=6 Torsion-Killing Surgery",
            "epistemic_tag": "CERTIFIED_EXACT",
            "status": "CERTIFIED_EXACT",
            "certificate_kind": "composite_dict",
            "elapsed_us": d4b["elapsed_us"],
            "certificate": d4b["certificate"],
            "witness_summary": {
                "constructive_width_table": d4b["constructive_width_table"],
                "v4_w6_feature_torsion_and_surgery": d4b["v4_w6_feature_torsion_and_surgery"],
            },
        },
    ]
    theorems_v2.extend(wave2_claims)

    counts_v2 = {
        "CERTIFIED_EXACT": sum(1 for t in theorems_v2 if t["epistemic_tag"] == "CERTIFIED_EXACT"),
        "FALSIFIED_COUNTEREXAMPLE": sum(1 for t in theorems_v2 if t["epistemic_tag"] == "FALSIFIED_COUNTEREXAMPLE"),
        "OPEN_BUDGET_EXCEEDED": sum(1 for t in theorems_v2 if t["epistemic_tag"] == "OPEN_BUDGET_EXCEEDED"),
    }
    return {
        "project": "Integral Tropical-Sheaf Torsion (Wave II v2.0)",
        "schema_version": "2.0",
        "total_claims": len(theorems_v2),
        "certified_coverage_percent": 100,
        "tag_counts": counts_v2,
        "theorems": theorems_v2,
    }


def main() -> int:
    t_all_ns = time.monotonic_ns()
    artifacts_dir = os.path.join(_ROOT, "artifacts")
    plots_dir = os.path.join(_ROOT, "plots")
    os.makedirs(artifacts_dir, exist_ok=True)
    os.makedirs(plots_dir, exist_ok=True)

    # 1. Architect Gate 0 + Wave I Tracks A, B, C, D, E + Wave II Tracks A2 & D4
    st_gate0 = _run_stage("gate0_wave1_sanity_traps", run_all_wave1_traps_and_flush)
    st_b = _run_stage("architect_track_b", run_track_b)
    st_c = _run_stage("architect_track_c", run_track_c)
    st_e = _run_stage("architect_track_e", run_track_e)
    st_a = _run_stage("architect_track_a", run_track_a)
    st_d = _run_stage("architect_track_d", run_track_d)
    st_a2_w2 = _run_stage("architect_track_a2_wave2", lambda: run_track_a2_wave2(flush_checkpoint=True))
    st_d4_w2 = _run_stage("architect_track_d4_wave2", lambda: run_track_d4_wave2(flush_checkpoint=True))

    # Flush Wave I Architect checkpoint & 100%-certified Theorem Ledgers v1 & v2 BEFORE peer suites!
    cycle2_arch_path = os.path.join(artifacts_dir, "cycle2_architect_tracks.json")
    cycle2_arch_doc = {
        "cycle": 2,
        "owner": "architect",
        "all_passed": True,
        "tracks": {
            "A": st_a["payload"],
            "B": st_b["payload"],
            "C": st_c["payload"],
            "D": st_d["payload"],
            "E": st_e["payload"],
        },
    }
    with open(cycle2_arch_path, "w", encoding="utf-8") as fh:
        json.dump(cycle2_arch_doc, fh, indent=2, sort_keys=True)

    def _assemble_and_self_verify_ledgers() -> dict[str, object]:
        doc_v1 = build_theorem_ledger_v1(
            gate0=st_gate0["payload"],  # type: ignore[arg-type]
            track_a=st_a["payload"],  # type: ignore[arg-type]
            track_b=st_b["payload"],  # type: ignore[arg-type]
            track_c=st_c["payload"],  # type: ignore[arg-type]
            track_d=st_d["payload"],  # type: ignore[arg-type]
            track_e=st_e["payload"],  # type: ignore[arg-type]
        )
        l1_path = os.path.join(artifacts_dir, "theorem_ledger_v1.json")
        with open(l1_path, "w", encoding="utf-8") as l1_fh:
            json.dump(doc_v1, l1_fh, indent=2, sort_keys=True)

        doc_v2 = build_theorem_ledger_v2(
            v1_doc=doc_v1,
            track_a2=st_a2_w2["payload"],  # type: ignore[arg-type]
            track_d4=st_d4_w2["payload"],  # type: ignore[arg-type]
        )
        l2_path = os.path.join(artifacts_dir, "theorem_ledger_v2.json")
        with open(l2_path, "w", encoding="utf-8") as l2_fh:
            json.dump(doc_v2, l2_fh, indent=2, sort_keys=True)

        cert_kernel = importlib.import_module("formalist.cert_kernel")
        for doc_chk in (doc_v1, doc_v2):
            for entry in doc_chk["theorems"]:  # type: ignore[attr-defined]
                cid = str(entry["id"])  # type: ignore[index]
                tag_str = str(entry["epistemic_tag"])  # type: ignore[index]
                cert_obj = entry.get("certificate")  # type: ignore[attr-defined]
                res_v = cert_kernel.verify_ledger_certificate(cert_obj, claim_id=cid, epistemic_tag=tag_str)
                if not res_v.get("verified", False):
                    raise AssertionError(f"Ledger self-verification failed on {cid}")
        return {"v1": doc_v1, "v2": doc_v2}

    st_ledger = _run_stage("theorem_ledgers_v1_v2_100pct_certificate_build", _assemble_and_self_verify_ledgers)
    ledger_v1_doc: dict[str, object] = st_ledger["payload"]["v1"]  # type: ignore[index,assignment]
    ledger_v2_doc: dict[str, object] = st_ledger["payload"]["v2"]  # type: ignore[index,assignment]
    stages_summary = [st_gate0, st_a, st_b, st_c, st_d, st_e, st_a2_w2, st_d4_w2, st_ledger]

    # 2. Simulator Parameterized Family Gate + Deterministic Vector Atlas (`plots/fig01..fig10`)
    sim_c3_path = os.path.join(_ROOT, "simulator", "run_cycle3_summary.py")
    if os.path.isfile(sim_c3_path):
        sim_mod = importlib.import_module("simulator.run_cycle3_summary")
        st_sim = _run_stage("simulator_cycle3_family_sweeps", sim_mod.run_cycle3_simulator_gate)
        stages_summary.append(st_sim)

    sim_atlas = importlib.import_module("simulator.svg_atlas")
    st_atlas = _run_stage("simulator_svg_atlas_generation", lambda: sim_atlas.generate_all_atlas_svgs(plots_dir))
    if st_atlas["payload"].get("status") != "PASS" or st_atlas["payload"].get("svg_count") != 10:  # type: ignore[union-attr]
        raise AssertionError(f"Simulator vector atlas generation failed: {st_atlas['payload']}")
    stages_summary.append(st_atlas)

    # 3. Formalist Independent Verification Suites (`proof_pack_v1.py` & `proof_pack_v2.py`)
    formalist_pp1 = importlib.import_module("formalist.proof_pack_v1")
    st_form1 = _run_stage("formalist_proof_pack_v1", formalist_pp1.run_all_verifications)
    if not st_form1["payload"]["all_passed"]:  # type: ignore[index]
        raise AssertionError("Formalist proof_pack_v1 reported failure")
    stages_summary.append(st_form1)

    formalist_pp2 = importlib.import_module("formalist.proof_pack_v2")
    st_form2 = _run_stage("formalist_proof_pack_v2", lambda: formalist_pp2.run_wave2_verification(flush_checkpoints=True))
    if not st_form2["payload"]["all_passed"]:  # type: ignore[index]
        raise AssertionError("Formalist proof_pack_v2 reported failure")
    stages_summary.append(st_form2)

    # 4. Inquisitor SVG Geometry Auditor + Wave II Torture Tests + AST & JSON Float Firewall + Cycle 1/2 Probes
    svg_auditor = importlib.import_module("inquisitor.svg_auditor")

    def _run_svg_geometry_audit() -> dict[str, object]:
        st_self = svg_auditor.run_svg_auditor_self_tests()
        st_plots = svg_auditor.audit_plots_directory(plots_dir, require_full_atlas=True)
        if st_self.get("status") != "PASS" or st_plots.get("status") != "PASS":
            raise AssertionError(f"SVG geometry auditor failed: self={st_self}, plots={st_plots}")
        return st_plots

    st_svg_audit = _run_stage("inquisitor_svg_geometry_auditor", _run_svg_geometry_audit)
    stages_summary.append(st_svg_audit)

    w2_torture = importlib.import_module("inquisitor.wave2_torture_tests")
    st_w2_torture = _run_stage(
        "inquisitor_wave2_torture_tests", lambda: w2_torture.run_all_wave2_torture_self_tests(_ROOT)
    )
    if st_w2_torture["payload"].get("status") != "PASS":  # type: ignore[union-attr]
        raise AssertionError(f"Inquisitor Wave II torture tests failed: {st_w2_torture['payload']}")
    stages_summary.append(st_w2_torture)

    ast_scanner = importlib.import_module("inquisitor.ast_scanner")

    def _run_inquisitor_gates() -> dict[str, object]:
        self_res = ast_scanner.run_scanner_self_tests()
        ws_res = ast_scanner.scan_workspace(_ROOT)
        json_floats = ast_scanner.scan_json_artifacts_for_floats(_ROOT)
        if self_res["status"] != "PASS" or ws_res["status"] != "PASS" or json_floats:
            raise AssertionError(f"AST or JSON float firewall failed: ws={ws_res}, json_floats={json_floats}")
        out_inq: dict[str, object] = {
            "scanned_python_files": ws_res["scanned_python_files"],
            "ast_violations": ws_res["total_violations"],
            "json_float_violations": len(json_floats),
        }
        c1_probes_path = os.path.join(_ROOT, "inquisitor", "cycle1_adversarial_probes.py")
        if os.path.isfile(c1_probes_path):
            c1_mod = importlib.import_module("inquisitor.cycle1_adversarial_probes")
            k_gt = c1_mod.run_kernel_ground_truth_probes()
            t_gt = c1_mod.run_traps_ground_truth_probes()
            if k_gt["status"] != "PASS" or t_gt["status"] != "PASS":
                raise AssertionError("Inquisitor Cycle 1 ground-truth probes failed")
            out_inq["cycle1_kernel_probes_passed"] = k_gt["probe_count"]
            out_inq["cycle1_trap_probes_passed"] = t_gt["probe_count"]

        c2_probes_path = os.path.join(_ROOT, "inquisitor", "cycle2_adversarial_probes.py")
        if os.path.isfile(c2_probes_path):
            c2_mod = importlib.import_module("inquisitor.cycle2_adversarial_probes")
            gt = c2_mod.run_cycle2_ground_truth_probes()
            peer = c2_mod.audit_cycle2_peer_modules(_ROOT)
            if gt["status"] != "PASS" or peer["findings"]:
                raise AssertionError(f"Inquisitor Cycle 2 adversarial audit failed: {peer['findings']}")
            out_inq["cycle2_probes_passed"] = gt["probe_count"]
            out_inq["cycle2_peer_findings"] = len(peer["findings"])
        return out_inq

    st_inq = _run_stage("inquisitor_ast_and_adversarial_audit", _run_inquisitor_gates)
    stages_summary.append(st_inq)

    total_ms = (time.monotonic_ns() - t_all_ns) // 1_000_000
    if total_ms >= 45_000:
        raise AssertionError(f"verify_all.py exceeded 45-second Wave II budget: {total_ms} ms")

    print(f"=== [verify_all.py PASS] Total clean-room runtime: {total_ms} ms (< 45000 ms budget) ===")
    for st in stages_summary:
        print(f"  [PASS] {st['stage']} ({st['elapsed_ms']} ms)")
    print(
        f"  [LEDGER v1] {ledger_v1_doc['total_claims']} claims (100% certified) -> "
        f"artifacts/theorem_ledger_v1.json: {ledger_v1_doc['tag_counts']}"
    )
    print(
        f"  [LEDGER v2] {ledger_v2_doc['total_claims']} claims (100% certified) -> "
        f"artifacts/theorem_ledger_v2.json: {ledger_v2_doc['tag_counts']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
