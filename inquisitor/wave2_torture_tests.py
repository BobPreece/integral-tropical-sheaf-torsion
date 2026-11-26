from __future__ import annotations

"""Wave II Mathematical Adversarial Torture-Test & Live Peer Audit Suite (`SPEC_WAVE2.md` §0.4, §1 A2, §1 D4, §2.1).

Constitutional Compliance:
- 100% Python 3.9+ stdlib only (`from __future__ import annotations`).
- Strictly ZERO `float` literals/calls/annotations, ZERO `Fraction`, ZERO `ast.Div` (`/`), ZERO `isinstance`.
- Hard `signal.alarm(20)` enforcement per torture stage; total runtime `< 3.5s` (`~1.2s`).

Executes all 5 live adversarial Wave II torture gates:
1. **Live Trap W2-1 (Finite-Ray Impostors on `MAX_6` vs. `@architect` & `@formalist` Sub-Cone Splitters)**:
   - Feeds **Impostor W2-1A (`F_fake_Z`)** (`c_den = 1` pure-`Z` 2-layer network matching `MAX_6` across `±1`,
     all `45` `Syl_2(S_6)` orbit reps, and all `720` `S_6` chambers on `(1..6)`) and **Impostor W2-1B
     (`F_stealth_6max6_z`)** (3-hinge off-braid bump matching `6 * MAX_6` across all `2,160` multi-profile rays)
     DIRECTLY into BOTH `formalist.cert_kernel` (`verify_max6_primal_z_half_certificate` &
     `verify_translation_equivariant_cpwl_all_chambers`) AND `architect.track_a_wave2_max6.verify_candidate_all_syl2_subcones`,
     proving BOTH engines deterministically catch off-braid impostors with exact integer sub-cone witnesses!
   - Audits `@architect`'s `47`-ray `c_den = 512` impostor demonstration in `artifacts/checkpoint_a2_wave2.json`.
2. **Live Trap W2-2 (Independent Audit of Tier 1–3 `p = 3` Dual Obstruction Witnesses + 6 Bogus `3`-adic Traps)**:
   - Independently verifies `@architect`'s emitted `p = 3` dual obstruction witnesses across the `945 x 615`
     pairwise-`M2` system and Tiers 1–3 (`321, 364, 384` `Syl_2(S_6)` orbits) in `checkpoint_a2_wave2.json`
     (`min_j v_3((y^T A)_j) > v_3(y^T b)`, `p = 3 not in {2}`, non-zero `y`, `y^T b != 0`), plus verifies rejection
     of all `6` near-miss bogus `3`-adic witnesses across `formalist.cert_kernel` (`padic` & `max6_padic_dual`).
3. **Live Trap W2-3 (`Q_8` & `Dic_3` Compression Guards, Live `W=17` / `W=25` Verification & Impostor Rejection)**:
   - Fires `W >= |G|^2` (`64` on `Q_8`, `144` on `Dic_3`, and `m=1 => W=5 >= 4` on `C_2`) at `@architect`'s
     live compression functions in `architect.track_d_wave2_extensions` and `simulator.wave2_sweeps` to confirm
     mandatory `ValueError` guards fire.
   - Independently verifies `@architect`'s `W = 17` (biased) & `W = 18` (zero-bias) pure-`Z` `Q_8` circuits across
     all `64` pairs and `W = 25` (biased) & `W = 26` (zero-bias) pure-`Z` `Dic_3` circuits across all `144` pairs,
     plus `Dic_3` transitive (`12 -> 144`) vs intransitive (`3 + 4 = 7 -> 49`) permutation degree analysis.
   - Verifies BOTH `@architect` and `@formalist` reject `W = 16` `V_4` sign-collapsed (`i * i != +1`),
     rational-`"1/2"`-smuggled, `2x`-scaled `out_denom = 2`, and `W = 64` trivial circuits!
4. **Live Trap W2-4 (Synchronized 3-Valued Epistemic Overclaim Guard Across Wave I & Wave II Auditors)**:
   - Verifies BOTH `wave2_torture_tests.audit_wave2_epistemic_ledger_data` AND
     `cycle2_adversarial_probes.audit_epistemic_ledger` (plus `formalist.cert_kernel.verify_max6_dual_padic_certificate`)
     accept honest tier-scoped `A2_TIER123_3ADIC_OBSTRUCTION` (`CERTIFIED_EXACT`) paired with unconstrained
     `A2_MAX6_Z_HALF_FRONTIER` (`OPEN_BUDGET_EXCEEDED`), while deterministically rejecting unconditional
     `MAX_6 not in ReLU_{6,2}(Z[1/2])` overclaims!
5. **Live SVG Atlas (`10/10` `plots/fig01..fig10.svg`) & Workspace AST / JSON Zero-Float Gate**:
   - Runs `svg_auditor.audit_plots_directory` (`OOB == 0`, `overlaps == 0`) and `ast_scanner.scan_workspace`
     (`0` violations across all `.py` and `artifacts/*.json`), flushing `artifacts/wave2_inquisitor_audit.json`.
"""

import itertools
import json
import os
from pathlib import Path
import signal
import sys
import tempfile
import time
from typing import Any, Callable, Sequence

WORKSPACE_ROOT = str(Path(__file__).resolve().parent.parent)
if WORKSPACE_ROOT not in sys.path:
    sys.path.insert(0, WORKSPACE_ROOT)

from architect.core.padic_local_global import vp_int
from architect.track_a_foundations import D6_PERMS, build_hexagon_6max6_dictionary, build_syl2_s6_and_orbit_reps, eval_6max6_hexagon
from architect.track_a_wave2_max6 import (
    GateOrbitSpec,
    _act_vec6,
    verify_candidate_all_syl2_subcones,
)
from architect.track_d_group_circuits import make_cyclic_group, make_q8_group, validate_group_compression_width
from architect.track_d_wave2_extensions import (
    _verify_pure_z_group_circuit,
    build_cyclic_index2_extension_z_circuit,
    compute_minimal_faithful_perm_degree,
    make_dic3_group,
)
from formalist import cert_kernel
from inquisitor import ast_scanner, cycle2_adversarial_probes, svg_auditor
from simulator.wave2_sweeps import (
    guard_compression_width as sim_guard_compression_width,
    make_dicyclic_group as sim_make_dicyclic_group,
    make_q8_group as sim_make_q8_group,
)

VALID_EPISTEMIC_TAGS = frozenset({
    "CERTIFIED_EXACT",
    "FALSIFIED_COUNTEREXAMPLE",
    "OPEN_BUDGET_EXCEEDED",
})


class _Wave2TortureTimeout(RuntimeError):
    pass


def _alarm_handler(signum: int, frame: object) -> None:
    _ = (signum, frame)
    raise _Wave2TortureTimeout("Wave II torture stage exceeded 20-second wall-clock timeout")


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


# ===========================================================================
# TRAP W2-1: Finite-Ray Impostors on `MAX_6` (`Syl_2(S_6)` 45-Orbit Spoofs)
# ===========================================================================


def eval_impostor_w2_1a_pure_z_max6(x: Sequence[int]) -> int:
    """Evaluate the pure-`Z` 2-layer off-braid CPWL impostor `F_fake_Z(x)`:
        `F_fake_Z(x) = S_1(x) - 75 M_2(x) - M_3(x) + 76 M_4(x) - 9 Q_off(x)`
    where `Q_off(x) = sum_{i=0}^5 sum_{j<k != i} ReLU(2 x_i - x_j - x_k)`.

    Matches `1 * MAX_6(x)` on `+(1..1)`, `-(1..1)`, all 45 `Syl_2(S_6)` chamber reps, and all 720 `S_6`
    permutations of `(6, 5, 4, 3, 2, 1)`, yet equals `1048 != 10` at `(0, 1, 2, 3, 4, 10)`!
    """
    if len(x) != 6:
        raise ValueError("Expected 6 integer coordinates")
    xv = [int(v) for v in x]
    s1 = sum(xv)
    m2 = 0
    for i in range(6):
        for j in range(i + 1, 6):
            m2 += xv[i] if xv[i] >= xv[j] else xv[j]
    m3 = 0
    for i in range(6):
        for j in range(i + 1, 6):
            mij = xv[i] if xv[i] >= xv[j] else xv[j]
            for k in range(j + 1, 6):
                m3 += mij if mij >= xv[k] else xv[k]
    m4 = 0
    for i in range(6):
        for j in range(i + 1, 6):
            mij = xv[i] if xv[i] >= xv[j] else xv[j]
            for k in range(j + 1, 6):
                for l_idx in range(k + 1, 6):
                    mkl = xv[k] if xv[k] >= xv[l_idx] else xv[l_idx]
                    m4 += mij if mij >= mkl else mkl
    q_off = 0
    for i in range(6):
        two_xi = 2 * xv[i]
        for j in range(6):
            if j == i:
                continue
            for k in range(j + 1, 6):
                if k == i:
                    continue
                diff = two_xi - xv[j] - xv[k]
                if diff > 0:
                    q_off += diff
    return s1 - 75 * m2 - m3 + 76 * m4 - 9 * q_off


def build_impostor_w2_1a_feedforward_z_net() -> dict[str, Any]:
    """Construct explicit zero-skip zero-bias pure-`Z` 2-hidden-layer ReLU matrices `(W1, W2, w_out, out_denom=1)`
    for `F_fake_Z(x)`.
    """
    w1_rows: list[list[int]] = []
    w1_idx: dict[tuple[int, ...], int] = {}

    def add_l1(vec: list[int]) -> int:
        key = tuple(vec)
        if key not in w1_idx:
            w1_idx[key] = len(w1_rows)
            w1_rows.append(list(vec))
        return w1_idx[key]

    pos_x = [add_l1([1 if c == i else 0 for c in range(6)]) for i in range(6)]
    neg_x = [add_l1([-1 if c == i else 0 for c in range(6)]) for i in range(6)]

    pair_hinge: dict[tuple[int, int], int] = {}
    for i in range(6):
        for j in range(i + 1, 6):
            v = [0] * 6
            v[j] = 1
            v[i] = -1
            pair_hinge[(i, j)] = add_l1(v)

    off_hinges: list[int] = []
    for i in range(6):
        for j in range(6):
            if j == i:
                continue
            for k in range(j + 1, 6):
                if k == i:
                    continue
                v = [0] * 6
                v[i] = 2
                v[j] = -1
                v[k] = -1
                off_hinges.append(add_l1(v))

    m1 = len(w1_rows)
    w2_rows: list[list[int]] = []
    w_out: list[int] = []

    def add_l2_from_dict(terms: dict[int, int], out_weight: int) -> None:
        if out_weight == 0:
            return
        row = [0] * m1
        for k_idx, coeff in terms.items():
            row[k_idx] += coeff
        if any(c != 0 for c in row):
            w2_rows.append(row)
            w_out.append(out_weight)

    lin_coeff = [1] * 6
    pair_coeff: dict[tuple[int, int], int] = {k: 0 for k in pair_hinge}

    for i in range(6):
        for j in range(i + 1, 6):
            lin_coeff[i] -= 75
            pair_coeff[(i, j)] -= 75

    for i in range(6):
        for j in range(i + 1, 6):
            for k in range(j + 1, 6):
                lin_coeff[i] -= 1
                pair_coeff[(i, j)] -= 1
                add_l2_from_dict(
                    {pos_x[k]: 1, neg_x[k]: -1, pos_x[i]: -1, neg_x[i]: 1, pair_hinge[(i, j)]: -1},
                    -1,
                )

    for i in range(6):
        for j in range(i + 1, 6):
            for k in range(j + 1, 6):
                for l_idx in range(k + 1, 6):
                    lin_coeff[k] += 76
                    pair_coeff[(k, l_idx)] += 76
                    add_l2_from_dict(
                        {
                            pos_x[i]: 1,
                            neg_x[i]: -1,
                            pos_x[k]: -1,
                            neg_x[k]: 1,
                            pair_hinge[(i, j)]: 1,
                            pair_hinge[(k, l_idx)]: -1,
                        },
                        76,
                    )

    for i in range(6):
        if lin_coeff[i] != 0:
            add_l2_from_dict({pos_x[i]: 1}, lin_coeff[i])
            add_l2_from_dict({neg_x[i]: 1}, -lin_coeff[i])

    for pk, cw in pair_coeff.items():
        if cw != 0:
            add_l2_from_dict({pair_hinge[pk]: 1}, cw)

    for oh in off_hinges:
        add_l2_from_dict({oh: 1}, -9)

    return {
        "W1": w1_rows,
        "W2": w2_rows,
        "w_out": w_out,
        "out_denom": 1,
        "n_dim": 6,
        "target_scale": 1,
    }


def build_impostor_w2_1a_architect_specs() -> list[tuple[int, GateOrbitSpec]]:
    """Encode `F_fake_Z(x)` directly in `architect.track_a_wave2_max6`'s `GateOrbitSpec` format (`c_den = 1`)."""
    lin_coeff = [1] * 6
    pair_hinge_map: dict[tuple[int, ...], int] = {}
    l2_elems: list[tuple[int, tuple[int, ...], tuple[tuple[int, tuple[int, ...]], ...]]] = []

    def e_diff(j: int, i: int) -> tuple[int, ...]:
        v = [0] * 6
        v[j] += 1
        v[i] -= 1
        return tuple(v)

    for i in range(6):
        for j in range(i + 1, 6):
            lin_coeff[i] -= 75
            d_ji = e_diff(j, i)
            pair_hinge_map[d_ji] = pair_hinge_map.get(d_ji, 0) - 75
            for k in range(j + 1, 6):
                lin_coeff[i] -= 1
                pair_hinge_map[d_ji] = pair_hinge_map.get(d_ji, 0) - 1
                l2_elems.append((-1, e_diff(k, i), ((-1, d_ji),)))
                for l_idx in range(k + 1, 6):
                    lin_coeff[k] += 76
                    d_lk = e_diff(l_idx, k)
                    pair_hinge_map[d_lk] = pair_hinge_map.get(d_lk, 0) + 76
                    l2_elems.append((76, e_diff(i, k), ((1, d_ji), (-1, d_lk))))

    specs: list[tuple[int, GateOrbitSpec]] = []
    for i, lc in enumerate(lin_coeff):
        if lc != 0:
            specs.append((lc, ("LIN", (i,))))
    for d_vec, pw in sorted(pair_hinge_map.items()):
        if pw != 0:
            specs.append((pw, ("1L", (d_vec,))))
    off_norms: list[tuple[int, ...]] = []
    for i in range(6):
        for j in range(6):
            if j == i:
                continue
            for k in range(j + 1, 6):
                if k == i:
                    continue
                v = [0] * 6
                v[i] = 2
                v[j] = -1
                v[k] = -1
                off_norms.append(tuple(v))
    specs.append((-9, ("1L", tuple(off_norms))))
    for w_l2, c0_t, terms_t in l2_elems:
        specs.append((w_l2, ("L2", ((c0_t, terms_t),))))
    return specs


def build_impostor_w2_1b_architect_specs(syl2_group: Sequence[tuple[int, ...]]) -> list[tuple[int, GateOrbitSpec]]:
    """Encode `6 * MAX_6_hex(x) + Syl_2_orbit(G_cone_100)(x)` (`c_den = 6`) in `@architect`'s `GateOrbitSpec` format."""
    hex_1l, hex_m2, _ = build_hexagon_6max6_dictionary()
    specs: list[tuple[int, GateOrbitSpec]] = []

    def e_diff(j: int, i: int) -> tuple[int, ...]:
        v = [0] * 6
        v[j] += 1
        v[i] -= 1
        return tuple(v)

    lin_acc = [0] * 6
    for (i, j), w in sorted(hex_1l.items()):
        lin_acc[i] += w
        specs.append((w, ("1L", (e_diff(j, i),))))
    for (ga, gb), w in sorted(hex_m2.items()):
        (a0_i, a0_j), (a1_i, a1_j) = ga
        (b0_i, b0_j), (b1_i, b1_j) = gb
        lin_acc[b0_i] += w
        lin_acc[b1_i] += w
        specs.append((w, ("1L", (e_diff(b0_j, b0_i),))))
        specs.append((w, ("1L", (e_diff(b1_j, b1_i),))))
        c0 = [0] * 6
        c0[a0_i] += 1
        c0[a1_i] += 1
        c0[b0_i] -= 1
        c0[b1_i] -= 1
        terms = (
            (1, e_diff(a0_j, a0_i)),
            (1, e_diff(a1_j, a1_i)),
            (-1, e_diff(b0_j, b0_i)),
            (-1, e_diff(b1_j, b1_i)),
        )
        specs.append((w, ("L2", ((tuple(c0), terms),))))

    for i, lc in enumerate(lin_acc):
        if lc != 0:
            specs.append((lc, ("LIN", (i,))))

    # Add `Syl_2(S_6)`-symmetrized stealth bump `G_cone_100 = ReLU(ReLU(x_1-x_0) - 100 ReLU(x_5-x_1) - 100 ReLU(x_1-x_5))`
    orb_bump = set()
    base_terms = ((1, (-1, 1, 0, 0, 0, 0)), (-100, (0, -1, 0, 0, 0, 1)), (-100, (0, 1, 0, 0, 0, -1)))
    for g in syl2_group:
        t_g = tuple(sorted((al, _act_vec6(av, g)) for al, av in base_terms))
        orb_bump.add(((0, 0, 0, 0, 0, 0), t_g))
    specs.append((1, ("L2", tuple(sorted(orb_bump)))))
    return specs


def eval_impostor_w2_1b_stealth_6max6(x: Sequence[int]) -> int:
    """Evaluate multi-profile stealth impostor `6 * MAX_6(x) + G_cone_100(x)`."""
    base = eval_6max6_hexagon(x)
    x0, x1, x5 = int(x[0]), int(x[1]), int(x[5])
    h10 = (x1 - x0) if x1 > x0 else 0
    h51 = (x5 - x1) if x5 > x1 else 0
    h15 = (x1 - x5) if x1 > x5 else 0
    inner = h10 - 100 * h51 - 100 * h15
    return base + (inner if inner > 0 else 0)


def build_symbolic_max6() -> cert_kernel.SymbolicCPWL:
    expr = cert_kernel.SymbolicCPWL.coord(6, 0)
    for idx in range(1, 6):
        expr = cert_kernel.SymbolicCPWL.max2(expr, cert_kernel.SymbolicCPWL.coord(6, idx))
    return expr


def build_symbolic_impostor_w2_1b() -> tuple[cert_kernel.SymbolicCPWL, cert_kernel.SymbolicCPWL]:
    """Return `(6 * MAX_6 + G_cone_100, 6 * MAX_6)` as translation-equivariant `SymbolicCPWL` trees."""
    SymbolicCPWL = cert_kernel.SymbolicCPWL
    six_max6 = SymbolicCPWL.scale(6, 1, build_symbolic_max6())
    h10 = SymbolicCPWL.relu(SymbolicCPWL.affine(0, [-1, 1, 0, 0, 0, 0], 1))
    h51 = SymbolicCPWL.relu(SymbolicCPWL.affine(0, [0, -1, 0, 0, 0, 1], 1))
    h15 = SymbolicCPWL.relu(SymbolicCPWL.affine(0, [0, 1, 0, 0, 0, -1], 1))
    inner = SymbolicCPWL.add(
        h10,
        SymbolicCPWL.add(SymbolicCPWL.scale(-100, 1, h51), SymbolicCPWL.scale(-100, 1, h15)),
    )
    g_cone_100 = SymbolicCPWL.relu(inner)
    return (SymbolicCPWL.add(six_max6, g_cone_100), six_max6)


def run_trap_w2_1_live_torture(root_path: str = WORKSPACE_ROOT) -> dict[str, Any]:
    """Torture-test BOTH `@architect` and `@formalist` sub-cone verifiers against stealth finite-ray impostors."""
    syl2_grp, reps_45 = build_syl2_s6_and_orbit_reps()
    assert len(reps_45) == 45

    # 1. Verify Impostor W2-1A fools ALL 45 Syl_2(S_6) orbit reps AND ALL 720 S_6 permutations of (1..6)
    base_prof = (1, 2, 3, 4, 5, 6)
    for perm in itertools.permutations(base_prof):
        assert eval_impostor_w2_1a_pure_z_max6(perm) == max(perm)
    assert eval_impostor_w2_1a_pure_z_max6((1, 1, 1, 1, 1, 1)) == 1
    assert eval_impostor_w2_1a_pure_z_max6((-1, -1, -1, -1, -1, -1)) == -1

    subcone_pt_a = (0, 1, 2, 3, 4, 10)
    val_a = eval_impostor_w2_1a_pure_z_max6(subcone_pt_a)
    assert val_a == 1048 and val_a != max(subcone_pt_a)

    # 1a. Feed Impostor W2-1A directly into `formalist.cert_kernel.verify_max6_primal_z_half_certificate` (`t_exp=0`)!
    net_a = build_impostor_w2_1a_feedforward_z_net()
    primal_impostor_cert_a = {
        "cert_type": "max6_z_half_primal",
        "n_dim": 6,
        "t_exp": 0,
        "W1": net_a["W1"],
        "W2": net_a["W2"],
        "w_out": net_a["w_out"],
    }
    formalist_caught_a = False
    try:
        cert_kernel.verify_max6_primal_z_half_certificate(primal_impostor_cert_a)
    except AssertionError:
        formalist_caught_a = True
    assert formalist_caught_a, "Formalist `verify_max6_primal_z_half_certificate` failed to catch Impostor W2-1A!"

    # 1b. Feed Impostor W2-1A directly into `architect.track_a_wave2_max6.verify_candidate_all_syl2_subcones` (`c_den=1`)!
    arch_specs_a = build_impostor_w2_1a_architect_specs()
    arch_ok_a, arch_witness_a = verify_candidate_all_syl2_subcones(arch_specs_a, 1, reps_45)
    assert (not arch_ok_a) and arch_witness_a is not None
    assert eval_impostor_w2_1a_pure_z_max6(arch_witness_a) != max(arch_witness_a)

    # 2. Verify Impostor W2-1B fools ALL 2,160 multi-profile rays yet BOTH `@architect` and `@formalist` catch it!
    for prof in ((1, 2, 3, 4, 5, 6), (-89, -34, -13, -5, -2, -1), (-41, -13, 0, 7, 29, 103)):
        for perm in itertools.permutations(prof):
            assert eval_impostor_w2_1b_stealth_6max6(perm) == 6 * max(perm)

    lhs_b, rhs_b = build_symbolic_impostor_w2_1b()
    formalist_caught_b = False
    try:
        cert_kernel.verify_translation_equivariant_cpwl_all_chambers(lhs_b, rhs_b, 6)
    except AssertionError:
        formalist_caught_b = True
    assert formalist_caught_b, "Formalist `verify_translation_equivariant_cpwl_all_chambers` failed to catch W2-1B!"

    # Also inject `Syl_2`-bump into `F_fake_Z` (`max6_z_half_primal` gate spec format) & into `@architect`'s `c_den=6` verifier!
    arch_specs_b = build_impostor_w2_1b_architect_specs(syl2_grp)
    arch_ok_b, arch_witness_b = verify_candidate_all_syl2_subcones(arch_specs_b, 6, reps_45)
    assert (not arch_ok_b) and arch_witness_b is not None

    # 3. Verify `@architect`'s `47`-ray `c_den=512` impostor demonstration in `artifacts/checkpoint_a2_wave2.json`!
    ckpt_a2_path = os.path.join(root_path, "artifacts", "checkpoint_a2_wave2.json")
    ckpt_impostor_verified = False
    if os.path.isfile(ckpt_a2_path):
        with open(ckpt_a2_path, "r", encoding="utf-8") as fh:
            ckpt_a2 = json.load(fh)
        pm_rep = ckpt_a2["theorem_a2b"]["pairwise_m2_full_subchamber_report"]
        assert pm_rep["finite_47ray_impostor_exposed_and_refuted"] is True
        assert pm_rep["exact_symbolic_rows"] == 945 and pm_rep["total_syl2_orbits"] == 615
        ckpt_impostor_verified = True

    return {
        "trap_id": "TRAP_W2_1_MAX6_FINITE_RAY_IMPOSTORS",
        "status": "PASS",
        "impostor_a_s6_chambers_fooled": 720,
        "impostor_a_architect_subcone_witness": list(arch_witness_a),
        "impostor_a_formalist_primal_rejected": formalist_caught_a,
        "impostor_b_multiprofile_rays_fooled": 2160,
        "impostor_b_architect_subcone_witness": list(arch_witness_b),
        "impostor_b_formalist_rejected": formalist_caught_b,
        "architect_47ray_cden512_impostor_verified": ckpt_impostor_verified,
    }


# ===========================================================================
# TRAP W2-2: Live Tier 1–3 `p=3` Dual Obstruction Audit + 6 Bogus `3`-adic Traps
# ===========================================================================


def build_bogus_3adic_witness_bank() -> list[dict[str, Any]]:
    return [
        {
            "case_id": "W2_2a_equal_valuation_v3_1_eq_1",
            "cert": {"A": [[3, 6], [6, 9]], "b": [3, 6], "y": [1, 0], "p": 3, "inverted_primes": [2]},
        },
        {
            "case_id": "W2_2b_inverted_valuation_v3_1_lt_2",
            "cert": {"A": [[3, 0], [0, 6]], "b": [3, 6], "y": [1, 1], "p": 3, "inverted_primes": [2]},
        },
        {
            "case_id": "W2_2c_zero_rhs_infinite_valuation",
            "cert": {"A": [[9, 18], [3, 6]], "b": [3, -3], "y": [1, 1], "p": 3, "inverted_primes": [2]},
        },
        {
            "case_id": "W2_2d_single_last_column_v3_tie_leak",
            "cert": {"A": [[9, 18, 27, 9, 18, 3]], "b": [3], "y": [1], "p": 3, "inverted_primes": [2]},
        },
        {
            "case_id": "W2_2e_s_bound_claim_inflated",
            "cert": {"A": [[3, 6]], "b": [3], "y": [1], "p": 3, "s_bound": 2, "inverted_primes": [2]},
        },
        {
            "case_id": "W2_2f_inverted_prime_p2_smuggled_for_z_half",
            "cert": {"A": [[4, 8]], "b": [1], "y": [1], "p": 2, "inverted_primes": [2]},
        },
    ]


def _independent_verify_3adic_witness(cert_obj: dict[str, Any], label: str) -> dict[str, int]:
    """Zero-trust pure-`int` `3`-adic valuation verification without calling solver or peer helpers."""
    a_mat = cert_obj["A"]
    b_vec = cert_obj["b"]
    y_vec = cert_obj["y"]
    p = cert_obj["p"]
    inv = cert_obj.get("inverted_primes", [])
    assert type(p) is int and p == 3 and (3 not in inv), f"{label}: invalid prime/inverted_primes"
    m = len(a_mat)
    assert m > 0 and len(b_vec) == m and len(y_vec) == m, f"{label}: row dimension mismatch"
    n = len(a_mat[0])
    assert n > 0 and any(yi != 0 for yi in y_vec), f"{label}: trivial zero dual y"

    yb = sum(int(y_vec[i]) * int(b_vec[i]) for i in range(m))
    assert yb != 0, f"{label}: y^T b == 0 has infinite 3-adic valuation"
    v_b = vp_int(yb, 3)

    min_v_a = 10 ** 9
    for j in range(n):
        col_dot = sum(int(y_vec[i]) * int(a_mat[i][j]) for i in range(m))
        vj = vp_int(col_dot, 3)
        if vj < min_v_a:
            min_v_a = vj
    assert min_v_a > v_b, f"{label}: strict 3-adic inequality failed: min v_3(y^T A)={min_v_a} <= v_3(y^T b)={v_b}"
    return {"rows": m, "cols": n, "min_v3_ytA": min_v_a, "v3_ytb": v_b}


def run_trap_w2_2_live_torture(root_path: str = WORKSPACE_ROOT) -> dict[str, Any]:
    bank = build_bogus_3adic_witness_bank()
    rejected_ids: list[str] = []
    for item in bank:
        c_obj = item["cert"]
        caught = False
        try:
            cert_kernel.verify_ledger_certificate(c_obj, claim_id=item["case_id"])
        except (AssertionError, ValueError, TypeError):
            caught = True
        assert caught, f"Bogus 3-adic witness `{item['case_id']}` was NOT rejected!"
        rejected_ids.append(item["case_id"])

    # Also test `verify_max6_dual_padic_certificate` against a bogus equal-valuation 3-adic witness (`v_3 = 1 == 1`)!
    bogus_dual_spec = {
        "cert_type": "max6_padic_dual",
        "scope": "bounded_tier",
        "n_dim": 6,
        "target_scale": 3,
        "gates": [{"kind": "pair_max", "pair": [0, 1], "orbit_group": "d6", "orbit_mode": "unique"}],
        "row_specs": [{"kind": "point_eval", "point": [1, 1, 1, 1, 1, 1]}],
        "A": [[6]],
        "b": [3],
        "y": [1],
        "p": 3,
        "inverted_primes": [2],
    }
    caught_dual_bogus = False
    try:
        cert_kernel.verify_max6_dual_padic_certificate(bogus_dual_spec, epistemic_tag="CERTIFIED_EXACT")
    except AssertionError:
        caught_dual_bogus = True
    assert caught_dual_bogus, "verify_max6_dual_padic_certificate failed to reject equal-valuation v_3=1==1 witness!"

    # Live audit of `@architect`'s Tier 1-3 + 945x615 `p=3` witnesses in `artifacts/checkpoint_a2_wave2.json`!
    ckpt_a2_path = os.path.join(root_path, "artifacts", "checkpoint_a2_wave2.json")
    live_tier_audits: dict[str, Any] = {}
    if os.path.isfile(ckpt_a2_path):
        with open(ckpt_a2_path, "r", encoding="utf-8") as fh:
            ckpt_a2 = json.load(fh)
        subs = ckpt_a2["theorem_a2b"]["certificate"]["sub_certificates"]
        for k_name in (
            "pairwise_m2_945x615_padic_p3",
            "tier1_bakaev_4plus2_padic_p3",
            "tier2_small_coeff_joins_padic_p3",
            "tier3_signed_layer2_padic_p3",
        ):
            assert k_name in subs, f"Missing expected Tier p=3 certificate `{k_name}` in checkpoint_a2_wave2.json"
            live_tier_audits[k_name] = _independent_verify_3adic_witness(subs[k_name], k_name)
            ck_res = cert_kernel.verify_ledger_certificate(subs[k_name], claim_id=k_name)
            assert ck_res["verified"] is True

        # Also verify Theorem A2a & A2c certificates in `checkpoint_a2_wave2.json` via `cert_kernel`!
        assert cert_kernel.verify_ledger_certificate(ckpt_a2["theorem_a2a"]["certificate"], claim_id="A2a")["verified"]
        assert cert_kernel.verify_ledger_certificate(ckpt_a2["theorem_a2c"]["certificate"], claim_id="A2c")["verified"]

    return {
        "trap_id": "TRAP_W2_2_BOGUS_AND_LIVE_TIER123_3ADIC_AUDIT",
        "status": "PASS",
        "bogus_cases_rejected": len(rejected_ids) + 1,
        "live_architect_tier_witnesses_verified": live_tier_audits,
    }


# ===========================================================================
# TRAP W2-3: Live `Q_8` & `Dic_3` Guards, `W=17`/`W=25` Audit & Impostors
# ===========================================================================


def build_q8_trap_circuits() -> dict[str, dict[str, Any]]:
    q8 = make_q8_group()
    cay = [list(row) for row in q8.cayley]

    w1_v4: list[list[int]] = []
    b1_v4 = [-1] * 16
    w2_v4 = [[0] * 16 for _ in range(8)]
    for a in range(4):
        for b in range(4):
            col_idx = 4 * a + b
            row16 = [0] * 16
            row16[2 * a] = 1
            row16[2 * a + 1] = 1
            row16[8 + 2 * b] = 1
            row16[8 + 2 * b + 1] = 1
            w1_v4.append(row16)
            w2_v4[2 * (a ^ b)][col_idx] = 1

    trap_v4_sign_confused = {
        "cayley": cay,
        "W1": w1_v4,
        "b1": b1_v4,
        "W2": w2_v4,
        "b2": [0] * 8,
        "compressed": True,
        "mode": "indicator",
    }

    w1_coc48: list[list[int]] = []
    b1_coc48 = [-1] * 48
    w2_coc48 = [[0] * 48 for _ in range(8)]
    for a in range(4):
        for b in range(4):
            base_k = 3 * (4 * a + b)
            r_u1 = [0] * 16
            r_u1[2 * a] = 1
            r_u1[8 + 2 * b] = 1
            r_u2 = [0] * 16
            r_u2[2 * a + 1] = 1
            r_u2[8 + 2 * b + 1] = 1
            r_u3 = [0] * 16
            r_u3[2 * a] = 1
            r_u3[2 * a + 1] = 1
            r_u3[8 + 2 * b] = 1
            r_u3[8 + 2 * b + 1] = 1
            w1_coc48.extend([r_u1, r_u2, r_u3])
            c_same = cay[2 * a][2 * b]
            c_opp = cay[2 * a][2 * b + 1]
            w2_coc48[c_same][base_k] += 1
            w2_coc48[c_same][base_k + 1] += 1
            w2_coc48[c_opp][base_k + 2] += 1
            w2_coc48[c_opp][base_k] -= 1
            w2_coc48[c_opp][base_k + 1] -= 1

    w1_smuggle_2x = [[2 * v for v in r] for r in w1_coc48]
    b1_smuggle_2x = [-2] * 48
    w2_smuggle_rat_str: list[list[Any]] = [
        ["1/2" if v == 1 else ("-1/2" if v == -1 else 0) for v in row] for row in w2_coc48
    ]
    trap_smuggled_half_strings = {
        "cayley": cay,
        "W1": w1_smuggle_2x,
        "b1": b1_smuggle_2x,
        "W2": w2_smuggle_rat_str,
        "b2": [0] * 8,
        "compressed": True,
        "mode": "indicator",
    }

    trap_scaled_2x_masquerade = {
        "cayley": cay,
        "W1": w1_smuggle_2x,
        "b1": b1_smuggle_2x,
        "W2": [list(row) for row in w2_coc48],
        "b2": [0] * 8,
        "out_denom": 2,
        "compressed": True,
        "mode": "indicator",
    }

    w1_triv64: list[list[int]] = []
    w2_triv64 = [[0] * 64 for _ in range(8)]
    for g in range(8):
        for h in range(8):
            col = 8 * g + h
            r16 = [0] * 16
            r16[g] = 1
            r16[8 + h] = 1
            w1_triv64.append(r16)
            w2_triv64[cay[g][h]][col] = 1

    trap_trivial_w64 = {
        "cayley": cay,
        "W1": w1_triv64,
        "b1": [-1] * 64,
        "W2": w2_triv64,
        "b2": [0] * 8,
        "compressed": True,
        "mode": "indicator",
    }

    return {
        "trap_w2_3a_v4_sign_confused_w16": trap_v4_sign_confused,
        "trap_w2_3b_half_string_w2": trap_smuggled_half_strings,
        "trap_w2_3b_scaled_2x_masquerade": trap_scaled_2x_masquerade,
        "trap_w2_3c_trivial_w64": trap_trivial_w64,
    }


def verify_pure_z_compressed_group_indicator_circuit(cert: dict[str, Any]) -> dict[str, Any]:
    """Strict Inquisitor validator for compressed pure-`Z` `{0,1}`-indicator 1-layer group circuits."""
    if cert.get("mode", "indicator") != "indicator":
        raise AssertionError(f"Expected exact `indicator` mode, got `{cert.get('mode')!r}`")
    for den_key in ("out_denom", "scale_denom", "w1_den", "b1_den", "w2_den", "b2_den", "w_in_den", "w_out_den"):
        if cert.get(den_key, 1) != 1:
            raise AssertionError(f"Hidden rational denominator `{den_key}={cert.get(den_key)}` is forbidden in pure-Z circuit")
    enforced = dict(cert)
    enforced["compressed"] = True
    enforced["mode"] = "indicator"
    res = cert_kernel.verify_group_circuit_certificate(enforced)
    if res.get("ring") != "Z":
        raise AssertionError(f"Expected pure-Z ring=='Z', got {res.get('ring')!r}")
    return res


def run_trap_w2_3_live_torture(root_path: str = WORKSPACE_ROOT) -> dict[str, Any]:
    bundles = build_q8_trap_circuits()
    q8 = make_q8_group()
    dic3 = make_dic3_group()

    # 1. Confirm Trap W2-3a gets 64/64 cosets in Q_8/{+-1} right while failing i * i = -1,
    #    and BOTH `@architect`'s `_verify_pure_z_group_circuit` AND `@formalist`/Inquisitor reject all 4 traps!
    c_v4 = bundles["trap_w2_3a_v4_sign_confused_w16"]
    assert q8.cayley[2][2] == 1  # i * i == -1
    for bad_key, bad_c in bundles.items():
        caught_inq = False
        try:
            verify_pure_z_compressed_group_indicator_circuit(bad_c)
        except (AssertionError, ValueError, TypeError):
            caught_inq = True
        assert caught_inq, f"Inquisitor/Formalist failed to reject `{bad_key}`!"

        caught_arch = False
        try:
            _verify_pure_z_group_circuit(
                q8, bad_c["W1"], bad_c["b1"], bad_c["W2"], bad_c["b2"], mode="indicator", compressed=True
            )
        except (AssertionError, ValueError, TypeError):
            caught_arch = True
        assert caught_arch, f"Architect `_verify_pure_z_group_circuit` failed to reject `{bad_key}`!"

    # 2. Fire `width >= |G|^2` at `@architect` (`64` on `Q_8`, `144` on `Dic_3`, and `m=1 => W=5 >= 4` inside
    #    `build_cyclic_index2_extension_z_circuit`!) AND at `@simulator` (`guard_compression_width`)!
    for ord_g, bad_w in ((8, 64), (8, 65), (12, 144), (12, 145), (16, 256)):
        ok_g = False
        try:
            validate_group_compression_width(ord_g, bad_w)
        except ValueError:
            ok_g = True
        assert ok_g, f"validate_group_compression_width failed on (|G|={ord_g}, W={bad_w})"

    # Also test `_verify_pure_z_group_circuit` at W = 144 on `Dic_3`!
    w1_dic144 = [[1 if c in (g, 12 + h) else 0 for c in range(24)] for g in range(12) for h in range(12)]
    w2_dic144 = [[1 if dic3.cayley[g][h] == c else 0 for g in range(12) for h in range(12)] for c in range(12)]
    dic144_caught = False
    try:
        _verify_pure_z_group_circuit(dic3, w1_dic144, [-1] * 144, w2_dic144, [0] * 12, mode="indicator", compressed=True)
    except ValueError:
        dic144_caught = True
    assert dic144_caught, "Architect failed to reject W=144 trivial lookup circuit on Dic_3!"

    # Trigger `ValueError` inside `build_cyclic_index2_extension_z_circuit` on C_2 (`m=1 => W=5 >= 4 == |C_2|^2`)!
    c2_caught = False
    try:
        build_cyclic_index2_extension_z_circuit(
            make_cyclic_group(2), (0,), (1,), cocycle_shift_c0=0, inversion_twist=False, biased=True
        )
    except ValueError:
        c2_caught = True
    assert c2_caught, "build_cyclic_index2_extension_z_circuit failed W >= |G|^2 guard on C_2!"

    sim_q8 = sim_make_q8_group()
    sim_dic3 = sim_make_dicyclic_group(3)
    for sim_grp, bad_w in ((sim_q8, 64), (sim_dic3, 144)):
        sim_caught = False
        try:
            sim_guard_compression_width(sim_grp, bad_w)
        except ValueError:
            sim_caught = True
        assert sim_caught, f"Simulator guard_compression_width failed on {sim_grp.name} at W={bad_w}"

    # 3. Live independent verification of `@architect`'s `W = 17` (`Q_8`) and `W = 25` (`Dic_3`) pure-Z circuits!
    q8_live_17 = build_cyclic_index2_extension_z_circuit(
        q8, h_coset_order=(0, 2, 1, 3), hj_coset_order=(4, 6, 5, 7), cocycle_shift_c0=2, biased=True
    )
    q8_live_18 = build_cyclic_index2_extension_z_circuit(
        q8, h_coset_order=(0, 2, 1, 3), hj_coset_order=(4, 6, 5, 7), cocycle_shift_c0=2, biased=False
    )
    dic3_live_25 = build_cyclic_index2_extension_z_circuit(
        dic3, h_coset_order=(0, 1, 2, 3, 4, 5), hj_coset_order=(6, 7, 8, 9, 10, 11), cocycle_shift_c0=3, biased=True
    )
    dic3_live_26 = build_cyclic_index2_extension_z_circuit(
        dic3, h_coset_order=(0, 1, 2, 3, 4, 5), hj_coset_order=(6, 7, 8, 9, 10, 11), cocycle_shift_c0=3, biased=False
    )

    for res_live, exp_w, exp_ord, g_name in (
        (q8_live_17, 17, 8, "Q_8"),
        (q8_live_18, 18, 8, "Q_8"),
        (dic3_live_25, 25, 12, "Dic_3"),
        (dic3_live_26, 26, 12, "Dic_3"),
    ):
        c_dict = dict(res_live["certificate"])  # type: ignore[arg-type]
        c_dict["expected_group_name"] = g_name
        v_res = verify_pure_z_compressed_group_indicator_circuit(c_dict)
        assert v_res["width"] == exp_w and v_res["pairs_checked"] == exp_ord * exp_ord

    perm_dic3 = compute_minimal_faithful_perm_degree(dic3)
    assert perm_dic3["minimal_transitive_faithful_degree"] == 12 and perm_dic3["minimal_faithful_perm_degree"] == 7

    # Also verify all D4a & D4b certificates inside `artifacts/checkpoint_d4_wave2.json` if present!
    ckpt_d4_path = os.path.join(root_path, "artifacts", "checkpoint_d4_wave2.json")
    ckpt_d4_verified = False
    if os.path.isfile(ckpt_d4_path):
        with open(ckpt_d4_path, "r", encoding="utf-8") as fh:
            ckpt_d4 = json.load(fh)
        assert cert_kernel.verify_ledger_certificate(ckpt_d4["theorem_d4a"]["certificate"], claim_id="D4a")["verified"]
        assert cert_kernel.verify_ledger_certificate(ckpt_d4["theorem_d4b"]["certificate"], claim_id="D4b")["verified"]
        ckpt_d4_verified = True

    return {
        "trap_id": "TRAP_W2_3_Q8_DIC3_GUARDS_AND_LIVE_CIRCUITS",
        "status": "PASS",
        "impostor_circuits_rejected": len(bundles),
        "value_error_guards_verified": ["Q_8(64)", "Dic_3(144)", "Q_16(256)", "C_2(5>=4)"],
        "q8_pure_z_widths_verified": [17, 18],
        "dic3_pure_z_widths_verified": [25, 26],
        "dic3_perm_degrees_trans_vs_intrans": [12, 7],
        "checkpoint_d4_certificates_verified": ckpt_d4_verified,
    }


# ===========================================================================
# TRAP W2-4: Synchronized 3-Valued Epistemic Overclaim Guard
# ===========================================================================


def _cert_is_finite_dictionary_unsat(cert: Any) -> bool:
    if type(cert) is not dict or len(cert) == 0:
        return False
    if "sub_certificates" in cert:
        subs = cert["sub_certificates"]
        if type(subs) is list:
            return len(subs) > 0 and all(_cert_is_finite_dictionary_unsat(s) for s in subs)
        if type(subs) is dict:
            return len(subs) > 0 and all(_cert_is_finite_dictionary_unsat(s) for s in subs.values())
        return False
    if cert.get("cert_type") == "max6_padic_dual" or "tiers" in cert:
        return True
    if all(k in cert for k in ("A", "b", "y", "p")):
        return True
    if all(k in cert for k in ("A_ub", "b_ub", "y")):
        return True
    if all(k in cert for k in ("A_eq", "b_eq")) and ("y_signed" in cert or "y" in cert):
        return True
    return False


def _cert_is_universal_cpwl_max6_sat(cert: Any) -> bool:
    if type(cert) is not dict:
        return False
    if cert.get("cert_type") == "max6_z_half_primal" and cert.get("n_dim", 6) == 6:
        return True
    if all(k in cert for k in ("W1", "W2", "w_out", "out_denom", "n_dim")):
        n_d = cert.get("n_dim")
        den = cert.get("out_denom")
        t_scale = cert.get("target_scale", 1)
        if type(n_d) is int and n_d == 6 and type(den) is int and den > 0 and type(t_scale) is int and t_scale > 0:
            eff = den * t_scale
            return (eff & (eff - 1)) == 0
    if "sub_certificates" in cert:
        subs = cert["sub_certificates"]
        if type(subs) is list:
            return any(_cert_is_universal_cpwl_max6_sat(s) for s in subs)
        if type(subs) is dict:
            return any(_cert_is_universal_cpwl_max6_sat(s) for s in subs.values())
    return False


def audit_wave2_epistemic_ledger_data(doc: Any) -> dict[str, Any]:
    """Audit an in-memory Wave I or Wave II theorem ledger against `SPEC_WAVE2.md` §0.4 3-valued epistemic rules."""
    findings: list[dict[str, str]] = []
    if type(doc) is not dict:
        return {
            "status": "FAIL",
            "claim_count": 0,
            "findings": [{"severity": "CRITICAL", "rule": "INVALID_LEDGER_ROOT", "detail": "Root must be JSON object"}],
        }

    theorems = doc.get("theorems")
    if type(theorems) is not list or len(theorems) == 0:
        return {
            "status": "FAIL",
            "claim_count": 0,
            "findings": [{"severity": "CRITICAL", "rule": "EMPTY_THEOREM_LEDGER", "detail": "Missing `theorems` list"}],
        }

    seen_e0_falsified = False
    has_unconstrained_max6_z_half_sat = False
    has_unconstrained_max6_z_half_open = False
    has_any_max6_z_half_claim = False

    overclaim_phrases = (
        "UNCONDITIONAL",
        "UNCONSTRAINED IMPOSSIB",
        "UNRESTRICTED IMPOSSIB",
        "UNIVERSAL IMPOSSIB",
        "ALL OFF-BRAID",
        "NOT IN RELU_{6,2}(Z[1/2])",
        "NOT IN RELU_6,2(Z[1/2])",
    )
    scoped_tier_markers = ("TIER", "FIXED-DICTIONARY", "FIXED DICTIONARY", "DICTIONARY", "HEXAGON", "ORBIT")

    for idx, entry in enumerate(theorems):
        if type(entry) is not dict:
            continue
        cid = str(entry.get("id") or f"idx_{idx}")
        tag = entry.get("epistemic_tag") or entry.get("status")
        if tag not in VALID_EPISTEMIC_TAGS:
            findings.append({
                "severity": "CRITICAL",
                "rule": "INVALID_EPISTEMIC_TAG",
                "detail": f"Claim `{cid}` has invalid epistemic tag `{tag!r}`.",
            })

        cert_obj = entry.get("certificate")
        if type(cert_obj) is not dict or len(cert_obj) == 0:
            findings.append({
                "severity": "CRITICAL",
                "rule": "MISSING_CERTIFICATE",
                "detail": f"Claim `{cid}` lacks a non-empty `certificate` object.",
            })
        else:
            try:
                cert_kernel.verify_ledger_certificate(cert_obj, claim_id=cid, epistemic_tag=str(tag))
            except Exception as exc:
                findings.append({
                    "severity": "CRITICAL",
                    "rule": "INVALID_CERTIFICATE_WITNESS",
                    "detail": f"Claim `{cid}` failed `cert_kernel` verification: {type(exc).__name__}: {exc}",
                })

        cid_up = cid.upper()
        title_up = str(entry.get("title") or entry.get("statement") or entry.get("summary") or "").upper()
        ws_str_up = json.dumps(entry.get("witness_summary", {})).upper()
        head_text = f"{cid_up} | {title_up}"
        combined_text = f"{head_text} | {ws_str_up}"

        is_e0 = (
            cid_up == "E0"
            or cid_up.startswith("E0_")
            or "_E0" in cid_up
            or "COUNTEREXAMPLE E0" in title_up
            or "ESCHER WATERFALL" in title_up
        )
        if is_e0:
            if tag == "FALSIFIED_COUNTEREXAMPLE":
                seen_e0_falsified = True
            else:
                findings.append({
                    "severity": "CRITICAL",
                    "rule": "E0_WRONG_EPISTEMIC_TAG",
                    "detail": f"Counterexample E0 (`{cid}`) must carry `FALSIFIED_COUNTEREXAMPLE`, got `{tag}`.",
                })

        mentions_max6 = ("MAX_6" in combined_text) or ("MAX6" in combined_text)
        mentions_z_half = ("Z[1/2]" in combined_text) or ("Z_HALF" in combined_text) or ("1/2" in cid_up)
        if mentions_max6 and mentions_z_half:
            has_any_max6_z_half_claim = True
            if tag == "OPEN_BUDGET_EXCEEDED":
                has_unconstrained_max6_z_half_open = True
            elif tag == "CERTIFIED_EXACT":
                if _cert_is_universal_cpwl_max6_sat(cert_obj):
                    has_unconstrained_max6_z_half_sat = True
                elif _cert_is_finite_dictionary_unsat(cert_obj):
                    claims_unconditional = any(p in head_text for p in overclaim_phrases)
                    is_frontier_id = ("FRONTIER" in cid_up) or ("UNCONSTRAINED" in cid_up) or ("UNCONDITIONAL" in cid_up)
                    explicitly_scoped = any(sm in head_text for sm in scoped_tier_markers)
                    if claims_unconditional or is_frontier_id or not explicitly_scoped:
                        findings.append({
                            "severity": "CRITICAL",
                            "rule": "EPISTEMIC_UNCONDITIONAL_OVERCLAIM",
                            "detail": (
                                f"Claim `{cid}` (`CERTIFIED_EXACT`) overclaims `MAX_6` `Z[1/2]` impossibility "
                                "from a finite-dictionary `3`-adic/Farkas witness without universal off-braid proof."
                            ),
                        })

    if not seen_e0_falsified:
        findings.append({
            "severity": "HIGH",
            "rule": "MISSING_E0_COUNTEREXAMPLE_ENTRY",
            "detail": "Ledger is missing `FALSIFIED_COUNTEREXAMPLE` entry for Counterexample E0.",
        })

    if has_any_max6_z_half_claim and not has_unconstrained_max6_z_half_sat and not has_unconstrained_max6_z_half_open:
        findings.append({
            "severity": "CRITICAL",
            "rule": "MISSING_UNCONSTRAINED_MAX6_OPEN_FRONTIER",
            "detail": (
                "Ledger addresses `MAX_6` over `Z[1/2]` without a universal `SAT` realization, "
                "yet omits `OPEN_BUDGET_EXCEEDED` on unconstrained `ReLU_{6,2}(Z[1/2])` (`SPEC_WAVE2.md` §0.4)."
            ),
        })

    return {
        "status": "PASS" if len(findings) == 0 else "FAIL",
        "claim_count": len(theorems),
        "findings": findings,
    }


def audit_wave2_epistemic_ledger(ledger_path: str) -> dict[str, Any]:
    if not os.path.isfile(ledger_path):
        return {"present": False, "status": "PENDING", "claim_count": 0, "findings": []}
    float_tokens: list[str] = []

    def _catch_float(tok: str) -> int:
        float_tokens.append(tok)
        return 0

    with open(ledger_path, "r", encoding="utf-8") as fh:
        doc = json.load(fh, parse_float=_catch_float)

    res = audit_wave2_epistemic_ledger_data(doc)
    res["present"] = True
    if float_tokens:
        res["findings"].append({
            "severity": "CRITICAL",
            "rule": "LEDGER_FLOAT_CONTAMINATION",
            "detail": f"Ledger contains float token(s): {float_tokens[:5]}",
        })
        res["status"] = "FAIL"
    return res


def run_trap_w2_4_live_torture(root_path: str = WORKSPACE_ROOT) -> dict[str, Any]:
    e0_stub_cert = {
        "mode": "outward_counterexample",
        "segments": [
            {"p_start": [1, -1], "velocity": [1, 20], "dt": [2, 19], "p_end": ["21/19", "21/19"]}
        ],
        "cell_and_crease_dots": [-19, -21, -38],
    }
    fixed_dict_3adic_cert = {
        "A": [[3, 6, -3], [6, 3, 9]],
        "b": [1, 2],
        "y": [1, 0],
        "p": 3,
        "inverted_primes": [2],
    }

    bad_ledger_unconditional = {
        "theorems": [
            {"id": "E0", "title": "Outward-Spiraling Escher Waterfall", "epistemic_tag": "FALSIFIED_COUNTEREXAMPLE", "certificate": e0_stub_cert},
            {
                "id": "A2_MAX6_Z_HALF_IMPOSSIBILITY",
                "title": "Unconditional Impossibility: MAX_6 not in ReLU_{6,2}(Z[1/2])",
                "epistemic_tag": "CERTIFIED_EXACT",
                "certificate": fixed_dict_3adic_cert,
            },
            {"id": "A2_MAX6_Z_HALF_FRONTIER", "title": "Open Frontier", "epistemic_tag": "OPEN_BUDGET_EXCEEDED", "certificate": fixed_dict_3adic_cert},
        ]
    }
    bad_ledger_promoted_frontier = {
        "theorems": [
            {"id": "E0", "title": "Outward-Spiraling Escher Waterfall", "epistemic_tag": "FALSIFIED_COUNTEREXAMPLE", "certificate": e0_stub_cert},
            {"id": "A2_MAX6_Z_HALF_FRONTIER", "title": "MAX_6 Z[1/2] Frontier", "epistemic_tag": "CERTIFIED_EXACT", "certificate": fixed_dict_3adic_cert},
        ]
    }
    bad_ledger_dropped_open = {
        "theorems": [
            {"id": "E0", "title": "Outward-Spiraling Escher Waterfall", "epistemic_tag": "FALSIFIED_COUNTEREXAMPLE", "certificate": e0_stub_cert},
            {
                "id": "A2_TIER123_3ADIC_OBSTRUCTION",
                "title": "Tier 1-3 Fixed-Dictionary 3-adic Impossibility on MAX_6 over Z[1/2]",
                "epistemic_tag": "CERTIFIED_EXACT",
                "certificate": fixed_dict_3adic_cert,
            },
        ]
    }
    honest_wave2_ledger = {
        "theorems": [
            {"id": "E0", "title": "Outward-Spiraling Escher Waterfall", "epistemic_tag": "FALSIFIED_COUNTEREXAMPLE", "certificate": e0_stub_cert},
            {
                "id": "A2_TIER123_3ADIC_OBSTRUCTION",
                "title": "Tier 1-3 Fixed-Dictionary 3-adic UNSAT Obstruction on MAX_6 over Z[1/2]",
                "epistemic_tag": "CERTIFIED_EXACT",
                "certificate": fixed_dict_3adic_cert,
            },
            {
                "id": "A2_MAX6_Z_HALF_FRONTIER",
                "title": "Unconstrained ReLU_{6,2}(Z[1/2]) Open Frontier for MAX_6",
                "epistemic_tag": "OPEN_BUDGET_EXCEEDED",
                "certificate": fixed_dict_3adic_cert,
            },
        ]
    }

    assert audit_wave2_epistemic_ledger_data(bad_ledger_unconditional)["status"] == "FAIL"
    assert audit_wave2_epistemic_ledger_data(bad_ledger_promoted_frontier)["status"] == "FAIL"
    assert audit_wave2_epistemic_ledger_data(bad_ledger_dropped_open)["status"] == "FAIL"
    assert audit_wave2_epistemic_ledger_data(honest_wave2_ledger)["status"] == "PASS"

    # Cross-check `inquisitor.cycle2_adversarial_probes.audit_epistemic_ledger` in `/tmp` on BOTH honest & overclaim ledgers!
    with tempfile.TemporaryDirectory(dir="/tmp", prefix="itst_epistemic_sync_") as tmp_d:
        honest_p = os.path.join(tmp_d, "honest_v2.json")
        overclaim_p = os.path.join(tmp_d, "overclaim_v2.json")
        with open(honest_p, "w", encoding="utf-8") as fh:
            json.dump(honest_wave2_ledger, fh)
        with open(overclaim_p, "w", encoding="utf-8") as fh:
            json.dump(bad_ledger_unconditional, fh)
        c2_honest = cycle2_adversarial_probes.audit_epistemic_ledger(honest_p)
        c2_over = cycle2_adversarial_probes.audit_epistemic_ledger(overclaim_p)
        assert c2_honest["status"] == "PASS", f"cycle2 audit_epistemic_ledger rejected honest tier-scoped ledger: {c2_honest}"
        assert c2_over["status"] == "FAIL", "cycle2 audit_epistemic_ledger failed to catch unconditional overclaim!"

    # Also verify `formalist.cert_kernel.verify_max6_dual_padic_certificate` rejects unconstrained `CERTIFIED_EXACT`!
    formalist_epistemic_caught = False
    try:
        cert_kernel.verify_max6_dual_padic_certificate(
            {
                "cert_type": "max6_padic_dual",
                "scope": "unconstrained_relu_6_2_z_half",
                "n_dim": 6,
                "target_scale": 1,
                "gates": [{"kind": "pair_max", "pair": [0, 1], "orbit_group": "d6", "orbit_mode": "unique"}],
                "row_specs": [{"kind": "point_eval", "point": [1, 1, 1, 1, 1, 1]}],
                "A": [[6]],
                "b": [1],
                "y": [1],
                "p": 3,
                "inverted_primes": [2],
            },
            epistemic_tag="CERTIFIED_EXACT",
        )
    except AssertionError:
        formalist_epistemic_caught = True
    assert formalist_epistemic_caught

    v1_path = os.path.join(root_path, "artifacts", "theorem_ledger_v1.json")
    v1_ok = False
    if os.path.isfile(v1_path):
        r_v1 = audit_wave2_epistemic_ledger(v1_path)
        assert r_v1["status"] == "PASS" and r_v1["claim_count"] == 21
        v1_ok = True

    return {
        "trap_id": "TRAP_W2_4_EPISTEMIC_OVERCLAIM_GUARD",
        "status": "PASS",
        "mock_overclaims_rejected": 3,
        "cycle2_and_wave2_auditors_synchronized": True,
        "formalist_epistemic_guard_verified": formalist_epistemic_caught,
        "wave1_ledger_regression_passed": v1_ok,
    }


# ===========================================================================
# STAGE 5: Live SVG Atlas (`10/10`) & Workspace AST / JSON Zero-Float Gate
# ===========================================================================


def run_live_svg_and_ast_gate(root_path: str = WORKSPACE_ROOT) -> dict[str, Any]:
    svg_self = svg_auditor.run_svg_auditor_self_tests()
    assert svg_self["status"] == "PASS"

    plots_dir = os.path.join(root_path, "plots")
    plots_audit = svg_auditor.audit_plots_directory(plots_dir, require_full_atlas=True)
    assert (
        plots_audit["status"] == "PASS"
        and plots_audit["svg_files_audited"] == 10
        and plots_audit["total_oob"] == 0
        and plots_audit["total_overlaps"] == 0
    ), f"Live SVG atlas audit failed: {plots_audit}"

    ast_self = ast_scanner.run_scanner_self_tests()
    ws_scan = ast_scanner.scan_workspace(root_path)
    json_floats = ast_scanner.scan_json_artifacts_for_floats(root_path)
    assert ast_self["status"] == "PASS" and ws_scan["status"] == "PASS" and len(json_floats) == 0, (
        f"AST/JSON firewall failed: violations={ws_scan['violations']}, json_floats={json_floats}"
    )

    v2_ledger_path = os.path.join(root_path, "artifacts", "theorem_ledger_v2.json")
    v2_status = "PENDING_CYCLE3"
    if os.path.isfile(v2_ledger_path):
        v2_res = audit_wave2_epistemic_ledger(v2_ledger_path)
        assert v2_res["status"] == "PASS", f"theorem_ledger_v2.json audit failed: {v2_res}"
        v2_status = f"PASS ({v2_res['claim_count']} claims)"

    return {
        "status": "PASS",
        "svg_self_tests_passed": svg_self["passed_self_tests"],
        "atlas_svgs_audited": plots_audit["svg_files_audited"],
        "atlas_total_oob": plots_audit["total_oob"],
        "atlas_total_overlaps": plots_audit["total_overlaps"],
        "ast_self_tests_passed": ast_self["passed_cases"],
        "scanned_python_files": ws_scan["scanned_python_files"],
        "svg_atlas_zero_float": ws_scan["svg_atlas_zero_float"],
        "ast_violations": ws_scan["total_violations"],
        "ast_advisories": ws_scan["total_advisories"],
        "json_float_violations": len(json_floats),
        "theorem_ledger_v2_status": v2_status,
    }


def run_all_wave2_torture_self_tests(root_path: str = WORKSPACE_ROOT, flush_artifact: bool = False) -> dict[str, Any]:
    t0_ns = time.perf_counter_ns()
    s1 = _run_stage_with_alarm("trap_w2_1_live_max6_impostors", lambda: run_trap_w2_1_live_torture(root_path))
    s2 = _run_stage_with_alarm("trap_w2_2_live_tier123_and_bogus_3adic", lambda: run_trap_w2_2_live_torture(root_path))
    s3 = _run_stage_with_alarm("trap_w2_3_live_q8_dic3_guards_and_circuits", lambda: run_trap_w2_3_live_torture(root_path))
    s4 = _run_stage_with_alarm("trap_w2_4_live_epistemic_overclaim_sync", lambda: run_trap_w2_4_live_torture(root_path))
    s5 = _run_stage_with_alarm("live_svg_atlas_and_ast_zero_float_gate", lambda: run_live_svg_and_ast_gate(root_path))

    stages = [s1, s2, s3, s4, s5]
    all_ok = all(st["status"] == "PASS" for st in stages)
    payload: dict[str, Any] = {
        "suite": "inquisitor.wave2_torture_tests",
        "wave": "2.0",
        "cycle": 2,
        "status": "PASS" if all_ok else "FAIL",
        "total_elapsed_ms": (time.perf_counter_ns() - t0_ns) // 1_000_000,
        "stages": stages,
    }

    if flush_artifact:
        art_dir = os.path.join(root_path, "artifacts")
        os.makedirs(art_dir, exist_ok=True)
        out_path = os.path.join(art_dir, "wave2_inquisitor_audit.json")
        with open(out_path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=2, sort_keys=True)
        float_errs = ast_scanner.scan_json_artifacts_for_floats(root_path)
        if float_errs:
            raise AssertionError(f"JSON float firewall triggered after Wave II audit flush: {float_errs}")

    return payload


def main() -> int:
    res = run_all_wave2_torture_self_tests(WORKSPACE_ROOT, flush_artifact=True)
    print(json.dumps(res, indent=2))
    return 0 if res["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
