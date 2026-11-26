from __future__ import annotations

import itertools
import math
import time
from typing import Any, Dict, List, Sequence, Tuple

from architect.core.exact_int_la import bareiss_det, dot_int, vec_mat_mul
from architect.core.padic_local_global import solve_s_integral, solve_z_half
from simulator.sim_exact_la import matrix_max_bit_length, rat_str


# ---------------------------------------------------------------------------
# 1. Minkowski Product Volume Sweep Vol_d(Delta_a x Delta_b) for d = 2..10
# ---------------------------------------------------------------------------

def _is_prime_power(d: int) -> Tuple[bool, int, int]:
    """Return (is_prime_power, base_prime, exponent) for integer d >= 2."""
    tmp = d
    primes_found: List[Tuple[int, int]] = []
    p = 2
    while p * p <= tmp:
        if tmp % p == 0:
            exp = 0
            while tmp % p == 0:
                tmp //= p
                exp += 1
            primes_found.append((p, exp))
        p += 1
    if tmp > 1:
        primes_found.append((tmp, 1))
    if len(primes_found) == 1:
        return True, primes_found[0][0], primes_found[0][1]
    return False, 0, 0


def _verify_staircase_triangulation_vol(a: int, b: int) -> int:
    """
    Explicitly triangulate Delta_a x Delta_b subset R^{a+b} into binom(a+b, a) simplices
    indexed by monotone lattice paths from (0, 0) to (a, b), verifying via Bareiss determinant
    that EVERY path simplex is unimodular (|det| == 1), hence Vol_{a+b}(Delta_a x Delta_b) == binom(a+b, a)!
    """
    d = a + b
    da_verts = [[0] * a] + [[1 if c == idx else 0 for c in range(a)] for idx in range(a)]
    db_verts = [[0] * b] + [[1 if c == idx else 0 for c in range(b)] for idx in range(b)]
    total_vol = 0
    for east_steps in itertools.combinations(range(d), a):
        east_set = set(east_steps)
        ci, cj = 0, 0
        edges_mat: List[List[int]] = []
        for step in range(d):
            if step in east_set:
                ci += 1
            else:
                cj += 1
            edges_mat.append(da_verts[ci] + db_verts[cj])
        det_val = abs(bareiss_det(edges_mat))
        assert det_val == 1
        total_vol += det_val
    assert total_vol == math.comb(d, a)
    return total_vol


def sweep_minkowski_product_volumes_d2_to_10() -> List[Dict[str, Any]]:
    """
    Sweep d = 2..10 (MAX_{d+1} ambient dimension d):
      - Certify exact staircase lattice volumes Vol_d(Delta_a x Delta_b) = binom(d, a) for all 1 <= a <= d // 2.
      - Certify Kummer's Prime-Power Dichotomy: gcd_{1 <= a <= d-1} binom(d, a) == p iff d = p^k, else 1!
      - Highlight d = 4 = 2^2 (Vol_4 mod 2 additive -> Delta_4 UNSAT over Z),
        d = 5 (Vol_5(Delta_2 x Delta_3) = 10 == 1 mod 3 with F_2 + F_3 in ReLU_{5,2}(Z), refuting mod-3 claim),
        d = 6, 10 (composite gcd = 1), and d = 9 = 3^2 (Vol_9 mod 3 restored).
    """
    rows: List[Dict[str, Any]] = []
    for d in range(2, 11):
        t0 = time.perf_counter_ns()
        is_pp, base_p, exp_k = _is_prime_power(d)
        binom_gcd = 0
        splits: List[Dict[str, Any]] = []
        for a in range(1, d):
            vol_ab = math.comb(d, a)
            binom_gcd = math.gcd(binom_gcd, vol_ab)
            if a <= d - a:
                # Run explicit Bareiss staircase determinant verification for all splits up to d = 10!
                # Max paths is binom(10, 5) = 252 (10x10 integer matrices -> ~3 ms total)
                verified_vol = _verify_staircase_triangulation_vol(a, d - a)
                assert verified_vol == vol_ab
                b = d - a
                in_relu_d_2_z = (a <= 3 and b <= 3)
                splits.append({
                    "split": [a, b],
                    "vol_d": vol_ab,
                    "vol_mod_2": vol_ab % 2,
                    "vol_mod_3": vol_ab % 3,
                    "both_factors_in_relu_2_z": in_relu_d_2_z,
                })

        expected_gcd = base_p if is_pp else 1
        assert binom_gcd == expected_gcd
        elapsed_us = (time.perf_counter_ns() - t0) // 1000
        rows.append({
            "d": d,
            "n_inputs_max_n": d + 1,
            "is_prime_power": is_pp,
            "prime_power_str": f"{base_p}^{exp_k}" if is_pp else "composite",
            "product_volume_gcd": binom_gcd,
            "mod2_additive_on_products": (binom_gcd % 2 == 0),
            "mod3_additive_on_products": (binom_gcd % 3 == 0),
            "splits": splits,
            "runtime_us": elapsed_us,
        })

    # Explicit assertion for Theorem A1: d = 5, split (2, 3) has Vol_5 = 10 == 1 mod 3 and both factors in ReLU_2(Z)
    d5_row = [r for r in rows if r["d"] == 5][0]
    s23 = [s for s in d5_row["splits"] if s["split"] == [2, 3]][0]
    assert s23["vol_d"] == 10 and s23["vol_mod_3"] == 1 and s23["both_factors_in_relu_2_z"] is True
    return rows


# ---------------------------------------------------------------------------
# 2. MAX_6 720-Chamber D_6 Hexagon Dictionary & 45-Orbit Syl_2(S_6) < 0.2s Engine
# ---------------------------------------------------------------------------

def build_d6_hexagon_dictionary_and_formula() -> Dict[str, Any]:
    """
    Construct the D_6-equivariant 2-layer hexagon gate dictionary over the 15 Layer-1 pairwise maxima
    m_{ij} = max(x_i, x_j) (0 <= i < j <= 5 on Z_6: 6 edges, 6 short diagonals, 3 long diagonals),
    returning both the exact 11-orbit pure-Z formula for 6 * MAX_6(x) and individual gate list.
    """
    d6_perms = sorted(
        {tuple((i + r) % 6 for i in range(6)) for r in range(6)}
        | {tuple((r - i) % 6 for i in range(6)) for r in range(6)}
    )
    assert len(d6_perms) == 12

    # Verify classification of the 15 pairwise maxima on Z_6 into 3 D_6 orbits:
    edges_6 = sorted({(min(i, (i + 1) % 6), max(i, (i + 1) % 6)) for i in range(6)})
    short_6 = sorted({(min(i, (i + 2) % 6), max(i, (i + 2) % 6)) for i in range(6)})
    long_3 = sorted({(i, i + 3) for i in range(3)})
    assert len(edges_6) == 6 and len(short_6) == 6 and len(long_3) == 3

    orbits_spec: List[Tuple[int, str, Any]] = [
        (-4, "1L", ((0, 1),)),
        (4, "M2", (((0, 1), (0, 2)), ((0, 1), (1, 3)))),
        (4, "M2", (((0, 1), (0, 2)), ((2, 3), (4, 5)))),
        (-4, "M2", (((0, 1), (0, 2)), ((2, 5), (3, 4)))),
        (2, "M2", (((0, 1), (0, 2)), ((3, 4), (3, 5)))),
        (-2, "M2", (((0, 1), (0, 2)), ((3, 5), (4, 5)))),
        (4, "M2", (((0, 1), (0, 3)), ((0, 2), (4, 5)))),
        (-4, "M2", (((0, 1), (0, 3)), ((2, 3), (4, 5)))),
        (4, "M2", (((0, 1), (0, 5)), ((1, 4), (2, 3)))),
        (-1, "M2", (((0, 1), (0, 5)), ((2, 3), (3, 4)))),
        (-4, "M2", (((0, 1), (2, 3)), ((0, 2), (4, 5)))),
    ]

    u1l: Dict[Tuple[int, int], int] = {}
    um2: Dict[Tuple[Tuple[Tuple[int, int], ...], ...], int] = {}
    orbit_gate_sets: List[List[Tuple[Tuple[Tuple[int, int], ...], ...]]] = []

    for w4, kind, data in orbits_spec:
        if kind == "1L":
            e0 = data[0]
            for g in d6_perms:
                ge = (min(g[e0[0]], g[e0[1]]), max(g[e0[0]], g[e0[1]]))
                u1l[ge] = u1l.get(ge, 0) + w4
        else:
            ea, eb = data
            orb_keys = set()
            for g in d6_perms:
                ga = tuple(sorted((min(g[i], g[j]), max(g[i], g[j])) for i, j in ea))
                gb = tuple(sorted((min(g[i], g[j]), max(g[i], g[j])) for i, j in eb))
                key = (ga, gb) if ga <= gb else (gb, ga)
                um2[key] = um2.get(key, 0) + w4
                orb_keys.add(key)
            orbit_gate_sets.append(sorted(orb_keys))

    for k in list(u1l.keys()):
        assert u1l[k] % 4 == 0
        u1l[k] //= 4
    for k in list(um2.keys()):
        assert um2[k] % 4 == 0
        um2[k] //= 4

    return {
        "d6_perms": d6_perms,
        "edges_6": edges_6,
        "short_diags_6": short_6,
        "long_diags_3": long_3,
        "u1l": u1l,
        "um2": um2,
        "orbit_gate_sets": orbit_gate_sets,
    }


def eval_6max6_hexagon(
    x: Sequence[int],
    u1l: Dict[Tuple[int, int], int],
    um2: Dict[Tuple[Tuple[Tuple[int, int], ...], ...], int],
) -> int:
    acc = 0
    for (i, j), w in u1l.items():
        acc += w * (x[i] if x[i] >= x[j] else x[j])
    for (ga, gb), w in um2.items():
        sa = (x[ga[0][0]] if x[ga[0][0]] >= x[ga[0][1]] else x[ga[0][1]]) + (
            x[ga[1][0]] if x[ga[1][0]] >= x[ga[1][1]] else x[ga[1][1]]
        )
        sb = (x[gb[0][0]] if x[gb[0][0]] >= x[gb[0][1]] else x[gb[0][1]]) + (
            x[gb[1][0]] if x[gb[1][0]] >= x[gb[1][1]] else x[gb[1][1]]
        )
        acc += w * (sa if sa >= sb else sb)
    return acc


def build_syl2_s6_and_45_orbits() -> Tuple[List[Tuple[int, ...]], List[Tuple[int, ...]]]:
    """
    Construct Syl_2(S_6) = D_4(0,1,2,3) x C_2(4,5) of order 16 = 2^4,
    and partition the 720 Weyl chambers of S_6 into 45 free orbits of size 16.
    """
    gens = [(1, 2, 3, 0, 4, 5), (3, 2, 1, 0, 4, 5), (0, 1, 2, 3, 5, 4)]
    syl2_set = {tuple(range(6))}
    stack = [tuple(range(6))]
    while stack:
        cur = stack.pop()
        for g in gens:
            nxt = tuple(cur[g[i]] for i in range(6))
            if nxt not in syl2_set:
                syl2_set.add(nxt)
                stack.append(nxt)
    syl2 = sorted(syl2_set)
    assert len(syl2) == 16

    unseen = set(itertools.permutations(range(6)))
    reps_45: List[Tuple[int, ...]] = []
    while unseen:
        rep = min(unseen)
        reps_45.append(rep)
        for g in syl2:
            orb_pt = tuple(rep[g[i]] for i in range(6))
            assert orb_pt in unseen  # Free action: every orbit has size strictly 16!
            unseen.remove(orb_pt)
    assert len(reps_45) == 45
    return syl2, reps_45


def benchmark_max6_and_syl2_engine() -> Dict[str, Any]:
    """
    Benchmark:
      1. 6 * MAX_6 pure-Z D_6 hexagon formula across 3 x 720 = 2160 Weyl chamber points
         (positive prime profile, all-negative Fibonacci profile, mixed sum-collision-free profile)
         PLUS explicit off-braid internal crease 2nd-difference linearity checks!
      2. Syl_2(S_6) (|D_4 x C_2| = 16, 45 chamber orbit reps) + padic_local_global.solve_z_half
         in < 0.2s (< 200,000 us) on:
           (a) 6 * MAX_6 (CERTIFIED_EXACT over Z[1/2] / Z), and
           (b) 1 * MAX_6 over the Syl_2(S_6)-orbit-compressed 105-gate hexagon dictionary
               (certifying instant F_3 mod-3 dual obstruction on that fixed dictionary,
               logged honestly as OPEN_BUDGET_EXCEEDED for unconstrained ReLU_{6,2}(Z[1/2])).
    """
    # Part A: 720-chamber x 3 profiles + off-braid hinge linearity verification
    t_hex0 = time.perf_counter_ns()
    hex_data = build_d6_hexagon_dictionary_and_formula()
    u1l = hex_data["u1l"]
    um2 = hex_data["um2"]

    profiles = [
        (2, 5, 11, 23, 47, 97),         # strictly positive prime gaps
        (-89, -34, -13, -5, -2, -1),    # all-negative Fibonacci (catches ReLU(0) sign bugs)
        (-40, -17, 3, 12, 29, 64),      # mixed signs, collision-free subset sums
    ]
    checked_pts = 0
    for prof in profiles:
        for perm in itertools.permutations(prof):
            val = eval_6max6_hexagon(perm, u1l, um2)
            assert val == 6 * max(perm)
            checked_pts += 1

    # Off-braid internal hinge 2nd-difference zero checks strictly inside chamber x0 < x1 < x2 < x3 < x4 < x5:
    # Probe across internal hyperplanes x3 + x0 - x2 - x1 = 0, 2*x2 - x3 - x0 = 0, 3*x2 - x3 - x1 - x0 = 0
    off_braid_probes = [
        ((10, 22, 28, 40, 70, 110), (0, 0, 0, 1, 0, 0)),   # crosses x3+x0 == x2+x1 (50 == 50)
        ((10, 19, 25, 40, 70, 110), (0, 0, 1, 0, 0, 0)),   # crosses 2*x2 == x3+x0 (50 == 50)
        ((10, 17, 23, 42, 70, 110), (0, 0, 1, 0, 0, 0)),   # crosses 3*x2 == x3+x1+x0 (69 == 69)
    ]
    for base_pt, delta_vec in off_braid_probes:
        p_minus = tuple(base_pt[i] - delta_vec[i] for i in range(6))
        p_zero = base_pt
        p_plus = tuple(base_pt[i] + delta_vec[i] for i in range(6))
        # Ensure all 3 points stay strictly inside the SAME braid chamber!
        assert list(p_minus) == sorted(p_minus) and len(set(p_minus)) == 6
        assert list(p_plus) == sorted(p_plus) and len(set(p_plus)) == 6
        v_m = eval_6max6_hexagon(p_minus, u1l, um2)
        v_0 = eval_6max6_hexagon(p_zero, u1l, um2)
        v_p = eval_6max6_hexagon(p_plus, u1l, um2)
        assert (v_p - 2 * v_0 + v_m) == 0  # Zero off-braid kink!
        assert v_m == 6 * max(p_minus) and v_0 == 6 * max(p_zero) and v_p == 6 * max(p_plus)

    hex_eval_us = (time.perf_counter_ns() - t_hex0) // 1000

    # Part B: Syl_2(S_6) 45-orbit compression + sub-200ms padic_local_global Z[1/2] & Z[1/6] benchmark!
    t_syl0 = time.perf_counter_ns()
    syl2_group, reps_45 = build_syl2_s6_and_45_orbits()

    # Build the 11 D_6-orbit gate columns evaluated at lineality (+1..-1) + 2 profiles x 45 Syl_2(S_6) chamber reps (92 rows x 11 cols):
    edges_6 = hex_data["edges_6"]
    orbit_m2_sets = hex_data["orbit_gate_sets"]

    eval_pts_92: List[Tuple[int, ...]] = [(1, 1, 1, 1, 1, 1), (-1, -1, -1, -1, -1, -1)]
    for sp in ((0, 3, 7, 15, 31, 63), (-29, -13, -5, 2, 9, 23)):
        for rep in reps_45:
            eval_pts_92.append(tuple(sp[rep[i]] for i in range(6)))

    A_syl: List[List[int]] = []
    b_6max6: List[int] = []
    b_1max6: List[int] = []
    for pt in eval_pts_92:
        row: List[int] = [sum(pt[i] if pt[i] >= pt[j] else pt[j] for i, j in edges_6)]
        for orbm2 in orbit_m2_sets:
            s_orb = 0
            for ga, gb in orbm2:
                sa = (pt[ga[0][0]] if pt[ga[0][0]] >= pt[ga[0][1]] else pt[ga[0][1]]) + (
                    pt[ga[1][0]] if pt[ga[1][0]] >= pt[ga[1][1]] else pt[ga[1][1]]
                )
                sb = (pt[gb[0][0]] if pt[gb[0][0]] >= pt[gb[0][1]] else pt[gb[0][1]]) + (
                    pt[gb[1][0]] if pt[gb[1][0]] >= pt[gb[1][1]] else pt[gb[1][1]]
                )
                s_orb += sa if sa >= sb else sb
            row.append(s_orb)
        A_syl.append(row)
        b_6max6.append(6 * max(pt))
        b_1max6.append(max(pt))

    t_solve0 = time.perf_counter_ns()
    res_6max6 = solve_z_half(A_syl, b_6max6)
    res_z_sixth = solve_s_integral(A_syl, b_1max6, inverted_primes=(2, 3), run_f3_prescreen=False)
    res_1max6 = solve_z_half(A_syl, b_1max6)
    solve_only_us = (time.perf_counter_ns() - t_solve0) // 1000
    syl_total_us = (time.perf_counter_ns() - t_syl0) // 1000

    assert res_6max6.status == "CERTIFIED_EXACT" and res_6max6.c_num is not None
    assert res_z_sixth.status == "CERTIFIED_EXACT" and (6 % res_z_sixth.c_den == 0)
    for r_i, row in enumerate(A_syl):
        assert dot_int(row, res_6max6.c_num) == res_6max6.c_den * b_6max6[r_i]

    assert res_1max6.status in ("UNSAT_MOD3_PRESCREEN", "UNSAT_PADIC")
    assert res_1max6.obstruction_prime == 3 and res_1max6.obstruction_y is not None
    ya = vec_mat_mul(res_1max6.obstruction_y, A_syl)
    yb = dot_int(res_1max6.obstruction_y, b_1max6)
    if res_1max6.status == "UNSAT_MOD3_PRESCREEN":
        assert all(v % 3 == 0 for v in ya) and (yb % 3 != 0)

    # Assert strict < 0.2s (< 200,000 us) performance requirement from SPEC.md §4!
    assert syl_total_us < 200_000, f"Syl_2(S_6) + Z[1/2] engine exceeded 0.2s budget: {syl_total_us} us"

    matrix_bits = matrix_max_bit_length(A_syl)
    sol_bits = max(abs(v).bit_length() for v in res_6max6.c_num)

    return {
        "d6_hexagon_formula": {
            "epistemic_tag": "CERTIFIED_EXACT",
            "layer1_pairwise_orbits": {"edges": 6, "short_diagonals": 6, "long_diagonals": 3, "total": 15},
            "active_layer1_gates": len(u1l),
            "active_layer2_m2_gates": len(um2),
            "weight_values_set": sorted(set(u1l.values()) | set(um2.values())),
            "chamber_points_verified": checked_pts,
            "off_braid_2nd_diff_probes_passed": len(off_braid_probes),
            "runtime_us": hex_eval_us,
        },
        "syl2_s6_z_half_engine": {
            "syl2_order": len(syl2_group),
            "braid_chamber_orbit_count": len(reps_45),
            "compressed_matrix_shape": [len(A_syl), len(A_syl[0])],
            "compressed_matrix_max_bits": matrix_bits,
            "six_max6_z_half_status": res_6max6.status,
            "six_max6_c_den": res_6max6.c_den,
            "six_max6_c_num_max_bits": sol_bits,
            "one_max6_fixed_dict_status": res_1max6.status,
            "one_max6_fixed_dict_obstruction_prime": res_1max6.obstruction_prime,
            "unconstrained_max6_z_half_epistemic_tag": "OPEN_BUDGET_EXCEEDED",
            "solve_only_runtime_us": solve_only_us,
            "total_syl2_engine_runtime_us": syl_total_us,
            "under_200ms_budget": syl_total_us < 200_000,
        },
    }


def sweep_track_a_stage() -> Dict[str, Any]:
    t0 = time.perf_counter_ns()
    vol_table = sweep_minkowski_product_volumes_d2_to_10()
    max6_bench = benchmark_max6_and_syl2_engine()
    total_us = (time.perf_counter_ns() - t0) // 1000
    return {
        "stage": "cycle2_track_a_max6_and_volumes",
        "minkowski_product_volumes_d2_to_10": vol_table,
        "max6_and_syl2_benchmarks": max6_bench,
        "total_runtime_us": total_us,
    }
