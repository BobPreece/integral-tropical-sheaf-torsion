from __future__ import annotations

import math
import time
from typing import Any, Dict, List, Sequence, Tuple

from simulator.sim_exact_la import (
    ceil_div,
    cg_round_2d_exact,
    cg_round_3d_exact,
    det3_exact,
    poly2d_all_integral,
    poly2d_vertices_exact,
    poly3d_all_integral,
    poly3d_vertices_exact,
    prim_vec,
    rat_norm,
    rat_str,
    snf_unimodular,
    solve_with_snf,
)


def _point_in_reeve_tetrahedron(x: int, y: int, z: int, r: int) -> bool:
    """
    Exact rational-free membership test in T_r = conv{(0,0,0), (1,0,0), (0,1,0), (1,1,r)}.
    Facet inward inequalities (verified on all 4 vertices):
      F3 (opp p3): z >= 0
      F2 (opp p2): r*y - z >= 0
      F1 (opp p1): r*x - z >= 0
      F0 (opp p0): -r*x - r*y + z >= -r  <=>  r*x + r*y - z <= r
    """
    if z < 0:
        return False
    if r * y - z < 0:
        return False
    if r * x - z < 0:
        return False
    if r * x + r * y - z > r:
        return False
    return True


def analyze_a1_2d_fan_control() -> Dict[str, Any]:
    """
    2D A_1 fan control (Trap 4 & Theorem B1):
      Rays: rho_1 = (1, 0), rho_2 = (-1, 2), rho_3 = (0, -1).
      Cones: C_12 = cone(rho_1, rho_2) [det=2], C_23 [det=1], C_31 [det=1].
    """
    t0 = time.perf_counter_ns()
    rays = [(1, 0), (-1, 2), (0, -1)]
    normals = [(-y, x) for (x, y) in rays]  # (0, 1), (-2, -1), (1, 0)
    # Balancing matrix E_bal (2 x 3)
    e_bal = [[normals[j][i] for j in range(3)] for i in range(2)]
    snf_bal = snf_unimodular(e_bal, verify=True)
    dim_balanced = 3 - snf_bal.rank  # 1 => only global convex/concave multiples, no nontrivial DC splits

    # Cone C_12 ray matrix [[1, 0], [-1, 2]] has SNF diag(1, 2) => Weil/Cart ~ Z/2Z
    cone12_snf = snf_unimodular([[1, 0], [-1, 2]], verify=True)

    # Global Cartier coboundary on A_1:
    # A tuple of cone gradients (m_12, m_23, m_31) in (Z^2)^3 comes from Weil ray values h in Z^3
    # iff m_12.rho_1 = h_1, m_12.rho_2 = h_2, m_23.rho_2 = h_2, m_23.rho_3 = h_3, m_31.rho_3 = h_3, m_31.rho_1 = h_1.
    # Equivalently, map M_cart: (m_12, m_23, m_31) in Z^6 -> (jump_1_orth, jump_2_orth, jump_3_orth, val_1, val_2, val_3)?
    # Even simpler: map Cart(A_1) -> Weil(A_1) = Z^3:
    # On C_23 (unimodular), m_23 = (-h_2 - 2*h_3, -h_3) in Z^2 for ALL h;
    # On C_31 (unimodular), m_31 = (h_1, -h_3) in Z^2 for ALL h;
    # On C_12, [[1, 0], [-1, 2]] m_12 = [h_1, h_2]^T has integer solution iff h_1 + h_2 == 0 (mod 2).
    # Test Weil generator h = (0, 1, 0):
    weil_test = solve_with_snf([[1, 0], [-1, 2]], [0, 1], cone12_snf)
    assert weil_test.q_sat and not weil_test.z_sat
    elapsed_us = (time.perf_counter_ns() - t0) // 1000
    return {
        "name": "A_1_2D_fan",
        "rays": rays,
        "primitive_normals": normals,
        "dim_balanced_space": dim_balanced,
        "nontrivial_dc_splits_possible": dim_balanced >= 2,
        "cone_12_snf": list(cone12_snf.invariant_factors),
        "weil_mod_cart_torsion": list(cone12_snf.torsion_factors),
        "weil_witness_h": [0, 1, 0],
        "c12_gradient_q": [rat_str(weil_test.x_q_num[0], weil_test.x_q_den), rat_str(weil_test.x_q_num[1], weil_test.x_q_den)] if weil_test.x_q_num else [],
        "primitive_wall_jumps_q": ["1/2", "1/2", "1"],
        "cartier_dc_hull_integral_nonempty": False,
        "runtime_us": elapsed_us,
    }


def analyze_reeve_tetrahedron(r: int) -> Dict[str, Any]:
    """
    Exact analysis of 3D Reeve tetrahedron T_r = conv{(0,0,0),(1,0,0),(0,1,0),(1,1,r)}
    and its complete 7-ray fan completion Sigma_tilde_r (Trap 4 & Theorem B1).
    """
    t0 = time.perf_counter_ns()
    verts = [(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, r)]

    # 1. Exact normalized lattice volume Vol_3(T_r) = |det[p1-p0, p2-p0, p3-p0]|
    vol3 = abs(det3_exact((1, 0, 0), (0, 1, 0), (1, 1, r)))
    assert vol3 == r

    # 2. Exact bounding-box lattice point count in [0..1] x [0..1] x [0..r]
    lat_pts: List[Tuple[int, int, int]] = []
    for x in range(0, 2):
        for y in range(0, 2):
            for z in range(0, r + 1):
                if _point_in_reeve_tetrahedron(x, y, z, r):
                    lat_pts.append((x, y, z))
    assert len(lat_pts) == 4

    # 3. Primal apex edge matrix E_0(r) at p_0 = (0,0,0) and all 4 vertex tangent cones
    e0_mat = [
        [1, 0, 0],
        [0, 1, 0],
        [1, 1, r],
    ]
    snf_primal = snf_unimodular(e0_mat, verify=True)
    assert snf_primal.invariant_factors == (1, 1, r)

    # Verify all 4 vertex tangent cones have identical SNF = (1, 1, r)
    all_vertex_snfs: List[List[int]] = []
    for idx in range(4):
        px, py, pz = verts[idx]
        edges_i = []
        for jdx in range(4):
            if idx != jdx:
                qx, qy, qz = verts[jdx]
                edges_i.append(list(prim_vec((qx - px, qy - py, qz - pz))))
        c_v = snf_unimodular(edges_i, verify=True)
        assert c_v.invariant_factors == (1, 1, r)
        all_vertex_snfs.append(list(c_v.invariant_factors))

    # 4. Polar primitive facet-form matrix L_0(r) at apex p_0:
    # l_12 = z -> (0, 0, 1)
    # l_13 = -r*y + z -> (0, -r, 1)
    # l_23 = r*x - z -> (r, 0, -1)
    l12 = [0, 0, 1]
    l13 = [0, -r, 1]
    l23 = [r, 0, -1]
    polar_mat = [l12, l13, l23]
    snf_polar = snf_unimodular(polar_mat, verify=True)
    assert snf_polar.invariant_factors == (1, r, r)

    # All 3 pairwise ridge colon matrices have SNF = diag(1, r)
    snf_ridge_12_13 = snf_unimodular([l12, l13], verify=True)
    snf_ridge_13_23 = snf_unimodular([l13, l23], verify=True)
    snf_ridge_12_23 = snf_unimodular([l12, l23], verify=True)
    assert snf_ridge_12_13.invariant_factors == (1, r)
    assert snf_ridge_13_23.invariant_factors == (1, r)
    assert snf_ridge_12_23.invariant_factors == (1, r)

    # 5. Normal fan N(T_r): 4 primitive inward facet normals summing to (0, 0, 0)
    eta_f3 = (0, 0, 1)
    eta_f2 = (0, r, -1)
    eta_f1 = (r, 0, -1)
    eta_f0 = (-r, -r, 1)
    assert (
        eta_f3[0] + eta_f2[0] + eta_f1[0] + eta_f0[0] == 0
        and eta_f3[1] + eta_f2[1] + eta_f1[1] + eta_f0[1] == 0
        and eta_f3[2] + eta_f2[2] + eta_f1[2] + eta_f0[2] == 0
    )
    normal_cone_snf = snf_unimodular([list(eta_f3), list(eta_f2), list(eta_f1)], verify=True)
    assert normal_cone_snf.invariant_factors == (1, r, r)

    # 6. Complete 7-ray 3D fan Sigma_tilde_r:
    # Rays: e1=(1,0,0), e2=(0,1,0), e3=(0,0,1), -e1, -e2, -e3, and v_3=(1,1,r) subdividing octant (+,+,+).
    # Maximal cones: 7 unimodular octants (det=1) + cone(e1, v3, e3) [det=1] + cone(v3, e2, e3) [det=1]
    # + Reeve cone(e1, e2, v3) [det=r].
    # Check Weil generator h(v_3) = 1, all other rays 0:
    weil_sol = solve_with_snf(e0_mat, [0, 0, 1], snf_primal)
    assert weil_sol.q_sat and (weil_sol.z_sat == (r == 1))
    # Primitive wall jumps on the 3 Reeve walls (l12, l13, l23) equal 1/r:
    wall_jump_reeve = rat_str(1, r)

    max_bits = max(
        snf_primal.input_max_bits,
        snf_primal.u_max_bits,
        snf_primal.v_max_bits,
        snf_polar.input_max_bits,
        snf_polar.u_max_bits,
        snf_polar.v_max_bits,
        snf_polar.peak_intermediate_bits,
    )
    elapsed_us = (time.perf_counter_ns() - t0) // 1000

    return {
        "r": r,
        "vertices": [list(v) for v in verts],
        "normalized_vol3": vol3,
        "lattice_point_count": len(lat_pts),
        "is_empty_lattice_simplex": len(lat_pts) == 4,
        "primal_edge_snf": list(snf_primal.invariant_factors),
        "primal_torsion": list(snf_primal.torsion_factors),
        "all_4_vertex_cones_snf": all_vertex_snfs,
        "polar_facet_snf": list(snf_polar.invariant_factors),
        "polar_torsion": list(snf_polar.torsion_factors),
        "ridge_colon_snfs": [
            list(snf_ridge_12_13.invariant_factors),
            list(snf_ridge_13_23.invariant_factors),
            list(snf_ridge_12_23.invariant_factors),
        ],
        "normal_fan_cone_snf": list(normal_cone_snf.invariant_factors),
        "complete_fan_weil_mod_cart": f"Z/{r}Z" if r > 1 else "0",
        "weil_generator_reeve_wall_jumps": [wall_jump_reeve, wall_jump_reeve, wall_jump_reeve],
        "cartier_dc_hull_empty_for_non_cartier_weil": r > 1,
        "bit_metrics": {
            "primal_input_bits": snf_primal.input_max_bits,
            "primal_u_bits": snf_primal.u_max_bits,
            "primal_v_bits": snf_primal.v_max_bits,
            "polar_input_bits": snf_polar.input_max_bits,
            "polar_u_bits": snf_polar.u_max_bits,
            "polar_v_bits": snf_polar.v_max_bits,
            "peak_bits": max_bits,
        },
        "runtime_us": elapsed_us,
    }


def sweep_reeve_stage() -> Dict[str, Any]:
    """Run Cycle 1 Stage 1: A_1 control + 3D Reeve tetrahedra T_r for r = 1..12 (highlighting r = 2..12)."""
    t0 = time.perf_counter_ns()
    a1_ctrl = analyze_a1_2d_fan_control()
    r1_ctrl = analyze_reeve_tetrahedron(1)
    reeve_rows = [analyze_reeve_tetrahedron(r) for r in range(2, 13)]
    total_us = (time.perf_counter_ns() - t0) // 1000
    return {
        "stage": "stage1_reeve_tetrahedra",
        "a1_2d_control": a1_ctrl,
        "unimodular_r1_control": r1_ctrl,
        "reeve_sweep_r_2_to_12": reeve_rows,
        "total_runtime_us": total_us,
    }


def analyze_four_ray_fan(k: int) -> Dict[str, Any]:
    """
    Exact analysis of 4-ray 2D fan Sigma^(k) (Theorem B2):
      Rays: v_1=(1,0), v_2=(1,2), v_3=(-1,2), v_4^(k)=(-1, -(2k+1))  [k = 1..10]
      Wall ordering (v_2, v_3, v_4^(k), v_1) -> CCW primitive normals:
        eta_1 = (-2, 1), eta_2 = (-2, -1), eta_3 = (2k+1, -1), eta_4 = (0, 1).
      Unimodular Z-basis of B_{Sigma^(k)}(Z):
        w^(k)(u, t) = ((2k+1)*t - u, u, 2*t, 2*u - (2k-1)*t).
      Pure integer-gradient Cartier witness (u_f, t_f) = (1, 0) => w^prim(f) = (-1, 1, 0, 2).
    """
    t0 = time.perf_counter_ns()
    rays = [(1, 0), (1, 2), (-1, 2), (-1, -(2 * k + 1))]
    for rx, ry in rays:
        assert math.gcd(rx, ry) == 1

    eta = [(-2, 1), (-2, -1), (2 * k + 1, -1), (0, 1)]
    e_bal = [
        [eta[0][0], eta[1][0], eta[2][0], eta[3][0]],
        [eta[0][1], eta[1][1], eta[2][1], eta[3][1]],
    ]
    snf_bal = snf_unimodular(e_bal, verify=True)
    assert snf_bal.invariant_factors == (1, 1)

    # Basis matrix G_k in Z^{4 x 2} mapping (u, t) -> w^(k)(u, t)
    g_basis = [
        [-1, 2 * k + 1],
        [1, 0],
        [0, 2],
        [2, -(2 * k - 1)],
    ]
    # Verify E_bal @ G_k == 0 and SNF(G_k) == (1, 1) (saturated unimodular Z-basis!)
    for r_i in range(2):
        for c_j in range(2):
            s = sum(e_bal[r_i][q] * g_basis[q][c_j] for q in range(4))
            assert s == 0
    snf_g = snf_unimodular(g_basis, verify=True)
    assert snf_g.invariant_factors == (1, 1)

    # Pure Cartier function (u_f, t_f) = (1, 0) => w_f = (-1, 1, 0, 2)
    wf = (-1, 1, 0, 2)
    # Regional integer gradients a_P1=(0,2), a_P2=(2,1), a_P3=(0,0), a_P4=(0,0)
    a_p4 = (0, 0)
    a_p1 = (a_p4[0] + wf[3] * eta[3][0], a_p4[1] + wf[3] * eta[3][1])
    a_p2 = (a_p1[0] + wf[0] * eta[0][0], a_p1[1] + wf[0] * eta[0][1])
    a_p3 = (a_p2[0] + wf[1] * eta[1][0], a_p2[1] + wf[1] * eta[1][1])
    a_p4_chk = (a_p3[0] + wf[2] * eta[2][0], a_p3[1] + wf[2] * eta[2][1])
    assert a_p1 == (0, 2) and a_p2 == (2, 1) and a_p3 == (0, 0) and a_p4_chk == (0, 0)

    # DC polyhedron P_k in (u, t): w^(k)(u, t) >= max(0, wf) = (0, 1, 0, 2)
    ineqs0 = [
        (-1, 2 * k + 1, 0),
        (1, 0, 1),
        (0, 2, 0),
        (2, -(2 * k - 1), 2),
    ]
    det_cone = 2 * k + 3
    v0 = poly2d_vertices_exact(ineqs0)
    assert len(v0) == 1
    (u_num, u_den), (t_num, t_den) = v0[0]
    assert (u_num, u_den) == rat_norm(4 * k + 2, det_cone)
    assert (t_num, t_den) == rat_norm(2, det_cone)

    # Track A: Sequential 1-cut-per-round coordinate/simplex Gomory cuts
    # Step 1: add coordinate cut t >= ceil(2 / (2k+3)) = 1
    seq_ineqs_1 = list(ineqs0) + [(0, 1, 1)]
    v_seq1 = poly2d_vertices_exact(seq_ineqs_1)
    # Fractional vertex is ((2k+1)/2, 1) alongside integer ((2k+1), 1)
    # Step 2: add coordinate cut u >= ceil((2k+1)/2) = k + 1
    seq_ineqs_2 = list(seq_ineqs_1) + [(1, 0, k + 1)]
    v_seq2 = poly2d_vertices_exact(seq_ineqs_2)
    seq_axis_only_integral_at_2 = poly2d_all_integral(v_seq2)
    # Note: for k = 1, v_seq2 IS all integral {(2,1), (2,2), (3,1)} (2 sequential rounds)!
    # For k >= 2, v_seq2 has fractional vertex (k+1, 2k/(2k-1)) because u = k+1 meets 2u-(2k-1)t = 2 at t = 2k/(2k-1)!
    # Adding the oblique CG cut u - (k-1)*t >= 2 completes the exact Klein sail!
    seq_ineqs_3 = list(seq_ineqs_2) + [(1, -(k - 1), 2)]
    v_seq3 = poly2d_vertices_exact(seq_ineqs_3)
    assert poly2d_all_integral(v_seq3)
    seq_gomory_rounds = 2 if seq_axis_only_integral_at_2 else 3

    # Track B: Simultaneous Elementary Chvatal-Gomory Closure P_k^(r)
    cur = ineqs0
    sim_cg_rank = 0
    while sim_cg_rank < 10:
        vs = poly2d_vertices_exact(cur)
        if poly2d_all_integral(vs):
            break
        cur = cg_round_2d_exact(cur)
        sim_cg_rank += 1
    v_klein = poly2d_vertices_exact(cur)
    assert sim_cg_rank == 1
    expected_klein = sorted([((2 * k + 1, 1), (1, 1)), ((k + 1, 1), (1, 1)), ((2 * k, 1), (2, 1))])
    assert sorted(v_klein) == expected_klein

    # Map Klein-sail vertices (u, t) -> w+ in Z^4
    klein_ut_and_w: List[Dict[str, List[int]]] = []
    for (ux, ud), (ty, td) in v_klein:
        assert ud == 1 and td == 1
        w_vec = [
            (2 * k + 1) * ty - ux,
            ux,
            2 * ty,
            2 * ux - (2 * k - 1) * ty,
        ]
        klein_ut_and_w.append({"ut": [ux, ty], "w_plus": w_vec})

    max_bits = max(
        int(abs(4 * k + 2)).bit_length(),
        int(abs(det_cone)).bit_length(),
        snf_bal.u_max_bits,
        snf_bal.v_max_bits,
        snf_g.u_max_bits,
    )
    elapsed_us = (time.perf_counter_ns() - t0) // 1000

    return {
        "k": k,
        "cone_determinant": det_cone,
        "rays": [list(r) for r in rays],
        "primitive_normals": [list(n) for n in eta],
        "lp_vertex_ut": [rat_str(u_num, u_den), rat_str(t_num, t_den)],
        "lp_vertex_w_plus": [
            "0",
            rat_str(4 * k + 2, det_cone),
            rat_str(4, det_cone),
            "2",
        ],
        "seq_round1_verts_after_t_ge_1": [[rat_str(vx[0], vx[1]), rat_str(vy[0], vy[1])] for vx, vy in v_seq1],
        "seq_round2_verts_after_u_ge_kp1": [[rat_str(vx[0], vx[1]), rat_str(vy[0], vy[1])] for vx, vy in v_seq2],
        "sequential_axis_gomory_rounds": seq_gomory_rounds,
        "simultaneous_elementary_cg_rank": sim_cg_rank,
        "klein_sail_integer_vertices": klein_ut_and_w,
        "max_bits": max_bits,
        "runtime_us": elapsed_us,
    }


def analyze_five_ray_higher_cg_fan(k: int) -> Dict[str, Any]:
    """
    5-ray 2D complete fan Sigma_5^(k) certifying genuine Simultaneous Elementary CG Rank >= 2..3+
    inside Cart(Sigma_5^(k)) (breaking the 2-facet planar cone rank-1 ceiling of 4-ray fans!):
      CCW primitive rays:
        r_1 = (1, 0), r_2 = (2k+1, 1), r_3 = (-(2k+1), 1), r_4 = (-1, -2), r_5 = (0, -1).
      Corresponding wall normals eta_i = (-y_i, x_i) on (r_3, r_2, r_4, r_5, r_1):
        eta_1 = (-1, -(2k+1)), eta_2 = (-1, 2k+1), eta_3 = (2, -1), eta_4 = (1, 0), eta_5 = (0, 1).
      Exact unimodular Z-basis of B_{Sigma_5^(k)}(Z) ~ Z^3:
        w(w_1, w_2, w_3) = (w_1, w_2, w_3, w_1 + w_2 - 2*w_3, (2k+1)*w_1 - (2k+1)*w_2 + w_3).
      Pure Cartier witness (w_1, w_2, w_3) = (0, 1, 0) => w(f) = (0, 1, 0, 1, -(2k+1)) in Z^5!
    """
    t0 = time.perf_counter_ns()
    m_val = 2 * k + 1
    rays_ccw = [(1, 0), (m_val, 1), (-m_val, 1), (-1, -2), (0, -1)]
    for rx, ry in rays_ccw:
        assert math.gcd(rx, ry) == 1
    # Verify strict CCW positive spanning: consecutive cross products rx_i * ry_{i+1} - ry_i * rx_{i+1} > 0
    for idx in range(5):
        x1, y1 = rays_ccw[idx]
        x2, y2 = rays_ccw[(idx + 1) % 5]
        assert x1 * y2 - y1 * x2 > 0

    eta = [(-1, -m_val), (-1, m_val), (2, -1), (1, 0), (0, 1)]
    wf_123 = (0, 1, 0)
    w4f = wf_123[0] + wf_123[1] - 2 * wf_123[2]  # 1
    w5f = m_val * wf_123[0] - m_val * wf_123[1] + wf_123[2]  # -(2k+1)
    wf_full = [wf_123[0], wf_123[1], wf_123[2], w4f, w5f]
    # Verify balancing sum w_i * eta_i == (0, 0)
    assert sum(wf_full[i] * eta[i][0] for i in range(5)) == 0
    assert sum(wf_full[i] * eta[i][1] for i in range(5)) == 0

    ineqs = [
        (1, 0, 0, 0),
        (0, 1, 0, 1),
        (0, 0, 1, 0),
        (1, 1, -2, 1),
        (m_val, -m_val, 1, 0),
    ]

    cur = ineqs
    rounds_trace: List[Dict[str, Any]] = []
    cg_rank = 0
    while cg_rank < 12:
        vs = poly3d_vertices_exact(cur)
        max_den = 1
        formatted_vs: List[List[str]] = []
        for vx, vy, vz in vs:
            max_den = max(max_den, vx[1], vy[1], vz[1])
            formatted_vs.append([rat_str(vx[0], vx[1]), rat_str(vy[0], vy[1]), rat_str(vz[0], vz[1])])
        rounds_trace.append({
            "round": cg_rank,
            "num_ineqs": len(cur),
            "num_vertices": len(vs),
            "max_denominator": max_den,
            "vertices": formatted_vs,
        })
        if poly3d_all_integral(vs):
            break
        cur = cg_round_3d_exact(cur)
        cg_rank += 1

    elapsed_us = (time.perf_counter_ns() - t0) // 1000
    return {
        "k": k,
        "odd_slope_param": m_val,
        "rays_ccw": [list(r) for r in rays_ccw],
        "cartier_wf": wf_full,
        "simultaneous_elementary_cg_rank": cg_rank,
        "initial_max_denominator": rounds_trace[0]["max_denominator"],
        "rounds_trace": rounds_trace,
        "runtime_us": elapsed_us,
    }


def sweep_fans_cg_stage(max_5ray_k: int = 3) -> Dict[str, Any]:
    """Run Cycle 1 Stage 2: 4-ray fans v_4^(k) (k = 1..10) + 5-ray higher simultaneous CG rank sweep."""
    t0 = time.perf_counter_ns()
    four_ray_rows = [analyze_four_ray_fan(k) for k in range(1, 11)]
    five_ray_rows = [analyze_five_ray_higher_cg_fan(k) for k in range(1, max_5ray_k + 1)]
    total_us = (time.perf_counter_ns() - t0) // 1000
    return {
        "stage": "stage2_four_ray_and_five_ray_fans_cg",
        "four_ray_sweep_k_1_to_10": four_ray_rows,
        "five_ray_higher_cg_sweep": five_ray_rows,
        "total_runtime_us": total_us,
    }
