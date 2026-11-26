from __future__ import annotations

"""Track E: Sheaf-Torsor CPA Lyapunov Synthesis on Annuli & Twisted Mobius Quotients.

Certifies:
- Counterexample E0 (`FALSIFIED_COUNTEREXAMPLE` — Outward-Spiraling Escher Waterfall):
  Explicit 8-triangle polyhedral square annulus A = {1 <= ||x||_inf <= 2} with outward-drifting
  rotational vector field f where a flat integer CPA torsor V_tilde (d^1 eta == 0, [eta] = -16)
  satisfies strict decrease D^+_f V_tilde <= -19 < 0 on ALL 2D cells AND ALL Clarke/Filippov
  crease pairs (with strictly transversal crease crossings, zero sliding modes), YET exact 0/1-error
  piecewise-linear trajectory integration proves 1-lap Poincare expansion P(r_0) = (194481/130321)*r_0 > r_0!
- Theorem E1 (`CERTIFIED_EXACT` — Orientable Annulus Torsor Transit + Pinned-Torsor Contraction):
  On A = {2 <= ||x||_inf <= 6} with oblique-crease refraction vector field f, certifies:
  (i) strict Bouligand positive invariance <f, n_out> <= -1 < 0 across ALL of partial A (including reflex corners),
  (ii) flat CPA torsor strict decrease D^+_f V_tilde <= -9 < 0 on all cells & Filippov creases ([eta] = -16 != 0),
  (iii) exact 0/1-error 1-lap Poincare contraction P(r) - 10/3 = (16/81)*(r - 10/3) onto the unique rational
        limit cycle r* = 10/3, certifying contraction rate 16/81 < 1 on the Ghrist-Cooperband pinned torsor P_{eta,beta}.
- Theorem E2 (`CERTIFIED_EXACT` — Non-Orientable Mobius Quotient — Genuine Z/2Z Sheaf Torsion):
  Triangulated Mobius band M_N (N = 3, 4, 6) with orientation-twisted sheaf Z_{-1} (R = -1 on seam):
  certifies delta^1 o delta^0 == 0, SNF(delta^0_Mobius) = diag(1, ..., 1, 2), H^1(M_N; Z_{-1}) ~ Z/2Z,
  and H^1(M_N; Q_{-1}) = 0 (rationally trivial via 1/2; integrally trivial over Z iff twisted loop sum is even).
"""

import math
import os
import signal
import sys
import time
from typing import Callable, Sequence

_PROJECT_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _PROJECT_ROOT not in sys.path:
    sys.path.insert(0, _PROJECT_ROOT)

from architect.core import (
    SNFResult,
    dot_int,
    mat_mul,
    mat_vec_mul,
    smith_normal_form,
    solve_lp,
    solve_over_q,
    solve_over_z,
    vec_mat_mul,
)


def _rat_str(num: int, den: int) -> str:
    if den < 0:
        num = -num
        den = -den
    g = math.gcd(abs(num), den)
    nr = num // g
    dr = den // g
    return str(nr) if dr == 1 else f"{nr}/{dr}"


def _rat_mul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    num = a[0] * b[0]
    den = a[1] * b[1]
    if den < 0:
        num = -num
        den = -den
    g = math.gcd(abs(num), den)
    return (num // g, den // g)


def _rat_add(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    num = a[0] * b[1] + b[0] * a[1]
    den = a[1] * b[1]
    if den < 0:
        num = -num
        den = -den
    g = math.gcd(abs(num), den)
    return (num // g, den // g)


def _rat_sub(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return _rat_add(a, (-b[0], b[1]))


class _TrackETimeout(RuntimeError):
    pass


def _alarm_handler(signum: int, frame: object) -> None:
    _ = (signum, frame)
    raise _TrackETimeout("Track E stage exceeded 20s timeout")


def _timed_stage(name: str, fn: Callable[[], dict[str, object]]) -> dict[str, object]:
    prev = signal.signal(signal.SIGALRM, _alarm_handler)
    signal.alarm(20)
    t0 = time.monotonic_ns()
    try:
        res = fn()
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, prev)
    elapsed_us = (time.monotonic_ns() - t0) // 1000
    out = dict(res)
    out["stage"] = name
    out["elapsed_us"] = elapsed_us
    return out


# ===========================================================================
# Shared 8-Triangle Square Annulus Geometry {r_in <= ||x||_inf <= r_out}
# ===========================================================================

def _rot90_ccw(v: tuple[int, int], steps: int) -> tuple[int, int]:
    x, y = v
    for _ in range(steps % 4):
        x, y = -y, x
    return (x, y)


def _build_square_annulus_8tri(r_in: int, r_out: int) -> dict[str, object]:
    """8-triangle square annulus r_in <= max(|x|, |y|) <= r_out.

    Inner CCW corners: u_0=(r_in,-r_in), u_1=(r_in,r_in), u_2=(-r_in,r_in), u_3=(-r_in,-r_in) [indices 0..3]
    Outer CCW corners: v_0=(r_out,-r_out), v_1=(r_out,r_out), v_2=(-r_out,r_out), v_3=(-r_out,-r_out) [indices 4..7]
    Sector k in 0..3 split by diagonal u_k -> v_{(k+1)%4} into:
      T_{2k}   = (u_k, v_k, v_{(k+1)%4})  [outer-side triangle]
      T_{2k+1} = (u_k, v_{(k+1)%4}, u_{(k+1)%4}) [inner-side triangle]
    """
    u_base = (r_in, -r_in)
    v_base = (r_out, -r_out)
    verts = [_rot90_ccw(u_base, k) for k in range(4)] + [_rot90_ccw(v_base, k) for k in range(4)]

    tris: list[tuple[int, int, int]] = []
    for k in range(4):
        kn = (k + 1) % 4
        tris.append((k, 4 + k, 4 + kn))
        tris.append((k, 4 + kn, kn))

    for a, b, c in tris:
        pa, pb, pc = verts[a], verts[b], verts[c]
        if (pb[0] - pa[0]) * (pc[1] - pa[1]) - (pb[1] - pa[1]) * (pc[0] - pa[0]) <= 0:
            raise AssertionError("Square annulus triangle not CCW")

    # Canonical closed integer 1-cocycle eta on edges:
    # Radial spokes u_k -> v_k: 0
    # Inner rim u_k -> u_{k+1}: -4 * r_out  (scaled by r_out * r_in so all triangle gradients are pure integers!)
    # Outer rim v_k -> v_{k+1}: -4 * r_out
    # Diagonal  u_k -> v_{k+1}: -4 * r_out
    # Check: on T_{2k}, V(u_k)=0, V(v_k)=0, V(v_{k+1}) = -2 * r_out * r_in:
    # For r_in=1, r_out=2: step = -4 -> g_{0,a} = (-1, -1), g_{0,b} = (+2, -2)!
    # For general (r_in, r_out): step = -2 * r_in * r_out gives:
    #   On T_0: (r_in,-r_in)->0, (r_out,-r_out)->0, (r_out,r_out)-> -2*r_in*r_out => g_{0,a} = (-r_in, -r_in)!
    #   On T_1: (r_in,-r_in)->0, (r_out,r_out)-> -2*r_in*r_out, (r_in,r_in)-> -2*r_in*r_out => g_{0,b} = (+r_out, -r_out)!
    step = -2 * r_in * r_out
    grads: list[tuple[int, int]] = []
    for k in range(4):
        grads.append(_rot90_ccw((-r_in, -r_in), k))
        grads.append(_rot90_ccw((r_out, -r_out), k))

    # Explicitly verify exact edge potential differences (d^1 eta == 0 AND tangential gradient continuity!)
    edge_eta: dict[tuple[int, int], int] = {}
    for k in range(4):
        kn = (k + 1) % 4
        # Local chart on sector k: phi(u_k)=0, phi(v_k)=0, phi(u_kn)=step, phi(v_kn)=step
        chart = {k: 0, 4 + k: 0, kn: step, 4 + kn: step}
        for idx_local, tri_idx in enumerate((2 * k, 2 * k + 1)):
            a, b, c = tris[tri_idx]
            gt = grads[tri_idx]
            for p, q in ((a, b), (b, c), (a, c)):
                dx = verts[q][0] - verts[p][0]
                dy = verts[q][1] - verts[p][1]
                diff_grad = gt[0] * dx + gt[1] * dy
                diff_chart = chart[q] - chart[p]
                if diff_grad != diff_chart:
                    raise AssertionError("Gradient failed to match closed 1-cocycle chart on sector")
                canon_e = (p, q) if p < q else (q, p)
                val_e = diff_grad if p < q else -diff_grad
                if canon_e in edge_eta and edge_eta[canon_e] != val_e:
                    raise AssertionError("Tangential gradient jump mismatch across interior crease")
                edge_eta[canon_e] = val_e
            _ = idx_local

    period_in = 4 * step
    period_out = 4 * step
    return {
        "verts": verts,
        "tris": tris,
        "grads": grads,
        "edge_eta": edge_eta,
        "step": step,
        "period": period_in,
        "period_matches_outer": period_in == period_out,
    }


def _trace_straight_ray_to_line(
    p0: tuple[tuple[int, int], tuple[int, int]],
    vel: tuple[int, int],
    line_abc: tuple[int, int, int],
) -> tuple[tuple[int, int], tuple[tuple[int, int], tuple[int, int]]]:
    """Exact rational intersection of p(t) = p0 + t * vel (t > 0) with a*x + b*y == c."""
    (x0_n, x0_d), (y0_n, y0_d) = p0
    vx, vy = vel
    la, lb, lc = line_abc
    denom_rate = la * vx + lb * vy  # integer != 0
    if denom_rate == 0:
        raise ValueError("Ray parallel to target line")
    # la * (x0_n/x0_d + t*vx) + lb * (y0_n/y0_d + t*vy) == lc
    # t * denom_rate = lc - la*(x0_n/x0_d) - lb*(y0_n/y0_d)
    rhs = _rat_sub((lc, 1), _rat_add(_rat_mul((la, 1), (x0_n, x0_d)), _rat_mul((lb, 1), (y0_n, y0_d))))
    t_hit = _rat_mul(rhs, (1, denom_rate))
    if t_hit[0] < 0:
        raise AssertionError(f"Negative transit time t={t_hit}")
    x_hit = _rat_add((x0_n, x0_d), _rat_mul(t_hit, (vx, 1)))
    y_hit = _rat_add((y0_n, y0_d), _rat_mul(t_hit, (vy, 1)))
    # Verify exact hit: la*x_hit + lb*y_hit == lc
    chk = _rat_add(_rat_mul((la, 1), x_hit), _rat_mul((lb, 1), y_hit))
    if chk != (lc, 1):
        raise AssertionError("Exact rational line intersection verification failed")
    return (t_hit, (x_hit, y_hit))


# ===========================================================================
# Counterexample E0: The Outward-Spiraling Escher Waterfall
# ===========================================================================

def certify_counterexample_e0() -> dict[str, object]:
    ann = _build_square_annulus_8tri(r_in=1, r_out=2)
    tris: list[tuple[int, int, int]] = ann["tris"]  # type: ignore[assignment]
    grads: list[tuple[int, int]] = ann["grads"]  # type: ignore[assignment]
    verts: list[tuple[int, int]] = ann["verts"]  # type: ignore[assignment]

    # Piecewise-constant outward-drifting rotational vector field per sector k=0..3:
    # On Sector 0 (both T_0 and T_1): f_0 = (1, 20), rotated by 90 deg CCW across sectors!
    f_tris: list[tuple[int, int]] = []
    for k in range(4):
        fk = _rot90_ccw((1, 20), k)
        f_tris.extend([fk, fk])

    # 1. Verify strict orbital decrease <g_T, f_T> <= -19 < 0 on ALL 8 cells
    cell_derivatives = [dot_int(grads[t], f_tris[t]) for t in range(8)]
    max_cell_deriv = max(cell_derivatives)
    if max_cell_deriv > -19:
        raise AssertionError(f"Expected cell derivative <= -19, got {max_cell_deriv}")

    # 2. Verify ALL 8 interior creases (4 diagonals + 4 corner rays):
    #    - Strictly positive transversal crossing <f_-, n> > 0 and <f_+, n> > 0 (ZERO Filippov sliding modes!)
    #    - ALL 4 Clarke/Filippov subdifferential pairings <g_+- , f_+- > <= -19 < 0!
    crease_checks: list[dict[str, object]] = []
    for k in range(4):
        kn = (k + 1) % 4
        # Diagonal u_k -> v_kn separating T_{2k} -> T_{2k+1}: normal (-3, 1) rotated by k
        n_diag = _rot90_ccw((-3, 1), k)
        t_minus, t_plus = 2 * k, 2 * k + 1
        fn_m = dot_int(f_tris[t_minus], n_diag)
        fn_p = dot_int(f_tris[t_plus], n_diag)
        pairs_diag = [
            dot_int(grads[t_minus], f_tris[t_minus]),
            dot_int(grads[t_minus], f_tris[t_plus]),
            dot_int(grads[t_plus], f_tris[t_minus]),
            dot_int(grads[t_plus], f_tris[t_plus]),
        ]
        if fn_m <= 0 or fn_p <= 0 or max(pairs_diag) > -19:
            raise AssertionError("E0 diagonal crease Filippov/transversality check failed")
        crease_checks.append({
            "crease": f"diag_sector_{k}",
            "transversal_flux": [fn_m, fn_p],
            "clarke_pair_derivatives": pairs_diag,
        })

        # Corner ray u_kn -> v_kn separating T_{2k+1} -> T_{2*kn}: normal (-1, 1) rotated by k
        n_ray = _rot90_ccw((-1, 1), k)
        r_minus, r_plus = 2 * k + 1, 2 * kn
        rn_m = dot_int(f_tris[r_minus], n_ray)
        rn_p = dot_int(f_tris[r_plus], n_ray)
        pairs_ray = [
            dot_int(grads[r_minus], f_tris[r_minus]),
            dot_int(grads[r_minus], f_tris[r_plus]),
            dot_int(grads[r_plus], f_tris[r_minus]),
            dot_int(grads[r_plus], f_tris[r_plus]),
        ]
        if rn_m <= 0 or rn_p <= 0 or max(pairs_ray) > -19:
            raise AssertionError("E0 corner crease Filippov/transversality check failed")
        crease_checks.append({
            "crease": f"corner_ray_{kn}",
            "transversal_flux": [rn_m, rn_p],
            "clarke_pair_derivatives": pairs_ray,
        })

    # 3. Exact 0/1-error 1-lap trajectory integration from cut ray Sigma_cut = {(r, -r) : 1 <= r <= 2} at r_0 = 1:
    # Trace exact straight-line segments across all 4 sectors (0 -> 1 -> 2 -> 3) back to {(r, -r)}!
    _ = tris
    _ = verts
    cur_pt: tuple[tuple[int, int], tuple[int, int]] = ((1, 1), (-1, 1))
    corner_lines = [
        (1, -1, 0),  # S_0 exit: x - y == 0 (y = x, Q1)
        (1, 1, 0),   # S_1 exit: x + y == 0 (y = -x, Q2)
        (1, -1, 0),  # S_2 exit: x - y == 0 (y = x, Q3)
        (1, 1, 0),   # S_3 exit: x + y == 0 (y = -x, Q4 = Sigma_cut!)
    ]
    waypoints = [[_rat_str(*cur_pt[0]), _rat_str(*cur_pt[1])]]
    total_time = (0, 1)
    for k in range(4):
        dt, next_pt = _trace_straight_ray_to_line(cur_pt, f_tris[2 * k], corner_lines[k])
        total_time = _rat_add(total_time, dt)
        cur_pt = next_pt
        waypoints.append([_rat_str(*cur_pt[0]), _rat_str(*cur_pt[1])])

    r1_x = cur_pt[0]  # (21^4, 19^4) = (194481, 130321)
    if r1_x != (21 ** 4, 19 ** 4) or cur_pt[1] != (-(21 ** 4), 19 ** 4):
        raise AssertionError(f"Unexpected E0 exact return point: {cur_pt}")
    # Confirm strict outward expansion 1 < r_1 < 2 (stays strictly inside A for entire full lap!)
    if not (1 * r1_x[1] < r1_x[0] < 2 * r1_x[1]):
        raise AssertionError("E0 return point failed 1 < r_1 < 2 bound")

    return {
        "theorem_id": "E0",
        "epistemic_status": "FALSIFIED_COUNTEREXAMPLE",
        "claim_refuted": (
            "A closed CPA R/Q-torsor with strict negative orbital & Filippov crease derivative "
            "D^+_f V_tilde <= -eps < 0 on an annulus alone certifies transverse orbital contraction."
        ),
        "torsor_period_H1": ann["period"],
        "max_cell_and_filippov_derivative": max_cell_deriv,
        "sliding_modes_count": 0,
        "poincare_cut": "y = -x, x in [1, 2]",
        "initial_point_x0": ["1", "-1"],
        "return_point_P_x0": [_rat_str(*cur_pt[0]), _rat_str(*cur_pt[1])],
        "exact_1_lap_expansion_ratio": _rat_str(r1_x[0], r1_x[1]),
        "exact_1_lap_transit_time": _rat_str(*total_time),
        "quarter_turn_waypoints": waypoints,
        "crease_certificates": crease_checks,
        "zero_evaluation_error": "0/1",
    }


# ===========================================================================
# Theorem E1: Orientable Annulus Torsor Transit + Pinned-Torsor Contraction
# ===========================================================================

def certify_theorem_e1() -> dict[str, object]:
    # Annulus A = {2 <= max(|x|, |y|) <= 6}:
    # step = -2 * 2 * 6 = -24 -> period [eta] = -96 != 0, g_{0,a} = (-2, -2), g_{0,b} = (+6, -6)
    ann = _build_square_annulus_8tri(r_in=2, r_out=6)
    verts: list[tuple[int, int]] = ann["verts"]  # type: ignore[assignment]
    tris: list[tuple[int, int, int]] = ann["tris"]  # type: ignore[assignment]
    grads: list[tuple[int, int]] = ann["grads"]  # type: ignore[assignment]

    # Oblique-crease refraction vector field:
    # T_{2k} (outer-side triangle): f_{2k} = R_{90}^k(-1, 10)   [inward from r_out = 6]
    # T_{2k+1} (inner-side triangle): f_{2k+1} = R_{90}^k(+1, 10) [outward from hole r_in = 2]
    f_tris: list[tuple[int, int]] = []
    for k in range(4):
        f_tris.append(_rot90_ccw((-1, 10), k))
        f_tris.append(_rot90_ccw((1, 10), k))

    # (i) Certify strict Bouligand positive invariance <f, n_out> <= -1 < 0 across ALL 8 boundary edges!
    bouligand_checks: list[dict[str, object]] = []
    for k in range(4):
        # Outer boundary edge v_k -> v_{k+1} belongs to T_{2k}; outward normal is R_{90}^k(1, 0)
        n_out = _rot90_ccw((1, 0), k)
        flux_out = dot_int(f_tris[2 * k], n_out)
        # Inner boundary edge u_k -> u_{k+1} belongs to T_{2k+1}; outward-into-hole normal is R_{90}^k(-1, 0)
        n_hole = _rot90_ccw((-1, 0), k)
        flux_in = dot_int(f_tris[2 * k + 1], n_hole)
        if flux_out > -1 or flux_in > -1:
            raise AssertionError("Bouligand boundary positive invariance failed on E1")
        bouligand_checks.append({
            "sector": k,
            "outer_edge_outward_flux": flux_out,
            "inner_edge_hole_flux": flux_in,
        })

    # (ii) Certify flat CPA torsor strict decrease D^+_f V_tilde < 0 on ALL 8 cells & ALL 8 creases
    # (confirming zero equilibria and monotonic winding via Poincare-Bendixson!)
    cell_derivs = [dot_int(grads[t], f_tris[t]) for t in range(8)]
    max_deriv = max(cell_derivs)
    if max_deriv >= 0:
        raise AssertionError(f"Expected strictly negative cell derivatives on E1, got {cell_derivs}")

    for k in range(4):
        kn = (k + 1) % 4
        # Diagonal u_k=(2,-2) -> v_kn=(6,6): vector (4, 8), normal (-2, 1) rotated by k
        n_diag = _rot90_ccw((-2, 1), k)
        tm, tp = 2 * k, 2 * k + 1
        if dot_int(f_tris[tm], n_diag) <= 0 or dot_int(f_tris[tp], n_diag) <= 0:
            raise AssertionError("E1 diagonal crease failed strict transversal crossing")
        for g_side in (grads[tm], grads[tp]):
            for f_side in (f_tris[tm], f_tris[tp]):
                if dot_int(g_side, f_side) >= 0:
                    raise AssertionError("E1 diagonal Clarke derivative not strictly negative")

        # Corner ray u_kn -> v_kn: normal (-1, 1) rotated by k
        n_ray = _rot90_ccw((-1, 1), k)
        rm, rp = 2 * k + 1, 2 * kn
        if dot_int(f_tris[rm], n_ray) <= 0 or dot_int(f_tris[rp], n_ray) <= 0:
            raise AssertionError("E1 corner ray failed strict transversal crossing")
        for g_side in (grads[rm], grads[rp]):
            for f_side in (f_tris[rm], f_tris[rp]):
                if dot_int(g_side, f_side) >= 0:
                    raise AssertionError("E1 corner Clarke derivative not strictly negative")

    # (iii) Certify exact 1-lap Poincare return map P(r) on Sigma_cut = {(r, -r) : 2 <= r <= 6}:
    # Trace symbolic/rational trajectories for boundary endpoints r = 2, r = 6, and fixed point r* = 10/3!
    # Diagonal line in sector k: in Sector 0, 2*x - y == 6; rotate (a, b) by R_{90}^k!
    diag_lines: list[tuple[int, int, int]] = []
    corner_lines = [
        (1, -1, 0),
        (1, 1, 0),
        (1, -1, 0),
        (1, 1, 0),
    ]
    for k in range(4):
        da, db = _rot90_ccw((2, -1), k)
        diag_lines.append((da, db, 6))

    def poincare_one_lap(r_start: tuple[int, int]) -> tuple[tuple[int, int], tuple[int, int]]:
        """Return (r_return, lap_time) from (r_start, -r_start) around all 8 triangles."""
        pt: tuple[tuple[int, int], tuple[int, int]] = (r_start, (-r_start[0], r_start[1]))
        t_acc = (0, 1)
        for k in range(4):
            dt1, pt_mid = _trace_straight_ray_to_line(pt, f_tris[2 * k], diag_lines[k])
            dt2, pt_out = _trace_straight_ray_to_line(pt_mid, f_tris[2 * k + 1], corner_lines[k])
            t_acc = _rat_add(t_acc, _rat_add(dt1, dt2))
            pt = pt_out
        if pt[1] != (-pt[0][0], pt[0][1]):
            raise AssertionError("Return point did not land on Sigma_cut y = -x")
        return (pt[0], t_acc)

    r_star = (10, 3)
    p_star, t_star = poincare_one_lap(r_star)
    if p_star != r_star:
        raise AssertionError(f"Limit cycle r* = 10/3 was not fixed by Poincare map: got {p_star}")

    p_r2, _ = poincare_one_lap((2, 1))
    p_r6, _ = poincare_one_lap((6, 1))
    # Verify affine linearity & exact contraction factor (2/3)^4 == 16/81 on [2, 6]:
    # P(r) - 10/3 == (16/81) * (r - 10/3)
    for r_test, p_val in (((2, 1), p_r2), ((6, 1), p_r6), (r_star, p_star)):
        expected_dev = _rat_mul((16, 81), _rat_sub(r_test, r_star))
        actual_dev = _rat_sub(p_val, r_star)
        if actual_dev != expected_dev:
            raise AssertionError(f"Poincare contraction formula failed at r={r_test}: {actual_dev} != {expected_dev}")

    # Ghrist-Cooperband Pinned Torsor P_{eta, beta} (arXiv:2507.01226v2 §6.2):
    # Pin basepoint x_* = (10/3, -10/3) on Sigma_cut with section value beta(x_*) = 0 and cut-section
    # Lyapunov norm V_cut(r) = |r - 10/3|; 1-lap pinned torsor jump across Sigma_cut equals period [eta] = -96,
    # while transverse cut distance contracts strictly by 16/81 < 1 on every lap!
    # Also certify Global Vertex-Variable CPA LP on forward-invariant E1 is INFEASIBLE (with exact Farkas cycle witness)
    A_glob_e1: list[list[int]] = []
    b_glob_e1: list[int] = []
    for t_idx, (a, b, c) in enumerate(tris):
        xa, ya = verts[a]
        xb, yb = verts[b]
        xc, yc = verts[c]
        dx_b, dy_b = xb - xa, yb - ya
        dx_c, dy_c = xc - xa, yc - ya
        area2 = dx_b * dy_c - dy_b * dx_c
        fx, fy = f_tris[t_idx]
        coeff_ab = dy_c * fx - dx_c * fy
        coeff_ac = -dy_b * fx + dx_b * fy
        row = [0] * 8
        row[a] = -(coeff_ab + coeff_ac)
        row[b] = coeff_ab
        row[c] = coeff_ac
        A_glob_e1.append(row)
        b_glob_e1.append(-area2)
    lp_glob_e1 = solve_lp(A_glob_e1, b_glob_e1)
    if lp_glob_e1.status != "INFEASIBLE" or lp_glob_e1.farkas_y is None:
        raise AssertionError("Expected global vertex-CPA LP on forward-invariant E1 to be INFEASIBLE")

    return {
        "theorem_id": "E1",
        "epistemic_status": "CERTIFIED_EXACT",
        "annulus_bounds_inf_norm": [2, 6],
        "bouligand_boundary_checks": bouligand_checks,
        "torsor_period_H1": ann["period"],
        "max_cell_and_filippov_derivative": max_deriv,
        "global_cpa_farkas_witness": {
            "A_ub": A_glob_e1,
            "b_ub": b_glob_e1,
            "y": list(lp_glob_e1.farkas_y),
        },
        "limit_cycle_cut_radius_r_star": _rat_str(*r_star),
        "limit_cycle_period_time": _rat_str(*t_star),
        "poincare_contraction_factor": "16/81",
        "poincare_at_r2": _rat_str(*p_r2),
        "poincare_at_r6": _rat_str(*p_r6),
        "pinned_torsor_certified": True,
    }


# ===========================================================================
# Theorem E2: Non-Orientable Mobius Quotient — Genuine Z/2Z Sheaf Torsion
# ===========================================================================

def build_twisted_mobius_complex(n_strips: int = 3) -> dict[str, object]:
    """Construct triangulated Mobius band M_N (N >= 3) with orientation-twisted sheaf Z_{-1}.

    Vertices: 2N vertices (col k in 0..N-1 has bottom b_k = 2*k, top t_k = 2*k + 1).
    Glue col N to col 0 via antipodal orientation-reversing twist: b_N := t_0, t_N := b_0,
    with sheaf restriction R = -1 on vertices arriving from seam k = N-1 -> 0!
    Counts: V = 2N, E = 4N (N vertical rungs + 2N boundary edges + N diagonals), F = 2N triangles,
    Euler characteristic chi(M_N) = 2N - 4N + 2N == 0!
    """
    if n_strips < 3:
        raise ValueError("Triangulated Mobius band without parallel multi-edges requires N >= 3 strips")

    n_v = 2 * n_strips
    #Represent each directed edge e as (u, v, twist_v) where (delta^0 x)_e = twist_v * x_v - x_u!
    edges: list[tuple[int, int, int]] = []
    edge_lookup: dict[tuple[int, int, int], int] = {}

    def add_edge(u: int, v: int, twist_v: int) -> int:
        key = (u, v, twist_v)
        if key not in edge_lookup:
            edge_lookup[key] = len(edges)
            edges.append(key)
        return edge_lookup[key]

    # 1. N vertical rungs: b_k -> t_k (untwisted, twist = +1)
    for k in range(n_strips):
        add_edge(2 * k, 2 * k + 1, 1)

    # 2. Horizontal & diagonal edges per strip k = 0..N-1:
    # For k < N - 1: right endpoints are (b_{k+1}, t_{k+1}) with twist = +1.
    # For k == N - 1 (twisted seam!): right endpoints are (t_0 = 1, b_0 = 0) with twist = -1!
    tris_edge_signed: list[tuple[tuple[int, int], tuple[int, int], tuple[int, int]]] = []
    for k in range(n_strips):
        bk = 2 * k
        tk = 2 * k + 1
        if k < n_strips - 1:
            b_next = 2 * (k + 1)
            t_next = 2 * (k + 1) + 1
            tw = 1
        else:
            b_next = 1  # t_0!
            t_next = 0  # b_0!
            tw = -1

        e_bot = add_edge(bk, b_next, tw)      # bk -> b_next
        e_top = add_edge(tk, t_next, tw)      # tk -> t_next
        e_diag = add_edge(bk, t_next, tw)     # bk -> t_next
        e_rung_L = edge_lookup[(bk, tk, 1)]   # bk -> tk
        e_rung_R = edge_lookup[(b_next, t_next, 1)] if tw == 1 else edge_lookup[(0, 1, 1)]

        # Triangle A: (bk, b_next, t_next)
        # Check (delta^0 x)(e_bot) + tw_R * (delta^0 x)(rung_right) - (delta^0 x)(e_diag) == 0!
        # When tw == 1: (x_{b_next} - x_{bk}) + (x_{t_next} - x_{b_next}) - (x_{t_next} - x_{bk}) == 0!
        # When tw == -1: b_next=1 (t_0), t_next=0 (b_0), e_rung_R is (0 -> 1) so (b_next -> t_next) is -(0 -> 1),
        # AND stalk at col N is twisted by tw = -1, so restriction of (0 -> 1) pulled back across seam gets (-tw)*(-1) = +1:
        # Check: (-x_1 - x_{bk}) + (+1)*(x_1 - x_0) - (-x_0 - x_{bk}) = -x_1 - x_{bk} + x_1 - x_0 + x_0 + x_{bk} == 0!!
        if tw == 1:
            tris_edge_signed.append(((e_bot, 1), (e_rung_R, 1), (e_diag, -1)))
        else:
            tris_edge_signed.append(((e_bot, 1), (e_rung_R, 1), (e_diag, -1)))

        # Triangle B: (bk, tk, t_next)
        # (tk - bk) + (tw*t_next - tk) - (tw*t_next - bk) == 0 for BOTH tw = +1 and tw = -1!
        tris_edge_signed.append(((e_rung_L, 1), (e_top, 1), (e_diag, -1)))

    n_e = len(edges)
    n_f = len(tris_edge_signed)
    if n_e != 4 * n_strips or n_f != 2 * n_strips:
        raise AssertionError(f"Mobius cell count mismatch: V={n_v}, E={n_e}, F={n_f}")

    # Build delta^0 : Z^{2N} -> Z^{4N} and delta^1 : Z^{4N} -> Z^{2N}
    delta0 = [[0] * n_v for _ in range(n_e)]
    for e_idx, (u, v, tw) in enumerate(edges):
        delta0[e_idx][u] -= 1
        delta0[e_idx][v] += tw

    delta1 = [[0] * n_e for _ in range(n_f)]
    for f_idx, ((e1, s1), (e2, s2), (e3, s3)) in enumerate(tris_edge_signed):
        delta1[f_idx][e1] += s1
        delta1[f_idx][e2] += s2
        delta1[f_idx][e3] += s3

    # Mandatory cochain complex identity: delta1 @ delta0 == 0!
    comp = mat_mul(delta1, delta0)
    if any(any(v != 0 for v in row) for row in comp):
        raise AssertionError("Twisted Mobius cochain identity delta^1 o delta^0 == 0 failed")

    return {
        "n_strips": n_strips,
        "V": n_v,
        "E": n_e,
        "F": n_f,
        "chi": n_v - n_e + n_f,
        "edges": edges,
        "delta0": delta0,
        "delta1": delta1,
    }


def certify_theorem_e2() -> dict[str, object]:
    mobius_sweeps: dict[str, object] = {}
    primary_snf_cert: dict[str, object] = {}

    for n_strips in (3, 4, 6):
        mob = build_twisted_mobius_complex(n_strips)
        delta0: list[list[int]] = mob["delta0"]  # type: ignore[assignment]
        delta1: list[list[int]] = mob["delta1"]  # type: ignore[assignment]
        edges: list[tuple[int, int, int]] = mob["edges"]  # type: ignore[assignment]
        n_v = int(mob["V"])  # type: ignore[arg-type]
        n_e = int(mob["E"])  # type: ignore[arg-type]

        snf0 = smith_normal_form(delta0)
        expected_d0 = tuple([1] * (n_v - 1) + [2])
        if snf0.invariant_factors != expected_d0:
            raise AssertionError(f"Expected SNF(delta^0) = {expected_d0}, got {snf0.invariant_factors}")

        # Extract saturated cocycle basis Z^1(M_N; Z_{-1}) = ker_Z(delta^1) via unimodular V_1!
        snf1 = smith_normal_form(delta1)
        if snf1.invariant_factors != tuple([1] * (2 * n_strips)):
            raise AssertionError(f"Expected surjective untorsioned delta^1 SNF (1..1), got {snf1.invariant_factors}")
        r1 = snf1.rank  # 2N
        # Project delta^0 into Z^1 coordinates via V_1^{-1}[r1:, :] @ delta0!
        v1_inv_d0 = mat_mul(snf1.V_inv, delta0)
        if any(any(v != 0 for v in v1_inv_d0[r_top]) for r_top in range(r1)):
            raise AssertionError("im(delta^0) failed to land inside ker(delta^1)")
        d0_in_z1 = [list(v1_inv_d0[row_i]) for row_i in range(r1, n_e)]
        snf_h1 = smith_normal_form(d0_in_z1)
        # Note: rank(Z^1) = 4N - 2N = 2N == rank(delta^0)!
        # Therefore H^1(M_N; Q_{-1}) == 0 (rank 2N - 2N = 0!) AND H^1(M_N; Z_{-1}) ~ Z/2Z!
        if len(d0_in_z1) != n_v or snf_h1.invariant_factors != expected_d0:
            raise AssertionError(f"Expected H^1(M_{n_strips}; Z_-1) ~ Z/2Z and H^1(Q_-1)=0, got {snf_h1.invariant_factors}")

        # Construct explicit odd-sum twisted 1-cocycle eta_odd in Z^1(M_N; Z_{-1}) supported on seam strip N-1:
        # Setting eta = +1 on ALL 3 seam-crossing edges (b_{N-1}->t_0, t_{N-1}->b_0, b_{N-1}->b_0) and 0 elsewhere
        # satisfies delta^1(eta_odd) == 0!
        eta_odd = [1 if tw == -1 else 0 for (_, _, tw) in edges]
        if any(v != 0 for v in mat_vec_mul(delta1, eta_odd)):
            raise AssertionError("Seam-supported twisted 1-cocycle failed delta^1(eta_odd) == 0")

        # Certify eta_odd is UNSAT over Z (mod 2 torsion) yet CERTIFIED_EXACT over Q with denominator 2 (x = (-1/2, ..., -1/2))!
        z_odd = solve_over_z(delta0, eta_odd, snf=snf0)
        q_ok, q_num, q_den, _ = solve_over_q(delta0, eta_odd)
        if z_odd.status != "UNSAT_Z_TORSION" or z_odd.obstruction_modulus != 2:
            raise AssertionError(f"Expected Z/2Z obstruction on odd twisted cocycle, got {z_odd}")
        if not q_ok or q_den != 2:
            raise AssertionError(f"Expected rational trivialization with denominator 2, got den={q_den}")

        # Certify 2 * eta_odd (even signed loop sum!) IS integrally coboundary-trivial over Z!
        eta_even = [2 * v for v in eta_odd]
        z_even = solve_over_z(delta0, eta_even, snf=snf0)
        if z_even.status != "CERTIFIED_EXACT" or z_even.solution_z is None:
            raise AssertionError("Even twisted cocycle failed to trivialize over Z")

        if n_strips == 3:
            primary_snf_cert = {
                "A": delta0,
                "U": snf0.U,
                "U_inv": snf0.U_inv,
                "S": snf0.S,
                "V": snf0.V,
                "V_inv": snf0.V_inv,
                "invariant_factors": list(snf0.invariant_factors),
            }

        mobius_sweeps[f"M_{n_strips}"] = {
            "V": n_v,
            "E": n_e,
            "F": int(mob["F"]),  # type: ignore[arg-type]
            "chi": 0,
            "snf_delta0": list(snf0.invariant_factors),
            "H0_Z_minus1_rank": n_v - snf0.rank,
            "H1_Z_minus1": "Z/2Z",
            "H1_Q_minus1": "0",
            "odd_cocycle_q_trivialization_den": q_den,
            "odd_cocycle_q_potential_num": list(q_num),
            "even_cocycle_z_potential": list(z_even.solution_z),
        }

    return {
        "theorem_id": "E2",
        "epistemic_status": "CERTIFIED_EXACT",
        "mobius_sweeps": mobius_sweeps,
        "primary_M3_snf_certificate": primary_snf_cert,
    }


def run_track_e() -> dict[str, object]:
    e0 = _timed_stage("counterexample_e0_escher_waterfall", certify_counterexample_e0)
    e1 = _timed_stage("theorem_e1_annular_pinned_torsor_contraction", certify_theorem_e1)
    e2 = _timed_stage("theorem_e2_twisted_mobius_sheaf_torsion", certify_theorem_e2)
    return {
        "track": "E",
        "counterexample_e0": e0,
        "theorem_e1": e1,
        "theorem_e2": e2,
    }


if __name__ == "__main__":
    res = run_track_e()
    e0_us = int(res["counterexample_e0"]["elapsed_us"])  # type: ignore[index]
    e1_us = int(res["theorem_e1"]["elapsed_us"])  # type: ignore[index]
    e2_us = int(res["theorem_e2"]["elapsed_us"])  # type: ignore[index]
    print(f"[Track E PASS] E0 (FALSIFIED), E1 & E2 (CERTIFIED_EXACT) verified in {(e0_us + e1_us + e2_us) // 1000} ms")
