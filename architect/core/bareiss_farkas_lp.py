from __future__ import annotations

"""Fraction-Free Bareiss Simplex with Avis Lexicographic Pivoting, Vertex Enumeration & Lattice Volume.

Strict Constitutional Compliance:
- 100% Python 3.9+ stdlib only (`math`, `dataclasses`, `itertools`, `typing`).
- Zero `float`, zero `fractions.Fraction`, zero `/` (`ast.Div`), zero `isinstance`.
"""

from dataclasses import dataclass
import itertools
import math
from typing import Sequence

from architect.core.exact_int_la import (
    bareiss_det,
    canonical_primitive_vector,
    dot_int,
    extract_pivot_basis,
    mat_shape,
    mat_vec_mul,
    primitive_direction,
    vec_mat_mul,
)


@dataclass(frozen=True)
class LPResult:
    status: str  # "OPTIMAL" | "FEASIBLE" | "INFEASIBLE" | "UNBOUNDED"
    primal_num: tuple[int, ...] | None
    primal_den: int
    obj_num: int | None
    obj_den: int
    farkas_y: tuple[int, ...] | None
    farkas_y_eq: tuple[int, ...] | None
    dual_opt_y: tuple[int, ...] | None
    dual_opt_den: int
    unbounded_ray: tuple[int, ...] | None
    pivots: int


def _reduce_rat_vec(nums: Sequence[int], den: int) -> tuple[tuple[int, ...], int]:
    if den == 0:
        raise ValueError("Zero denominator in _reduce_rat_vec")
    if den < 0:
        nums = [-int(x) for x in nums]
        den = -den
    g = math.gcd(den, *(abs(int(x)) for x in nums))
    return (tuple(int(x) // g for x in nums), den // g)


def _reduce_rat_scalar(num: int, den: int) -> tuple[int, int]:
    if den == 0:
        raise ValueError("Zero denominator in _reduce_rat_scalar")
    if den < 0:
        num = -num
        den = -den
    g = math.gcd(abs(num), den)
    return (num // g, den // g)


def _lex_ratio_less(
    row_a: Sequence[int],
    piv_a: int,
    row_b: Sequence[int],
    piv_b: int,
    lex_cols: Sequence[int],
) -> bool:
    """Exact integer comparison: is (1/piv_a) * row_a[lex_cols] <_lex (1/piv_b) * row_b[lex_cols]?"""
    for col in lex_cols:
        lhs = row_a[col] * piv_b
        rhs = row_b[col] * piv_a
        if lhs < rhs:
            return True
        if lhs > rhs:
            return False
    return False


def _bareiss_simplex_pivot(
    T: list[list[int]],
    cbar: list[int],
    basis: list[int],
    D: int,
    leave_r: int,
    enter_e: int,
    n_cols_total: int,
) -> int:
    """Execute one exact fraction-free Bareiss Simplex pivot on (leave_r, enter_e)."""
    piv = T[leave_r][enter_e]
    if piv <= 0:
        raise AssertionError("Simplex pivot entry must be strictly positive")
    row_r = T[leave_r]
    m = len(T)

    for i in range(m):
        if i == leave_r:
            continue
        row_i = T[i]
        tie = row_i[enter_e]
        if tie == 0:
            for j in range(n_cols_total):
                num = piv * row_i[j]
                if num % D != 0:
                    raise AssertionError("Bareiss zero-col exact division failed")
                row_i[j] = num // D
        else:
            for j in range(n_cols_total):
                num = piv * row_i[j] - tie * row_r[j]
                if num % D != 0:
                    raise AssertionError("Bareiss row exact division failed")
                row_i[j] = num // D

    ce = cbar[enter_e]
    for j in range(n_cols_total):
        num = piv * cbar[j] - ce * row_r[j]
        if num % D != 0:
            raise AssertionError("Bareiss objective exact division failed")
        cbar[j] = num // D

    basis[leave_r] = enter_e
    return piv


def solve_lp(
    A_ub: Sequence[Sequence[int]],
    b_ub: Sequence[int],
    c_max: Sequence[int] | None = None,
    A_eq: Sequence[Sequence[int]] | None = None,
    b_eq: Sequence[int] | None = None,
) -> LPResult:
    """Exact rational LP solver over integer A_ub x <= b_ub (and optional A_eq x == b_eq).

    Uses Fraction-Free Bareiss Simplex with Avis-Chvatal Lexicographic Pivoting:
    - 100% immune to cycling on degenerate cones (including origin/braid arrangements b = 0).
    - Emits exact rational primal point (primal_num, primal_den) OR exact non-negative
      integer Farkas dual certificate y >= 0 with y^T A == 0 and y^T b < 0.
    - Self-verifies primal feasibility, strong duality, or Farkas infeasibility on every call.
    """
    m_ub, d_ub = mat_shape(A_ub)
    if len(b_ub) != m_ub:
        raise ValueError("b_ub length mismatch in solve_lp")

    m_eq = 0
    d_eq = 0
    if A_eq is not None:
        m_eq, d_eq = mat_shape(A_eq)
        if b_eq is None or len(b_eq) != m_eq:
            raise ValueError("b_eq length mismatch in solve_lp")

    if m_ub > 0 and m_eq > 0 and d_ub != d_eq:
        raise ValueError("Column dimension mismatch between A_ub and A_eq")
    d = d_ub if m_ub > 0 else (d_eq if m_eq > 0 else (len(c_max) if c_max is not None else 0))
    if c_max is not None and len(c_max) != d:
        raise ValueError("c_max dimension mismatch in solve_lp")

    # Assemble combined inequality system A_all x <= b_all:
    # rows 0 .. m_ub-1:              A_ub x <= b_ub
    # rows m_ub .. m_ub+m_eq-1:      A_eq x <= b_eq
    # rows m_ub+m_eq .. m_ub+2m_eq-1: -A_eq x <= -b_eq
    A_all: list[list[int]] = [[int(x) for x in row] for row in A_ub]
    b_all: list[int] = [int(x) for x in b_ub]
    if A_eq is not None and b_eq is not None and m_eq > 0:
        for i in range(m_eq):
            A_all.append([int(x) for x in A_eq[i]])
            b_all.append(int(b_eq[i]))
        for i in range(m_eq):
            A_all.append([-int(x) for x in A_eq[i]])
            b_all.append(-int(b_eq[i]))

    m = len(A_all)
    if m == 0:
        if c_max is None or all(int(ci) == 0 for ci in c_max):
            return LPResult(
                status="OPTIMAL" if c_max is not None else "FEASIBLE",
                primal_num=tuple(0 for _ in range(d)),
                primal_den=1,
                obj_num=0 if c_max is not None else None,
                obj_den=1,
                farkas_y=None,
                farkas_y_eq=None,
                dual_opt_y=(),
                dual_opt_den=1,
                unbounded_ray=None,
                pivots=0,
            )
        ray = tuple(1 if int(ci) > 0 else (-1 if int(ci) < 0 else 0) for ci in c_max)
        return LPResult(
            status="UNBOUNDED",
            primal_num=tuple(0 for _ in range(d)),
            primal_den=1,
            obj_num=None,
            obj_den=1,
            farkas_y=None,
            farkas_y_eq=None,
            dual_opt_y=None,
            dual_opt_den=1,
            unbounded_ray=ray,
            pivots=0,
        )

    # Phase I variable layout:
    # u_0..u_{d-1} (cols 0..d-1)
    # v_0..v_{d-1} (cols d..2d-1)
    # x_0          (col 2d)
    # s_0..s_{m-1} (cols 2d+1 .. 2d+m)
    # rhs          (col 2d+m+1)
    col_x0 = 2 * d
    col_s0 = 2 * d + 1
    col_rhs = 2 * d + 1 + m
    n_cols_p1 = col_rhs + 1
    lex_cols_p1 = [col_rhs] + [col_s0 + i for i in range(m)]

    T: list[list[int]] = []
    for i in range(m):
        row = [0] * n_cols_p1
        ai = A_all[i]
        for j in range(d):
            row[j] = ai[j]
            row[d + j] = -ai[j]
        row[col_x0] = -1
        row[col_s0 + i] = 1
        row[col_rhs] = b_all[i]
        T.append(row)

    basis = [col_s0 + i for i in range(m)]
    D = 1
    pivots = 0

    # Phase I objective: maximize z = -x_0  <=>  D * z + D * x_0 = 0
    cbar = [0] * n_cols_p1
    cbar[col_x0] = 1

    min_b = min(b_all)
    if min_b < 0:
        # Choose lexicographically smallest (b_i, e_i): among tied min b_i, largest row index i
        # has e_i = (0, ..., 0, 1) which is strictly lexicographically smallest!
        r_min = -1
        for i in range(m):
            if b_all[i] == min_b:
                r_min = i  # last index with b_i == min_b achieves strict lex minimum!
        # Negate row r_min so T[r_min][col_x0] becomes +1, keeping D = 1
        for j in range(n_cols_p1):
            T[r_min][j] = -T[r_min][j]
        D = _bareiss_simplex_pivot(T, cbar, basis, D, r_min, col_x0, n_cols_p1)
        pivots += 1

    # Phase I Lexicographic Simplex Loop
    while True:
        enter_e = -1
        for j in range(col_rhs):
            if cbar[j] < 0:
                enter_e = j
                break
        if enter_e == -1:
            break

        leave_r = -1
        for i in range(m):
            piv_cand = T[i][enter_e]
            if piv_cand <= 0:
                continue
            if leave_r == -1 or _lex_ratio_less(
                T[i], piv_cand, T[leave_r], T[leave_r][enter_e], lex_cols_p1
            ):
                leave_r = i
        if leave_r == -1:
            raise AssertionError("Phase I auxiliary LP cannot be unbounded above 0")

        D = _bareiss_simplex_pivot(T, cbar, basis, D, leave_r, enter_e, n_cols_p1)
        pivots += 1

    # Check Phase I optimum: rhs_obj = cbar[col_rhs] == D * (-x_0)
    if cbar[col_rhs] < 0:
        # INFEASIBLE! Extract exact Farkas dual witness from slack columns s_0..s_{m-1}
        y_raw = [cbar[col_s0 + i] for i in range(m)]
        if any(yi < 0 for yi in y_raw):
            raise AssertionError("Farkas witness entry unexpectedly negative")
        y_prim, g_y = primitive_direction(y_raw)
        if g_y == 0:
            raise AssertionError("Farkas witness unexpectedly all zero")

        # Split back into inequality part y_ub >= 0 and equality part y_eq in Z^{m_eq}
        y_ub_raw = list(y_prim[:m_ub])
        y_eq_raw: list[int] | None = None
        if m_eq > 0:
            y_eq_raw = [
                y_prim[m_ub + i] - y_prim[m_ub + m_eq + i] for i in range(m_eq)
            ]
            g_comb = math.gcd(*(abs(v) for v in (y_ub_raw + y_eq_raw)))
            if g_comb > 1:
                y_ub_raw = [v // g_comb for v in y_ub_raw]
                y_eq_raw = [v // g_comb for v in y_eq_raw]

        # Self-verify Farkas certificate!
        lhs_dual = [0] * d
        if m_ub > 0:
            ub_part = vec_mat_mul(y_ub_raw, A_ub)
            for j in range(d):
                lhs_dual[j] += ub_part[j]
        rhs_dual = dot_int(y_ub_raw, b_ub) if m_ub > 0 else 0
        if m_eq > 0 and A_eq is not None and b_eq is not None and y_eq_raw is not None:
            eq_part = vec_mat_mul(y_eq_raw, A_eq)
            for j in range(d):
                lhs_dual[j] += eq_part[j]
            rhs_dual += dot_int(y_eq_raw, b_eq)

        if any(yi < 0 for yi in y_ub_raw):
            raise AssertionError("Farkas inequality multipliers must be >= 0")
        if any(v != 0 for v in lhs_dual) or rhs_dual >= 0:
            raise AssertionError("Farkas infeasibility certificate failed algebraic check")

        return LPResult(
            status="INFEASIBLE",
            primal_num=None,
            primal_den=1,
            obj_num=None,
            obj_den=1,
            farkas_y=tuple(y_ub_raw),
            farkas_y_eq=tuple(y_eq_raw) if y_eq_raw is not None else None,
            dual_opt_y=None,
            dual_opt_den=1,
            unbounded_ray=None,
            pivots=pivots,
        )

    if cbar[col_rhs] != 0 or col_x0 in basis:
        raise AssertionError("Lexicographic Phase I invariant violated at feasibility")

    # Drop col_x0 to form clean Phase II tableau with columns:
    # u_0..u_{d-1} (0..d-1), v_0..v_{d-1} (d..2d-1), s_0..s_{m-1} (2d..2d+m-1), rhs (2d+m)
    T2: list[list[int]] = [
        row[:col_x0] + row[col_x0 + 1 :] for row in T
    ]
    basis2 = [b_col if b_col < col_x0 else b_col - 1 for b_col in basis]
    col_s0_p2 = 2 * d
    col_rhs_p2 = 2 * d + m
    n_cols_p2 = col_rhs_p2 + 1
    lex_cols_p2 = [col_rhs_p2] + [col_s0_p2 + i for i in range(m)]

    def extract_primal_point() -> tuple[tuple[int, ...], int]:
        var_vals = [0] * (2 * d + m)
        for i in range(m):
            var_vals[basis2[i]] = T2[i][col_rhs_p2]
        x_raw = [var_vals[j] - var_vals[d + j] for j in range(d)]
        x_num, x_den = _reduce_rat_vec(x_raw, D)
        # Verify primal feasibility against original constraints!
        if m_ub > 0:
            ax = mat_vec_mul(A_ub, x_num)
            for i in range(m_ub):
                if ax[i] > int(b_ub[i]) * x_den:
                    raise AssertionError("Primal feasibility check A_ub x <= b_ub failed")
        if m_eq > 0 and A_eq is not None and b_eq is not None:
            aeq_x = mat_vec_mul(A_eq, x_num)
            for i in range(m_eq):
                if aeq_x[i] != int(b_eq[i]) * x_den:
                    raise AssertionError("Primal equality check A_eq x == b_eq failed")
        return (x_num, x_den)

    if c_max is None:
        p_num, p_den = extract_primal_point()
        return LPResult(
            status="FEASIBLE",
            primal_num=p_num,
            primal_den=p_den,
            obj_num=None,
            obj_den=1,
            farkas_y=None,
            farkas_y_eq=None,
            dual_opt_y=None,
            dual_opt_den=1,
            unbounded_ray=None,
            pivots=pivots,
        )

    # Build Phase II canonical objective row for maximizing c_max^T (u - v):
    # cbar2[j] = sum_{i=0}^{m-1} c_var[basis2[i]] * T2[i][j] - D * c_var[j]
    c_var = [int(c_max[j]) for j in range(d)] + [-int(c_max[j]) for j in range(d)] + [0] * m
    cbar2 = [0] * n_cols_p2
    for j in range(col_rhs_p2):
        acc = -D * c_var[j]
        for i in range(m):
            c_bi = c_var[basis2[i]]
            if c_bi != 0:
                acc += c_bi * T2[i][j]
        cbar2[j] = acc
    acc_rhs = 0
    for i in range(m):
        c_bi = c_var[basis2[i]]
        if c_bi != 0:
            acc_rhs += c_bi * T2[i][col_rhs_p2]
    cbar2[col_rhs_p2] = acc_rhs

    # Phase II Lexicographic Simplex Loop
    while True:
        enter_e = -1
        for j in range(col_rhs_p2):
            if cbar2[j] < 0:
                enter_e = j
                break
        if enter_e == -1:
            break

        leave_r = -1
        for i in range(m):
            piv_cand = T2[i][enter_e]
            if piv_cand <= 0:
                continue
            if leave_r == -1 or _lex_ratio_less(
                T2[i], piv_cand, T2[leave_r], T2[leave_r][enter_e], lex_cols_p2
            ):
                leave_r = i

        if leave_r == -1:
            # UNBOUNDED! Extract exact integer ray in Q^d
            # Setting var[enter_e] = D and var[basis2[i]] = -T2[i][enter_e] >= 0 gives M * ray_var == 0
            ray_vars = [0] * (2 * d + m)
            ray_vars[enter_e] = D
            for i in range(m):
                ray_vars[basis2[i]] = -T2[i][enter_e]
            ray_x = [ray_vars[j] - ray_vars[d + j] for j in range(d)]
            ray_prim, _ = primitive_direction(ray_x)
            if m_ub > 0:
                ar = mat_vec_mul(A_ub, ray_prim)
                if any(v > 0 for v in ar):
                    raise AssertionError("Unbounded ray violated A_ub r <= 0")
            if m_eq > 0 and A_eq is not None:
                aer = mat_vec_mul(A_eq, ray_prim)
                if any(v != 0 for v in aer):
                    raise AssertionError("Unbounded ray violated A_eq r == 0")
            if dot_int(c_max, ray_prim) <= 0:
                raise AssertionError("Unbounded ray failed c^T r > 0")
            p_num, p_den = extract_primal_point()
            return LPResult(
                status="UNBOUNDED",
                primal_num=p_num,
                primal_den=p_den,
                obj_num=None,
                obj_den=1,
                farkas_y=None,
                farkas_y_eq=None,
                dual_opt_y=None,
                dual_opt_den=1,
                unbounded_ray=ray_prim,
                pivots=pivots,
            )

        D = _bareiss_simplex_pivot(T2, cbar2, basis2, D, leave_r, enter_e, n_cols_p2)
        pivots += 1

    # OPTIMAL! Extract primal point, objective, and strong-duality certificate
    p_num, p_den = extract_primal_point()
    obj_num, obj_den = _reduce_rat_scalar(cbar2[col_rhs_p2], D)

    # Verify strong LP duality: c^T p_num / p_den == obj_num / obj_den == y_dual^T b_all / D
    if dot_int(c_max, p_num) * obj_den != obj_num * p_den:
        raise AssertionError("Primal objective mismatch at LP optimum")

    y_opt_all = [cbar2[col_s0_p2 + i] for i in range(m)]
    if any(yi < 0 for yi in y_opt_all):
        raise AssertionError("Dual optimal multipliers unexpectedly negative")
    ya_opt = vec_mat_mul(y_opt_all, A_all)
    for j in range(d):
        if ya_opt[j] != D * int(c_max[j]):
            raise AssertionError("Dual stationarity y^T A == D * c^T failed")
    if dot_int(y_opt_all, b_all) != cbar2[col_rhs_p2]:
        raise AssertionError("Strong LP duality y^T b == rhs_obj failed")

    y_opt_red, y_opt_den = _reduce_rat_vec(y_opt_all[:m_ub], D)
    return LPResult(
        status="OPTIMAL",
        primal_num=p_num,
        primal_den=p_den,
        obj_num=obj_num,
        obj_den=obj_den,
        farkas_y=None,
        farkas_y_eq=None,
        dual_opt_y=y_opt_red,
        dual_opt_den=y_opt_den,
        unbounded_ray=None,
        pivots=pivots,
    )


def check_polyhedron_feasibility(
    A_ub: Sequence[Sequence[int]],
    b_ub: Sequence[int],
    A_eq: Sequence[Sequence[int]] | None = None,
    b_eq: Sequence[int] | None = None,
) -> LPResult:
    return solve_lp(A_ub=A_ub, b_ub=b_ub, c_max=None, A_eq=A_eq, b_eq=b_eq)


# ---------------------------------------------------------------------------
# Exact Vertex Enumeration for Low-Dimensional (1D-4D) Pointed Polyhedra
# ---------------------------------------------------------------------------

def enumerate_vertices(
    A_ub: Sequence[Sequence[int]],
    b_ub: Sequence[int],
    A_eq: Sequence[Sequence[int]] | None = None,
    b_eq: Sequence[int] | None = None,
) -> list[tuple[tuple[int, ...], int]]:
    """Enumerate all exact rational vertices (v_num, v_den) of a pointed 1D-4D polyhedron.

    Deduplicates parallel halfspaces, optionally prunes redundant inequalities via LP
    when m is large, solves nonsingular d x d active constraint subsystems via Bareiss,
    and verifies every returned vertex against all constraints and rank == d.
    """
    m_ub, d_ub = mat_shape(A_ub)
    m_eq, d_eq = mat_shape(A_eq) if A_eq is not None else (0, 0)
    d = d_ub if m_ub > 0 else d_eq
    if d == 0:
        return [((), 1)]
    if d > 5:
        raise ValueError(f"enumerate_vertices is designed for low-dimensional polyhedra (d <= 5), got d={d}")

    feas = check_polyhedron_feasibility(A_ub, b_ub, A_eq=A_eq, b_eq=b_eq)
    if feas.status == "INFEASIBLE":
        return []

    # Normalize & deduplicate inequality halfspaces: keep tightest rhs per primitive direction
    tightest: dict[tuple[int, ...], int] = {}
    for i in range(m_ub):
        prim_a, g = primitive_direction(A_ub[i])
        if g == 0:
            if int(b_ub[i]) < 0:
                return []
            continue
        # Since prim_a * g == A_ub[i], prim_a . x <= b_ub[i] / g — keep unscaled if b_ub[i] % g != 0!
        # Wait: A_ub x <= b_ub is over Q^d (NOT integer x!), so we must only divide by gcd(A_ub[i], b_ub[i])!
        g_both = math.gcd(g, abs(int(b_ub[i])))
        row_red = tuple(int(c) // g_both for c in A_ub[i])
        rhs_red = int(b_ub[i]) // g_both
        # Key by primitive direction prim_a and compare rhs_red / (g // g_both)
        scale = g // g_both
        if prim_a not in tightest:
            tightest[prim_a] = i
        else:
            prev_i = tightest[prim_a]
            _, prev_g = primitive_direction(A_ub[prev_i])
            # Compare b_ub[i] / g vs b_ub[prev_i] / prev_g <=> b_ub[i] * prev_g < b_ub[prev_i] * g
            if int(b_ub[i]) * prev_g < int(b_ub[prev_i]) * g:
                tightest[prim_a] = i
        _ = (row_red, rhs_red, scale)

    ineq_rows = [[int(x) for x in A_ub[idx]] for idx in sorted(tightest.values())]
    ineq_rhs = [int(b_ub[idx]) for idx in sorted(tightest.values())]

    # Prune redundant inequalities via LP if count > 16
    if len(ineq_rows) > 16:
        kept_rows: list[list[int]] = []
        kept_rhs: list[int] = []
        for idx in range(len(ineq_rows)):
            other_A = kept_rows + ineq_rows[idx + 1 :]
            other_b = kept_rhs + ineq_rhs[idx + 1 :]
            res = solve_lp(other_A, other_b, c_max=ineq_rows[idx], A_eq=A_eq, b_eq=b_eq)
            # Redundant iff OPTIMAL and max_val < ineq_rhs[idx] (strictly slack? Wait: even <= ineq_rhs[idx]
            # can be dropped sequentially because we update kept_rows with only kept ones!)
            if res.status == "OPTIMAL" and res.obj_num is not None:
                if res.obj_num <= ineq_rhs[idx] * res.obj_den:
                    continue
            kept_rows.append(ineq_rows[idx])
            kept_rhs.append(ineq_rhs[idx])
        ineq_rows = kept_rows
        ineq_rhs = kept_rhs

    eq_rows: list[list[int]] = []
    eq_rhs: list[int] = []
    if A_eq is not None and b_eq is not None and m_eq > 0:
        pb_eq = extract_pivot_basis(A_eq)
        for r_idx in pb_eq.row_pivots:
            eq_rows.append([int(x) for x in A_eq[r_idx]])
            eq_rhs.append(int(b_eq[r_idx]))

    r_eq = len(eq_rows)
    if r_eq > d:
        return []
    needed = d - r_eq
    if len(ineq_rows) < needed:
        return []

    found_set: set[tuple[tuple[int, ...], int]] = set()
    for combo in itertools.combinations(range(len(ineq_rows)), needed):
        sub_A = eq_rows + [ineq_rows[idx] for idx in combo]
        sub_b = eq_rhs + [ineq_rhs[idx] for idx in combo]
        det_val = bareiss_det(sub_A)
        if det_val == 0:
            continue
        # Solve sub_A @ v_num = det_abs * sub_b via Cramer / Bareiss
        v_num_raw, det_abs = _solve_square_system(sub_A, sub_b)
        v_num, v_den = _reduce_rat_vec(v_num_raw, det_abs)

        # Verify against ALL original inequalities & equalities
        ok = True
        for i in range(m_ub):
            if dot_int(A_ub[i], v_num) > int(b_ub[i]) * v_den:
                ok = False
                break
        if not ok:
            continue
        if m_eq > 0 and A_eq is not None and b_eq is not None:
            for i in range(m_eq):
                if dot_int(A_eq[i], v_num) != int(b_eq[i]) * v_den:
                    ok = False
                    break
        if ok:
            found_set.add((v_num, v_den))

    # Sort vertices lexicographically using exact cross-multiplied rational comparison
    vertices = list(found_set)
    vertices.sort(key=lambda item: _rat_sort_key(item[0], item[1], vertices))
    return vertices


def _solve_square_system(
    B: Sequence[Sequence[int]],
    rhs: Sequence[int],
) -> tuple[list[int], int]:
    """Exact Bareiss Gauss-Jordan solver for nonsingular d x d system."""
    d = len(B)
    M = [[int(B[i][j]) for j in range(d)] + [int(rhs[i])] for i in range(d)]
    prev_piv = 1
    for k in range(d):
        if M[k][k] == 0:
            swap_i = -1
            for i in range(k + 1, d):
                if M[i][k] != 0:
                    swap_i = i
                    break
            if swap_i == -1:
                raise ValueError("Singular system in _solve_square_system")
            M[k], M[swap_i] = M[swap_i], M[k]
        piv = M[k][k]
        rk = M[k]
        for i in range(d):
            if i == k:
                continue
            ri = M[i]
            mik = ri[k]
            for j in range(k + 1, d + 1):
                ri[j] = (piv * ri[j] - mik * rk[j]) // prev_piv
            ri[k] = 0
        for i in range(k):
            M[i][i] = piv
        prev_piv = piv
    x_raw = [M[i][d] for i in range(d)]
    if prev_piv < 0:
        return ([-v for v in x_raw], -prev_piv)
    return (x_raw, prev_piv)


def _rat_sort_key(
    v_num: tuple[int, ...],
    v_den: int,
    all_verts: Sequence[tuple[tuple[int, ...], int]],
) -> tuple[int, ...]:
    L = 1
    for _, den in all_verts:
        L = math.lcm(L, den)
    mul = L // v_den
    return tuple(c * mul for c in v_num)


# ---------------------------------------------------------------------------
# Exact Normalized Lattice Volume Vol_k(P) = k! * vol_k(P) via Beneath-Beyond
# ---------------------------------------------------------------------------

def _facet_outward_normal(
    facet_pts: Sequence[Sequence[int]],
    interior_sum: Sequence[int],
    interior_count: int,
) -> tuple[tuple[int, ...], int]:
    """Compute exact integer outward normal n and rhs = n . facet_pts[0] for (d-1)-simplex in Z^d.

    interior_sum / interior_count is strictly inside the polytope, so we orient n such that
    n . interior_sum < interior_count * rhs.
    """
    d = len(facet_pts[0])
    if len(facet_pts) != d:
        raise ValueError("A (d-1)-simplex in Z^d must have exactly d vertices")
    p0 = facet_pts[0]
    edges = [[facet_pts[i][c] - p0[c] for c in range(d)] for i in range(1, d)]
    # Cofactor normal: n[c] = (-1)^c * det(edges without column c)
    normal = [0] * d
    for c in range(d):
        minor = [[edges[r][j] for j in range(d) if j != c] for r in range(d - 1)]
        det_m = bareiss_det(minor)
        normal[c] = det_m if (c % 2 == 0) else -det_m
    prim_n, g = primitive_direction(normal)
    if g == 0:
        raise ValueError("Degenerate (d-1)-simplex in _facet_outward_normal")
    rhs = dot_int(prim_n, p0)
    lhs_int = dot_int(prim_n, interior_sum)
    if lhs_int > interior_count * rhs:
        prim_n = tuple(-x for x in prim_n)
        rhs = -rhs
    elif lhs_int == interior_count * rhs:
        raise AssertionError("Interior witness unexpectedly lies on boundary facet")
    return (prim_n, rhs)


def normalized_lattice_volume_vertices(vertices: Sequence[Sequence[int]]) -> int:
    """Compute exact normalized volume Vol_d(conv(vertices)) = d! * vol_d(conv(vertices)) in Z.

    Uses exact integer Beneath-Beyond placing triangulation in arbitrary dimension d >= 1.
    Returns 0 if the point set is affinely degenerate (affine dimension < d).
    """
    if not vertices:
        return 0
    # Deduplicate integer points deterministically
    pts_unique = sorted({tuple(int(c) for c in v) for v in vertices})
    d = len(pts_unique[0])
    if d == 0 or len(pts_unique) <= d:
        return 0

    p0 = pts_unique[0]
    diffs = [[pt[c] - p0[c] for c in range(d)] for pt in pts_unique[1:]]
    pb = extract_pivot_basis(diffs)
    if pb.rank < d:
        return 0  # Affinely lower-dimensional inside Z^d -> full-dim d-volume is 0

    # Initial full-dimensional d-simplex indices in pts_unique
    init_indices = [0] + [r_idx + 1 for r_idx in pb.row_pivots[:d]]
    init_set = set(init_indices)
    s0_pts = [pts_unique[idx] for idx in init_indices]
    s0_edges = [[s0_pts[i][c] - s0_pts[0][c] for c in range(d)] for i in range(1, d + 1)]
    total_norm_vol = abs(bareiss_det(s0_edges))
    if total_norm_vol == 0:
        raise AssertionError("Initial d-simplex unexpectedly had zero volume")

    # Exact interior centroid sum = sum_{i=0}^d s0_pts[i], count = d + 1
    interior_sum = [sum(s0_pts[i][c] for i in range(d + 1)) for c in range(d)]
    interior_count = d + 1

    # Boundary is a list of (sorted_vertex_idx_tuple, normal_tuple, rhs_int)
    boundary: list[tuple[tuple[int, ...], tuple[int, ...], int]] = []
    for omit in range(d + 1):
        f_idx = tuple(sorted(init_indices[i] for i in range(d + 1) if i != omit))
        f_pts = [pts_unique[idx] for idx in f_idx]
        n_vec, rhs = _facet_outward_normal(f_pts, interior_sum, interior_count)
        boundary.append((f_idx, n_vec, rhs))

    # Insert remaining points one by one via Beneath-Beyond
    for pt_idx in range(len(pts_unique)):
        if pt_idx in init_set:
            continue
        p = pts_unique[pt_idx]
        visible: list[tuple[tuple[int, ...], tuple[int, ...], int]] = []
        non_visible: list[tuple[tuple[int, ...], tuple[int, ...], int]] = []
        for facet in boundary:
            _, n_vec, rhs = facet
            if dot_int(n_vec, p) > rhs:
                visible.append(facet)
            else:
                non_visible.append(facet)

        if not visible:
            continue

        # Add normalized volume of cone(p, F) for every visible facet F
        ridge_counts: dict[tuple[int, ...], int] = {}
        for f_idx, _, _ in visible:
            f_pts = [pts_unique[idx] for idx in f_idx]
            cone_edges = [[f_pts[i][c] - p[c] for c in range(d)] for i in range(d)]
            vol_piece = abs(bareiss_det(cone_edges))
            if vol_piece == 0:
                raise AssertionError("Visible facet produced zero-volume cone simplex")
            total_norm_vol += vol_piece

            # Count (d-2)-ridges of visible facets to find horizon
            for omit_r in range(d):
                ridge = f_idx[:omit_r] + f_idx[omit_r + 1 :]
                ridge_counts[ridge] = ridge_counts.get(ridge, 0) + 1

        new_facets: list[tuple[tuple[int, ...], tuple[int, ...], int]] = []
        for ridge, cnt in ridge_counts.items():
            if cnt == 1:
                nf_idx = tuple(sorted(ridge + (pt_idx,)))
                nf_pts = [pts_unique[idx] for idx in nf_idx]
                n_vec, rhs = _facet_outward_normal(nf_pts, interior_sum, interior_count)
                new_facets.append((nf_idx, n_vec, rhs))

        boundary = non_visible + new_facets

    return total_norm_vol


def normalized_rational_volume_vertices(
    rational_vertices: Sequence[tuple[Sequence[int], int]],
) -> tuple[int, int]:
    """Compute exact normalized volume (vol_num, vol_den) = d! * vol_d(conv(V)) for rational V in Q^d."""
    if not rational_vertices:
        return (0, 1)
    d = len(rational_vertices[0][0])
    if d == 0:
        return (0, 1)
    L = 1
    for _, den in rational_vertices:
        if den <= 0:
            raise ValueError("Denominator must be positive in normalized_rational_volume_vertices")
        L = math.lcm(L, int(den))
    scaled_pts: list[list[int]] = []
    for nums, den in rational_vertices:
        mul = L // int(den)
        scaled_pts.append([int(c) * mul for c in nums])
    vol_scaled = normalized_lattice_volume_vertices(scaled_pts)
    return _reduce_rat_scalar(vol_scaled, L ** d)


def normalized_lattice_volume_hrep(
    A_ub: Sequence[Sequence[int]],
    b_ub: Sequence[int],
    A_eq: Sequence[Sequence[int]] | None = None,
    b_eq: Sequence[int] | None = None,
) -> tuple[int, int]:
    """Compute exact normalized volume (vol_num, vol_den) of a bounded 1D-4D H-polytope."""
    verts = enumerate_vertices(A_ub, b_ub, A_eq=A_eq, b_eq=b_eq)
    return normalized_rational_volume_vertices(verts)
