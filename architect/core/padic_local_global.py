from __future__ import annotations

"""Lemma A-LocalGlobal: Sub-150ms Exact Z[1/2] & Z[1/S] Linear Solver via p-adic Valuation Elimination.

Strict Constitutional Compliance:
- 100% Python 3.9+ stdlib only (`math`, `dataclasses`, `typing`).
- Zero `float`, zero `fractions.Fraction`, zero `/` (`ast.Div`), zero `isinstance`.
- ZERO unreduced full-matrix integer HNF: uses F_3 pre-screen + Q-pivot basis + Z/p^k Z CRT.
"""

from dataclasses import dataclass
import math
from typing import Sequence

from architect.core.exact_int_la import (
    _bareiss_solve_nonsingular,
    canonical_primitive_vector,
    dot_int,
    extract_pivot_basis,
    mat_shape,
    mat_transpose,
    mat_vec_mul,
    primitive_direction,
    vec_mat_mul,
    xgcd,
)

VP_ZERO_SENTINEL: int = 10 ** 9


@dataclass(frozen=True)
class PadicSolveResult:
    status: str  # "CERTIFIED_EXACT" | "UNSAT_MOD3_PRESCREEN" | "UNSAT_Q" | "UNSAT_PADIC"
    c_num: tuple[int, ...] | None
    c_den: int
    obstruction_prime: int | None
    obstruction_y: tuple[int, ...] | None
    obstruction_s: int | None
    pivot_rank: int
    l_odd: int


def vp_int(n: int, p: int, zero_val: int = VP_ZERO_SENTINEL) -> int:
    """Exact p-adic valuation v_p(n) for prime p >= 2."""
    if p < 2:
        raise ValueError("Prime p must be >= 2 in vp_int")
    val = abs(int(n))
    if val == 0:
        return zero_val
    cnt = 0
    while val % p == 0:
        val = val // p
        cnt += 1
    return cnt


# ---------------------------------------------------------------------------
# Fast Deterministic Primality & Pollard-Brent Integer Factorization
# ---------------------------------------------------------------------------

def _is_prime_int(n: int) -> bool:
    if n < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    if n in small_primes:
        return True
    for sp in small_primes:
        if n % sp == 0:
            return False
    # Deterministic Miller-Rabin bases valid well past 2^64 (in fact 3.3 * 10^24)
    d = n - 1
    s = 0
    while d % 2 == 0:
        d = d // 2
        s += 1
    for a in small_primes:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        composite = True
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                composite = False
                break
        if composite:
            return False
    return True


def _brent_pollard_rho(n: int) -> int:
    if n % 2 == 0:
        return 2
    for c in range(1, 64):
        y = 2
        r = 1
        q = 1
        g = 1
        ys = 2
        x = 2
        m_step = 128
        while g == 1:
            x = y
            for _ in range(r):
                y = (y * y + c) % n
            k = 0
            while k < r and g == 1:
                ys = y
                upper = m_step if (r - k) > m_step else (r - k)
                for _ in range(upper):
                    y = (y * y + c) % n
                    q = (q * abs(x - y)) % n
                g = math.gcd(q, n)
                k += m_step
            r = r * 2
        if g == n:
            while True:
                ys = (ys * ys + c) % n
                g = math.gcd(abs(x - ys), n)
                if g > 1:
                    break
        if 1 < g < n:
            return g
    # Fallback trial division
    f = 3
    while f * f <= n:
        if n % f == 0:
            return f
        f += 2
    return n


def factor_positive_int(n: int) -> dict[int, int]:
    """Exact prime factorization of positive integer n >= 1."""
    val = abs(int(n))
    if val <= 1:
        return {}
    out: dict[int, int] = {}
    cnt2 = 0
    while val % 2 == 0:
        val = val // 2
        cnt2 += 1
    if cnt2 > 0:
        out[2] = cnt2

    d = 3
    while d <= 1009 and d * d <= val:
        if val % d == 0:
            cnt = 0
            while val % d == 0:
                val = val // d
                cnt += 1
            out[d] = out.get(d, 0) + cnt
        d += 2

    stack: list[int] = [val] if val > 1 else []
    while stack:
        cur = stack.pop()
        if cur <= 1:
            continue
        if _is_prime_int(cur):
            out[cur] = out.get(cur, 0) + 1
        else:
            fac = _brent_pollard_rho(cur)
            stack.append(fac)
            stack.append(cur // fac)

    return dict(sorted(out.items()))


def _split_s_part(n: int, inverted_primes: Sequence[int]) -> tuple[int, int]:
    """Split n >= 1 into (s_smooth_part, coprime_part) relative to inverted_primes."""
    val = abs(int(n))
    if val == 0:
        raise ValueError("_split_s_part requires nonzero integer")
    s_part = 1
    for p in inverted_primes:
        while val % p == 0:
            val = val // p
            s_part *= p
    return (s_part, val)


# ---------------------------------------------------------------------------
# Step 1: Fast F_3 Pre-Screen on [A | b] mod 3
# ---------------------------------------------------------------------------

def f3_prescreen(
    A: Sequence[Sequence[int]],
    b: Sequence[int],
) -> tuple[bool, tuple[int, ...] | None]:
    """Fast mod-3 Gaussian elimination on [A | b] mod 3.

    Returns (True, None) if consistent mod 3, or (False, y) with y in {0,1,2}^M
    satisfying y^T A == 0 (mod 3) and y^T b == 1 (mod 3).
    """
    m, n = mat_shape(A)
    if len(b) != m:
        raise ValueError("RHS length mismatch in f3_prescreen")
    if m == 0:
        return (True, None)

    rows_a: list[dict[int, int]] = []
    rows_b: list[int] = []
    rows_comb: list[dict[int, int]] = []
    for i in range(m):
        da: dict[int, int] = {}
        row = A[i]
        for j in range(n):
            v = int(row[j]) % 3
            if v != 0:
                da[j] = v
        rows_a.append(da)
        rows_b.append(int(b[i]) % 3)
        rows_comb.append({i: 1})

    # Immediate check for zero-mod-3 rows with nonzero-mod-3 RHS
    for i in range(m):
        if not rows_a[i] and rows_b[i] != 0:
            scale = 1 if rows_b[i] == 1 else 2  # 2 * 2 == 1 mod 3
            y = [0] * m
            y[i] = scale
            return (False, tuple(y))

    active = [i for i in range(m) if rows_a[i]]
    active_set = set(active)

    while active_set:
        # Pick sparsest active row
        piv_r = min(active_set, key=lambda r: (len(rows_a[r]), r))
        active_set.remove(piv_r)
        piv_da = rows_a[piv_r]
        if not piv_da:
            if rows_b[piv_r] != 0:
                return (False, _finalize_f3_witness(rows_comb[piv_r], rows_b[piv_r], m, A, b))
            continue

        piv_c = min(piv_da.keys())
        piv_val = piv_da[piv_c]  # 1 or 2; note inv mod 3 of 1 is 1, of 2 is 2!
        inv_piv = piv_val  # since 1^-1 = 1 and 2^-1 = 2 in F_3!

        # Normalize pivot row so entry at piv_c is 1 mod 3
        if inv_piv != 1:
            for c in list(piv_da.keys()):
                piv_da[c] = (piv_da[c] * inv_piv) % 3
            rows_b[piv_r] = (rows_b[piv_r] * inv_piv) % 3
            p_comb = rows_comb[piv_r]
            for idx in list(p_comb.keys()):
                p_comb[idx] = (p_comb[idx] * inv_piv) % 3

        p_comb = rows_comb[piv_r]
        p_rhs = rows_b[piv_r]

        for r in list(active_set):
            rd = rows_a[r]
            fac = rd.pop(piv_c, 0)
            if fac == 0:
                continue
            for c, pv in piv_da.items():
                if c == piv_c:
                    continue
                nv = (rd.get(c, 0) - fac * pv) % 3
                if nv == 0:
                    rd.pop(c, None)
                else:
                    rd[c] = nv
            rows_b[r] = (rows_b[r] - fac * p_rhs) % 3

            rc = rows_comb[r]
            for idx, cv in p_comb.items():
                nv = (rc.get(idx, 0) - fac * cv) % 3
                if nv == 0:
                    rc.pop(idx, None)
                else:
                    rc[idx] = nv

            if not rd:
                active_set.remove(r)
                if rows_b[r] != 0:
                    return (False, _finalize_f3_witness(rc, rows_b[r], m, A, b))

    return (True, None)


def _finalize_f3_witness(
    comb: dict[int, int],
    rhs_mod3: int,
    m: int,
    A: Sequence[Sequence[int]],
    b: Sequence[int],
) -> tuple[int, ...]:
    scale = 1 if rhs_mod3 == 1 else 2
    y = [0] * m
    for idx, val in comb.items():
        y[idx] = (val * scale) % 3
    ya = vec_mat_mul(y, A)
    yb = dot_int(y, b)
    if any(v % 3 != 0 for v in ya) or (yb % 3 != 1):
        raise AssertionError("F_3 obstruction witness failed algebraic verification")
    return tuple(y)


# ---------------------------------------------------------------------------
# Step 3: Minimum-v_p Valuation Elimination Modulo p^k
# ---------------------------------------------------------------------------

def _solve_mod_pk(
    A_P: Sequence[Sequence[int]],
    b_P: Sequence[int],
    row_pivots: Sequence[int],
    m_full: int,
    A_full: Sequence[Sequence[int]],
    b_full: Sequence[int],
    p: int,
    k: int,
) -> tuple[bool, list[int] | None, tuple[int, ...] | None, int | None]:
    """Minimum-v_p full-column pivot elimination on A_P z == b_P (mod p^k).

    Returns:
      (True, z_mod_pk, None, None) with A_P @ z == b_P (mod p^k)
    OR:
      (False, None, y_obs, s_val) with y_obs in Z^{m_full} satisfying
      v_p(y_obs^T A_full) >= s_val > v_p(y_obs^T b_full).
    """
    r, n = mat_shape(A_P)
    pk = p ** k
    W = [[int(A_P[i][j]) % pk for j in range(n)] for i in range(r)]
    rhs = [int(b_P[i]) % pk for i in range(r)]
    R = [[1 if i == j else 0 for j in range(r)] for i in range(r)]

    used_cols: set[int] = set()
    piv_cols: list[int] = []
    piv_vps: list[int] = []

    for step in range(r):
        best_vp = k
        best_i = -1
        best_j = -1
        for i in range(step, r):
            wi = W[i]
            for j in range(n):
                if j in used_cols:
                    continue
                val = wi[j]
                if val == 0:
                    continue
                v = vp_int(val, p, zero_val=k)
                if v < best_vp:
                    best_vp = v
                    best_i = i
                    best_j = j
                    if v == 0:
                        break
            if best_vp == 0:
                break

        if best_i == -1:
            # All remaining rows step..r-1 are 0 mod p^k across all columns!
            for i in range(step, r):
                if rhs[i] % pk != 0:
                    y_obs, s_obs = _lift_padic_witness(R[i], row_pivots, m_full, A_full, b_full, p, k)
                    return (False, None, y_obs, s_obs)
            break

        # Swap best_i <-> step
        if best_i != step:
            W[step], W[best_i] = W[best_i], W[step]
            rhs[step], rhs[best_i] = rhs[best_i], rhs[step]
            R[step], R[best_i] = R[best_i], R[step]

        pv = p ** best_vp
        unit_part = W[step][best_j] // pv
        inv_unit = pow(unit_part, -1, pk)

        # Multiply row `step` by inv_unit mod p^k so W[step][best_j] == p^{best_vp}
        w_step = W[step]
        for j in range(n):
            if w_step[j] != 0:
                w_step[j] = (w_step[j] * inv_unit) % pk
        rhs[step] = (rhs[step] * inv_unit) % pk
        r_step = R[step]
        for j in range(r):
            if r_step[j] != 0:
                r_step[j] = (r_step[j] * inv_unit) % pk

        # Check divisibility of rhs[step] by p^{best_vp} IMMEDIATELY:
        # Every entry in w_step has v_p >= best_vp (0 on previous piv_cols, >= best_vp on remaining)!
        if rhs[step] % pv != 0:
            y_obs, s_obs = _lift_padic_witness(R[step], row_pivots, m_full, A_full, b_full, p, best_vp)
            return (False, None, y_obs, s_obs)

        # Eliminate W[i][best_j] for all i > step (guaranteed divisible by pv!)
        for i in range(step + 1, r):
            val_i = W[i][best_j]
            if val_i == 0:
                continue
            q = val_i // pv
            wi = W[i]
            for j in range(n):
                if w_step[j] != 0:
                    wi[j] = (wi[j] - q * w_step[j]) % pk
            rhs[i] = (rhs[i] - q * rhs[step]) % pk
            ri = R[i]
            for j in range(r):
                if r_step[j] != 0:
                    ri[j] = (ri[j] - q * r_step[j]) % pk

        used_cols.add(best_j)
        piv_cols.append(best_j)
        piv_vps.append(best_vp)

    # Back-substitution over Z / p^k Z
    n_piv = len(piv_cols)
    for i in range(n_piv, r):
        if rhs[i] % pk != 0:
            y_obs, s_obs = _lift_padic_witness(R[i], row_pivots, m_full, A_full, b_full, p, k)
            return (False, None, y_obs, s_obs)

    z = [0] * n
    for t in range(n_piv - 1, -1, -1):
        jt = piv_cols[t]
        pv = p ** piv_vps[t]
        wt = W[t]
        acc = rhs[t]
        for c in range(n):
            if c == jt or z[c] == 0 or wt[c] == 0:
                continue
            acc = (acc - wt[c] * z[c]) % pk
        if acc % pv != 0:
            raise AssertionError("p-adic back-substitution divisibility invariant failed")
        z[jt] = (acc // pv) % pk

    # Verify A_P @ z == b_P (mod p^k)
    check = mat_vec_mul(A_P, z)
    for i in range(r):
        if (check[i] - int(b_P[i])) % pk != 0:
            raise AssertionError("Mod p^k solution verification failed")
    return (True, z, None, None)


def _lift_padic_witness(
    r_row: Sequence[int],
    row_pivots: Sequence[int],
    m_full: int,
    A_full: Sequence[Sequence[int]],
    b_full: Sequence[int],
    p: int,
    s_bound: int,
) -> tuple[tuple[int, ...], int]:
    y = [0] * m_full
    for idx, orig_r in enumerate(row_pivots):
        y[orig_r] = int(r_row[idx])
    y_prim, _ = primitive_direction(y)
    ya = vec_mat_mul(y_prim, A_full)
    yb = dot_int(y_prim, b_full)
    vp_yb = vp_int(yb, p)
    min_vp_ya = min((vp_int(v, p) for v in ya), default=VP_ZERO_SENTINEL)
    if not (min_vp_ya > vp_yb):
        raise AssertionError(
            f"p-adic obstruction failed valuation inequality: min v_{p}(y^T A)={min_vp_ya} <= v_{p}(y^T b)={vp_yb}"
        )
    s_cert = min_vp_ya if min_vp_ya < VP_ZERO_SENTINEL else vp_yb + 1
    _ = s_bound
    return (y_prim, s_cert)


def _crt_combine_vectors(
    congruences: Sequence[tuple[Sequence[int], int]],
    n_dim: int,
) -> tuple[list[int], int]:
    """Chinese Remainder Theorem for pairwise coprime moduli m_i > 0."""
    if not congruences:
        return ([0] * n_dim, 1)
    cur_vec = [int(x) % congruences[0][1] for x in congruences[0][0]]
    cur_mod = congruences[0][1]
    for vec_next, mod_next in congruences[1:]:
        g, s, _ = xgcd(cur_mod, mod_next)
        if g != 1:
            raise AssertionError("CRT moduli must be pairwise coprime")
        new_mod = cur_mod * mod_next
        for j in range(n_dim):
            diff = (int(vec_next[j]) - cur_vec[j]) % mod_next
            step = (diff * s) % mod_next
            cur_vec[j] = (cur_vec[j] + cur_mod * step) % new_mod
        cur_mod = new_mod
    return (cur_vec, cur_mod)


# ---------------------------------------------------------------------------
# Main Solvers: Lemma A-LocalGlobal over Z[1/2], Z[1/S], and Z_{(p)}
# ---------------------------------------------------------------------------

def solve_s_integral(
    A: Sequence[Sequence[int]],
    b: Sequence[int],
    inverted_primes: Sequence[int] = (2,),
    run_f3_prescreen: bool = True,
) -> PadicSolveResult:
    """Decide exists c in (Z[1/S])^N : A c = b with ZERO full-matrix integer HNF.

    When inverted_primes == (2,), implements Lemma A-LocalGlobal (§2.3) verbatim:
    - Step 1: Fast F_3 pre-screen (when 3 not in inverted_primes).
    - Step 2: Maximal Q-pivot basis (P, J) solve; early exit if L_non_S == 1.
    - Step 3: Minimum-v_p elimination modulo p^k across all N columns + CRT + pivot lift.
    """
    m, n = mat_shape(A)
    if len(b) != m:
        raise ValueError("RHS dimension mismatch in solve_s_integral")
    inv_set = {int(p) for p in inverted_primes}

    # Step 1: Fast F_3 Pre-Screen (whenever 3 is not inverted)
    if run_f3_prescreen and (3 not in inv_set):
        ok_f3, y_f3 = f3_prescreen(A, b)
        if not ok_f3 and y_f3 is not None:
            return PadicSolveResult(
                status="UNSAT_MOD3_PRESCREEN",
                c_num=None,
                c_den=1,
                obstruction_prime=3,
                obstruction_y=y_f3,
                obstruction_s=1,
                pivot_rank=0,
                l_odd=0,
            )

    # Step 2: Q-Pivot Basis Extraction & Exact Q-Basic Solution
    pb = extract_pivot_basis(A)
    r = pb.rank
    P = pb.row_pivots
    J = pb.col_pivots

    if r == 0:
        for i in range(m):
            if int(b[i]) != 0:
                y_zero = [0] * m
                y_zero[i] = 1 if int(b[i]) > 0 else -1
                return PadicSolveResult(
                    status="UNSAT_Q",
                    c_num=None,
                    c_den=1,
                    obstruction_prime=0,
                    obstruction_y=tuple(y_zero),
                    obstruction_s=None,
                    pivot_rank=0,
                    l_odd=1,
                )
        return PadicSolveResult(
            status="CERTIFIED_EXACT",
            c_num=tuple(0 for _ in range(n)),
            c_den=1,
            obstruction_prime=None,
            obstruction_y=None,
            obstruction_s=None,
            pivot_rank=0,
            l_odd=1,
        )

    B_sub = [[int(A[p_idx][j_idx]) for j_idx in J] for p_idx in P]
    b_sub = [int(b[p_idx]) for p_idx in P]
    c_sub_num, d_basis_abs = _bareiss_solve_nonsingular(B_sub, b_sub)

    c_q_full = [0] * n
    for idx, j_idx in enumerate(J):
        c_q_full[j_idx] = c_sub_num[idx]

    # Verify Q-consistency on non-pivot rows i not in P
    P_set = set(P)
    B_sub_T = mat_transpose(B_sub)
    for i in range(m):
        if i in P_set:
            continue
        if dot_int(A[i], c_q_full) != d_basis_abs * int(b[i]):
            ai_J = [int(A[i][j_idx]) for j_idx in J]
            w_num, det_w = _bareiss_solve_nonsingular(B_sub_T, ai_J)
            y_q = [0] * m
            y_q[i] = det_w
            for idx, p_row in enumerate(P):
                y_q[p_row] = -w_num[idx]
            y_q_prim, _ = canonical_primitive_vector(y_q)
            if any(v != 0 for v in vec_mat_mul(y_q_prim, A)) or dot_int(y_q_prim, b) == 0:
                raise AssertionError("Q-obstruction in solve_s_integral failed verification")
            return PadicSolveResult(
                status="UNSAT_Q",
                c_num=None,
                c_den=1,
                obstruction_prime=0,
                obstruction_y=y_q_prim,
                obstruction_s=None,
                pivot_rank=r,
                l_odd=0,
            )

    # Reduce c_Q denominator L
    g_cq = math.gcd(d_basis_abs, *(abs(v) for v in c_q_full))
    cq_num = [v // g_cq for v in c_q_full]
    L_den = d_basis_abs // g_cq

    L_s_part, L_coprime = _split_s_part(L_den, inverted_primes)
    if L_coprime == 1:
        # Early exit! c_Q is ALREADY in (Z[1/S])^N!
        lhs = mat_vec_mul(A, cq_num)
        for i in range(m):
            if lhs[i] != L_s_part * int(b[i]):
                raise AssertionError("Step 2 early-exit Z[1/S] solution failed check")
        return PadicSolveResult(
            status="CERTIFIED_EXACT",
            c_num=tuple(cq_num),
            c_den=L_s_part,
            obstruction_prime=None,
            obstruction_y=None,
            obstruction_s=None,
            pivot_rank=r,
            l_odd=1,
        )

    # Step 3: Local-Global Z / p^k Z Valuation Elimination + CRT Reconstruction
    D_s_part, D_coprime = _split_s_part(d_basis_abs, inverted_primes)
    prime_fac_D = factor_positive_int(D_coprime)
    prime_fac_L = factor_positive_int(L_coprime)

    A_P = [[int(A[p_idx][j]) for j in range(n)] for p_idx in P]
    congruences: list[tuple[list[int], int]] = []

    for p, e_d in prime_fac_D.items():
        mod_target = p ** e_d
        if p not in prime_fac_L:
            # L_den is coprime to p -> reduce cq_num * L_den^{-1} mod p^{e_d} in O(N)!
            inv_L = pow(L_den, -1, mod_target)
            z_p = [(val * inv_L) % mod_target for val in cq_num]
            congruences.append((z_p, mod_target))
        else:
            e_l = prime_fac_L[p]
            k_prec = max(e_l + 2, e_d + 1)
            ok_p, z_pk, y_obs, s_obs = _solve_mod_pk(
                A_P=A_P,
                b_P=b_sub,
                row_pivots=P,
                m_full=m,
                A_full=A,
                b_full=b,
                p=p,
                k=k_prec,
            )
            if not ok_p or z_pk is None:
                return PadicSolveResult(
                    status="UNSAT_PADIC",
                    c_num=None,
                    c_den=1,
                    obstruction_prime=p,
                    obstruction_y=y_obs,
                    obstruction_s=s_obs,
                    pivot_rank=r,
                    l_odd=L_coprime,
                )
            congruences.append(([val % mod_target for val in z_pk], mod_target))

    # CRT across all p | D_coprime so A z_crt == b (mod D_coprime)
    z_crt, mod_all = _crt_combine_vectors(congruences, n)
    if mod_all != D_coprime:
        raise AssertionError("CRT modulus did not equal D_coprime")

    # Compute exact residual r_P = (b_P - A_P z_crt) // D_coprime in Z^r
    az_P = mat_vec_mul(A_P, z_crt)
    res_P: list[int] = []
    for idx in range(r):
        diff = b_sub[idx] - az_P[idx]
        if diff % D_coprime != 0:
            raise AssertionError("Residual b_P - A_P z_crt not divisible by D_coprime")
        res_P.append(diff // D_coprime)

    # Solve B_sub delta_J = D_coprime * res_P:
    # _bareiss_solve_nonsingular(B_sub, res_P) returns (u_num, d_basis_abs) with
    # B_sub @ u_num == d_basis_abs * res_P = D_s_part * (D_coprime * res_P)!
    # Therefore delta_J = u_num / D_s_part lies purely in (Z[1/S])^r!
    u_num, d_check = _bareiss_solve_nonsingular(B_sub, res_P)
    if d_check != d_basis_abs:
        raise AssertionError("Bareiss determinant mismatch during CRT residual lift")

    final_num = [D_s_part * z_crt[j] for j in range(n)]
    for idx, j_idx in enumerate(J):
        final_num[j_idx] += u_num[idx]
    final_den = D_s_part

    g_fin = math.gcd(final_den, *(abs(v) for v in final_num))
    c_num_out = tuple(v // g_fin for v in final_num)
    c_den_out = final_den // g_fin

    # Mandatory self-verification: A @ c_num_out == c_den_out * b AND c_den_out is S-smooth!
    _, bad_den = _split_s_part(c_den_out, inverted_primes)
    if bad_den != 1:
        raise AssertionError(f"Reconstructed denominator {c_den_out} contains non-S prime factor")
    lhs_fin = mat_vec_mul(A, c_num_out)
    for i in range(m):
        if lhs_fin[i] != c_den_out * int(b[i]):
            raise AssertionError("Global Z[1/S] solution failed exact A @ c == b verification")

    return PadicSolveResult(
        status="CERTIFIED_EXACT",
        c_num=c_num_out,
        c_den=c_den_out,
        obstruction_prime=None,
        obstruction_y=None,
        obstruction_s=None,
        pivot_rank=r,
        l_odd=L_coprime,
    )


def solve_z_half(A: Sequence[Sequence[int]], b: Sequence[int]) -> PadicSolveResult:
    """Lemma A-LocalGlobal (§2.3): Decide exists c in (Z[1/2])^N : A c = b."""
    res = solve_s_integral(A, b, inverted_primes=(2,), run_f3_prescreen=True)
    if res.status == "CERTIFIED_EXACT":
        # Explicitly assert c_den is a power of 2: c_den > 0 and (c_den & (c_den - 1)) == 0
        if res.c_den <= 0 or (res.c_den & (res.c_den - 1)) != 0:
            raise AssertionError(f"solve_z_half denominator {res.c_den} is not a power of 2")
    return res


def solve_z_localized_at_p(
    A: Sequence[Sequence[int]],
    b: Sequence[int],
    p: int,
) -> PadicSolveResult:
    """Decide exists c in (Z_{(p)})^N : A c = b (denominators coprime to prime p).

    Checks Q-solvability via Step 2, then runs Step 3 modulo p^k ONLY at the single prime p!
    """
    if p < 2 or not _is_prime_int(p):
        raise ValueError(f"solve_z_localized_at_p requires prime p, got {p}")
    m, n = mat_shape(A)
    if len(b) != m:
        raise ValueError("RHS dimension mismatch in solve_z_localized_at_p")

    pb = extract_pivot_basis(A)
    r = pb.rank
    P = pb.row_pivots
    J = pb.col_pivots
    if r == 0:
        for i in range(m):
            if int(b[i]) != 0:
                yz = [0] * m
                yz[i] = 1 if int(b[i]) > 0 else -1
                return PadicSolveResult("UNSAT_Q", None, 1, 0, tuple(yz), None, 0, 1)
        return PadicSolveResult("CERTIFIED_EXACT", tuple(0 for _ in range(n)), 1, None, None, None, 0, 1)

    B_sub = [[int(A[p_idx][j_idx]) for j_idx in J] for p_idx in P]
    b_sub = [int(b[p_idx]) for p_idx in P]
    c_sub_num, d_basis_abs = _bareiss_solve_nonsingular(B_sub, b_sub)
    c_q_full = [0] * n
    for idx, j_idx in enumerate(J):
        c_q_full[j_idx] = c_sub_num[idx]

    P_set = set(P)
    B_sub_T = mat_transpose(B_sub)
    for i in range(m):
        if i in P_set:
            continue
        if dot_int(A[i], c_q_full) != d_basis_abs * int(b[i]):
            ai_J = [int(A[i][j_idx]) for j_idx in J]
            w_num, det_w = _bareiss_solve_nonsingular(B_sub_T, ai_J)
            y_q = [0] * m
            y_q[i] = det_w
            for idx, p_row in enumerate(P):
                y_q[p_row] = -w_num[idx]
            y_q_prim, _ = canonical_primitive_vector(y_q)
            return PadicSolveResult("UNSAT_Q", None, 1, 0, y_q_prim, None, r, 0)

    g_cq = math.gcd(d_basis_abs, *(abs(v) for v in c_q_full))
    cq_num = [v // g_cq for v in c_q_full]
    L_den = d_basis_abs // g_cq
    if L_den % p != 0:
        return PadicSolveResult("CERTIFIED_EXACT", tuple(cq_num), L_den, None, None, None, r, 1)

    e_d = vp_int(d_basis_abs, p)
    e_l = vp_int(L_den, p)
    k_prec = max(e_l + 2, e_d + 1)
    A_P = [[int(A[p_idx][j]) for j in range(n)] for p_idx in P]
    ok_p, z_pk, y_obs, s_obs = _solve_mod_pk(A_P, b_sub, P, m, A, b, p, k_prec)
    if not ok_p or z_pk is None:
        return PadicSolveResult("UNSAT_PADIC", None, 1, p, y_obs, s_obs, r, p ** e_l)

    p_ed = p ** e_d
    d_coprime = d_basis_abs // p_ed
    z_mod = [val % p_ed for val in z_pk]
    az_P = mat_vec_mul(A_P, z_mod)
    res_P = [(b_sub[idx] - az_P[idx]) // p_ed for idx in range(r)]
    u_num, _ = _bareiss_solve_nonsingular(B_sub, res_P)

    fin_num = [d_coprime * z_mod[j] for j in range(n)]
    for idx, j_idx in enumerate(J):
        fin_num[j_idx] += u_num[idx]
    g_fin = math.gcd(d_coprime, *(abs(v) for v in fin_num))
    c_out = tuple(v // g_fin for v in fin_num)
    den_out = d_coprime // g_fin
    if den_out % p == 0:
        raise AssertionError("Localized Z_(p) denominator unexpectedly divisible by p")
    lhs = mat_vec_mul(A, c_out)
    for i in range(m):
        if lhs[i] != den_out * int(b[i]):
            raise AssertionError("Localized Z_(p) solution failed A @ c == b")
    return PadicSolveResult("CERTIFIED_EXACT", c_out, den_out, None, None, None, r, p ** e_l)
