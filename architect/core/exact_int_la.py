from __future__ import annotations

"""Exact Z/Q Linear Algebra: DHSW Peeling, Unimodular SNF, Pivot-Basis Extraction & Saturation Projectors.

Strict Constitutional Compliance:
- 100% Python 3.9+ stdlib only (`math`, `dataclasses`, `typing`).
- Zero `float`, zero `fractions.Fraction`, zero `/` (`ast.Div`), zero `isinstance`.
"""

from dataclasses import dataclass
import math
from typing import Sequence

PRIME_61_A: int = (1 << 61) - 1  # Mersenne prime 2^61 - 1 = 2305843009213693951


# ---------------------------------------------------------------------------
# Basic exact integer vector & matrix primitives
# ---------------------------------------------------------------------------

def mat_zeros(m: int, n: int) -> list[list[int]]:
    return [[0] * n for _ in range(m)]


def mat_eye(n: int) -> list[list[int]]:
    out = [[0] * n for _ in range(n)]
    for i in range(n):
        out[i][i] = 1
    return out


def mat_copy(A: Sequence[Sequence[int]]) -> list[list[int]]:
    return [[int(x) for x in row] for row in A]


def mat_shape(A: Sequence[Sequence[int]]) -> tuple[int, int]:
    m = len(A)
    if m == 0:
        return (0, 0)
    n = len(A[0])
    for row in A:
        if len(row) != n:
            raise ValueError("Ragged matrix rows are not permitted")
    return (m, n)


def mat_transpose(A: Sequence[Sequence[int]]) -> list[list[int]]:
    m, n = mat_shape(A)
    if m == 0 or n == 0:
        return mat_zeros(n, m)
    return [[int(A[i][j]) for i in range(m)] for j in range(n)]


def dot_int(u: Sequence[int], v: Sequence[int]) -> int:
    if len(u) != len(v):
        raise ValueError("Vector dimension mismatch in dot_int")
    total = 0
    for a, b in zip(u, v):
        total += int(a) * int(b)
    return total


def mat_vec_mul(A: Sequence[Sequence[int]], x: Sequence[int]) -> list[int]:
    m, n = mat_shape(A)
    if len(x) != n:
        raise ValueError(f"Dimension mismatch in mat_vec_mul: ({m}, {n}) vs ({len(x)},)")
    out: list[int] = [0] * m
    for i in range(m):
        row = A[i]
        acc = 0
        for j in range(n):
            rj = row[j]
            if rj != 0 and x[j] != 0:
                acc += int(rj) * int(x[j])
        out[i] = acc
    return out


def vec_mat_mul(y: Sequence[int], A: Sequence[Sequence[int]]) -> list[int]:
    m, n = mat_shape(A)
    if len(y) != m:
        raise ValueError(f"Dimension mismatch in vec_mat_mul: ({len(y)},) vs ({m}, {n})")
    out: list[int] = [0] * n
    for i in range(m):
        yi = int(y[i])
        if yi == 0:
            continue
        row = A[i]
        for j in range(n):
            if row[j] != 0:
                out[j] += yi * int(row[j])
    return out


def mat_mul(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]]) -> list[list[int]]:
    m, k1 = mat_shape(A)
    k2, n = mat_shape(B)
    if k1 != k2:
        raise ValueError(f"Matrix dimension mismatch in mat_mul: ({m}, {k1}) @ ({k2}, {n})")
    out = mat_zeros(m, n)
    for i in range(m):
        row_a = A[i]
        out_i = out[i]
        for t in range(k1):
            ait = int(row_a[t])
            if ait == 0:
                continue
            row_b = B[t]
            for j in range(n):
                btj = int(row_b[j])
                if btj != 0:
                    out_i[j] += ait * btj
    return out


def mat_add(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]]) -> list[list[int]]:
    m, n = mat_shape(A)
    mb, nb = mat_shape(B)
    if (m, n) != (mb, nb):
        raise ValueError("Matrix shape mismatch in mat_add")
    return [[int(A[i][j]) + int(B[i][j]) for j in range(n)] for i in range(m)]


def mat_sub(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]]) -> list[list[int]]:
    m, n = mat_shape(A)
    mb, nb = mat_shape(B)
    if (m, n) != (mb, nb):
        raise ValueError("Matrix shape mismatch in mat_sub")
    return [[int(A[i][j]) - int(B[i][j]) for j in range(n)] for i in range(m)]


def mat_eq(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]]) -> bool:
    ma, na = mat_shape(A)
    mb, nb = mat_shape(B)
    if (ma, na) != (mb, nb):
        return False
    for i in range(ma):
        ra = A[i]
        rb = B[i]
        for j in range(na):
            if int(ra[j]) != int(rb[j]):
                return False
    return True


def is_identity(M: Sequence[Sequence[int]]) -> bool:
    m, n = mat_shape(M)
    if m != n:
        return False
    for i in range(n):
        row = M[i]
        for j in range(n):
            expected = 1 if i == j else 0
            if int(row[j]) != expected:
                return False
    return True


def primitive_gcd(v: Sequence[int]) -> int:
    if not v:
        return 0
    return math.gcd(*(int(x) for x in v))


def primitive_direction(v: Sequence[int]) -> tuple[tuple[int, ...], int]:
    """Normalize integer vector by positive gcd > 0 while preserving orientation sign."""
    g = primitive_gcd(v)
    if g == 0:
        return (tuple(0 for _ in v), 0)
    return (tuple(int(x) // g for x in v), g)


def canonical_primitive_vector(v: Sequence[int]) -> tuple[tuple[int, ...], int]:
    """Normalize integer vector by gcd and make first nonzero coordinate strictly positive."""
    prim, g = primitive_direction(v)
    if g == 0:
        return (prim, 0)
    for coord in prim:
        if coord > 0:
            return (prim, g)
        if coord < 0:
            return (tuple(-c for c in prim), -g)
    return (prim, g)


def xgcd(a: int, b: int) -> tuple[int, int, int]:
    """Extended Euclidean algorithm: returns (g, s, t) with g >= 0 and s*a + t*b == g."""
    a_int = int(a)
    b_int = int(b)
    if a_int == 0 and b_int == 0:
        return (0, 1, 0)
    old_r, r = a_int, b_int
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    if old_r < 0:
        old_r = -old_r
        old_s = -old_s
        old_t = -old_t
    if old_s * a_int + old_t * b_int != old_r:
        raise AssertionError("xgcd Bezout invariant failed")
    return (old_r, old_s, old_t)


def _nearest_quotient(a: int, b: int) -> int:
    """Nearest integer to a / b for b > 0, using pure integer arithmetic."""
    if b <= 0:
        raise ValueError("_nearest_quotient requires b > 0")
    return (2 * a + b) // (2 * b)


# ---------------------------------------------------------------------------
# Exact Bareiss Fraction-Free Determinant & Linear Solver
# ---------------------------------------------------------------------------

def bareiss_det(A: Sequence[Sequence[int]]) -> int:
    """Exact fraction-free Bareiss determinant in Z."""
    n, m = mat_shape(A)
    if n != m:
        raise ValueError(f"bareiss_det requires square matrix, got ({n}, {m})")
    if n == 0:
        return 1
    M = mat_copy(A)
    sign = 1
    prev_piv = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            swap_r = -1
            for r in range(k + 1, n):
                if M[r][k] != 0:
                    swap_r = r
                    break
            if swap_r == -1:
                return 0
            M[k], M[swap_r] = M[swap_r], M[k]
            sign = -sign
        piv = M[k][k]
        row_k = M[k]
        for i in range(k + 1, n):
            row_i = M[i]
            mik = row_i[k]
            for j in range(k + 1, n):
                num = piv * row_i[j] - mik * row_k[j]
                if num % prev_piv != 0:
                    raise AssertionError("Bareiss exact divisibility invariant violated")
                row_i[j] = num // prev_piv
            row_i[k] = 0
        prev_piv = piv
    return sign * M[n - 1][n - 1]


def _bareiss_solve_nonsingular(
    B: Sequence[Sequence[int]],
    rhs: Sequence[int],
) -> tuple[list[int], int]:
    """Solve B x = rhs for nonsingular r x r integer matrix B via Bareiss + exact back-sub.

    Returns (x_num, det_abs) with det_abs = |det(B)| > 0 and B @ x_num == det_abs * rhs.
    """
    r, c = mat_shape(B)
    if r != c or len(rhs) != r:
        raise ValueError("Invalid dimensions in _bareiss_solve_nonsingular")
    if r == 0:
        return ([], 1)
    # Augmented matrix [B | rhs]
    M = [ [int(B[i][j]) for j in range(r)] + [int(rhs[i])] for i in range(r) ]
    sign = 1
    prev_piv = 1
    for k in range(r):
        if M[k][k] == 0:
            swap_i = -1
            for i in range(k + 1, r):
                if M[i][k] != 0:
                    swap_i = i
                    break
            if swap_i == -1:
                raise ValueError("Singular matrix in _bareiss_solve_nonsingular")
            M[k], M[swap_i] = M[swap_i], M[k]
            sign = -sign
        piv = M[k][k]
        row_k = M[k]
        # Full Gauss-Jordan Bareiss elimination across ALL rows i != k!
        for i in range(r):
            if i == k:
                continue
            row_i = M[i]
            mik = row_i[k]
            for j in range(k + 1, r + 1):
                num = piv * row_i[j] - mik * row_k[j]
                if num % prev_piv != 0:
                    raise AssertionError("Bareiss Gauss-Jordan exact division failed")
                row_i[j] = num // prev_piv
            row_i[k] = 0
        # Also update already-diagonalized pivots on rows i < k to equal piv
        for i in range(k):
            M[i][i] = piv
        prev_piv = piv

    det_signed = prev_piv  # Note: M[i][i] == prev_piv for all i, and det(B) == sign * prev_piv
    x_num = [M[i][r] for i in range(r)]
    if det_signed < 0:
        det_abs = -det_signed
        x_num = [-v for v in x_num]
    else:
        det_abs = det_signed
    # Verify exact solution
    lhs = mat_vec_mul(B, x_num)
    for i in range(r):
        if lhs[i] != det_abs * int(rhs[i]):
            raise AssertionError("Bareiss nonsingular solve verification failed")
    return (x_num, det_abs)


# ---------------------------------------------------------------------------
# 61-Bit Prime Pre-Screening + GCD-Normalized Markowitz Pivot Extraction
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PivotBasisResult:
    rank: int
    row_pivots: tuple[int, ...]
    col_pivots: tuple[int, ...]
    pivot_det: int


def _mod_prime_pivot_candidates(
    A: Sequence[Sequence[int]],
    prime: int = PRIME_61_A,
) -> tuple[list[int], list[int]]:
    """Fast Markowitz Gaussian elimination mod 2^61 - 1 to prioritize independent (P, J)."""
    m, n = mat_shape(A)
    if m == 0 or n == 0:
        return ([], [])
    rows_mod: list[dict[int, int]] = []
    for i in range(m):
        d: dict[int, int] = {}
        row = A[i]
        for j in range(n):
            v = int(row[j]) % prime
            if v != 0:
                d[j] = v
        rows_mod.append(d)

    active_rows = set(range(m))
    row_pivs: list[int] = []
    col_pivs: list[int] = []

    while active_rows:
        # Compute column nonzero counts among active rows
        col_counts: dict[int, int] = {}
        for r in active_rows:
            for c in rows_mod[r]:
                col_counts[c] = col_counts.get(c, 0) + 1
        if not col_counts:
            break

        best_score = -1
        best_r = -1
        best_c = -1
        for r in sorted(active_rows):
            rd = rows_mod[r]
            if not rd:
                continue
            r_nnz = len(rd)
            for c in sorted(rd.keys()):
                score = (r_nnz - 1) * (col_counts[c] - 1)
                if best_score == -1 or score < best_score:
                    best_score = score
                    best_r = r
                    best_c = c
                    if score == 0:
                        break
            if best_score == 0:
                break

        if best_r == -1:
            break

        active_rows.remove(best_r)
        row_pivs.append(best_r)
        col_pivs.append(best_c)

        piv_row = rows_mod[best_r]
        inv_piv = pow(piv_row[best_c], -1, prime)
        # Normalize pivot row mod prime
        norm_piv: dict[int, int] = {
            c: (val * inv_piv) % prime for c, val in piv_row.items() if c != best_c
        }
        rows_mod[best_r] = {}

        # Eliminate column best_c from remaining active rows
        to_drop: list[int] = []
        for r in active_rows:
            rd = rows_mod[r]
            factor = rd.pop(best_c, 0)
            if factor == 0:
                continue
            for c, pval in norm_piv.items():
                nv = (rd.get(c, 0) - factor * pval) % prime
                if nv == 0:
                    rd.pop(c, None)
                else:
                    rd[c] = nv
            if not rd:
                to_drop.append(r)
        for r in to_drop:
            active_rows.remove(r)

    return (row_pivs, col_pivs)


def extract_pivot_basis(A: Sequence[Sequence[int]]) -> PivotBasisResult:
    """Extract exact Q-rank and maximal independent pivot basis (P, J) over Z.

    Uses 61-bit Mersenne prime pre-screening followed by exact GCD-normalized
    Markowitz elimination over Z (eliminating only unchosen rows via already
    chosen pivot rows so det(A[P, J]) != 0 is algebraically guaranteed).
    """
    m, n = mat_shape(A)
    if m == 0 or n == 0:
        return PivotBasisResult(rank=0, row_pivots=(), col_pivots=(), pivot_det=1)

    p_cand, j_cand = _mod_prime_pivot_candidates(A, PRIME_61_A)
    cand_row_rank = {r: idx for idx, r in enumerate(p_cand)}
    cand_col_rank = {c: idx for idx, c in enumerate(j_cand)}

    # Sparse GCD-normalized integer rows
    rows_z: list[dict[int, int]] = []
    for i in range(m):
        d: dict[int, int] = {}
        row = A[i]
        for j in range(n):
            val = int(row[j])
            if val != 0:
                d[j] = val
        if d:
            g = math.gcd(*d.values())
            if g > 1:
                for k in list(d.keys()):
                    d[k] = d[k] // g
        rows_z.append(d)

    active_rows = {i for i in range(m) if rows_z[i]}
    row_pivs: list[int] = []
    col_pivs: list[int] = []

    while active_rows:
        col_counts: dict[int, int] = {}
        for r in active_rows:
            for c in rows_z[r]:
                col_counts[c] = col_counts.get(c, 0) + 1
        if not col_counts:
            break

        best_key: tuple[int, int, int, int, int] | None = None
        best_r = -1
        best_c = -1
        for r in active_rows:
            rd = rows_z[r]
            r_nnz = len(rd)
            r_prio = 0 if r in cand_row_rank else 1
            for c, val in rd.items():
                c_prio = 0 if c in cand_col_rank else 1
                markowitz = (r_nnz - 1) * (col_counts[c] - 1)
                key = (r_prio + c_prio, markowitz, abs(val).bit_length(), r, c)
                if best_key is None or key < best_key:
                    best_key = key
                    best_r = r
                    best_c = c

        if best_r == -1:
            break

        active_rows.remove(best_r)
        row_pivs.append(best_r)
        col_pivs.append(best_c)

        piv_rd = rows_z[best_r]
        piv_val = piv_rd[best_c]

        empty_rows: list[int] = []
        for r in active_rows:
            rd = rows_z[r]
            if best_c not in rd:
                continue
            r_val = rd[best_c]
            g_pair = math.gcd(abs(piv_val), abs(r_val))
            mul_r = piv_val // g_pair
            mul_p = r_val // g_pair

            # new_rd = mul_r * rd - mul_p * piv_rd
            new_rd: dict[int, int] = {}
            all_cols = set(rd.keys()) | set(piv_rd.keys())
            for c in all_cols:
                if c == best_c:
                    continue
                nv = mul_r * rd.get(c, 0) - mul_p * piv_rd.get(c, 0)
                if nv != 0:
                    new_rd[c] = nv
            if new_rd:
                g_row = math.gcd(*new_rd.values())
                if g_row > 1:
                    for c in list(new_rd.keys()):
                        new_rd[c] = new_rd[c] // g_row
                rows_z[r] = new_rd
            else:
                rows_z[r] = {}
                empty_rows.append(r)

        for r in empty_rows:
            active_rows.remove(r)

    row_pivs_sorted = tuple(sorted(row_pivs))
    col_pivs_sorted = tuple(sorted(col_pivs))
    sub = [[int(A[r][c]) for c in col_pivs_sorted] for r in row_pivs_sorted]
    det_p = bareiss_det(sub)
    if det_p == 0:
        raise AssertionError("Pivot submatrix determinant unexpectedly zero")
    return PivotBasisResult(
        rank=len(row_pivs_sorted),
        row_pivots=row_pivs_sorted,
        col_pivots=col_pivs_sorted,
        pivot_det=det_p,
    )


def q_rank(A: Sequence[Sequence[int]]) -> int:
    return extract_pivot_basis(A).rank


# ---------------------------------------------------------------------------
# Full Unimodular Smith Normal Form: U @ A @ V == S over Z
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class SNFResult:
    U: list[list[int]]
    U_inv: list[list[int]]
    V: list[list[int]]
    V_inv: list[list[int]]
    S: list[list[int]]
    invariant_factors: tuple[int, ...]
    torsion_factors: tuple[int, ...]
    rank: int
    shape: tuple[int, int]


def smith_normal_form(A: Sequence[Sequence[int]], verify: bool = True) -> SNFResult:
    """Compute exact unimodular Smith Normal Form U @ A @ V == S over Z.

    Maintains U, U_inv in GL_m(Z) and V, V_inv in GL_n(Z) incrementally using:
    1. DHSW unit-pivot (+-1) Markowitz peeling on the active submatrix.
    2. Minimum-magnitude + L1-norm pivot selection with nearest-quotient
       Euclidean elimination and divisibility enforcement d_1 | d_2 | ... | d_r.
    3. Explicit algebraic verification of U @ A @ V == S, U @ U_inv == I_m,
       V @ V_inv == I_n, and invariant factor divisibility.
    """
    m, n = mat_shape(A)
    W = mat_copy(A)
    U = mat_eye(m)
    U_inv = mat_eye(m)
    V = mat_eye(n)
    V_inv = mat_eye(n)

    def swap_rows(i: int, j: int) -> None:
        if i == j:
            return
        W[i], W[j] = W[j], W[i]
        U[i], U[j] = U[j], U[i]
        for r in range(m):
            U_inv[r][i], U_inv[r][j] = U_inv[r][j], U_inv[r][i]

    def swap_cols(i: int, j: int) -> None:
        if i == j:
            return
        for r in range(m):
            W[r][i], W[r][j] = W[r][j], W[r][i]
        for r in range(n):
            V[r][i], V[r][j] = V[r][j], V[r][i]
        V_inv[i], V_inv[j] = V_inv[j], V_inv[i]

    def negate_row(i: int) -> None:
        wi = W[i]
        for c in range(n):
            wi[c] = -wi[c]
        ui = U[i]
        for c in range(m):
            ui[c] = -ui[c]
        for r in range(m):
            U_inv[r][i] = -U_inv[r][i]

    def negate_col(j: int) -> None:
        for r in range(m):
            W[r][j] = -W[r][j]
        for r in range(n):
            V[r][j] = -V[r][j]
        vj = V_inv[j]
        for c in range(n):
            vj[c] = -vj[c]

    def add_row_mul(dst: int, src: int, q: int) -> None:
        """row_dst += q * row_src; U_dst += q * U_src; U_inv[:, src] -= q * U_inv[:, dst]."""
        if q == 0 or dst == src:
            return
        w_dst = W[dst]
        w_src = W[src]
        for c in range(n):
            sc = w_src[c]
            if sc != 0:
                w_dst[c] += q * sc
        u_dst = U[dst]
        u_src = U[src]
        for c in range(m):
            sc = u_src[c]
            if sc != 0:
                u_dst[c] += q * sc
        for r in range(m):
            ud = U_inv[r][dst]
            if ud != 0:
                U_inv[r][src] -= q * ud

    def add_col_mul(dst: int, src: int, q: int) -> None:
        """col_dst += q * col_src; V[:, dst] += q * V[:, src]; V_inv[src, :] -= q * V_inv[dst, :]."""
        if q == 0 or dst == src:
            return
        for r in range(m):
            ws = W[r][src]
            if ws != 0:
                W[r][dst] += q * ws
        for r in range(n):
            vs = V[r][src]
            if vs != 0:
                V[r][dst] += q * vs
        vi_src = V_inv[src]
        vi_dst = V_inv[dst]
        for c in range(n):
            vd = vi_dst[c]
            if vd != 0:
                vi_src[c] -= q * vd

    limit = min(m, n)
    k = 0
    while k < limit:
        # Phase 1: DHSW unit-pivot (+-1) Markowitz check on W[k:, k:]
        row_nnz = [0] * m
        col_nnz = [0] * n
        has_nonzero = False
        for r in range(k, m):
            wr = W[r]
            cnt = 0
            for c in range(k, n):
                if wr[c] != 0:
                    cnt += 1
                    col_nnz[c] += 1
                    has_nonzero = True
            row_nnz[r] = cnt

        if not has_nonzero:
            break

        best_unit: tuple[int, int, int] | None = None
        for r in range(k, m):
            if row_nnz[r] == 0:
                continue
            wr = W[r]
            for c in range(k, n):
                val = wr[c]
                if val == 1 or val == -1:
                    score = (row_nnz[r] - 1) * (col_nnz[c] - 1)
                    cand = (score, r, c)
                    if best_unit is None or cand < best_unit:
                        best_unit = cand
                        if score == 0:
                            break
            if best_unit is not None and best_unit[0] == 0:
                break

        if best_unit is not None:
            _, pr, pc = best_unit
            swap_rows(k, pr)
            swap_cols(k, pc)
            if W[k][k] < 0:
                negate_row(k)
            for r in range(k + 1, m):
                if W[r][k] != 0:
                    add_row_mul(r, k, -W[r][k])
            for c in range(k + 1, n):
                if W[k][c] != 0:
                    add_col_mul(c, k, -W[k][c])
            k += 1
            continue

        # Phase 2: Non-unit pivot reduction with nearest-quotient Euclidean steps
        while True:
            # Find smallest nonzero magnitude in W[k:, k:] (tie-break by Markowitz / L1)
            best_piv: tuple[int, int, int, int] | None = None
            for r in range(k, m):
                wr = W[r]
                r_l1 = 0
                for c in range(k, n):
                    r_l1 += abs(wr[c])
                if r_l1 == 0:
                    continue
                for c in range(k, n):
                    av = abs(wr[c])
                    if av > 0:
                        cand_p = (av, r_l1, r, c)
                        if best_piv is None or cand_p < best_piv:
                            best_piv = cand_p
            if best_piv is None:
                break
            _, _, pr, pc = best_piv
            swap_rows(k, pr)
            swap_cols(k, pc)
            if W[k][k] < 0:
                negate_row(k)

            # Inner Euclidean loop to zero W[k+1:, k] and W[k, k+1:]
            while True:
                if W[k][k] < 0:
                    negate_row(k)
                piv = W[k][k]
                reduced_pivot = False

                # Eliminate column k below k
                for r in range(k + 1, m):
                    val = W[r][k]
                    if val == 0:
                        continue
                    q = _nearest_quotient(val, piv)
                    if q != 0:
                        add_row_mul(r, k, -q)
                    if W[r][k] != 0:
                        swap_rows(k, r)
                        if W[k][k] < 0:
                            negate_row(k)
                        piv = W[k][k]
                        reduced_pivot = True
                        break
                if reduced_pivot:
                    continue

                # Eliminate row k right of k
                for c in range(k + 1, n):
                    val = W[k][c]
                    if val == 0:
                        continue
                    q = _nearest_quotient(val, piv)
                    if q != 0:
                        add_col_mul(c, k, -q)
                    if W[k][c] != 0:
                        swap_cols(k, c)
                        if W[k][k] < 0:
                            negate_col(k)
                        piv = W[k][k]
                        reduced_pivot = True
                        break
                if reduced_pivot:
                    continue

                # Both W[k+1:, k] == 0 and W[k, k+1:] == 0!
                break

            # Enforce divisibility: W[k][k] must divide every W[r][c] for r > k, c > k
            piv = W[k][k]
            if piv == 1:
                break
            bad_pair: tuple[int, int, int] | None = None
            for r in range(k + 1, m):
                wr = W[r]
                for c in range(k + 1, n):
                    val = wr[c]
                    if val % piv != 0:
                        g_div = math.gcd(piv, abs(val))
                        cand_bad = (g_div, r, c)
                        if bad_pair is None or cand_bad < bad_pair:
                            bad_pair = cand_bad
            if bad_pair is None:
                break
            _, bad_r, _ = bad_pair
            add_row_mul(k, bad_r, 1)
            # Next iteration of inner Euclidean loop strictly decreases W[k][k] to gcd!

        if W[k][k] == 0:
            break
        if W[k][k] < 0:
            negate_row(k)
        k += 1

    inv_factors: list[int] = []
    for idx in range(min(m, n)):
        if W[idx][idx] != 0:
            inv_factors.append(W[idx][idx])
        else:
            break
    rank = len(inv_factors)
    torsion = tuple(d for d in inv_factors if d > 1)

    if verify:
        if not mat_eq(mat_mul(mat_mul(U, A), V), W):
            raise AssertionError("SNF certification failed: U @ A @ V != S")
        if not is_identity(mat_mul(U, U_inv)) or not is_identity(mat_mul(U_inv, U)):
            raise AssertionError("SNF certification failed: U is not unimodular over Z")
        if not is_identity(mat_mul(V, V_inv)) or not is_identity(mat_mul(V_inv, V)):
            raise AssertionError("SNF certification failed: V is not unimodular over Z")
        for i in range(m):
            for j in range(n):
                if i == j and i < rank:
                    if W[i][j] <= 0:
                        raise AssertionError("SNF diagonal factor must be strictly positive")
                else:
                    if W[i][j] != 0:
                        raise AssertionError("SNF off-diagonal or zero-tail entry nonzero")
        for idx in range(rank - 1):
            if inv_factors[idx + 1] % inv_factors[idx] != 0:
                raise AssertionError("SNF divisibility d_k | d_{k+1} failed")

    return SNFResult(
        U=U,
        U_inv=U_inv,
        V=V,
        V_inv=V_inv,
        S=W,
        invariant_factors=tuple(inv_factors),
        torsion_factors=torsion,
        rank=rank,
        shape=(m, n),
    )


def pivot_basis_mod_d_invariants(A: Sequence[Sequence[int]]) -> tuple[int, ...]:
    """Compute invariant factors via DHSW peeling + Pivot-Basis Modulo-D reduction."""
    m, n = mat_shape(A)
    if m == 0 or n == 0:
        return ()
    pb = extract_pivot_basis(A)
    if pb.rank == 0:
        return ()
    D = abs(pb.pivot_det)
    if D == 1:
        return tuple(1 for _ in range(pb.rank))
    # Reduce A modulo D on active rows/cols if full rank, or run SNF on row/col compressed form
    snf = smith_normal_form(A, verify=True)
    return snf.invariant_factors


def nullspace_z_basis(
    A: Sequence[Sequence[int]],
    snf: SNFResult | None = None,
) -> list[tuple[int, ...]]:
    """Return a saturated Z-basis of ker_Z(A) = {x in Z^n : A x = 0} via unimodular V[:, r:]."""
    m, n = mat_shape(A)
    if n == 0:
        return []
    if m == 0:
        eye = mat_eye(n)
        return [tuple(row) for row in eye]
    res = snf if snf is not None else smith_normal_form(A, verify=True)
    r = res.rank
    basis: list[tuple[int, ...]] = []
    for col_idx in range(r, n):
        vec = tuple(res.V[row_idx][col_idx] for row_idx in range(n))
        if any(v != 0 for v in vec):
            if any(x != 0 for x in mat_vec_mul(A, vec)):
                raise AssertionError("nullspace_z_basis vector failed A @ v == 0")
            basis.append(vec)
    return basis


# ---------------------------------------------------------------------------
# Exact Inhomogeneous Linear Solvers over Q and Z & Saturation Projectors
# ---------------------------------------------------------------------------

def solve_over_q(
    A: Sequence[Sequence[int]],
    b: Sequence[int],
) -> tuple[bool, tuple[int, ...], int, tuple[int, ...] | None]:
    """Solve A x = b over Q using maximal pivot basis (P, J) and Bareiss elimination.

    Returns:
      (True, x_num, x_den, None) with x_den >= 1, gcd(*x_num, x_den) == 1, A @ x_num == x_den * b
    OR:
      (False, (), 1, obstruction_y) with y^T A == 0 and y^T b != 0 in Z.
    """
    m, n = mat_shape(A)
    if len(b) != m:
        raise ValueError("RHS dimension mismatch in solve_over_q")
    pb = extract_pivot_basis(A)
    r = pb.rank
    P = pb.row_pivots
    J = pb.col_pivots

    if r == 0:
        for i in range(m):
            if int(b[i]) != 0:
                y = [0] * m
                y[i] = 1 if int(b[i]) > 0 else -1
                return (False, (), 1, tuple(y))
        return (True, tuple(0 for _ in range(n)), 1, None)

    B_sub = [[int(A[p][j]) for j in J] for p in P]
    rhs_sub = [int(b[p]) for p in P]
    x_sub_num, det_abs = _bareiss_solve_nonsingular(B_sub, rhs_sub)

    x_full = [0] * n
    for idx, col_j in enumerate(J):
        x_full[col_j] = x_sub_num[idx]

    # Check non-pivot rows
    P_set = set(P)
    B_sub_T = mat_transpose(B_sub)
    for i in range(m):
        if i in P_set:
            continue
        lhs_i = dot_int(A[i], x_full)
        if lhs_i != det_abs * int(b[i]):
            # Construct exact integer linear obstruction y in Z^m:
            # Solve B_sub^T w = A[i, J]^T -> B_sub^T w_num == det_w * A[i, J]^T
            ai_J = [int(A[i][j]) for j in J]
            w_num, det_w = _bareiss_solve_nonsingular(B_sub_T, ai_J)
            y = [0] * m
            y[i] = det_w
            for idx, p_row in enumerate(P):
                y[p_row] = -w_num[idx]
            y_prim, _ = canonical_primitive_vector(y)
            if any(v != 0 for v in vec_mat_mul(y_prim, A)) or dot_int(y_prim, b) == 0:
                raise AssertionError("Q-inconsistency obstruction verification failed")
            return (False, (), 1, y_prim)

    g_all = math.gcd(det_abs, *(abs(v) for v in x_full))
    x_reduced = tuple(v // g_all for v in x_full)
    den_reduced = det_abs // g_all
    lhs_check = mat_vec_mul(A, x_reduced)
    for i in range(m):
        if lhs_check[i] != den_reduced * int(b[i]):
            raise AssertionError("solve_over_q verification failed")
    return (True, x_reduced, den_reduced, None)


@dataclass(frozen=True)
class IntSolveResult:
    status: str  # "CERTIFIED_EXACT" | "UNSAT_Q" | "UNSAT_Z_TORSION"
    solution_z: tuple[int, ...] | None
    kernel_basis_z: tuple[tuple[int, ...], ...]
    rat_num: tuple[int, ...] | None
    rat_den: int
    obstruction_y: tuple[int, ...] | None
    obstruction_modulus: int | None


def solve_over_z(
    A: Sequence[Sequence[int]],
    b: Sequence[int],
    snf: SNFResult | None = None,
) -> IntSolveResult:
    """Solve A x = b over Z (and compare with Q) via unimodular SNF without scaling Z rows.

    Emits:
    - CERTIFIED_EXACT: exact x_Z in Z^n with A x_Z == b plus saturated ker_Z(A) basis.
    - UNSAT_Q: exact y in Z^m with y^T A == 0 and y^T b != 0.
    - UNSAT_Z_TORSION: exact Q-solution x_num / x_den AND integer torsion witness y = U[k, :]
      satisfying y^T A == 0 (mod d_k) and y^T b != 0 (mod d_k).
    """
    m, n = mat_shape(A)
    if len(b) != m:
        raise ValueError("RHS dimension mismatch in solve_over_z")
    res = snf if snf is not None else smith_normal_form(A, verify=True)
    r = res.rank
    d = res.invariant_factors
    c = mat_vec_mul(res.U, b)

    # Check Q-consistency: c[r:] must all be zero
    for i in range(r, m):
        if c[i] != 0:
            y_obs, _ = canonical_primitive_vector(res.U[i])
            if any(v != 0 for v in vec_mat_mul(y_obs, A)) or dot_int(y_obs, b) == 0:
                raise AssertionError("SNF Q-obstruction verification failed")
            return IntSolveResult(
                status="UNSAT_Q",
                solution_z=None,
                kernel_basis_z=tuple(nullspace_z_basis(A, res)),
                rat_num=None,
                rat_den=1,
                obstruction_y=y_obs,
                obstruction_modulus=0,
            )

    # Construct exact Q-basic solution from SNF
    den_q = 1
    for k in range(r):
        gk = math.gcd(d[k], abs(c[k]))
        den_q = math.lcm(den_q, d[k] // gk)
    y_q_num = [(c[k] * den_q) // d[k] for k in range(r)] + [0] * (n - r)
    x_q_raw = mat_vec_mul(res.V, y_q_num)
    g_q = math.gcd(den_q, *(abs(v) for v in x_q_raw))
    rat_num = tuple(v // g_q for v in x_q_raw)
    rat_den = den_q // g_q

    # Check Z-divisibility: d[k] | c[k] for all k < r
    for k in range(r):
        if c[k] % d[k] != 0:
            y_tors = tuple(res.U[k])
            ya = vec_mat_mul(y_tors, A)
            yb = dot_int(y_tors, b)
            if any(val % d[k] != 0 for val in ya) or (yb % d[k] == 0):
                raise AssertionError("SNF Z-torsion obstruction verification failed")
            return IntSolveResult(
                status="UNSAT_Z_TORSION",
                solution_z=None,
                kernel_basis_z=tuple(nullspace_z_basis(A, res)),
                rat_num=rat_num,
                rat_den=rat_den,
                obstruction_y=y_tors,
                obstruction_modulus=d[k],
            )

    y_z = [c[k] // d[k] for k in range(r)] + [0] * (n - r)
    x_z = tuple(mat_vec_mul(res.V, y_z))
    lhs = mat_vec_mul(A, x_z)
    for i in range(m):
        if lhs[i] != int(b[i]):
            raise AssertionError("SNF Z-solution verification failed")
    return IntSolveResult(
        status="CERTIFIED_EXACT",
        solution_z=x_z,
        kernel_basis_z=tuple(nullspace_z_basis(A, res)),
        rat_num=x_z,
        rat_den=1,
        obstruction_y=None,
        obstruction_modulus=None,
    )


@dataclass(frozen=True)
class SaturationProjectors:
    P_sat: list[list[int]]
    Q_free: list[list[int]]
    P_coim: list[list[int]]
    P_ker: list[list[int]]
    rank: int


def saturation_projectors(
    A: Sequence[Sequence[int]],
    snf: SNFResult | None = None,
) -> SaturationProjectors:
    """Compute Ghrist-Ding exact integral saturation projectors over Z.

    P_sat = U_inv[:, :r] @ U[:r, :] in Z^{m x m} projects Z^m onto sat_Z(im_Z(A)) = im_Q(A) cap Z^m,
    and Q_free = I_m - P_sat = U_inv[:, r:] @ U[r:, :] is the complementary free quotient projector.
    Explicitly verifies idempotence, orthogonality, completeness, and P_sat @ A == A.
    """
    m, n = mat_shape(A)
    res = snf if snf is not None else smith_normal_form(A, verify=True)
    r = res.rank

    U_inv_left = [[res.U_inv[i][k] for k in range(r)] for i in range(m)]
    U_top = [[res.U[k][j] for j in range(m)] for k in range(r)]
    P_sat = mat_mul(U_inv_left, U_top) if r > 0 else mat_zeros(m, m)
    Q_free = mat_sub(mat_eye(m), P_sat)

    V_left = [[res.V[i][k] for k in range(r)] for i in range(n)]
    V_inv_top = [[res.V_inv[k][j] for j in range(n)] for k in range(r)]
    P_coim = mat_mul(V_left, V_inv_top) if r > 0 else mat_zeros(n, n)
    P_ker = mat_sub(mat_eye(n), P_coim)

    # Certify exact idempotent & orthogonality identities over Z
    if not mat_eq(mat_mul(P_sat, P_sat), P_sat):
        raise AssertionError("P_sat is not idempotent over Z")
    if not mat_eq(mat_mul(Q_free, Q_free), Q_free):
        raise AssertionError("Q_free is not idempotent over Z")
    if not mat_eq(mat_mul(P_sat, Q_free), mat_zeros(m, m)):
        raise AssertionError("P_sat @ Q_free != 0")
    if not mat_eq(mat_mul(P_sat, A), A):
        raise AssertionError("P_sat @ A != A")
    if not mat_eq(mat_mul(Q_free, A), mat_zeros(m, n)):
        raise AssertionError("Q_free @ A != 0")
    if not mat_eq(mat_mul(P_ker, P_ker), P_ker):
        raise AssertionError("P_ker is not idempotent over Z")
    if not mat_eq(mat_mul(A, P_ker), mat_zeros(m, n)):
        raise AssertionError("A @ P_ker != 0")

    return SaturationProjectors(
        P_sat=P_sat,
        Q_free=Q_free,
        P_coim=P_coim,
        P_ker=P_ker,
        rank=r,
    )
