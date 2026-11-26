"""Independent zero-dependency pure-integer certificate verification kernel.

Strictly enforces:
- 100% Python 3.9+ standard library only (`from __future__ import annotations`).
- Zero `float` literals/calls/annotations, zero `/` division, zero `Fraction`, zero `isinstance`.
- Pure certificate verification (matrix identities, unimodularity, SNF divisibility,
  Ghrist-Ding integer saturation idempotents, Farkas duals, p-adic valuation obstructions,
  and exact full-dimensional sub-chamber symbolic CPWL identity checks).
"""

from __future__ import annotations

import itertools
import math
from typing import Any, Callable, Sequence

IntMatrix = list[list[int]]
IntVector = list[int]
RatPair = tuple[int, int]  # (num, den) with den > 0 and gcd(|num|, den) == 1


# ---------------------------------------------------------------------------
# Strict pure-int type & shape guards (using `type(x) is int`, rejecting bool!)
# ---------------------------------------------------------------------------


def assert_strict_int(val: Any, context: str = "value") -> int:
    """Assert `val` is strictly a native Python `int` (rejecting `bool`, `float`, etc.)."""
    if type(val) is not int:
        raise TypeError(f"{context}: expected strict int, got {type(val).__name__}")
    return val


def assert_int_vector(vec: Sequence[Any], context: str = "vector") -> IntVector:
    """Validate and copy a 1D integer sequence."""
    out: IntVector = []
    for idx, entry in enumerate(vec):
        out.append(assert_strict_int(entry, f"{context}[{idx}]"))
    return out


def assert_int_matrix(
    mat: Sequence[Sequence[Any]],
    expected_rows: int | None = None,
    expected_cols: int | None = None,
    context: str = "matrix",
) -> IntMatrix:
    """Validate and copy a 2D rectangular integer matrix."""
    rows = len(mat)
    if expected_rows is not None and rows != expected_rows:
        raise ValueError(f"{context}: expected {expected_rows} rows, got {rows}")
    if rows == 0:
        if expected_cols is not None and expected_cols != 0:
            raise ValueError(f"{context}: empty rows with expected_cols={expected_cols}")
        return []
    cols = len(mat[0])
    if expected_cols is not None and cols != expected_cols:
        raise ValueError(f"{context}: expected {expected_cols} cols, got {cols}")
    out: IntMatrix = []
    for r_idx, row in enumerate(mat):
        if len(row) != cols:
            raise ValueError(f"{context}: ragged row {r_idx} (len {len(row)} != {cols})")
        out_row: IntVector = []
        for c_idx, val in enumerate(row):
            out_row.append(assert_strict_int(val, f"{context}[{r_idx}][{c_idx}]"))
        out.append(out_row)
    return out


# ---------------------------------------------------------------------------
# Elementary exact integer & rational-pair (`(num, den)`) operations
# ---------------------------------------------------------------------------


def rat_norm(num: int, den: int) -> RatPair:
    """Normalize an exact rational `(num, den)` using strictly integer operations."""
    assert_strict_int(num, "rat_num")
    assert_strict_int(den, "rat_den")
    if den == 0:
        raise ZeroDivisionError("Rational denominator cannot be zero")
    if den < 0:
        num = -num
        den = -den
    if num == 0:
        return (0, 1)
    g = math.gcd(abs(num), den)
    return (num // g, den // g)


def rat_add(a: RatPair, b: RatPair) -> RatPair:
    return rat_norm(a[0] * b[1] + b[0] * a[1], a[1] * b[1])


def rat_sub(a: RatPair, b: RatPair) -> RatPair:
    return rat_norm(a[0] * b[1] - b[0] * a[1], a[1] * b[1])


def rat_mul(a: RatPair, b: RatPair) -> RatPair:
    return rat_norm(a[0] * b[0], a[1] * b[1])


def rat_lt(a: RatPair, b: RatPair) -> bool:
    return a[0] * b[1] < b[0] * a[1]


def rat_le(a: RatPair, b: RatPair) -> bool:
    return a[0] * b[1] <= b[0] * a[1]


def rat_max(a: RatPair, b: RatPair) -> RatPair:
    return b if rat_lt(a, b) else a


def rat_relu(a: RatPair) -> RatPair:
    return a if a[0] > 0 else (0, 1)


def rat_str(a: RatPair) -> str:
    qn = rat_norm(a[0], a[1])
    return str(qn[0]) if qn[1] == 1 else f"{qn[0]}/{qn[1]}"


def mat_eye(n: int) -> IntMatrix:
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def mat_zeros(rows: int, cols: int) -> IntMatrix:
    return [[0 for _ in range(cols)] for _ in range(rows)]


def mat_transpose(a: IntMatrix) -> IntMatrix:
    if not a:
        return []
    m = len(a)
    n = len(a[0])
    return [[a[i][j] for i in range(m)] for j in range(n)]


def mat_mul(a: IntMatrix, b: IntMatrix) -> IntMatrix:
    """Exact integer matrix product `A @ B`."""
    if not a or not b:
        return []
    m = len(a)
    k = len(a[0])
    if len(b) != k:
        raise ValueError(f"mat_mul shape mismatch: ({m}, {k}) @ ({len(b)}, {len(b[0])})")
    n = len(b[0])
    bt = mat_transpose(b)
    out: IntMatrix = []
    for i in range(m):
        ai = a[i]
        row: IntVector = []
        for j in range(n):
            bj = bt[j]
            acc = 0
            for t in range(k):
                acc += ai[t] * bj[t]
            row.append(acc)
        out.append(row)
    return out


def mat_vec_mul(a: IntMatrix, x: IntVector) -> IntVector:
    """Exact integer matrix-vector product `A @ x`."""
    if not a:
        return []
    k = len(a[0])
    if len(x) != k:
        raise ValueError(f"mat_vec_mul shape mismatch: ({len(a)}, {k}) @ ({len(x)},)")
    out: IntVector = []
    for row in a:
        acc = 0
        for t in range(k):
            acc += row[t] * x[t]
        out.append(acc)
    return out


def vec_mat_mul(y: IntVector, a: IntMatrix) -> IntVector:
    """Exact integer vector-matrix product `y^T @ A`."""
    if not a:
        if len(y) != 0:
            raise ValueError("vec_mat_mul empty matrix with non-empty vector")
        return []
    m = len(a)
    n = len(a[0])
    if len(y) != m:
        raise ValueError(f"vec_mat_mul shape mismatch: ({len(y)},) @ ({m}, {n})")
    out = [0] * n
    for i in range(m):
        yi = y[i]
        if yi != 0:
            ai = a[i]
            for j in range(n):
                out[j] += yi * ai[j]
    return out


def vec_dot(u: IntVector, v: IntVector) -> int:
    if len(u) != len(v):
        raise ValueError(f"vec_dot length mismatch: {len(u)} != {len(v)}")
    acc = 0
    for ui, vi in zip(u, v):
        acc += ui * vi
    return acc


def mat_sub(a: IntMatrix, b: IntMatrix) -> IntMatrix:
    return [[a[i][j] - b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def mat_add(a: IntMatrix, b: IntMatrix) -> IntMatrix:
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def mat_trace(a: IntMatrix) -> int:
    n = len(a)
    acc = 0
    for i in range(n):
        acc += a[i][i]
    return acc


def exact_det_bareiss(mat: IntMatrix) -> int:
    """Exact fraction-free Bareiss determinant over Z."""
    a = assert_int_matrix(mat, context="det_mat")
    n = len(a)
    if n == 0:
        return 1
    if len(a[0]) != n:
        raise ValueError("Determinant requires a square matrix")
    m = [list(row) for row in a]
    sign = 1
    prev_pivot = 1
    for k in range(n - 1):
        if m[k][k] == 0:
            swap_row = None
            for r in range(k + 1, n):
                if m[r][k] != 0:
                    swap_row = r
                    break
            if swap_row is None:
                return 0
            m[k], m[swap_row] = m[swap_row], m[k]
            sign = -sign
        piv = m[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                num = m[i][j] * piv - m[i][k] * m[k][j]
                if num % prev_pivot != 0:
                    raise AssertionError("Bareiss exactness invariant violated")
                m[i][j] = num // prev_pivot
            m[i][k] = 0
        prev_pivot = piv
    return sign * m[n - 1][n - 1]


def is_prime_int(p: int) -> bool:
    """Exact deterministic primality check over Z."""
    assert_strict_int(p, "prime_p")
    if p < 2:
        return False
    if p in (2, 3):
        return True
    if p % 2 == 0 or p % 3 == 0:
        return False
    d = 5
    while d * d <= p:
        if p % d == 0 or p % (d + 2) == 0:
            return False
        d += 6
    return True


def padic_valuation(n: int, p: int) -> int | None:
    """Return `v_p(n)` as non-negative `int`, or `None` representing `+infinity` at `n == 0`."""
    assert_strict_int(n, "n")
    assert_strict_int(p, "p")
    if p < 2:
        raise ValueError(f"Invalid prime base p={p}")
    if n == 0:
        return None
    val = abs(n)
    k = 0
    while val % p == 0:
        val //= p
        k += 1
    return k


# ---------------------------------------------------------------------------
# 1. Unimodular SNF Factorization Verifier
# ---------------------------------------------------------------------------


def verify_snf_certificate(
    a: Sequence[Sequence[int]],
    u: Sequence[Sequence[int]],
    u_inv: Sequence[Sequence[int]],
    s: Sequence[Sequence[int]],
    v: Sequence[Sequence[int]],
    v_inv: Sequence[Sequence[int]],
    claimed_invariant_factors: Sequence[int] | None = None,
) -> dict[str, Any]:
    """Independently verify `U @ A @ V == S` over Z with `U @ U_inv == I`, `V @ V_inv == I`, and `d_1 | ... | d_r`."""
    a_mat = assert_int_matrix(a, context="A")
    m = len(a_mat)
    n = len(a_mat[0]) if m > 0 else 0
    u_mat = assert_int_matrix(u, m, m, context="U")
    u_inv_mat = assert_int_matrix(u_inv, m, m, context="U_inv")
    s_mat = assert_int_matrix(s, m, n, context="S")
    v_mat = assert_int_matrix(v, n, n, context="V")
    v_inv_mat = assert_int_matrix(v_inv, n, n, context="V_inv")

    eye_m = mat_eye(m)
    eye_n = mat_eye(n)
    if mat_mul(u_mat, u_inv_mat) != eye_m:
        raise AssertionError("SNF certificate failed: U @ U_inv != I_m")
    if mat_mul(u_inv_mat, u_mat) != eye_m:
        raise AssertionError("SNF certificate failed: U_inv @ U != I_m")
    if mat_mul(v_mat, v_inv_mat) != eye_n:
        raise AssertionError("SNF certificate failed: V @ V_inv != I_n")
    if mat_mul(v_inv_mat, v_mat) != eye_n:
        raise AssertionError("SNF certificate failed: V_inv @ V != I_n")

    uav = mat_mul(mat_mul(u_mat, a_mat), v_mat)
    if uav != s_mat:
        raise AssertionError("SNF certificate failed: U @ A @ V != S")

    # Check S is strictly diagonal with positive non-decreasingly divisible invariant factors followed by zeros
    diag_len = min(m, n)
    for i in range(m):
        for j in range(n):
            if i != j and s_mat[i][j] != 0:
                raise AssertionError(f"SNF certificate failed: off-diagonal S[{i}][{j}]={s_mat[i][j]} != 0")

    invariant_factors: list[int] = []
    seen_zero = False
    for k in range(diag_len):
        dk = s_mat[k][k]
        if dk < 0:
            raise AssertionError(f"SNF certificate failed: negative diagonal S[{k}][{k}]={dk}")
        if dk == 0:
            seen_zero = True
        else:
            if seen_zero:
                raise AssertionError(f"SNF certificate failed: non-zero S[{k}][{k}]={dk} after zero diagonal")
            invariant_factors.append(dk)

    rank = len(invariant_factors)
    for k in range(rank - 1):
        if invariant_factors[k + 1] % invariant_factors[k] != 0:
            raise AssertionError(
                f"SNF divisibility failed: d_{k+1}={invariant_factors[k]} does not divide d_{k+2}={invariant_factors[k+1]}"
            )

    if claimed_invariant_factors is not None:
        claimed = assert_int_vector(claimed_invariant_factors, "claimed_invariant_factors")
        if invariant_factors != claimed:
            raise AssertionError(
                f"SNF invariant factor mismatch: certified {invariant_factors} != claimed {claimed}"
            )

    return {
        "verified": True,
        "shape": [m, n],
        "rank": rank,
        "invariant_factors": invariant_factors,
        "torsion_factors": [d for d in invariant_factors if d > 1],
    }


# ---------------------------------------------------------------------------
# 2. Ghrist-Ding Integer Saturation Idempotent Verifier
# ---------------------------------------------------------------------------


def verify_saturation_projector(
    a: Sequence[Sequence[int]],
    p_sat: Sequence[Sequence[int]],
    q_free: Sequence[Sequence[int]] | None = None,
    u: Sequence[Sequence[int]] | None = None,
    u_inv: Sequence[Sequence[int]] | None = None,
    rank: int | None = None,
) -> dict[str, Any]:
    """Verify Ghrist-Ding integral saturation projector `P_sat in Z^{m x m}` (and `Q_free = I - P_sat`).

    Checks:
      - `P_sat @ P_sat == P_sat` over Z (exact integer idempotent)
      - `Q_free == I_m - P_sat`, `Q_free @ Q_free == Q_free`, `P_sat @ Q_free == 0`, `Q_free @ P_sat == 0`
      - `P_sat @ A == A` and `Q_free @ A == 0`
      - If `(U, U_inv, rank)` provided: `U @ U_inv == I_m` and `P_sat == U_inv[:, :r] @ U[:r, :]`
      - `trace(P_sat) == r`
    """
    a_mat = assert_int_matrix(a, context="A")
    m = len(a_mat)
    p_mat = assert_int_matrix(p_sat, m, m, context="P_sat")
    eye_m = mat_eye(m)
    zero_m = mat_zeros(m, m)

    if mat_mul(p_mat, p_mat) != p_mat:
        raise AssertionError("Saturation projector failed: P_sat @ P_sat != P_sat")

    expected_q = mat_sub(eye_m, p_mat)
    q_mat = assert_int_matrix(q_free, m, m, context="Q_free") if q_free is not None else expected_q
    if q_mat != expected_q:
        raise AssertionError("Saturation projector failed: P_sat + Q_free != I_m")
    if mat_mul(q_mat, q_mat) != q_mat:
        raise AssertionError("Saturation projector failed: Q_free @ Q_free != Q_free")
    if mat_mul(p_mat, q_mat) != zero_m or mat_mul(q_mat, p_mat) != zero_m:
        raise AssertionError("Saturation projector failed: P_sat and Q_free not mutually orthogonal")

    if m > 0 and len(a_mat[0]) > 0:
        if mat_mul(p_mat, a_mat) != a_mat:
            raise AssertionError("Saturation projector failed: P_sat @ A != A")
        if mat_mul(q_mat, a_mat) != mat_zeros(m, len(a_mat[0])):
            raise AssertionError("Saturation projector failed: Q_free @ A != 0")

    tr = mat_trace(p_mat)
    if rank is not None:
        assert_strict_int(rank, "rank")
        if tr != rank:
            raise AssertionError(f"Saturation projector trace={tr} != rank={rank}")

    if u is not None and u_inv is not None:
        u_mat = assert_int_matrix(u, m, m, context="U")
        u_inv_mat = assert_int_matrix(u_inv, m, m, context="U_inv")
        if mat_mul(u_mat, u_inv_mat) != eye_m or mat_mul(u_inv_mat, u_mat) != eye_m:
            raise AssertionError("Saturation projector failed: U is not unimodular")
        r = tr if rank is None else rank
        if r == 0:
            expected_p = zero_m
        else:
            u_inv_left = [[u_inv_mat[i][k] for k in range(r)] for i in range(m)]
            u_top = [[u_mat[k][j] for j in range(m)] for k in range(r)]
            expected_p = mat_mul(u_inv_left, u_top)
        if p_mat != expected_p:
            raise AssertionError("Saturation projector failed: P_sat != U_inv[:, :r] @ U[:r, :]")

    return {
        "verified": True,
        "dim": m,
        "rank": tr,
        "corank": m - tr,
    }


# ---------------------------------------------------------------------------
# 3. Exact Non-Negative Integer Farkas Dual Witness Verifiers
# ---------------------------------------------------------------------------


def verify_farkas_le_certificate(
    a_ub: Sequence[Sequence[int]],
    b_ub: Sequence[int],
    y: Sequence[int],
) -> dict[str, Any]:
    """Verify Farkas dual certificate refuting `A_ub x <= b_ub` over Q^n.

    Checks strictly over Z:
      - `y_i >= 0` for all `i`
      - `y^T @ A_ub == 0`
      - `y^T @ b_ub < 0`
    """
    a_mat = assert_int_matrix(a_ub, context="A_ub")
    m = len(a_mat)
    b_vec = assert_int_vector(b_ub, context="b_ub")
    y_vec = assert_int_vector(y, context="y")
    if len(b_vec) != m or len(y_vec) != m:
        raise ValueError(f"Farkas dimension mismatch: m={m}, len(b)={len(b_vec)}, len(y)={len(y_vec)}")

    for idx, yi in enumerate(y_vec):
        if yi < 0:
            raise AssertionError(f"Farkas certificate failed: negative dual weight y[{idx}]={yi}")

    yta = vec_mat_mul(y_vec, a_mat)
    for j, val in enumerate(yta):
        if val != 0:
            raise AssertionError(f"Farkas certificate failed: (y^T A)[{j}] = {val} != 0")

    ytb = vec_dot(y_vec, b_vec)
    if ytb >= 0:
        raise AssertionError(f"Farkas certificate failed: y^T b = {ytb} is not < 0")

    return {
        "verified": True,
        "num_constraints": m,
        "num_vars": len(a_mat[0]) if m > 0 else 0,
        "support_size": sum(1 for yi in y_vec if yi > 0),
        "yt_b": ytb,
    }


def verify_farkas_equality_certificate(
    a_eq: Sequence[Sequence[int]],
    b_eq: Sequence[int],
    y_signed: Sequence[int],
) -> dict[str, Any]:
    """Verify exact integer dual refuting `A_eq x == b_eq` over Q^n, AND reduce to `A_ub x <= b_ub` with `y >= 0`.

    Given `y_signed in Z^m` with `y_signed^T A_eq == 0` and `y_signed^T b_eq != 0` (flipping sign if `> 0`?
    No: verifier checks `y_signed^T b_eq < 0` directly AND constructs canonical `y_nonneg >= 0` on `[A_eq; -A_eq] x <= [b_eq; -b_eq]`).
    """
    a_mat = assert_int_matrix(a_eq, context="A_eq")
    b_vec = assert_int_vector(b_eq, context="b_eq")
    y_vec = assert_int_vector(y_signed, context="y_signed")
    m = len(a_mat)
    if len(b_vec) != m or len(y_vec) != m:
        raise ValueError("Equality Farkas dimension mismatch")

    a_ub = [list(row) for row in a_mat] + [[-val for val in row] for row in a_mat]
    b_ub = list(b_vec) + [-val for val in b_vec]
    y_nonneg = [yi if yi > 0 else 0 for yi in y_vec] + [-yi if yi < 0 else 0 for yi in y_vec]
    res = verify_farkas_le_certificate(a_ub, b_ub, y_nonneg)
    res["equality_rows"] = m
    return res


# ---------------------------------------------------------------------------
# 4. p-Adic Valuation & Z[1/2] Local-Global Certificate Verifiers
# ---------------------------------------------------------------------------


def verify_padic_obstruction_certificate(
    a: Sequence[Sequence[int]],
    b: Sequence[int],
    y: Sequence[int],
    p: int,
    s_bound: int | None = None,
    inverted_primes: Sequence[int] = (),
) -> dict[str, Any]:
    """Verify p-adic dual obstruction refuting `exists c in Z_{(p)}^N : A c == b`.

    Checks:
      - `p` is prime and `p` is NOT in `inverted_primes` (e.g., `p != 2` when refuting `Z[1/2]`).
      - `y^T b != 0` so `v_p(y^T b)` is finite.
      - `min_j v_p((y^T A)_j) >= s > v_p(y^T b)`.
    """
    assert_strict_int(p, "p")
    if not is_prime_int(p):
        raise AssertionError(f"p-adic obstruction failed: p={p} is not prime")
    inv_list = assert_int_vector(inverted_primes, "inverted_primes")
    if p in inv_list:
        raise AssertionError(f"p-adic obstruction invalid: prime p={p} is inverted in target ring")

    a_mat = assert_int_matrix(a, context="A")
    b_vec = assert_int_vector(b, context="b")
    y_vec = assert_int_vector(y, context="y")
    if len(a_mat) != len(b_vec) or len(a_mat) != len(y_vec):
        raise ValueError("p-adic obstruction dimension mismatch")

    yta = vec_mat_mul(y_vec, a_mat)
    ytb = vec_dot(y_vec, b_vec)
    if ytb == 0:
        raise AssertionError("p-adic obstruction failed: y^T b == 0 has infinite valuation")

    vb = padic_valuation(ytb, p)
    assert vb is not None

    min_va: int | None = None
    for val in yta:
        v_val = padic_valuation(val, p)
        if v_val is not None:
            if min_va is None or v_val < min_va:
                min_va = v_val

    if s_bound is not None:
        assert_strict_int(s_bound, "s_bound")
        if s_bound <= vb:
            raise AssertionError(f"p-adic obstruction failed: s={s_bound} is not > v_p(y^T b)={vb}")
        if min_va is not None and min_va < s_bound:
            raise AssertionError(f"p-adic obstruction failed: v_p(y^T A)={min_va} < s={s_bound}")
        effective_s = s_bound
    else:
        if min_va is not None and min_va <= vb:
            raise AssertionError(f"p-adic obstruction failed: v_p(y^T A)={min_va} <= v_p(y^T b)={vb}")
        effective_s = (vb + 1) if min_va is None else min_va

    return {
        "verified": True,
        "prime": p,
        "vp_yt_a": "inf" if min_va is None else min_va,
        "s_threshold": effective_s,
        "vp_yt_b": vb,
        "yt_b": ytb,
    }


def verify_z_half_solution_certificate(
    a: Sequence[Sequence[int]],
    b: Sequence[int],
    c_num: Sequence[int],
    k_exp: int,
) -> dict[str, Any]:
    """Verify `A @ (c_num / 2^k_exp) == b` with `c_num in Z^N, k_exp >= 0`."""
    assert_strict_int(k_exp, "k_exp")
    if k_exp < 0:
        raise ValueError(f"k_exp must be >= 0, got {k_exp}")
    a_mat = assert_int_matrix(a, context="A")
    b_vec = assert_int_vector(b, context="b")
    c_vec = assert_int_vector(c_num, context="c_num")
    scale = 1 << k_exp
    lhs = mat_vec_mul(a_mat, c_vec)
    rhs = [scale * bi for bi in b_vec]
    if lhs != rhs:
        raise AssertionError("Z[1/2] solution certificate failed: A @ c_num != 2^k * b")
    return {
        "verified": True,
        "k_exp": k_exp,
        "denom_pow2": scale,
    }


# ---------------------------------------------------------------------------
# 5. Exact Symbolic Full-Dimensional Sub-Chamber CPWL Identity Verifier
# ---------------------------------------------------------------------------
# Represents piecewise-affine expressions symbolically and splits chambers whenever
# an off-braid hyperplane strictly cuts a cone with non-empty interior, proving
# unconditional equality across ALL x in R^n (not mere finite point sampling!).


class SymbolicCPWL:
    """Symbolic tree for exact integer-coefficient homogeneous/affine CPWL expressions on R^n."""

    def __init__(self, kind: str, args: tuple[Any, ...]) -> None:
        self.kind = kind
        self.args = args

    @staticmethod
    def affine(bias: int, coeffs: Sequence[int], denom: int = 1) -> SymbolicCPWL:
        assert_strict_int(bias, "bias")
        assert_strict_int(denom, "denom")
        if denom <= 0:
            raise ValueError("denom must be positive")
        c_tup = tuple(assert_int_vector(coeffs, "coeffs"))
        return SymbolicCPWL("affine", (bias, c_tup, denom))

    @staticmethod
    def coord(n_dim: int, idx: int, scale: int = 1) -> SymbolicCPWL:
        coeffs = [scale if j == idx else 0 for j in range(n_dim)]
        return SymbolicCPWL.affine(0, coeffs, 1)

    @staticmethod
    def relu(expr: SymbolicCPWL) -> SymbolicCPWL:
        return SymbolicCPWL("relu", (expr,))

    @staticmethod
    def max2(e1: SymbolicCPWL, e2: SymbolicCPWL) -> SymbolicCPWL:
        # max(e1, e2) == e1 + ReLU(e2 - e1)
        return SymbolicCPWL.add(e1, SymbolicCPWL.relu(SymbolicCPWL.sub(e2, e1)))

    @staticmethod
    def add(e1: SymbolicCPWL, e2: SymbolicCPWL) -> SymbolicCPWL:
        return SymbolicCPWL("add", (e1, e2))

    @staticmethod
    def sub(e1: SymbolicCPWL, e2: SymbolicCPWL) -> SymbolicCPWL:
        return SymbolicCPWL("add", (e1, SymbolicCPWL.scale(-1, 1, e2)))

    @staticmethod
    def scale(num: int, den: int, expr: SymbolicCPWL) -> SymbolicCPWL:
        qn = rat_norm(num, den)
        return SymbolicCPWL("scale", (qn[0], qn[1], expr))

    def eval_rat(self, x: Sequence[RatPair]) -> RatPair:
        """Exact `(num, den)` rational point evaluation."""
        if self.kind == "affine":
            bias, coeffs, denom = self.args
            acc = rat_norm(bias, denom)
            for ci, xi in zip(coeffs, x):
                if ci != 0:
                    acc = rat_add(acc, rat_mul(rat_norm(ci, denom), xi))
            return acc
        if self.kind == "relu":
            return rat_relu(self.args[0].eval_rat(x))
        if self.kind == "add":
            return rat_add(self.args[0].eval_rat(x), self.args[1].eval_rat(x))
        if self.kind == "scale":
            num, den, sub = self.args
            return rat_mul((num, den), sub.eval_rat(x))
        raise ValueError(f"Unknown SymbolicCPWL kind: {self.kind}")


# Affine form normalized tuple: (bias_num, c_0_num, ..., c_{n-1}_num, common_den)
AffineForm = tuple[int, tuple[int, ...], int]


def _norm_affine(bias: int, coeffs: Sequence[int], den: int) -> AffineForm:
    if den < 0:
        bias = -bias
        coeffs = [-c for c in coeffs]
        den = -den
    g = den
    g = math.gcd(g, abs(bias))
    for c in coeffs:
        g = math.gcd(g, abs(c))
    if g > 1:
        bias //= g
        coeffs = [c // g for c in coeffs]
        den //= g
    return (bias, tuple(coeffs), den)


def _add_affine(f1: AffineForm, f2: AffineForm) -> AffineForm:
    b1, c1, d1 = f1
    b2, c2, d2 = f2
    b = b1 * d2 + b2 * d1
    c = [x * d2 + y * d1 for x, y in zip(c1, c2)]
    return _norm_affine(b, c, d1 * d2)


def _scale_affine(num: int, den: int, f: AffineForm) -> AffineForm:
    bf, cf, df = f
    return _norm_affine(bf * num, [num * x for x in cf], df * den)


ConeState = tuple[list[IntVector], list[int], int]  # (extreme_rays, ray_facet_bitmasks, num_facets)


def _pointed_cone_split(
    state: ConeState,
    normal: Sequence[int],
) -> tuple[str, ConeState | None, ConeState | None]:
    """Exact Motzkin-Burger / Fukuda bitmask double-description split of a pointed cone by `<normal, x> == 0`.

    Maintains ONLY true extreme rays using the combinatorial adjacency test on facet-incidence bitmasks:
    two rays `(r_p, mask_p)` (`<normal, r_p> > 0`) and `(r_n, mask_n)` (`<normal, r_n> < 0`) generate an
    extreme ray on the slicing hyperplane `<normal, x> == 0` iff no other ray `r_k` contains `mask_p & mask_n`!
    """
    rays, masks, n_facets = state
    pos_idx: list[tuple[int, int]] = []
    neg_idx: list[tuple[int, int]] = []
    zero_idx: list[int] = []

    for idx, r in enumerate(rays):
        val = sum(ni * ri for ni, ri in zip(normal, r))
        if val > 0:
            pos_idx.append((idx, val))
        elif val < 0:
            neg_idx.append((idx, val))
        else:
            zero_idx.append(idx)

    if not neg_idx:
        return ("nonneg", state, None)
    if not pos_idx:
        return ("nonpos", None, state)

    new_facet_bit = 1 << n_facets
    next_n_facets = n_facets + 1

    mid_rays: list[IntVector] = []
    mid_masks: list[int] = []
    num_all = len(rays)

    for i_p, v_p in pos_idx:
        m_p = masks[i_p]
        r_p = rays[i_p]
        for i_n, v_n in neg_idx:
            m_n = masks[i_n]
            shared = m_p & m_n
            # Combinatorial adjacency check in pointed cone: no third ray contains `shared`
            adjacent = True
            for k in range(num_all):
                if k != i_p and k != i_n and (shared & ~masks[k]) == 0:
                    adjacent = False
                    break
            if not adjacent:
                continue
            r_n = rays[i_n]
            comb = [v_p * rni - v_n * rpi for rpi, rni in zip(r_p, r_n)]
            g = 0
            for c in comb:
                g = math.gcd(g, abs(c))
            if g > 1:
                comb = [c // g for c in comb]
            mid_rays.append(comb)
            mid_masks.append(shared | new_facet_bit)

    z_rays = [rays[i] for i in zero_idx]
    z_masks = [masks[i] | new_facet_bit for i in zero_idx]

    pos_state: ConeState = (
        z_rays + [rays[i] for i, _ in pos_idx] + mid_rays,
        z_masks + [masks[i] for i, _ in pos_idx] + mid_masks,
        next_n_facets,
    )
    neg_state: ConeState = (
        z_rays + [rays[i] for i, _ in neg_idx] + mid_rays,
        z_masks + [masks[i] for i, _ in neg_idx] + mid_masks,
        next_n_facets,
    )
    return ("split", pos_state, neg_state)


def verify_homogeneous_cpwl_identity_all_chambers(
    lhs: SymbolicCPWL,
    rhs: SymbolicCPWL,
    n_dim: int,
) -> dict[str, Any]:
    """Prove `lhs(x) == rhs(x)` for ALL `x in R^n` via exact signed-braid + off-braid cone splitting.

    Covers `R^n` by `n! * (n + 1)` pointed simplicial signed-braid cones:
      `x_{p_0} <= ... <= x_{p_{m-1}} <= 0 <= x_{p_m} <= ... <= x_{p_{n-1}}` (`m = 0..n`).
    Each signed-braid cone has `n` linearly independent `{0, +-1}^n` extreme rays and `n` facets.
    Whenever an off-braid hyperplane strictly cuts a cone, `_pointed_cone_split` refines it via
    exact bitmask double description and verifies exact symbolic linear coefficient equality on every leaf!
    """
    combined_diff = SymbolicCPWL.sub(lhs, rhs)
    total_braid_chambers = 0
    total_signed_cones = 0
    total_leaf_subchambers = 0
    off_braid_splits = 0

    def reduce_and_check(expr: SymbolicCPWL, state: ConeState) -> list[tuple[AffineForm, ConeState]]:
        nonlocal off_braid_splits
        if expr.kind == "affine":
            b, c, d = expr.args
            if b != 0:
                raise ValueError("verify_homogeneous_cpwl_identity_all_chambers requires zero-bias homogeneous tree")
            return [(_norm_affine(0, c, d), state)]
        if expr.kind == "scale":
            num, den, sub = expr.args
            sub_leaves = reduce_and_check(sub, state)
            return [(_scale_affine(num, den, form), st_sub) for form, st_sub in sub_leaves]
        if expr.kind == "add":
            left_leaves = reduce_and_check(expr.args[0], state)
            out: list[tuple[AffineForm, ConeState]] = []
            for f_left, st_left in left_leaves:
                right_leaves = reduce_and_check(expr.args[1], st_left)
                for f_right, st_both in right_leaves:
                    out.append((_add_affine(f_left, f_right), st_both))
            return out
        if expr.kind == "relu":
            inner_leaves = reduce_and_check(expr.args[0], state)
            out_relu: list[tuple[AffineForm, ConeState]] = []
            zero_form = _norm_affine(0, [0] * n_dim, 1)
            for form, st_cur in inner_leaves:
                _, coeffs, _ = form
                status, st_pos, st_neg = _pointed_cone_split(st_cur, coeffs)
                if status == "nonneg":
                    assert st_pos is not None
                    out_relu.append((form, st_pos))
                elif status == "nonpos":
                    assert st_neg is not None
                    out_relu.append((zero_form, st_neg))
                else:
                    assert st_pos is not None and st_neg is not None
                    off_braid_splits += 1
                    out_relu.append((form, st_pos))
                    out_relu.append((zero_form, st_neg))
            return out_relu
        raise ValueError(f"Unsupported kind {expr.kind}")

    # In any simplicial n-cone, ray i lies on all (n - 1) facets EXCEPT facet i:
    all_facets_mask = (1 << n_dim) - 1
    simplicial_masks = [all_facets_mask ^ (1 << i) for i in range(n_dim)]

    for perm in itertools.permutations(range(n_dim)):
        total_braid_chambers += 1
        for m_zero in range(n_dim + 1):
            total_signed_cones += 1
            cone_rays: list[IntVector] = []
            # Negative prefix rays: -1_{p_0..p_{k-1}} for k = 1..m_zero
            for k in range(1, m_zero + 1):
                r_neg = [0] * n_dim
                for idx in perm[:k]:
                    r_neg[idx] = -1
                cone_rays.append(r_neg)
            # Positive suffix rays: +1_{p_k..p_{n-1}} for k = m_zero..n_dim-1
            for k in range(m_zero, n_dim):
                r_pos = [0] * n_dim
                for idx in perm[k:]:
                    r_pos[idx] = 1
                cone_rays.append(r_pos)

            init_state: ConeState = (cone_rays, list(simplicial_masks), n_dim)
            leaves = reduce_and_check(combined_diff, init_state)
            for form, (leaf_rays, _, _) in leaves:
                total_leaf_subchambers += 1
                bias, coeffs, _ = form
                if bias != 0 or any(c != 0 for c in coeffs):
                    witness_int = [sum(r[j] for r in leaf_rays) for j in range(n_dim)]
                    raise AssertionError(
                        f"CPWL identity violated on sub-chamber of perm={perm}: residual_form={form}, witness={witness_int}"
                    )

    return {
        "verified": True,
        "n_dim": n_dim,
        "braid_chambers": total_braid_chambers,
        "signed_braid_cones": total_signed_cones,
        "leaf_subchambers_checked": total_leaf_subchambers,
        "off_braid_splits_resolved": off_braid_splits,
    }


def verify_translation_equivariant_cpwl_all_chambers(
    lhs: SymbolicCPWL,
    rhs: SymbolicCPWL,
    n_dim: int,
) -> dict[str, Any]:
    """Fast universal R^n prover for translation-equivariant homogeneous CPWL identities (`F(x + t*1) == F(x) + k*t`).

    Explicitly certifies:
      1. `LHS(1,...,1) == RHS(1,...,1)` and `LHS(-1,...,-1) == RHS(-1,...,-1)`.
      2. Every internal `ReLU(L(x))` inside `LHS - RHS` satisfies `<coeff(L), (1,...,1)> == 0`
         (so shifting `x -> x - x_{p_0} * 1` leaves every ReLU activation invariant!).
      3. On the exact quotient slice `0 == x_{p_0} <= x_{p_1} <= ... <= x_{p_{n-1}}` (one pointed `(n-1)`-ray
         simplicial cone per permutation `p in S_n`), dynamic Motzkin-Burger off-braid splitting certifies
         `LHS(x) - RHS(x) == 0` on EVERY full-dimensional sub-chamber!
    """
    ones_q = [(1, 1)] * n_dim
    neg_ones_q = [(-1, 1)] * n_dim
    if lhs.eval_rat(ones_q) != rhs.eval_rat(ones_q):
        raise AssertionError("Translation-equivariant check failed at +(1,...,1)")
    if lhs.eval_rat(neg_ones_q) != rhs.eval_rat(neg_ones_q):
        raise AssertionError("Translation-equivariant check failed at -(1,...,1)")

    combined_diff = SymbolicCPWL.sub(lhs, rhs)
    zero_form = _norm_affine(0, [0] * n_dim, 1)
    n_rays = n_dim - 1
    all_facets_mask = (1 << n_rays) - 1
    simplicial_masks = [all_facets_mask ^ (1 << i) for i in range(n_rays)]

    total_braid_chambers = 0
    total_leaf_subchambers = 0
    off_braid_splits = 0

    def reduce_quotient(expr: SymbolicCPWL, state: ConeState) -> list[tuple[AffineForm, ConeState]]:
        nonlocal off_braid_splits
        if expr.kind == "affine":
            b, c, d = expr.args
            if b != 0:
                raise ValueError("Homogeneous expression expected (bias == 0)")
            return [(_norm_affine(0, c, d), state)]
        if expr.kind == "scale":
            num, den, sub = expr.args
            return [(_scale_affine(num, den, f), st) for f, st in reduce_quotient(sub, state)]
        if expr.kind == "add":
            out_a: list[tuple[AffineForm, ConeState]] = []
            for fl, stl in reduce_quotient(expr.args[0], state):
                for fr, str_ in reduce_quotient(expr.args[1], stl):
                    out_a.append((_add_affine(fl, fr), str_))
            return out_a
        if expr.kind == "relu":
            out_r: list[tuple[AffineForm, ConeState]] = []
            for form, st_cur in reduce_quotient(expr.args[0], state):
                _, coeffs, _ = form
                if sum(coeffs) != 0:
                    raise AssertionError(
                        f"ReLU argument violates translation invariance (<coeffs, 1> = {sum(coeffs)} != 0)"
                    )
                status, st_p, st_n = _pointed_cone_split(st_cur, coeffs)
                if status == "nonneg":
                    assert st_p is not None
                    out_r.append((form, st_p))
                elif status == "nonpos":
                    assert st_n is not None
                    out_r.append((zero_form, st_n))
                else:
                    assert st_p is not None and st_n is not None
                    off_braid_splits += 1
                    out_r.append((form, st_pos := st_p))
                    out_r.append((zero_form, st_neg := st_n))
            return out_r
        raise ValueError(f"Unsupported kind {expr.kind}")

    for perm in itertools.permutations(range(n_dim)):
        total_braid_chambers += 1
        cone_rays: list[IntVector] = []
        for k in range(1, n_dim):
            r_pos = [0] * n_dim
            for idx in perm[k:]:
                r_pos[idx] = 1
            cone_rays.append(r_pos)
        init_state: ConeState = (cone_rays, list(simplicial_masks), n_rays)
        for form, (leaf_rays, _, _) in reduce_quotient(combined_diff, init_state):
            total_leaf_subchambers += 1
            bias, coeffs, _ = form
            # On the slice x_{perm[0]} == 0, an affine linear form sum_j c_j x_j vanishes on a full-dim
            # (n-1)-cone AND at (1,...,1) iff ALL c_j == 0! Verify sum(coeffs) == 0 AND c_j == 0 for j != perm[0]:
            p0 = perm[0]
            sum_c = sum(coeffs)
            if bias != 0 or sum_c != 0 or any(coeffs[j] != 0 for j in range(n_dim) if j != p0):
                witness_int = [sum(r[j] for r in leaf_rays) for j in range(n_dim)]
                raise AssertionError(
                    f"Translation-equivariant CPWL identity failed on perm={perm}: residual={form}, witness={witness_int}"
                )

    return {
        "verified": True,
        "n_dim": n_dim,
        "braid_chambers": total_braid_chambers,
        "leaf_subchambers_checked": total_leaf_subchambers,
        "off_braid_splits_resolved": off_braid_splits,
    }


def verify_feedforward_relu_network_homogeneous(
    w1: Sequence[Sequence[int]],
    w2: Sequence[Sequence[int]],
    w_out: Sequence[int],
    out_denom: int,
    target_expr: SymbolicCPWL,
) -> dict[str, Any]:
    """Evaluate a strict zero-skip 2-hidden-layer ReLU network layer-by-layer (DAG-aware, no tree blowup)
    across all pointed signed-braid cones and dynamic off-braid sub-cones, proving universal identity on R^n!
    """
    w1_mat = assert_int_matrix(w1, context="W1")
    w2_mat = assert_int_matrix(w2, context="W2")
    w_out_vec = assert_int_vector(w_out, context="w_out")
    assert_strict_int(out_denom, "out_denom")
    if out_denom <= 0:
        raise ValueError("out_denom must be > 0")

    m1 = len(w1_mat)
    n_dim = len(w1_mat[0])
    m2 = len(w2_mat)
    if len(w2_mat[0]) != m1 or len(w_out_vec) != m2:
        raise ValueError("Feedforward 2-layer network shape mismatch")

    zero_form = _norm_affine(0, [0] * n_dim, 1)
    all_facets_mask = (1 << n_dim) - 1
    simplicial_masks = [all_facets_mask ^ (1 << i) for i in range(n_dim)]

    total_braid_chambers = 0
    total_signed_cones = 0
    total_leaf_subchambers = 0
    off_braid_splits = 0

    def eval_target_on_cone(expr: SymbolicCPWL, state: ConeState) -> list[tuple[AffineForm, ConeState]]:
        nonlocal off_braid_splits
        if expr.kind == "affine":
            b, c, d = expr.args
            return [(_norm_affine(b, c, d), state)]
        if expr.kind == "scale":
            num, den, sub = expr.args
            return [(_scale_affine(num, den, f), st) for f, st in eval_target_on_cone(sub, state)]
        if expr.kind == "add":
            out_a: list[tuple[AffineForm, ConeState]] = []
            for fl, stl in eval_target_on_cone(expr.args[0], state):
                for fr, str_ in eval_target_on_cone(expr.args[1], stl):
                    out_a.append((_add_affine(fl, fr), str_))
            return out_a
        if expr.kind == "relu":
            out_r: list[tuple[AffineForm, ConeState]] = []
            for f_in, st_in in eval_target_on_cone(expr.args[0], state):
                status, st_p, st_n = _pointed_cone_split(st_in, f_in[1])
                if status == "nonneg":
                    assert st_p is not None
                    out_r.append((f_in, st_p))
                elif status == "nonpos":
                    assert st_n is not None
                    out_r.append((zero_form, st_n))
                else:
                    assert st_p is not None and st_n is not None
                    off_braid_splits += 1
                    out_r.append((f_in, st_p))
                    out_r.append((zero_form, st_n))
            return out_r
        raise ValueError(f"Unsupported kind {expr.kind}")

    for perm in itertools.permutations(range(n_dim)):
        total_braid_chambers += 1
        for m_zero in range(n_dim + 1):
            total_signed_cones += 1
            cone_rays: list[IntVector] = []
            for k in range(1, m_zero + 1):
                r_neg = [0] * n_dim
                for idx in perm[:k]:
                    r_neg[idx] = -1
                cone_rays.append(r_neg)
            for k in range(m_zero, n_dim):
                r_pos = [0] * n_dim
                for idx in perm[k:]:
                    r_pos[idx] = 1
                cone_rays.append(r_pos)

            # Layer 1 DAG pass: refine cone across all m1 Layer-1 neurons once
            l1_states: list[tuple[list[AffineForm], ConeState]] = [([], (cone_rays, list(simplicial_masks), n_dim))]
            for i in range(m1):
                w1_i = w1_mat[i]
                f_i = _norm_affine(0, w1_i, 1)
                next_l1: list[tuple[list[AffineForm], ConeState]] = []
                for h1_forms, st_cur in l1_states:
                    status, st_p, st_n = _pointed_cone_split(st_cur, w1_i)
                    if status == "nonneg":
                        assert st_p is not None
                        next_l1.append((h1_forms + [f_i], st_p))
                    elif status == "nonpos":
                        assert st_n is not None
                        next_l1.append((h1_forms + [zero_form], st_n))
                    else:
                        assert st_p is not None and st_n is not None
                        off_braid_splits += 1
                        next_l1.append((h1_forms + [f_i], st_p))
                        next_l1.append((h1_forms + [zero_form], st_n))
                l1_states = next_l1

            # Layer 2 DAG pass: accumulate linear combination of active h1_forms, split if needed, add to net output
            out_states: list[tuple[AffineForm, ConeState]] = []
            for h1_forms, st_l1 in l1_states:
                cur_net_states: list[tuple[AffineForm, ConeState]] = [(zero_form, st_l1)]
                for j in range(m2):
                    cj = w_out_vec[j]
                    if cj == 0:
                        continue
                    # Pre-activation g_j(x) is purely linear on st_l1!
                    pre_coeffs = [0] * n_dim
                    w2_j = w2_mat[j]
                    for i in range(m1):
                        wij = w2_j[i]
                        if wij != 0:
                            _, ci_tup, di = h1_forms[i]
                            assert di == 1
                            for coord_idx in range(n_dim):
                                pre_coeffs[coord_idx] += wij * ci_tup[coord_idx]
                    f_pre = _norm_affine(0, pre_coeffs, 1)
                    scaled_active = _scale_affine(cj, out_denom, f_pre)

                    next_net_states: list[tuple[AffineForm, ConeState]] = []
                    for acc_form, st_c in cur_net_states:
                        status, st_p, st_n = _pointed_cone_split(st_c, pre_coeffs)
                        if status == "nonneg":
                            assert st_p is not None
                            next_net_states.append((_add_affine(acc_form, scaled_active), st_p))
                        elif status == "nonpos":
                            assert st_n is not None
                            next_net_states.append((acc_form, st_n))
                        else:
                            assert st_p is not None and st_n is not None
                            off_braid_splits += 1
                            next_net_states.append((_add_affine(acc_form, scaled_active), st_p))
                            next_net_states.append((acc_form, st_n))
                    cur_net_states = next_net_states
                out_states.extend(cur_net_states)

            # Compare against target_expr on every leaf sub-cone!
            for net_form, st_leaf in out_states:
                for tgt_form, st_final in eval_target_on_cone(target_expr, st_leaf):
                    total_leaf_subchambers += 1
                    diff_form = _add_affine(net_form, _scale_affine(-1, 1, tgt_form))
                    bias, coeffs, _ = diff_form
                    if bias != 0 or any(c != 0 for c in coeffs):
                        leaf_rays = st_final[0]
                        witness_int = [sum(r[j] for r in leaf_rays) for j in range(n_dim)]
                        raise AssertionError(
                            f"CPWL identity violated on sub-chamber of perm={perm}: residual_form={diff_form}, witness={witness_int}"
                        )

    return {
        "verified": True,
        "n_dim": n_dim,
        "braid_chambers": total_braid_chambers,
        "signed_braid_cones": total_signed_cones,
        "leaf_subchambers_checked": total_leaf_subchambers,
        "off_braid_splits_resolved": off_braid_splits,
        "layer1_width": m1,
        "layer2_width": m2,
        "total_hidden_neurons": m1 + m2,
    }


# ---------------------------------------------------------------------------
# 6. Universal Cycle 3 Theorem-Ledger Certificate Dispatcher (`SPEC.md` §0.4)
# ---------------------------------------------------------------------------


def _as_rat_pair(val: Any, ctx: str = "rat") -> RatPair:
    if type(val) is int:
        return (val, 1)
    if type(val) in (list, tuple) and len(val) == 2:
        return rat_norm(assert_strict_int(val[0], f"{ctx}[0]"), assert_strict_int(val[1], f"{ctx}[1]"))
    if type(val) is str:
        s = val.strip()
        if s.find("/") >= 0:
            parts = s.split("/")
            if len(parts) != 2:
                raise ValueError(f"{ctx}: malformed rational string {val!r}")
            return rat_norm(int(parts[0]), int(parts[1]))
        return (int(s), 1)
    raise TypeError(f"{ctx}: unsupported rational representation {type(val).__name__}")


def verify_eisenstein_certificate(
    coeffs_low_to_high: Sequence[int],
    prime_p: int,
) -> dict[str, Any]:
    """Verify Eisenstein's irreducibility criterion over Q at `prime_p` on integer polynomial `sum_{k=0}^d c_k x^k`."""
    c = assert_int_vector(coeffs_low_to_high, "poly_coeffs")
    p = assert_strict_int(prime_p, "prime_p")
    if len(c) < 2:
        raise ValueError("Polynomial degree must be >= 1")
    if not is_prime_int(p):
        raise AssertionError(f"Eisenstein prime p={p} is not prime")
    if c[-1] % p == 0:
        raise AssertionError(f"Eisenstein failed: leading coeff {c[-1]} divisible by p={p}")
    for k in range(len(c) - 1):
        if c[k] % p != 0:
            raise AssertionError(f"Eisenstein failed: coeff c[{k}]={c[k]} not divisible by p={p}")
    if c[0] % (p * p) == 0:
        raise AssertionError(f"Eisenstein failed: constant term c[0]={c[0]} divisible by p^2={p * p}")
    return {"verified": True, "degree": len(c) - 1, "prime": p}


def verify_simplex_triangulation_volume_certificate(
    simplices: Sequence[Sequence[Sequence[int]]],
    expected_volume: int,
    modulus: int | None = None,
    expected_mod_residue: int | None = None,
) -> dict[str, Any]:
    """Verify normalized lattice volume `sum_k |det(S_k)| == expected_volume` across `d`-simplices."""
    assert_strict_int(expected_volume, "expected_volume")
    if len(simplices) == 0:
        raise AssertionError("Empty simplex triangulation")
    total_vol = 0
    for idx, simp in enumerate(simplices):
        rows = assert_int_matrix(simp, context=f"simplex[{idx}]")
        m_r = len(rows)
        n_c = len(rows[0])
        if m_r == n_c:
            edge_mat = rows
        elif m_r == n_c + 1:
            v0 = rows[0]
            edge_mat = [[rows[r][c] - v0[c] for c in range(n_c)] for r in range(1, m_r)]
        else:
            raise ValueError(f"Simplex {idx} invalid shape ({m_r}, {n_c})")
        dv = abs(exact_det_bareiss(edge_mat))
        if dv <= 0:
            raise AssertionError(f"Degenerate zero-volume simplex at index {idx}")
        total_vol += dv
    if total_vol != expected_volume:
        raise AssertionError(f"Triangulation volume {total_vol} != expected {expected_volume}")
    if modulus is not None and expected_mod_residue is not None:
        assert_strict_int(modulus, "modulus")
        assert_strict_int(expected_mod_residue, "expected_mod_residue")
        if (total_vol % modulus) != (expected_mod_residue % modulus):
            raise AssertionError("Modular volume residue mismatch")
    return {"verified": True, "simplex_count": len(simplices), "normalized_volume": total_vol}


def verify_cg_cuts_certificate(cert: dict[str, Any]) -> dict[str, Any]:
    """Verify elementary Chvatal-Gomory cuts on either `A_ge x >= b_ge` (ceil) or `A_ub x <= b_ub` (floor)."""
    cuts = cert.get("cuts")
    if type(cuts) is not list or len(cuts) == 0:
        raise AssertionError("CG certificate requires non-empty `cuts` list")
    is_ge = "A_ge" in cert and "b_ge" in cert
    is_ub = "A_ub" in cert and "b_ub" in cert
    if not is_ge and not is_ub:
        raise AssertionError("CG certificate requires (A_ge, b_ge) or (A_ub, b_ub)")
    a_mat = assert_int_matrix(cert["A_ge"] if is_ge else cert["A_ub"], context="CG_A")
    b_vec = assert_int_vector(cert["b_ge"] if is_ge else cert["b_ub"], context="CG_b")

    for idx, c_item in enumerate(cuts):
        lam_num = assert_int_vector(c_item["lam_num"], f"cuts[{idx}].lam_num")
        lam_den = assert_strict_int(c_item["lam_den"], f"cuts[{idx}].lam_den")
        exp_lhs = assert_int_vector(c_item["cut_lhs"], f"cuts[{idx}].cut_lhs")
        exp_rhs = assert_strict_int(c_item["cut_rhs"], f"cuts[{idx}].cut_rhs")
        if lam_den <= 0 or any(v < 0 for v in lam_num):
            raise AssertionError(f"Invalid CG multiplier at cut {idx}")
        comb_lhs = vec_mat_mul(lam_num, a_mat)
        comb_rhs = vec_dot(lam_num, b_vec)
        for j, val in enumerate(comb_lhs):
            if val % lam_den != 0 or (val // lam_den) != exp_lhs[j]:
                raise AssertionError(f"CG cut {idx} LHS mismatch at coord {j}")
        rounded = -((-comb_rhs) // lam_den) if is_ge else (comb_rhs // lam_den)
        if rounded != exp_rhs:
            raise AssertionError(f"CG cut {idx} rounded RHS {rounded} != {exp_rhs}")

    if "hull_vertices" in cert:
        verts = assert_int_matrix(cert["hull_vertices"], context="hull_vertices")
        for v_pt in verts:
            for row, rhs in zip(a_mat, b_vec):
                lhs_v = vec_dot(row, v_pt)
                if (is_ge and lhs_v < rhs) or (is_ub and lhs_v > rhs):
                    raise AssertionError(f"Hull vertex {v_pt} violates base inequality")
            for c_item in cuts:
                exp_lhs = assert_int_vector(c_item["cut_lhs"], "cut_lhs")
                exp_rhs = assert_strict_int(c_item["cut_rhs"], "cut_rhs")
                lhs_c = vec_dot(exp_lhs, v_pt)
                if (is_ge and lhs_c < exp_rhs) or (is_ub and lhs_c > exp_rhs):
                    raise AssertionError(f"Hull vertex {v_pt} violates CG cut")

    return {"verified": True, "cuts_verified": len(cuts)}


def verify_poincare_trajectory_certificate(cert: dict[str, Any]) -> dict[str, Any]:
    """Verify exact 0/1-error rational piecewise-linear trajectory segments & cell/Filippov decrease."""
    segments = cert.get("segments")
    if type(segments) is not list or len(segments) == 0:
        raise AssertionError("Poincare trajectory certificate requires non-empty `segments`")

    for idx, seg in enumerate(segments):
        p0 = [_as_rat_pair(v, f"seg[{idx}].p_start") for v in seg["p_start"]]
        vel = [_as_rat_pair(v, f"seg[{idx}].velocity") for v in seg["velocity"]]
        dt = _as_rat_pair(seg["dt"], f"seg[{idx}].dt")
        p1 = [_as_rat_pair(v, f"seg[{idx}].p_end") for v in seg["p_end"]]
        if dt[0] <= 0:
            raise AssertionError(f"Segment {idx} non-positive transit time dt={dt}")
        for d_i in range(len(p0)):
            reached = rat_add(p0[d_i], rat_mul(dt, vel[d_i]))
            if reached != p1[d_i]:
                raise AssertionError(f"Segment {idx} ODE integration mismatch at coord {d_i}: {reached} != {p1[d_i]}")

    # Check expansion (for FALSIFIED_COUNTEREXAMPLE E0) or contraction (for CERTIFIED_EXACT E1):
    start_0 = [_as_rat_pair(v, "start0") for v in segments[0]["p_start"]]
    end_f = [_as_rat_pair(v, "endf") for v in segments[-1]["p_end"]]
    r_start = start_0[0] if start_0[0][0] >= 0 else (-start_0[0][0], start_0[0][1])
    for qv in start_0[1:]:
        aq = qv if qv[0] >= 0 else (-qv[0], qv[1])
        r_start = rat_max(r_start, aq)
    r_end = end_f[0] if end_f[0][0] >= 0 else (-end_f[0][0], end_f[0][1])
    for qv in end_f[1:]:
        aq = qv if qv[0] >= 0 else (-qv[0], qv[1])
        r_end = rat_max(r_end, aq)

    mode = str(cert.get("mode", "outward_counterexample"))
    if mode == "outward_counterexample":
        if not rat_lt(r_start, r_end):
            raise AssertionError(f"Outward counterexample failed r_end={r_end} > r_start={r_start}")
    elif mode == "contraction":
        r_star = _as_rat_pair(cert["r_star"], "r_star")
        d0 = rat_sub(r_start, r_star)
        d1 = rat_sub(r_end, r_star)
        abs0 = (abs(d0[0]), d0[1])
        abs1 = (abs(d1[0]), d1[1])
        if not rat_lt(abs1, abs0):
            raise AssertionError(f"Poincare contraction failed |r_end - r*| < |r_start - r*|")

    if "cell_and_crease_dots" in cert:
        dots = assert_int_vector(cert["cell_and_crease_dots"], "cell_and_crease_dots")
        if len(dots) == 0 or any(d >= 0 for d in dots):
            raise AssertionError("Torsor decrease failed on cell_and_crease_dots")

    return {"verified": True, "segments_verified": len(segments), "r_start": rat_str(r_start), "r_end": rat_str(r_end)}


def verify_group_circuit_certificate(cert: dict[str, Any]) -> dict[str, Any]:
    """Verify exact 1-layer Z or Q group circuit (`indicator` or `strict_argmax`) + optional `W < |G|^2` guard."""
    cayley = assert_int_matrix(cert["cayley"], context="cayley")
    verify_group_axioms(cayley)
    n = len(cayley)

    if "expected_group_name" in cert and cert["expected_group_name"] is not None:
        g_name = str(cert["expected_group_name"])
        canon = build_canonical_group_cayley(g_name)
        iso = find_group_isomorphism(cayley, canon)
        if iso is None:
            raise AssertionError(f"Group circuit Cayley table is NOT isomorphic to canonical {g_name}")

    if "cocycle_certificate" in cert and cert["cocycle_certificate"] is not None:
        coc_res = verify_central_extension_cocycle_certificate(cert["cocycle_certificate"])
        ext_tbl = coc_res["extension_cayley"]
        if find_group_isomorphism(cayley, ext_tbl) is None:
            raise AssertionError("Group circuit Cayley table is NOT isomorphic to certified cocycle extension")

    raw_w1 = cert["W1"] if "W1" in cert else cert["W_in"]
    raw_w2 = cert["W2"] if "W2" in cert else cert["W_out"]
    w1 = assert_int_matrix(raw_w1, expected_cols=2 * n, context="W_in")
    w = len(w1)
    raw_b1 = cert.get("b1", cert.get("b_in", [0] * w))
    b1 = assert_int_vector(raw_b1, "b_in")
    w2 = assert_int_matrix(raw_w2, expected_rows=n, expected_cols=w, context="W_out")
    raw_b2 = cert.get("b2", cert.get("b_out", [0] * n))
    b2 = assert_int_vector(raw_b2, "b_out")
    if len(b1) != w or len(b2) != n:
        raise ValueError("Group circuit bias length mismatch")

    if cert.get("zero_bias", False):
        if any(v != 0 for v in b1) or any(v != 0 for v in b2):
            raise AssertionError("Group circuit claimed zero_bias=True but has non-zero bias entry")
    if cert.get("zero_readout_bias", False):
        if any(v != 0 for v in b2):
            raise AssertionError("Group circuit claimed zero_readout_bias=True but has non-zero b_out entry")

    if cert.get("compressed", False) and w >= n * n:
        raise ValueError(f"Compressed group circuit violated Trap 5 guard: W={w} >= |G|^2={n * n}")

    w1_den = assert_strict_int(cert.get("w1_den", cert.get("w_in_den", 1)), "w1_den")
    b1_den = assert_strict_int(cert.get("b1_den", cert.get("b_in_den", w1_den)), "b1_den")
    w2_den = assert_strict_int(cert.get("w2_den", cert.get("w_out_den", cert.get("out_denom", 1))), "w2_den")
    b2_den = assert_strict_int(cert.get("b2_den", cert.get("b_out_den", w2_den)), "b2_den")
    if w1_den <= 0 or b1_den <= 0 or w2_den <= 0 or b2_den <= 0:
        raise ValueError("Group circuit denominators must be strictly positive integers")

    mode = str(cert.get("mode", "indicator"))
    pure_z_fast = w1_den == 1 and b1_den == 1 and w2_den == 1 and b2_den == 1

    if pure_z_fast:
        for g in range(n):
            for h in range(n):
                hidden: IntVector = []
                for row_i, bi in zip(w1, b1):
                    v = row_i[g] + row_i[n + h] + bi
                    hidden.append(v if v > 0 else 0)
                out = [vec_dot(w2[c], hidden) + b2[c] for c in range(n)]
                tgt_c = cayley[g][h]
                if mode == "indicator":
                    expected = [1 if c == tgt_c else 0 for c in range(n)]
                    if out != expected:
                        raise AssertionError(f"Indicator circuit failed at ({g},{h}): got {out} != {expected}")
                elif mode == "strict_argmax":
                    best_other = max(out[c] for c in range(n) if c != tgt_c)
                    if out[tgt_c] <= best_other:
                        raise AssertionError(f"Strict argmax failed at ({g},{h}): {out[tgt_c]} <= {best_other}")
                else:
                    raise ValueError(f"Unknown group circuit mode {mode!r}")
    else:
        for g in range(n):
            for h in range(n):
                hidden_q: list[RatPair] = []
                for row_i, bi in zip(w1, b1):
                    lin_q = rat_add(rat_norm(row_i[g] + row_i[n + h], w1_den), rat_norm(bi, b1_den))
                    hidden_q.append(rat_relu(lin_q))
                out_q: list[RatPair] = []
                for c in range(n):
                    acc_q = rat_norm(b2[c], b2_den)
                    w2_c = w2[c]
                    for j_idx in range(w):
                        if w2_c[j_idx] != 0 and hidden_q[j_idx][0] != 0:
                            acc_q = rat_add(acc_q, rat_mul(rat_norm(w2_c[j_idx], w2_den), hidden_q[j_idx]))
                    out_q.append(acc_q)
                tgt_c = cayley[g][h]
                if mode == "indicator":
                    for c in range(n):
                        exp_q = (1, 1) if c == tgt_c else (0, 1)
                        if out_q[c] != exp_q:
                            raise AssertionError(f"Rational indicator circuit failed at ({g},{h}), c={c}: {out_q[c]} != {exp_q}")
                elif mode == "strict_argmax":
                    for c in range(n):
                        if c != tgt_c and not rat_lt(out_q[c], out_q[tgt_c]):
                            raise AssertionError(f"Rational strict argmax failed at ({g},{h})")
                else:
                    raise ValueError(f"Unknown group circuit mode {mode!r}")

    return {
        "verified": True,
        "group_order": n,
        "width": w,
        "mode": mode,
        "ring": "Z" if pure_z_fast else "Q",
        "pairs_checked": n * n,
    }


def verify_linear_realization_certificate(cert: dict[str, Any]) -> dict[str, Any]:
    """Verify exact rational/integer linear realization `A @ x_num == x_den * b` (e.g. `Z[1/6]` or `Z[1/2]` dictionary solve)."""
    a_mat = assert_int_matrix(cert["A"], context="A")
    b_vec = assert_int_vector(cert["b"], context="b")
    x_num = assert_int_vector(cert["c_num"] if "c_num" in cert else cert["x_num"], context="c_num")
    x_den = assert_strict_int(cert.get("c_den", cert.get("x_den", 1)), "c_den")
    if x_den <= 0:
        raise ValueError("Denominator must be > 0")
    lhs = mat_vec_mul(a_mat, x_num)
    rhs = [x_den * bi for bi in b_vec]
    if lhs != rhs:
        raise AssertionError("Linear realization failed: A @ c_num != c_den * b")
    return {"verified": True, "rows": len(a_mat), "cols": len(x_num), "denom": x_den}


# ---------------------------------------------------------------------------
# 7. Wave II Independent Exact Linear Algebra, Polyhedral & Group Kernels
# ---------------------------------------------------------------------------


def exact_q_rank_bareiss(mat: Sequence[Sequence[int]]) -> int:
    """Exact fraction-free Bareiss rank over Q with full submatrix pivot search (zero modular collisions)."""
    a_in = assert_int_matrix(mat, context="rank_mat")
    m = len(a_in)
    if m == 0:
        return 0
    n = len(a_in[0])
    if n == 0:
        return 0
    a = [list(r) for r in a_in]
    r_idx = 0
    prev_piv = 1
    while r_idx < m and r_idx < n:
        best_pos: tuple[int, int] | None = None
        for i in range(r_idx, m):
            for j in range(r_idx, n):
                if a[i][j] != 0:
                    best_pos = (i, j)
                    break
            if best_pos is not None:
                break
        if best_pos is None:
            break
        bi, bj = best_pos
        if bi != r_idx:
            a[r_idx], a[bi] = a[bi], a[r_idx]
        if bj != r_idx:
            for row in a:
                row[r_idx], row[bj] = row[bj], row[r_idx]
        piv = a[r_idx][r_idx]
        for i in range(r_idx + 1, m):
            for j in range(r_idx + 1, n):
                num = a[i][j] * piv - a[i][r_idx] * a[r_idx][j]
                if num % prev_piv != 0:
                    raise AssertionError("Bareiss rank exact division invariant violated")
                a[i][j] = num // prev_piv
            a[i][r_idx] = 0
        prev_piv = piv
        r_idx += 1
    return r_idx


def _primitive_canonical_vec(vec: Sequence[int]) -> tuple[int, ...]:
    """Divide non-zero integer vector by its positive GCD and make first non-zero coordinate positive."""
    v = assert_int_vector(vec, "prim_vec")
    g = 0
    for c in v:
        g = math.gcd(g, abs(c))
    if g == 0:
        return tuple(v)
    scaled = [c // g for c in v]
    for c in scaled:
        if c != 0:
            if c < 0:
                scaled = [-x for x in scaled]
            break
    return tuple(scaled)


def compute_convex_hull_normalized_volume(
    points: Sequence[Sequence[int]],
    d_dim: int,
) -> dict[str, Any]:
    """Independently compute exact normalized d-volume `d! * Vol_Eucl(conv(points))` over Z^d via Beneath-Beyond."""
    assert_strict_int(d_dim, "d_dim")
    if d_dim < 1:
        raise ValueError(f"d_dim must be >= 1, got {d_dim}")
    raw_pts = assert_int_matrix(points, expected_cols=d_dim, context="hull_points")
    pts = sorted({tuple(r) for r in raw_pts})
    if len(pts) == 0:
        return {"normalized_volume": 0, "affine_rank": 0, "outward_inequalities": []}

    if d_dim == 1:
        lo = pts[0][0]
        hi = pts[-1][0]
        if hi == lo:
            return {"normalized_volume": 0, "affine_rank": 0, "outward_inequalities": []}
        return {
            "normalized_volume": hi - lo,
            "affine_rank": 1,
            "outward_inequalities": [([1], hi), ([-1], -lo)],
        }

    p0 = pts[0]
    if len(pts) <= d_dim:
        diff_rows = [[pts[k][c] - p0[c] for c in range(d_dim)] for k in range(1, len(pts))]
        return {
            "normalized_volume": 0,
            "affine_rank": exact_q_rank_bareiss(diff_rows),
            "outward_inequalities": [],
        }

    chosen = [0]
    cur_edges: IntMatrix = []
    for idx in range(1, len(pts)):
        cand = [pts[idx][c] - p0[c] for c in range(d_dim)]
        if exact_q_rank_bareiss(cur_edges + [cand]) > len(cur_edges):
            cur_edges.append(cand)
            chosen.append(idx)
            if len(chosen) == d_dim + 1:
                break

    if len(chosen) < d_dim + 1:
        return {
            "normalized_volume": 0,
            "affine_rank": len(cur_edges),
            "outward_inequalities": [],
        }

    vol0 = abs(exact_det_bareiss(cur_edges))
    if vol0 <= 0:
        raise AssertionError("Initial d-simplex unexpectedly had zero determinant")

    s_sum = [sum(pts[idx][c] for idx in chosen) for c in range(d_dim)]

    def _facet_cofactor_outward(f_indices: tuple[int, ...]) -> tuple[IntVector, int]:
        w0 = pts[f_indices[0]]
        m_rows = [[pts[f_indices[r]][c] - w0[c] for c in range(d_dim)] for r in range(1, d_dim)]
        c_vec: IntVector = []
        for col_drop in range(d_dim):
            sub = [[m_rows[r][c] for c in range(d_dim) if c != col_drop] for r in range(d_dim - 1)]
            minor = exact_det_bareiss(sub)
            c_vec.append(-minor if (col_drop % 2 == 1) else minor)
        if all(v == 0 for v in c_vec):
            raise AssertionError("Degenerate (d-1)-simplex encountered on convex hull boundary")
        rhs_w0 = vec_dot(c_vec, w0)
        lhs_int = vec_dot(c_vec, s_sum)
        scale_w0 = (d_dim + 1) * rhs_w0
        if lhs_int == scale_w0:
            raise AssertionError("Interior barycenter lies on hull boundary hyperplane")
        if lhs_int > scale_w0:
            c_vec = [-v for v in c_vec]
            rhs_w0 = -rhs_w0
        return (c_vec, rhs_w0)

    boundary: list[tuple[tuple[int, ...], IntVector, int]] = []
    for drop_k in range(d_dim + 1):
        f_tup = tuple(chosen[j] for j in range(d_dim + 1) if j != drop_k)
        c_f, b_f = _facet_cofactor_outward(f_tup)
        boundary.append((f_tup, c_f, b_f))

    chosen_set = set(chosen)
    total_vol = vol0

    for p_idx, pt in enumerate(pts):
        if p_idx in chosen_set:
            continue
        pt_list = list(pt)
        vis_facets: list[tuple[tuple[int, ...], int]] = []
        keep_facets: list[tuple[tuple[int, ...], IntVector, int]] = []
        for f_tup, c_vec, b_rhs in boundary:
            delta = vec_dot(c_vec, pt_list) - b_rhs
            if delta > 0:
                vis_facets.append((f_tup, delta))
            else:
                keep_facets.append((f_tup, c_vec, b_rhs))
        if not vis_facets:
            continue

        ridge_counts: dict[tuple[int, ...], int] = {}
        for f_tup, delta in vis_facets:
            total_vol += delta
            for r_drop in range(d_dim):
                ridge = tuple(sorted(f_tup[j] for j in range(d_dim) if j != r_drop))
                ridge_counts[ridge] = ridge_counts.get(ridge, 0) + 1

        for ridge, cnt in ridge_counts.items():
            if cnt not in (1, 2):
                raise AssertionError(f"Beneath-Beyond manifold ridge invariant violated: degree={cnt}")
            if cnt == 1:
                new_f = tuple(sorted(ridge + (p_idx,)))
                c_new, b_new = _facet_cofactor_outward(new_f)
                keep_facets.append((new_f, c_new, b_new))
        boundary = keep_facets

    prim_ineqs_set: set[tuple[tuple[int, ...], int]] = set()
    for _, c_vec, b_rhs in boundary:
        g_c = 0
        for val in c_vec:
            g_c = math.gcd(g_c, abs(val))
        assert g_c > 0 and (b_rhs % g_c == 0)
        prim_ineqs_set.add((tuple(val // g_c for val in c_vec), b_rhs // g_c))

    out_ineqs = [(list(c_t), b_v) for c_t, b_v in sorted(prim_ineqs_set)]
    return {
        "normalized_volume": total_vol,
        "affine_rank": d_dim,
        "num_boundary_simplices": len(boundary),
        "outward_inequalities": out_ineqs,
    }


def _expand_zonotope_vertices(
    base: Sequence[int],
    gens: Sequence[Sequence[int]],
    d_dim: int,
    ctx: str,
) -> tuple[list[IntVector], IntMatrix]:
    base_v = assert_int_vector(base, f"{ctx}_base")
    if len(base_v) != d_dim:
        raise ValueError(f"{ctx}_base length {len(base_v)} != d_dim={d_dim}")
    g_mat = assert_int_matrix(gens, expected_cols=d_dim, context=f"{ctx}_gens") if len(gens) > 0 else []
    m_g = len(g_mat)
    if m_g > 14:
        raise ValueError(f"{ctx}_gens count {m_g} exceeds 14-generator guard")
    pts_set: set[tuple[int, ...]] = set()
    for mask in range(1 << m_g):
        cur = list(base_v)
        for i in range(m_g):
            if (mask >> i) & 1:
                gi = g_mat[i]
                for c in range(d_dim):
                    cur[c] += gi[c]
        pts_set.add(tuple(cur))
    return ([list(p) for p in sorted(pts_set)], g_mat)


def _verify_single_zonotope_join(item: dict[str, Any], ctx: str = "join") -> dict[str, Any]:
    d_dim = assert_strict_int(item["d_dim"], f"{ctx}.d_dim")
    r1 = assert_strict_int(item["r1"], f"{ctx}.r1")
    r2 = assert_strict_int(item["r2"], f"{ctx}.r2")
    expected_vol = assert_strict_int(item["expected_volume"], f"{ctx}.expected_volume")
    if r1 < 0 or r2 < 0 or d_dim < 1:
        raise ValueError(f"{ctx}: invalid dimensions d={d_dim}, r1={r1}, r2={r2}")

    has_g1 = "Z1_gens" in item
    has_g2 = "Z2_gens" in item
    b1 = assert_int_vector(item.get("Z1_base", [0] * d_dim), f"{ctx}.Z1_base")
    b2 = assert_int_vector(item.get("Z2_base", [0] * d_dim), f"{ctx}.Z2_base")

    if has_g1:
        pts1, g1_mat = _expand_zonotope_vertices(b1, item["Z1_gens"], d_dim, f"{ctx}.Z1")
        if "Z1_vertices" in item:
            v1_claim = sorted({tuple(r) for r in assert_int_matrix(item["Z1_vertices"], expected_cols=d_dim, context=f"{ctx}.Z1_vertices")})
            if v1_claim != [tuple(p) for p in pts1]:
                # Allow Z1_vertices to be extreme vertices only if same hull, or check subset + hull equality:
                for vp in v1_claim:
                    if vp not in {tuple(p) for p in pts1}:
                        raise AssertionError(f"{ctx}: Z1_vertices contains point outside generator Minkowski sum")
    elif "Z1_vertices" in item:
        pts1 = assert_int_matrix(item["Z1_vertices"], expected_cols=d_dim, context=f"{ctx}.Z1_vertices")
        g1_mat = []
    else:
        raise AssertionError(f"{ctx}: requires Z1_gens or Z1_vertices")

    if has_g2:
        pts2, g2_mat = _expand_zonotope_vertices(b2, item["Z2_gens"], d_dim, f"{ctx}.Z2")
        if "Z2_vertices" in item:
            v2_claim = sorted({tuple(r) for r in assert_int_matrix(item["Z2_vertices"], expected_cols=d_dim, context=f"{ctx}.Z2_vertices")})
            for vp in v2_claim:
                if vp not in {tuple(p) for p in pts2}:
                    raise AssertionError(f"{ctx}: Z2_vertices contains point outside generator Minkowski sum")
    elif "Z2_vertices" in item:
        pts2 = assert_int_matrix(item["Z2_vertices"], expected_cols=d_dim, context=f"{ctx}.Z2_vertices")
        g2_mat = []
    else:
        raise AssertionError(f"{ctx}: requires Z2_gens or Z2_vertices")

    rank1 = exact_q_rank_bareiss([[p[c] - pts1[0][c] for c in range(d_dim)] for p in pts1[1:]]) if len(pts1) > 1 else 0
    rank2 = exact_q_rank_bareiss([[p[c] - pts2[0][c] for c in range(d_dim)] for p in pts2[1:]]) if len(pts2) > 1 else 0
    if rank1 != r1:
        raise AssertionError(f"{ctx}: Z1 affine rank {rank1} != claimed r1={r1}")
    if rank2 != r2:
        raise AssertionError(f"{ctx}: Z2 affine rank {rank2} != claimed r2={r2}")

    hull_res = compute_convex_hull_normalized_volume(pts1 + pts2, d_dim)
    vol_hull = int(hull_res["normalized_volume"])
    if vol_hull != expected_vol:
        raise AssertionError(f"{ctx}: independent Beneath-Beyond volume {vol_hull} != expected {expected_vol}")

    fac_divisor = math.factorial(r1) * math.factorial(r2)
    if r1 + r2 == d_dim - 1:
        if vol_hull % fac_divisor != 0:
            raise AssertionError(
                f"{ctx}: factorial join law violated: r1!*r2!={fac_divisor} does not divide Vol_{d_dim}={vol_hull}"
            )
        if has_g1 and has_g2 and vol_hull > 0:
            comb_dirs = g1_mat + g2_mat
            if exact_q_rank_bareiss(comb_dirs) != r1 + r2:
                raise AssertionError(f"{ctx}: full-dimensional join requires skew Z1, Z2 direction subspaces")
            bridge = [b2[c] - b1[c] for c in range(d_dim)]
            det_sum = 0
            for c1 in itertools.combinations(range(len(g1_mat)), r1):
                rows1 = [g1_mat[i] for i in c1]
                if r1 > 0 and exact_q_rank_bareiss(rows1) < r1:
                    continue
                for c2 in itertools.combinations(range(len(g2_mat)), r2):
                    rows2 = [g2_mat[j] for j in c2]
                    if r2 > 0 and exact_q_rank_bareiss(rows2) < r2:
                        continue
                    sq_mat = rows1 + rows2 + [bridge]
                    det_sum += abs(exact_det_bareiss(sq_mat))
            cayley_vol = fac_divisor * det_sum
            if cayley_vol != vol_hull:
                raise AssertionError(f"{ctx}: Cayley-Shephard determinant formula {cayley_vol} != hull volume {vol_hull}")

    if "simplices" in item and item["simplices"] is not None:
        verify_simplex_triangulation_volume_certificate(item["simplices"], expected_vol)
        ineqs = hull_res["outward_inequalities"]
        for s_idx, simp in enumerate(item["simplices"]):
            s_rows = assert_int_matrix(simp, context=f"{ctx}.simplices[{s_idx}]")
            verts_to_check = s_rows if len(s_rows) == d_dim + 1 else ([[0] * d_dim] + s_rows)
            for v_pt in verts_to_check:
                for c_n, b_r in ineqs:
                    if vec_dot(c_n, v_pt) > b_r:
                        raise AssertionError(f"{ctx}: simplex[{s_idx}] vertex {v_pt} lies outside conv(Z1 u Z2)")

    if "divisible_by" in item and item["divisible_by"] is not None:
        div_b = assert_strict_int(item["divisible_by"], f"{ctx}.divisible_by")
        if div_b <= 0 or (vol_hull % div_b != 0):
            raise AssertionError(f"{ctx}: volume {vol_hull} not divisible by {div_b}")

    if "modulus" in item and "expected_mod_residue" in item and item["modulus"] is not None:
        mod_m = assert_strict_int(item["modulus"], f"{ctx}.modulus")
        rem_m = assert_strict_int(item["expected_mod_residue"], f"{ctx}.expected_mod_residue")
        if (vol_hull % mod_m) != (rem_m % mod_m):
            raise AssertionError(f"{ctx}: volume {vol_hull} mod {mod_m} != {rem_m % mod_m}")

    return {
        "verified": True,
        "d_dim": d_dim,
        "r1": r1,
        "r2": r2,
        "normalized_volume": vol_hull,
        "factorial_divisor": fac_divisor,
    }


def verify_zonotope_join_volume_certificate(cert: dict[str, Any]) -> dict[str, Any]:
    """Theorem A2a verifier: independent Beneath-Beyond + Cayley-Shephard determinant verification of `conv(Z_1 u Z_2)`."""
    cases_key = "join_cases" if "join_cases" in cert else ("instances" if "instances" in cert else None)
    if cases_key is not None:
        cases = cert[cases_key]
        if type(cases) is not list or len(cases) == 0:
            raise AssertionError(f"Empty {cases_key} in zonotope join certificate")
        results = [_verify_single_zonotope_join(c, f"{cases_key}[{i}]") for i, c in enumerate(cases)]
        if cert.get("verify_d6_all_partitions_div6", False):
            for r1 in range(6):
                r2 = 5 - r1
                if (math.factorial(r1) * math.factorial(r2)) % 6 != 0:
                    raise AssertionError(f"d=6 partition ({r1},{r2}) failed 6 | r1!*r2!")
        return {"verified": True, "kind": "zonotope_join_batch", "cases_verified": len(results), "results": results}
    return _verify_single_zonotope_join(cert, "zonotope_join")


# ---------------------------------------------------------------------------
# 8. Wave II Universal 2-Layer Gate Compiler & Theorem A2b Primal / Dual Verifiers
# ---------------------------------------------------------------------------


CompiledGate = tuple[
    IntVector,
    list[tuple[int, IntVector]],
    list[tuple[int, IntVector, list[tuple[int, IntVector]]]],
]


def _get_symmetry_group_perms(spec: Any, n_dim: int) -> list[tuple[int, ...]]:
    if spec is None:
        return [tuple(range(n_dim))]
    if type(spec) is str:
        key = spec.lower()
        if key in ("none", "trivial", "id"):
            return [tuple(range(n_dim))]
        if key == "syl2_s6":
            if n_dim != 6:
                raise ValueError("syl2_s6 requires n_dim == 6")
            gens = [(1, 2, 3, 0, 4, 5), (3, 2, 1, 0, 4, 5), (0, 1, 2, 3, 5, 4)]
        elif key == "d6":
            if n_dim != 6:
                raise ValueError("d6 requires n_dim == 6")
            gens = [(1, 2, 3, 4, 5, 0), (5, 4, 3, 2, 1, 0)]
        elif key == "s6" or key == f"s_{n_dim}":
            return sorted(itertools.permutations(range(n_dim)))
        else:
            raise ValueError(f"Unknown symmetry_group string: {spec!r}")
        ident = tuple(range(n_dim))
        seen = {ident}
        stack = [ident]
        while stack:
            cur = stack.pop()
            for g in gens:
                nxt = tuple(cur[g[i]] for i in range(n_dim))
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        return sorted(seen)
    if type(spec) in (list, tuple):
        out_p: list[tuple[int, ...]] = []
        for idx, p in enumerate(spec):
            pv = assert_int_vector(p, f"perm[{idx}]")
            if sorted(pv) != list(range(n_dim)):
                raise ValueError(f"Invalid permutation at index {idx}: {pv}")
            out_p.append(tuple(pv))
        if len(out_p) == 0:
            raise ValueError("Empty permutation group list")
        return out_p
    raise TypeError(f"Unsupported symmetry group spec type: {type(spec).__name__}")


def _permute_vec(vec: Sequence[int], perm: tuple[int, ...]) -> IntVector:
    n_d = len(perm)
    out = [0] * n_d
    for i in range(n_d):
        out[perm[i]] = vec[i]
    return out


def _empty_compiled_gate(n_dim: int) -> CompiledGate:
    return ([0] * n_dim, [], [])


def _add_scaled_compiled_gate(dst: CompiledGate, scale: int, src: CompiledGate) -> CompiledGate:
    if scale == 0:
        return dst
    n_dim = len(dst[0])
    lin = [dst[0][j] + scale * src[0][j] for j in range(n_dim)]
    r1 = list(dst[1]) + [(scale * w, list(nrm)) for w, nrm in src[1] if scale * w != 0]
    r2 = list(dst[2]) + [
        (scale * ow, list(ilin), [(aw, list(anrm)) for aw, anrm in ih])
        for ow, ilin, ih in src[2]
        if scale * ow != 0
    ]
    return (lin, r1, r2)


def _permute_compiled_gate(gate: CompiledGate, perm: tuple[int, ...]) -> CompiledGate:
    lin_p = _permute_vec(gate[0], perm)
    r1_p = [(w, _permute_vec(nrm, perm)) for w, nrm in gate[1]]
    r2_p = [
        (ow, _permute_vec(ilin, perm), [(aw, _permute_vec(anrm, perm)) for aw, anrm in ih])
        for ow, ilin, ih in gate[2]
    ]
    return (lin_p, r1_p, r2_p)


def _canonical_gate_signature(gate: CompiledGate) -> tuple[Any, ...]:
    r1_acc: dict[tuple[int, ...], int] = {}
    for w, nrm in gate[1]:
        if all(x == 0 for x in nrm):
            continue
        r1_acc[tuple(nrm)] = r1_acc.get(tuple(nrm), 0) + w
    r1_sig = tuple(sorted((k, v) for k, v in r1_acc.items() if v != 0))

    r2_acc: dict[tuple[tuple[int, ...], tuple[tuple[tuple[int, ...], int], ...]], int] = {}
    for ow, ilin, ih in gate[2]:
        ih_map: dict[tuple[int, ...], int] = {}
        for aw, anrm in ih:
            if any(x != 0 for x in anrm):
                ih_map[tuple(anrm)] = ih_map.get(tuple(anrm), 0) + aw
        ih_sig = tuple(sorted((k, v) for k, v in ih_map.items() if v != 0))
        key2 = (tuple(ilin), ih_sig)
        r2_acc[key2] = r2_acc.get(key2, 0) + ow
    r2_sig = tuple(sorted((k, v) for k, v in r2_acc.items() if v != 0))
    return (tuple(gate[0]), r1_sig, r2_sig)


def _parse_l1_form(spec: Any, n_dim: int, ctx: str) -> tuple[IntVector, list[tuple[int, IntVector]]]:
    """Parse a 1-layer CPWL form `u_0 . x + sum_r alpha_r ReLU(a_r . x)` (or sum of pair maxima)."""
    if type(spec) is list:
        # Shorthand list of index pairs `[[i, j], [k, l]]` -> sum of `max(x_i, x_j)`
        lin = [0] * n_dim
        hinges: list[tuple[int, IntVector]] = []
        for p_idx, pair in enumerate(spec):
            pv = assert_int_vector(pair, f"{ctx}[{p_idx}]")
            if len(pv) != 2 or not (0 <= pv[0] < n_dim and 0 <= pv[1] < n_dim):
                raise ValueError(f"{ctx}[{p_idx}]: invalid coordinate pair {pv}")
            i, j = pv[0], pv[1]
            lin[j] += 1
            if i != j:
                diff = [0] * n_dim
                diff[i] += 1
                diff[j] -= 1
                hinges.append((1, diff))
        return (lin, hinges)
    if type(spec) is dict:
        lin = assert_int_vector(spec.get("linear", [0] * n_dim), f"{ctx}.linear")
        if len(lin) != n_dim:
            raise ValueError(f"{ctx}.linear length != {n_dim}")
        hinges_out: list[tuple[int, IntVector]] = []
        for h_idx, h_item in enumerate(spec.get("hinges", [])):
            if type(h_item) is dict:
                w = assert_strict_int(h_item.get("weight", 1), f"{ctx}.hinges[{h_idx}].weight")
                nrm = assert_int_vector(h_item["normal"], f"{ctx}.hinges[{h_idx}].normal")
            else:
                w = assert_strict_int(h_item[0], f"{ctx}.hinges[{h_idx}][0]")
                nrm = assert_int_vector(h_item[1], f"{ctx}.hinges[{h_idx}][1]")
            if len(nrm) != n_dim:
                raise ValueError(f"{ctx}.hinges[{h_idx}] normal length != {n_dim}")
            if w != 0 and any(x != 0 for x in nrm):
                hinges_out.append((w, nrm))
        for p_idx, pair in enumerate(spec.get("pair_maxima", [])):
            pv = assert_int_vector(pair, f"{ctx}.pair_maxima[{p_idx}]")
            if len(pv) != 2 or not (0 <= pv[0] < n_dim and 0 <= pv[1] < n_dim):
                raise ValueError(f"{ctx}.pair_maxima[{p_idx}] invalid")
            i, j = pv[0], pv[1]
            lin[j] += 1
            if i != j:
                diff = [0] * n_dim
                diff[i] += 1
                diff[j] -= 1
                hinges_out.append((1, diff))
        return (lin, hinges_out)
    raise TypeError(f"{ctx}: unsupported L1 form spec {type(spec).__name__}")


def compile_2layer_gate(spec: dict[str, Any], n_dim: int, ctx: str = "gate") -> CompiledGate:
    """Compile any JSON-serializable 2-layer homogeneous Z-gate spec (including orbit sums) into `CompiledGate`."""
    if type(spec) is not dict:
        raise TypeError(f"{ctx}: expected dict gate spec, got {type(spec).__name__}")

    if "orbit_group" in spec and spec["orbit_group"] is not None:
        base_spec = {k: v for k, v in spec.items() if k not in ("orbit_group", "orbit_mode")}
        base_gate = compile_2layer_gate(base_spec, n_dim, f"{ctx}.base")
        perms = _get_symmetry_group_perms(spec["orbit_group"], n_dim)
        orbit_mode = str(spec.get("orbit_mode", "sum"))
        acc = _empty_compiled_gate(n_dim)
        seen_sigs: set[tuple[Any, ...]] = set()
        for p in perms:
            pg = _permute_compiled_gate(base_gate, p)
            if orbit_mode == "unique":
                sig = _canonical_gate_signature(pg)
                if sig in seen_sigs:
                    continue
                seen_sigs.add(sig)
            acc = _add_scaled_compiled_gate(acc, 1, pg)
        return acc

    kind = str(spec.get("kind", "relu2"))
    if kind == "linear":
        c = assert_int_vector(spec["coeffs"], f"{ctx}.coeffs")
        if len(c) != n_dim:
            raise ValueError(f"{ctx}.coeffs length != {n_dim}")
        return (c, [], [])

    if kind in ("relu1", "1L_relu"):
        nrm = assert_int_vector(spec["normal"], f"{ctx}.normal")
        w = assert_strict_int(spec.get("weight", 1), f"{ctx}.weight")
        if len(nrm) != n_dim:
            raise ValueError(f"{ctx}.normal length != {n_dim}")
        return ([0] * n_dim, [(w, nrm)] if (w != 0 and any(x != 0 for x in nrm)) else [], [])

    if kind in ("pair_max", "1L"):
        pv = assert_int_vector(spec["pair"], f"{ctx}.pair")
        w = assert_strict_int(spec.get("weight", 1), f"{ctx}.weight")
        if len(pv) != 2 or not (0 <= pv[0] < n_dim and 0 <= pv[1] < n_dim):
            raise ValueError(f"{ctx}.pair invalid: {pv}")
        i, j = pv[0], pv[1]
        lin = [0] * n_dim
        lin[j] += w
        r1: list[tuple[int, IntVector]] = []
        if i != j and w != 0:
            diff = [0] * n_dim
            diff[i] += 1
            diff[j] -= 1
            r1.append((w, diff))
        return (lin, r1, [])

    if kind == "relu2":
        w_out = assert_strict_int(spec.get("weight", 1), f"{ctx}.weight")
        b_lin = assert_int_vector(spec.get("base_linear", [0] * n_dim), f"{ctx}.base_linear")
        i_lin = assert_int_vector(spec.get("inner_linear", [0] * n_dim), f"{ctx}.inner_linear")
        if len(b_lin) != n_dim or len(i_lin) != n_dim:
            raise ValueError(f"{ctx}: linear length != {n_dim}")
        ih_list: list[tuple[int, IntVector]] = []
        for idx, h_item in enumerate(spec.get("inner_hinges", [])):
            if type(h_item) is dict:
                hw = assert_strict_int(h_item.get("weight", 1), f"{ctx}.inner_hinges[{idx}].weight")
                hn = assert_int_vector(h_item["normal"], f"{ctx}.inner_hinges[{idx}].normal")
            else:
                hw = assert_strict_int(h_item[0], f"{ctx}.inner_hinges[{idx}][0]")
                hn = assert_int_vector(h_item[1], f"{ctx}.inner_hinges[{idx}][1]")
            if len(hn) != n_dim:
                raise ValueError(f"{ctx}.inner_hinges[{idx}] length != {n_dim}")
            if hw != 0 and any(x != 0 for x in hn):
                ih_list.append((hw, hn))
        base_scaled = [w_out * v for v in b_lin]
        r2_list = [(w_out, i_lin, ih_list)] if w_out != 0 else []
        return (base_scaled, [], r2_list)

    if kind in ("zonotope_max", "max2_l1", "M2"):
        w_out = assert_strict_int(spec.get("weight", 1), f"{ctx}.weight")
        u_lin, u_h = _parse_l1_form(spec["left"] if "left" in spec else spec["U"], n_dim, f"{ctx}.U")
        v_lin, v_h = _parse_l1_form(spec["right"] if "right" in spec else spec["V"], n_dim, f"{ctx}.V")
        # max(U, V) = V + ReLU((U - V))
        diff_lin = [u_lin[c] - v_lin[c] for c in range(n_dim)]
        diff_h = list(u_h) + [(-hw, list(hn)) for hw, hn in v_h]
        lin_scaled = [w_out * x for x in v_lin]
        r1_scaled = [(w_out * hw, list(hn)) for hw, hn in v_h if w_out * hw != 0]
        r2_scaled = [(w_out, diff_lin, diff_h)] if w_out != 0 else []
        return (lin_scaled, r1_scaled, r2_scaled)

    if kind in ("sum", "linear_comb"):
        acc_s = _empty_compiled_gate(n_dim)
        for t_idx, term in enumerate(spec.get("terms", [])):
            tw = assert_strict_int(term.get("weight", 1), f"{ctx}.terms[{t_idx}].weight")
            tg = compile_2layer_gate(term["gate"], n_dim, f"{ctx}.terms[{t_idx}].gate")
            acc_s = _add_scaled_compiled_gate(acc_s, tw, tg)
        return acc_s

    raise ValueError(f"{ctx}: unsupported gate kind {kind!r}")


def eval_compiled_gate_int(gate: CompiledGate, x: Sequence[int]) -> int:
    """Exact integer point evaluation of a `CompiledGate` at `x in Z^n`."""
    acc = vec_dot(gate[0], list(x))
    for w, nrm in gate[1]:
        v = vec_dot(nrm, list(x))
        if v > 0:
            acc += w * v
    for ow, ilin, ih in gate[2]:
        inner = vec_dot(ilin, list(x))
        for aw, anrm in ih:
            va = vec_dot(anrm, list(x))
            if va > 0:
                inner += aw * va
        if inner > 0:
            acc += ow * inner
    return acc


def smooth_gradient_compiled_gate_int(gate: CompiledGate, x: Sequence[int]) -> tuple[bool, IntVector]:
    """Check strict smoothness (zero non-trivial active kinks `== 0`) of `gate` at `x` and return exact integer gradient."""
    x_v = list(x)
    n_dim = len(gate[0])
    grad = list(gate[0])
    for w, nrm in gate[1]:
        if w == 0 or all(z == 0 for z in nrm):
            continue
        v = vec_dot(nrm, x_v)
        if v == 0:
            return (False, [])
        if v > 0:
            for j in range(n_dim):
                grad[j] += w * nrm[j]
    for ow, ilin, ih in gate[2]:
        if ow == 0:
            continue
        inner_val = vec_dot(ilin, x_v)
        inner_grad = list(ilin)
        for aw, anrm in ih:
            if aw == 0 or all(z == 0 for z in anrm):
                continue
            va = vec_dot(anrm, x_v)
            if va == 0:
                return (False, [])
            if va > 0:
                inner_val += aw * va
                for j in range(n_dim):
                    inner_grad[j] += aw * anrm[j]
        if inner_val == 0:
            if any(z != 0 for z in inner_grad):
                return (False, [])
            continue
        if inner_val > 0:
            for j in range(n_dim):
                grad[j] += ow * inner_grad[j]
    return (True, grad)


def _evaluate_compiled_gate_subcones(
    gate: CompiledGate,
    init_state: ConeState,
    n_dim: int,
) -> tuple[list[tuple[IntVector, ConeState]], int]:
    """Refine `init_state` across ALL Layer-1 and Layer-2 kinks of `gate`, returning exact linear gradient per leaf sub-cone."""
    prim_l1_map: dict[tuple[int, ...], None] = {}
    for w, nrm in gate[1]:
        if w != 0 and any(x != 0 for x in nrm):
            prim_l1_map[_primitive_canonical_vec(nrm)] = None
    for ow, _, ih in gate[2]:
        if ow != 0:
            for aw, anrm in ih:
                if aw != 0 and any(x != 0 for x in anrm):
                    prim_l1_map[_primitive_canonical_vec(anrm)] = None

    splits = 0
    l1_cones: list[ConeState] = [init_state]
    for p_nrm in prim_l1_map:
        nxt_cones: list[ConeState] = []
        for st_c in l1_cones:
            status, st_p, st_n = _pointed_cone_split(st_c, p_nrm)
            if status == "nonneg":
                assert st_p is not None
                nxt_cones.append(st_p)
            elif status == "nonpos":
                assert st_n is not None
                nxt_cones.append(st_n)
            else:
                assert st_p is not None and st_n is not None
                splits += 1
                nxt_cones.append(st_p)
                nxt_cones.append(st_n)
        l1_cones = nxt_cones

    leaf_results: list[tuple[IntVector, ConeState]] = []
    for st_l1 in l1_cones:
        rays_l1 = st_l1[0]
        interior_pt = [sum(r[j] for r in rays_l1) for j in range(n_dim)]
        base_g = list(gate[0])
        for w, nrm in gate[1]:
            if vec_dot(nrm, interior_pt) > 0:
                for j in range(n_dim):
                    base_g[j] += w * nrm[j]

        cur_states: list[tuple[IntVector, ConeState]] = [(base_g, st_l1)]
        for ow, ilin, ih in gate[2]:
            if ow == 0:
                continue
            eff_in = list(ilin)
            for aw, anrm in ih:
                if vec_dot(anrm, interior_pt) > 0:
                    for j in range(n_dim):
                        eff_in[j] += aw * anrm[j]
            if all(x == 0 for x in eff_in):
                continue
            nxt_states: list[tuple[IntVector, ConeState]] = []
            for g_acc, st_sub in cur_states:
                status, st_p, st_n = _pointed_cone_split(st_sub, eff_in)
                if status == "nonneg":
                    assert st_p is not None
                    nxt_states.append(([g_acc[j] + ow * eff_in[j] for j in range(n_dim)], st_p))
                elif status == "nonpos":
                    assert st_n is not None
                    nxt_states.append((g_acc, st_n))
                else:
                    assert st_p is not None and st_n is not None
                    splits += 1
                    nxt_states.append(([g_acc[j] + ow * eff_in[j] for j in range(n_dim)], st_p))
                    nxt_states.append((g_acc, st_n))
            cur_states = nxt_states
        leaf_results.extend(cur_states)

    return (leaf_results, splits)


def verify_max6_primal_z_half_certificate(cert: dict[str, Any]) -> dict[str, Any]:
    """Theorem A2b Primal Verifier: prove `2^t * MAX_n(x) == sum_k c_k g_k(x)` across ALL refined polyhedral sub-cones."""
    n_dim = assert_strict_int(cert.get("n_dim", 6), "n_dim")
    if n_dim < 2:
        raise ValueError("n_dim must be >= 2")

    if "t_exp" in cert:
        t_exp = assert_strict_int(cert["t_exp"], "t_exp")
        if t_exp < 0:
            raise ValueError("t_exp must be >= 0")
        scale = 1 << t_exp
    elif "pow2_denom" in cert:
        scale = assert_strict_int(cert["pow2_denom"], "pow2_denom")
        if scale <= 0 or (scale & (scale - 1)) != 0:
            raise AssertionError(f"pow2_denom={scale} is not a power of 2 (not in Z[1/2])")
        t_exp = scale.bit_length() - 1
    else:
        raise AssertionError("Primal Z[1/2] certificate requires `t_exp` or `pow2_denom`")

    total_gate = _empty_compiled_gate(n_dim)
    if "W1" in cert and "W2" in cert and "w_out" in cert:
        w1_m = assert_int_matrix(cert["W1"], expected_cols=n_dim, context="W1")
        w2_m = assert_int_matrix(cert["W2"], expected_cols=len(w1_m), context="W2")
        w_out = assert_int_vector(cert["w_out"], "w_out")
        if len(w_out) != len(w2_m):
            raise ValueError("w_out length != len(W2)")
        w_skip = assert_int_vector(cert.get("w_skip", [0] * n_dim), "w_skip")
        if len(w_skip) != n_dim:
            raise ValueError("w_skip length != n_dim")
        r2_terms: list[tuple[int, IntVector, list[tuple[int, IntVector]]]] = []
        for j_idx, cj in enumerate(w_out):
            if cj != 0:
                ih = [(w2_m[j_idx][i], list(w1_m[i])) for i in range(len(w1_m)) if w2_m[j_idx][i] != 0]
                r2_terms.append((cj, [0] * n_dim, ih))
        total_gate = (w_skip, [], r2_terms)
    else:
        gates_raw = cert["gates"]
        coeffs_z = assert_int_vector(cert["coeffs_z"], "coeffs_z")
        if type(gates_raw) is not list or len(gates_raw) != len(coeffs_z):
            raise ValueError("gates and coeffs_z length mismatch")
        for k_idx, (gk_spec, ck) in enumerate(zip(gates_raw, coeffs_z)):
            if ck != 0:
                gk = compile_2layer_gate(gk_spec, n_dim, f"gates[{k_idx}]")
                total_gate = _add_scaled_compiled_gate(total_gate, ck, gk)

    ones = [1] * n_dim
    neg_ones = [-1] * n_dim
    if eval_compiled_gate_int(total_gate, ones) != scale:
        raise AssertionError("Primal Z[1/2] certificate failed at +(1,...,1)")
    if eval_compiled_gate_int(total_gate, neg_ones) != -scale:
        raise AssertionError("Primal Z[1/2] certificate failed at -(1,...,1)")

    trans_inv = True
    for w, nrm in total_gate[1]:
        if w != 0 and sum(nrm) != 0:
            trans_inv = False
            break
    if trans_inv:
        for ow, ilin, ih in total_gate[2]:
            if ow != 0:
                if sum(ilin) != 0 or any(aw != 0 and sum(anrm) != 0 for aw, anrm in ih):
                    trans_inv = False
                    break

    total_sig = _canonical_gate_signature(total_gate)
    perms_to_check = list(itertools.permutations(range(n_dim)))
    symmetry_used = "none"
    if n_dim == 6:
        syl2_gens = [(1, 2, 3, 0, 4, 5), (3, 2, 1, 0, 4, 5), (0, 1, 2, 3, 5, 4)]
        if all(_canonical_gate_signature(_permute_compiled_gate(total_gate, g)) == total_sig for g in syl2_gens):
            syl2_grp = _get_symmetry_group_perms("syl2_s6", 6)
            unseen = set(perms_to_check)
            reps: list[tuple[int, ...]] = []
            while unseen:
                rep = min(unseen)
                reps.append(rep)
                for g in syl2_grp:
                    unseen.discard(tuple(rep[g[i]] for i in range(6)))
            perms_to_check = reps
            symmetry_used = "syl2_s6_verified"

    leaf_subcones = 0
    total_splits = 0

    if trans_inv:
        n_rays = n_dim - 1
        all_m = (1 << n_rays) - 1
        simp_m = [all_m ^ (1 << i) for i in range(n_rays)]
        for perm in perms_to_check:
            c_rays: list[IntVector] = []
            for k in range(1, n_dim):
                r_pos = [0] * n_dim
                for idx in perm[k:]:
                    r_pos[idx] = 1
                c_rays.append(r_pos)
            leaves, sp = _evaluate_compiled_gate_subcones(total_gate, (c_rays, list(simp_m), n_rays), n_dim)
            total_splits += sp
            expected_g = [scale if j == perm[-1] else 0 for j in range(n_dim)]
            p0 = perm[0]
            for grad_leaf, (l_rays, _, _) in leaves:
                leaf_subcones += 1
                # On slice x_{p0} == 0 plus global translation slope `scale` along (1,...,1):
                if sum(grad_leaf) != scale or any(grad_leaf[j] != expected_g[j] for j in range(n_dim) if j != p0):
                    witness = [sum(r[j] for r in l_rays) for j in range(n_dim)]
                    raise AssertionError(
                        f"Primal Z[1/2] identity failed on sub-cone of perm={perm}: grad={grad_leaf} != {expected_g}, witness={witness}"
                    )
    else:
        all_m_full = (1 << n_dim) - 1
        simp_m_full = [all_m_full ^ (1 << i) for i in range(n_dim)]
        for perm in perms_to_check:
            expected_g = [scale if j == perm[-1] else 0 for j in range(n_dim)]
            for m_zero in range(n_dim + 1):
                c_rays_f: list[IntVector] = []
                for k in range(1, m_zero + 1):
                    r_neg = [0] * n_dim
                    for idx in perm[:k]:
                        r_neg[idx] = -1
                    c_rays_f.append(r_neg)
                for k in range(m_zero, n_dim):
                    r_pos = [0] * n_dim
                    for idx in perm[k:]:
                        r_pos[idx] = 1
                    c_rays_f.append(r_pos)
                leaves, sp = _evaluate_compiled_gate_subcones(total_gate, (c_rays_f, list(simp_m_full), n_dim), n_dim)
                total_splits += sp
                for grad_leaf, (l_rays, _, _) in leaves:
                    leaf_subcones += 1
                    if grad_leaf != expected_g:
                        witness = [sum(r[j] for r in l_rays) for j in range(n_dim)]
                        raise AssertionError(
                            f"Primal Z[1/2] identity failed on signed cone of perm={perm}: grad={grad_leaf} != {expected_g}, witness={witness}"
                        )

    return {
        "verified": True,
        "n_dim": n_dim,
        "t_exp": t_exp,
        "pow2_scale": scale,
        "translation_equivariant": trans_inv,
        "symmetry_reduction": symmetry_used,
        "braid_representatives_checked": len(perms_to_check),
        "leaf_subcones_verified": leaf_subcones,
        "off_braid_splits_resolved": total_splits,
    }


def verify_max6_dual_padic_certificate(
    cert: dict[str, Any],
    epistemic_tag: str | None = None,
) -> dict[str, Any]:
    """Theorem A2b Dual Verifier: independently reconstruct `(A, b)` from CPWL gate & row functionals,
    verify `v_p(y^T A) >= s > v_p(y^T b)`, and enforce the Wave II 3-valued epistemic guardrail.
    """
    eff_tag = str(epistemic_tag) if epistemic_tag is not None else (
        str(cert["epistemic_tag"]) if "epistemic_tag" in cert and cert["epistemic_tag"] is not None else None
    )
    scope = str(cert.get("scope", "bounded_tier"))
    is_unconstrained = bool(
        cert.get("unconstrained", False)
        or scope in ("unconstrained", "unconstrained_relu_6_2_z_half", "global_unconstrained")
    )
    if is_unconstrained and eff_tag == "CERTIFIED_EXACT" and not cert.get("universal_proof_supplied", False):
        raise AssertionError(
            "Epistemic guardrail violation: bounded-dictionary p-adic UNSAT cannot claim CERTIFIED_EXACT "
            "for unconstrained ReLU_{6,2}(Z[1/2]); must carry OPEN_BUDGET_EXCEEDED"
        )

    if "tiers" in cert and type(cert["tiers"]) is dict:
        if len(cert["tiers"]) == 0:
            raise AssertionError("Empty `tiers` dict in dual p-adic certificate")
        tier_res = {
            t_name: verify_max6_dual_padic_certificate(t_cert, epistemic_tag=t_cert.get("epistemic_tag"))
            for t_name, t_cert in cert["tiers"].items()
        }
        return {
            "verified": True,
            "kind": "multi_tier_padic_obstruction",
            "scope": scope,
            "tiers_verified": len(tier_res),
            "tiers": tier_res,
        }

    n_dim = assert_strict_int(cert.get("n_dim", 6), "n_dim")
    target_scale = assert_strict_int(cert.get("target_scale", 1), "target_scale")
    if target_scale <= 0:
        raise ValueError("target_scale must be > 0")

    a_mat = assert_int_matrix(cert["A"], context="A")
    b_vec = assert_int_vector(cert["b"], context="b")
    m_rows = len(a_mat)
    if m_rows == 0 or len(b_vec) != m_rows:
        raise ValueError("Invalid (A, b) row count in dual p-adic certificate")
    n_cols = len(a_mat[0])

    gates_raw = cert.get("gates")
    if type(gates_raw) is not list or len(gates_raw) != n_cols:
        raise AssertionError(f"Dual p-adic certificate requires `gates` list matching A columns ({n_cols})")
    compiled_gates = [compile_2layer_gate(g_sp, n_dim, f"gates[{j}]") for j, g_sp in enumerate(gates_raw)]

    if "row_specs" in cert:
        row_specs = cert["row_specs"]
    elif "eval_points" in cert:
        row_specs = [{"kind": "point_eval", "point": pt} for pt in cert["eval_points"]]
    else:
        raise AssertionError("Dual p-adic certificate requires `row_specs` or `eval_points` to verify (A, b)")

    if type(row_specs) is not list or len(row_specs) != m_rows:
        raise AssertionError(f"row_specs length {len(row_specs) if type(row_specs) is list else -1} != A rows {m_rows}")

    for i_row, r_spec in enumerate(row_specs):
        if type(r_spec) is not dict:
            raise TypeError(f"row_specs[{i_row}] must be a dict")
        r_kind = str(r_spec.get("kind", "point_eval"))
        if r_kind == "point_eval":
            pt = assert_int_vector(r_spec["point"], f"row_specs[{i_row}].point")
            if len(pt) != n_dim:
                raise ValueError(f"row_specs[{i_row}] point length != {n_dim}")
            exp_b = target_scale * max(pt)
            if b_vec[i_row] != exp_b:
                raise AssertionError(f"Row {i_row} b mismatch: {b_vec[i_row]} != {exp_b}")
            for j_col, cg in enumerate(compiled_gates):
                exp_aij = eval_compiled_gate_int(cg, pt)
                if a_mat[i_row][j_col] != exp_aij:
                    raise AssertionError(f"Row {i_row} col {j_col} A mismatch: {a_mat[i_row][j_col]} != {exp_aij}")
        elif r_kind == "finite_diff":
            terms = r_spec.get("terms", [])
            if type(terms) is not list or len(terms) == 0:
                raise AssertionError(f"row_specs[{i_row}] empty finite_diff terms")
            parsed_terms: list[tuple[int, IntVector]] = []
            for t_i, t_obj in enumerate(terms):
                if type(t_obj) is dict:
                    tw = assert_strict_int(t_obj["weight"], f"row_specs[{i_row}].terms[{t_i}].weight")
                    tpt = assert_int_vector(t_obj["point"], f"row_specs[{i_row}].terms[{t_i}].point")
                else:
                    tw = assert_strict_int(t_obj[0], f"row_specs[{i_row}].terms[{t_i}][0]")
                    tpt = assert_int_vector(t_obj[1], f"row_specs[{i_row}].terms[{t_i}][1]")
                if len(tpt) != n_dim:
                    raise ValueError(f"row_specs[{i_row}] term point length != {n_dim}")
                parsed_terms.append((tw, tpt))
            exp_b = sum(tw * target_scale * max(tpt) for tw, tpt in parsed_terms)
            if b_vec[i_row] != exp_b:
                raise AssertionError(f"Row {i_row} finite_diff b mismatch: {b_vec[i_row]} != {exp_b}")
            for j_col, cg in enumerate(compiled_gates):
                exp_aij = sum(tw * eval_compiled_gate_int(cg, tpt) for tw, tpt in parsed_terms)
                if a_mat[i_row][j_col] != exp_aij:
                    raise AssertionError(f"Row {i_row} col {j_col} finite_diff A mismatch")
        elif r_kind == "subcone_grad":
            pt = assert_int_vector(r_spec["interior_point"], f"row_specs[{i_row}].interior_point")
            if len(pt) != n_dim:
                raise ValueError(f"row_specs[{i_row}] interior_point length != {n_dim}")
            mx = max(pt)
            max_indices = [idx for idx, val in enumerate(pt) if val == mx]
            if len(max_indices) != 1:
                raise AssertionError(f"Row {i_row} interior_point {pt} lies on MAX_{n_dim} braid kink (non-smooth)")
            tgt_grad = [target_scale if idx == max_indices[0] else 0 for idx in range(n_dim)]
            if "coord" in r_spec:
                c_idx = assert_strict_int(r_spec["coord"], f"row_specs[{i_row}].coord")
                if not (0 <= c_idx < n_dim):
                    raise ValueError(f"Invalid coord {c_idx}")
                dir_v = [1 if idx == c_idx else 0 for idx in range(n_dim)]
            else:
                dir_v = assert_int_vector(r_spec["direction"], f"row_specs[{i_row}].direction")
                if len(dir_v) != n_dim:
                    raise ValueError(f"row_specs[{i_row}] direction length != {n_dim}")
            exp_b = vec_dot(tgt_grad, dir_v)
            if b_vec[i_row] != exp_b:
                raise AssertionError(f"Row {i_row} subcone_grad b mismatch: {b_vec[i_row]} != {exp_b}")
            for j_col, cg in enumerate(compiled_gates):
                smooth_ok, g_vec = smooth_gradient_compiled_gate_int(cg, pt)
                if not smooth_ok:
                    raise AssertionError(f"Row {i_row} interior_point {pt} lies on an active kink of gate {j_col}")
                exp_aij = vec_dot(g_vec, dir_v)
                if a_mat[i_row][j_col] != exp_aij:
                    raise AssertionError(f"Row {i_row} col {j_col} subcone_grad A mismatch")
        else:
            raise ValueError(f"Unsupported row functional kind {r_kind!r}")

    p_val = assert_strict_int(cert.get("p", 3), "p")
    inv_primes = cert.get("inverted_primes", [2])
    padic_res = verify_padic_obstruction_certificate(
        a_mat,
        b_vec,
        cert["y"],
        p=p_val,
        s_bound=cert.get("s_bound"),
        inverted_primes=inv_primes,
    )
    padic_res["scope"] = scope
    padic_res["rows_independently_reconstructed"] = m_rows
    padic_res["gates_verified"] = n_cols
    return padic_res


# ---------------------------------------------------------------------------
# 9. Theorem A2c Verifier: Finite-Arrangement Integral Paramid Quotient SNF
# ---------------------------------------------------------------------------


def _enumerate_arrangement_chambers_zero_sum(
    n_dim: int,
    hyperplanes: Sequence[Sequence[int]],
    chamber_perms: Sequence[tuple[int, ...]] | None = None,
) -> list[tuple[tuple[int, ...], ConeState]]:
    """Enumerate all full-dimensional chambers `(base_perm, cone_state)` of a zero-sum arrangement `H_n >= B_n`."""
    braid_prims = {
        _primitive_canonical_vec([1 if k == i else (-1 if k == j else 0) for k in range(n_dim)])
        for i in range(n_dim)
        for j in range(i + 1, n_dim)
    }
    all_prims = {_primitive_canonical_vec(h) for h in hyperplanes if any(x != 0 for x in h)}
    for h_p in all_prims:
        if sum(h_p) != 0:
            raise AssertionError(f"Arrangement hyperplane {h_p} violates zero-sum lineality (<eta, 1> != 0)")
    missing_braid = braid_prims - all_prims
    if missing_braid:
        raise AssertionError("Arrangement H_n must contain all braid hyperplanes x_i - x_j == 0")

    off_braid = sorted(all_prims - braid_prims)
    perms = list(chamber_perms) if chamber_perms is not None else list(itertools.permutations(range(n_dim)))
    n_rays = n_dim - 1
    all_m = (1 << n_rays) - 1
    simp_m = [all_m ^ (1 << i) for i in range(n_rays)]

    chambers: list[tuple[tuple[int, ...], ConeState]] = []
    for perm in perms:
        c_rays: list[IntVector] = []
        for k in range(1, n_dim):
            r_pos = [0] * n_dim
            for idx in perm[k:]:
                r_pos[idx] = 1
            c_rays.append(r_pos)
        cones: list[ConeState] = [(c_rays, list(simp_m), n_rays)]
        for ob_h in off_braid:
            nxt_c: list[ConeState] = []
            for st_c in cones:
                status, st_p, st_n = _pointed_cone_split(st_c, ob_h)
                if status == "nonneg":
                    assert st_p is not None
                    nxt_c.append(st_p)
                elif status == "nonpos":
                    assert st_n is not None
                    nxt_c.append(st_n)
                else:
                    assert st_p is not None and st_n is not None
                    nxt_c.append(st_p)
                    nxt_c.append(st_n)
            cones = nxt_c
        for st_leaf in cones:
            chambers.append((perm, st_leaf))
    return chambers


def _verify_single_arrangement_snf(cert: dict[str, Any], ctx: str = "arrangement_snf") -> dict[str, Any]:
    snf_res = verify_snf_certificate(
        cert["A"],
        cert["U"],
        cert["U_inv"],
        cert["S"],
        cert["V"],
        cert["V_inv"],
        cert.get("invariant_factors"),
    )
    n_dim = assert_strict_int(cert["n_dim"], f"{ctx}.n_dim")
    if n_dim < 2:
        raise ValueError(f"{ctx}: n_dim must be >= 2")

    a_mat = assert_int_matrix(cert["A"], context=f"{ctx}.A")
    d_rows = len(a_mat)
    k_cols = len(a_mat[0]) if d_rows > 0 else 0

    hyperplanes = assert_int_matrix(cert["hyperplanes"], expected_cols=n_dim, context=f"{ctx}.hyperplanes")
    gates_raw = cert["gates"]
    if type(gates_raw) is not list or len(gates_raw) != k_cols:
        raise AssertionError(f"{ctx}: `gates` list length must match cols(A) == {k_cols}")
    compiled_gates = [compile_2layer_gate(g_sp, n_dim, f"{ctx}.gates[{j}]") for j, g_sp in enumerate(gates_raw)]

    sym_spec = cert.get("symmetry_group")
    sym_perms = _get_symmetry_group_perms(sym_spec, n_dim)
    if len(sym_perms) > 1:
        hp_set = {_primitive_canonical_vec(h) for h in hyperplanes if any(x != 0 for x in h)}
        for p in sym_perms:
            for h in hp_set:
                if _primitive_canonical_vec(_permute_vec(h, p)) not in hp_set:
                    raise AssertionError(f"{ctx}: arrangement H_{n_dim} is not invariant under symmetry_group")
        unseen_p = set(itertools.permutations(range(n_dim)))
        rep_perms: list[tuple[int, ...]] = []
        while unseen_p:
            rep = min(unseen_p)
            rep_perms.append(rep)
            for g in sym_perms:
                unseen_p.discard(tuple(rep[g[i]] for i in range(n_dim)))
        chambers = _enumerate_arrangement_chambers_zero_sum(n_dim, hyperplanes, chamber_perms=rep_perms)
    else:
        chambers = _enumerate_arrangement_chambers_zero_sum(n_dim, hyperplanes)

    m_chambers = len(chambers)
    # Verify EVERY gate has ZERO unmodeled kinks strictly inside any chamber of H_n, and extract chamber gradients!
    m_gates_grad = [[0] * k_cols for _ in range(n_dim * m_chambers)]
    for j_col, cg in enumerate(compiled_gates):
        slope_1 = eval_compiled_gate_int(cg, [1] * n_dim)
        if eval_compiled_gate_int(cg, [-1] * n_dim) != -slope_1:
            raise AssertionError(f"{ctx}: gate {j_col} failed lineality along (1,...,1)")
        for w, nrm in cg[1]:
            if w != 0 and sum(nrm) != 0:
                raise AssertionError(f"{ctx}: gate {j_col} has non-zero-sum Layer-1 hinge outside H_{n_dim}")
        for ow, ilin, ih in cg[2]:
            if ow != 0 and (sum(ilin) != 0 or any(aw != 0 and sum(anrm) != 0 for aw, anrm in ih)):
                raise AssertionError(f"{ctx}: gate {j_col} has non-zero-sum Layer-2 hinge outside H_{n_dim}")

        for c_idx, (perm_c, c_state) in enumerate(chambers):
            leaves_c, _ = _evaluate_compiled_gate_subcones(cg, c_state, n_dim)
            p0 = perm_c[0]
            ref_raw = leaves_c[0][0]
            # Reconstruct unique R^n gradient from slice `x_{p0} == 0` + global `<g, 1> == slope_1`:
            other_sum = sum(ref_raw[d_i] for d_i in range(n_dim) if d_i != p0)
            g_vec = [(slope_1 - other_sum) if d_i == p0 else ref_raw[d_i] for d_i in range(n_dim)]
            for leaf_g, _ in leaves_c[1:]:
                other_l = sum(leaf_g[d_i] for d_i in range(n_dim) if d_i != p0)
                g_l = [(slope_1 - other_l) if d_i == p0 else leaf_g[d_i] for d_i in range(n_dim)]
                if g_l != g_vec:
                    raise AssertionError(
                        f"{ctx}: gate {j_col} has unmodeled kink strictly cutting chamber {c_idx}: {g_vec} vs {g_l}"
                    )
            for d_i in range(n_dim):
                m_gates_grad[c_idx * n_dim + d_i][j_col] = g_vec[d_i]

    if cert.get("braid_boolean_basis", False):
        braid_count = (n_dim * (n_dim - 1)) // 2
        hp_prims = {_primitive_canonical_vec(h) for h in hyperplanes if any(x != 0 for x in h)}
        if len(hp_prims) != braid_count:
            raise AssertionError(f"{ctx}: braid_boolean_basis=True is valid ONLY on pure braid arrangement B_{n_dim}")
        if len(sym_perms) != 1:
            raise AssertionError(f"{ctx}: braid_boolean_basis=True requires unreduced B_{n_dim}")
        expected_d = (1 << n_dim) - 1
        if d_rows != expected_d:
            raise AssertionError(f"{ctx}: CPWL_{{B_{n_dim}}}(Z) rank must be {expected_d}, got {d_rows}")
        eval_vecs: list[IntVector] = [[1] * n_dim]
        for mask in range(1, (1 << n_dim) - 1):
            eval_vecs.append([(mask >> d_i) & 1 for d_i in range(n_dim)])
        a_bool = [[eval_compiled_gate_int(compiled_gates[j], pt) for j in range(k_cols)] for pt in eval_vecs]
        if "basis_change_P" in cert and "basis_change_P_inv" in cert:
            p_m = assert_int_matrix(cert["basis_change_P"], expected_rows=d_rows, expected_cols=d_rows, context=f"{ctx}.P")
            p_inv = assert_int_matrix(cert["basis_change_P_inv"], expected_rows=d_rows, expected_cols=d_rows, context=f"{ctx}.P_inv")
            eye_d = mat_eye(d_rows)
            if mat_mul(p_m, p_inv) != eye_d or mat_mul(p_inv, p_m) != eye_d:
                raise AssertionError(f"{ctx}: basis_change_P is not unimodular")
            if mat_mul(p_m, a_bool) != a_mat:
                raise AssertionError(f"{ctx}: P @ A_bool != A")
        else:
            if a_bool != a_mat:
                raise AssertionError(f"{ctx}: A does not match canonical boolean basis evaluation on B_{n_dim}")
    elif "basis_chamber_gradients" in cert and "basis_left_inverse" in cert:
        b_basis = assert_int_matrix(
            cert["basis_chamber_gradients"],
            expected_rows=n_dim * m_chambers,
            expected_cols=d_rows,
            context=f"{ctx}.basis_chamber_gradients",
        )
        l_inv = assert_int_matrix(
            cert["basis_left_inverse"],
            expected_rows=d_rows,
            expected_cols=n_dim * m_chambers,
            context=f"{ctx}.basis_left_inverse",
        )
        if mat_mul(l_inv, b_basis) != mat_eye(d_rows):
            raise AssertionError(f"{ctx}: basis_left_inverse @ basis_chamber_gradients != I_{d_rows} (not Z-saturated)")
        if mat_mul(b_basis, a_mat) != m_gates_grad:
            raise AssertionError(f"{ctx}: basis_chamber_gradients @ A != true chamber-gradient matrix of gates")

        # Verify continuity of every basis column across shared rays & (1,...,1) lineality!
        ray_owner: dict[tuple[int, ...], int] = {}
        cont_rows: IntMatrix = []
        for c_idx, (_, c_state) in enumerate(chambers):
            c_rays = c_state[0]
            if c_idx > 0:
                # Lineality: <g_c - g_0, 1> == 0
                row_lin = [0] * (n_dim * m_chambers)
                for d_i in range(n_dim):
                    row_lin[d_i] = -1
                    row_lin[c_idx * n_dim + d_i] = 1
                cont_rows.append(row_lin)
            for r_vec in c_rays:
                r_key = _primitive_canonical_vec(r_vec)
                if r_key not in ray_owner:
                    ray_owner[r_key] = c_idx
                else:
                    owner = ray_owner[r_key]
                    if owner != c_idx:
                        row_r = [0] * (n_dim * m_chambers)
                        for d_i in range(n_dim):
                            row_r[owner * n_dim + d_i] = -r_key[d_i]
                            row_r[c_idx * n_dim + d_i] = r_key[d_i]
                        cont_rows.append(row_r)
                # If symmetry_group active, also enforce G-invariance `<g_c, sigma(r)> == <g_{c'}, r>` via ray orbits:
                if len(sym_perms) > 1:
                    for p in sym_perms:
                        pr = _permute_vec(list(r_key), p)
                        pr_key = _primitive_canonical_vec(pr)
                        if pr_key in ray_owner:
                            owner_p = ray_owner[pr_key]
                            row_sym = [0] * (n_dim * m_chambers)
                            for d_i in range(n_dim):
                                row_sym[c_idx * n_dim + d_i] += r_key[d_i]
                                row_sym[owner_p * n_dim + d_i] -= pr[d_i]
                            if any(v != 0 for v in row_sym):
                                cont_rows.append(row_sym)

        if cont_rows:
            chk_zero = mat_mul(cont_rows, b_basis)
            if chk_zero != mat_zeros(len(cont_rows), d_rows):
                raise AssertionError(f"{ctx}: basis_chamber_gradients violates CPWL wall continuity or G-invariance")
            if len(sym_perms) == 1 and (n_dim * m_chambers) <= 1800:
                q_nullity = (n_dim * m_chambers) - exact_q_rank_bareiss(cont_rows)
                if q_nullity != d_rows:
                    raise AssertionError(
                        f"{ctx}: basis rank {d_rows} != true Q-dimension {q_nullity} of CPWL_{{H_{n_dim}}}(Z)"
                    )
    else:
        raise AssertionError(
            f"{ctx}: requires `braid_boolean_basis=True` or (`basis_chamber_gradients`, `basis_left_inverse`)"
        )

    out = dict(snf_res)
    out["n_dim"] = n_dim
    out["chambers_checked"] = m_chambers
    out["gates_verified"] = k_cols
    out["quotient_free_corank"] = d_rows - int(snf_res["rank"])
    return out


def verify_arrangement_paramid_snf_certificate(cert: dict[str, Any]) -> dict[str, Any]:
    """Theorem A2c verifier: unimodular SNF + zero-trust CPWL_{H_n}(Z) basis & gate-column verification."""
    if "arrangement_cases" in cert:
        cases = cert["arrangement_cases"]
        if type(cases) is not list or len(cases) == 0:
            raise AssertionError("Empty `arrangement_cases` list")
        res_list = [_verify_single_arrangement_snf(c, f"arrangement_cases[{i}]") for i, c in enumerate(cases)]
        return {"verified": True, "kind": "arrangement_snf_batch", "cases_verified": len(res_list), "results": res_list}
    return _verify_single_arrangement_snf(cert, "arrangement_snf")


# ---------------------------------------------------------------------------
# 10. Theorem D4a & D4b Verifiers: Group Axioms, 2-Cocycles & `{0,1}` Bounds
# ---------------------------------------------------------------------------


def verify_group_axioms(cayley: Sequence[Sequence[int]]) -> dict[str, Any]:
    """Exhaustively verify finite group axioms (closure, unique identity, two-sided inverses, associativity)."""
    tbl = assert_int_matrix(cayley, context="group_cayley")
    n = len(tbl)
    if n == 0 or len(tbl[0]) != n:
        raise ValueError("Cayley table must be non-empty square matrix")
    for i in range(n):
        for j in range(n):
            v = tbl[i][j]
            if v < 0 or v >= n:
                raise AssertionError(f"Cayley entry out of range [0, {n-1}] at ({i},{j}): {v}")

    id_cands = [e for e in range(n) if all(tbl[e][x] == x and tbl[x][e] == x for x in range(n))]
    if len(id_cands) != 1:
        raise AssertionError(f"Group axiom failed: expected unique identity, found {id_cands}")
    e_id = id_cands[0]

    for x in range(n):
        invs = [y for y in range(n) if tbl[x][y] == e_id and tbl[y][x] == e_id]
        if len(invs) != 1:
            raise AssertionError(f"Group axiom failed: element {x} lacks unique two-sided inverse")

    for x in range(n):
        tx = tbl[x]
        for y in range(n):
            xy = tx[y]
            txy = tbl[xy]
            ty = tbl[y]
            for z in range(n):
                if txy[z] != tx[ty[z]]:
                    raise AssertionError(f"Associativity failed at ({x},{y},{z}): ({x}*{y})*{z} != {x}*({y}*{z})")

    return {"verified": True, "order": n, "identity": e_id}


def build_canonical_group_cayley(group_name: str) -> IntMatrix:
    """Independently construct exact Cayley tables of `C_n`, `V_4`, `S_3`, `D_4`, `Q_8`, and `Dic_3` (order 12)."""
    nm = group_name.strip()
    if nm.startswith("C_") and nm[2:].isdigit():
        n_c = int(nm[2:])
        if n_c < 1:
            raise ValueError(f"Invalid cyclic order {n_c}")
        return [[(i + j) % n_c for j in range(n_c)] for i in range(n_c)]
    if nm == "V_4":
        return [[i ^ j for j in range(4)] for i in range(4)]
    if nm == "S_3":
        perms = sorted(itertools.permutations(range(3)))
        idx = {p: i for i, p in enumerate(perms)}
        return [[idx[tuple(p[q[k]] for k in range(3))] for q in perms] for p in perms]
    if nm == "D_4":
        # Elements (r in 0..3, s in 0..1) representing a^r b^s with a^4=1, b^2=1, b a b = a^{-1}
        elems = [(r, s) for s in (0, 1) for r in range(4)]
        idx_d4 = {el: i for i, el in enumerate(elems)}
        out_d4 = [[0] * 8 for _ in range(8)]
        for i, (r1, s1) in enumerate(elems):
            for j, (r2, s2) in enumerate(elems):
                r_out = (r1 + r2) % 4 if s1 == 0 else (r1 - r2) % 4
                out_d4[i][j] = idx_d4[(r_out, s1 ^ s2)]
        return out_d4
    if nm == "Q_8":
        # Elements (s in {0,1}, u in {0=1, 1=i, 2=j, 3=k}) representing (-1)^s e_u
        elems_q8 = [(s, u) for u in range(4) for s in (0, 1)]
        idx_q8 = {el: i for i, el in enumerate(elems_q8)}
        beta_q8 = [
            [0, 0, 0, 0],
            [0, 1, 0, 1],
            [0, 1, 1, 0],
            [0, 0, 1, 1],
        ]
        out_q8 = [[0] * 8 for _ in range(8)]
        for i, (s1, u1) in enumerate(elems_q8):
            for j, (s2, u2) in enumerate(elems_q8):
                out_q8[i][j] = idx_q8[(s1 ^ s2 ^ beta_q8[u1][u2], u1 ^ u2)]
        return out_q8
    if nm in ("Dic_3", "T_12"):
        # Dicyclic group of order 12: <a, x | a^6 = 1, x^2 = a^3, x^{-1} a x = a^{-1}>
        elems_dic = [(k, t) for t in (0, 1) for k in range(6)]
        idx_dic = {el: i for i, el in enumerate(elems_dic)}
        out_dic = [[0] * 12 for _ in range(12)]
        for i, (k1, t1) in enumerate(elems_dic):
            for j, (k2, t2) in enumerate(elems_dic):
                if t1 == 0:
                    el_prod = ((k1 + k2) % 6, t2)
                elif t2 == 0:
                    el_prod = ((k1 - k2) % 6, 1)
                else:
                    el_prod = ((k1 - k2 + 3) % 6, 0)
                out_dic[i][j] = idx_dic[el_prod]
        return out_dic
    if nm == "Q_16":
        # Generalized quaternion group of order 16: <a, x | a^8 = 1, x^2 = a^4, x^{-1} a x = a^{-1}>
        elems_q16 = [(k, t) for t in (0, 1) for k in range(8)]
        idx_q16 = {el: i for i, el in enumerate(elems_q16)}
        out_q16 = [[0] * 16 for _ in range(16)]
        for i, (k1, t1) in enumerate(elems_q16):
            for j, (k2, t2) in enumerate(elems_q16):
                if t1 == 0:
                    el_prod = ((k1 + k2) % 8, t2)
                elif t2 == 0:
                    el_prod = ((k1 - k2) % 8, 1)
                else:
                    el_prod = ((k1 - k2 + 4) % 8, 0)
                out_q16[i][j] = idx_q16[el_prod]
        return out_q16
    raise ValueError(f"Unsupported canonical group name {group_name!r}")


def find_group_isomorphism(
    cayley1: Sequence[Sequence[int]],
    cayley2: Sequence[Sequence[int]],
) -> IntVector | None:
    """Find an explicit group isomorphism `pi: G_1 -> G_2` (`pi[x *_1 y] == pi[x] *_2 pi[y]`), or return `None`."""
    ax1 = verify_group_axioms(cayley1)
    ax2 = verify_group_axioms(cayley2)
    n = int(ax1["order"])
    if int(ax2["order"]) != n:
        return None
    t1 = assert_int_matrix(cayley1, n, n)
    t2 = assert_int_matrix(cayley2, n, n)
    e1 = int(ax1["identity"])
    e2 = int(ax2["identity"])
    if n == 1:
        return [0]

    # Find small generating set `gens` of G_1 greedily:
    gens: list[int] = []
    closure = {e1}
    while len(closure) < n:
        best_g = -1
        best_sz = len(closure)
        for cand in range(n):
            if cand in closure:
                continue
            cur = set(closure) | {cand}
            stack = list(cur)
            while stack:
                x = stack.pop()
                for y in list(cur):
                    for prod in (t1[x][y], t1[y][x]):
                        if prod not in cur:
                            cur.add(prod)
                            stack.append(prod)
            if len(cur) > best_sz:
                best_sz = len(cur)
                best_g = cand
        assert best_g >= 0
        gens.append(best_g)
        cur = set(closure) | {best_g}
        stack = list(cur)
        while stack:
            x = stack.pop()
            for y in list(cur):
                for prod in (t1[x][y], t1[y][x]):
                    if prod not in cur:
                        cur.add(prod)
                        stack.append(prod)
        closure = cur

    def elem_order(tbl: IntMatrix, e_idx: int, x: int) -> int:
        cur_x = x
        k = 1
        while cur_x != e_idx:
            cur_x = tbl[cur_x][x]
            k += 1
        return k

    ord1 = [elem_order(t1, e1, x) for x in range(n)]
    ord2 = [elem_order(t2, e2, y) for y in range(n)]
    cand_lists = [[y for y in range(n) if ord2[y] == ord1[g]] for g in gens]

    for img_tuple in itertools.product(*cand_lists):
        if len(set(img_tuple)) != len(img_tuple):
            continue
        mapping: dict[int, int] = {e1: e2}
        ok = True
        for g_src, g_dst in zip(gens, img_tuple):
            mapping[g_src] = g_dst
        queue = list(mapping.keys())
        used_targets = set(mapping.values())
        while queue and ok:
            u = queue.pop()
            u_img = mapping[u]
            for g_src, g_dst in zip(gens, img_tuple):
                v = t1[u][g_src]
                v_img = t2[u_img][g_dst]
                if v in mapping:
                    if mapping[v] != v_img:
                        ok = False
                        break
                else:
                    if v_img in used_targets:
                        ok = False
                        break
                    mapping[v] = v_img
                    used_targets.add(v_img)
                    queue.append(v)
        if not ok or len(mapping) != n:
            continue
        pi = [mapping[i] for i in range(n)]
        full_hom = True
        for x in range(n):
            px = pi[x]
            for y in range(n):
                if pi[t1[x][y]] != t2[px][pi[y]]:
                    full_hom = False
                    break
            if not full_hom:
                break
        if full_hom:
            return pi
    return None


def verify_central_extension_cocycle_certificate(cert: dict[str, Any]) -> dict[str, Any]:
    """Theorem D4a Cohomology Verifier: verify 2-cocycle `beta in Z^2(Q; Z_m)`, non-triviality `[beta] != 0 in H^2`,
    and central extension isomorphism `1 -> Z_m -> E_beta -> Q -> 1`.
    """
    q_cay = assert_int_matrix(cert["quotient_cayley"], context="quotient_cayley")
    q_ax = verify_group_axioms(q_cay)
    q_ord = int(q_ax["order"])
    e_q = int(q_ax["identity"])

    m_mod = assert_strict_int(cert.get("central_modulus", 2), "central_modulus")
    if m_mod < 2:
        raise ValueError("central_modulus must be >= 2")

    beta = assert_int_matrix(cert["cocycle_beta"], expected_rows=q_ord, expected_cols=q_ord, context="cocycle_beta")
    for u in range(q_ord):
        for v in range(q_ord):
            if beta[u][v] < 0 or beta[u][v] >= m_mod:
                raise AssertionError(f"cocycle_beta[{u}][{v}]={beta[u][v]} outside [0, {m_mod - 1}]")

    if cert.get("require_normalized", True):
        for u in range(q_ord):
            if beta[e_q][u] != 0 or beta[u][e_q] != 0:
                raise AssertionError("2-cocycle failed normalization beta(e, u) == beta(u, e) == 0")

    # Verify exact 2-cocycle identity: beta(x, y) + beta(xy, z) == beta(y, z) + beta(x, yz) (mod m_mod)
    for x in range(q_ord):
        for y in range(q_ord):
            xy = q_cay[x][y]
            b_xy = beta[x][y]
            for z in range(q_ord):
                yz = q_cay[y][z]
                lhs = (b_xy + beta[xy][z]) % m_mod
                rhs = (beta[y][z] + beta[x][yz]) % m_mod
                if lhs != rhs:
                    raise AssertionError(f"2-cocycle condition violated at ({x},{y},{z}): {lhs} != {rhs} mod {m_mod}")

    # Exhaustively decide coboundary triviality `[beta] == 0 in H^2(Q; Z_m)` across all normalized 1-cochains alpha:
    non_id_elems = [u for u in range(q_ord) if u != e_q]
    search_space = m_mod ** len(non_id_elems)
    if search_space > 65536:
        raise ValueError(f"1-cochain search space {search_space} exceeds exhaustive threshold")
    is_coboundary = False
    for vals in itertools.product(range(m_mod), repeat=len(non_id_elems)):
        alpha = [0] * q_ord
        for u_idx, val in zip(non_id_elems, vals):
            alpha[u_idx] = val
        match_all = True
        for x in range(q_ord):
            for y in range(q_ord):
                d_alpha = (alpha[x] + alpha[y] - alpha[q_cay[x][y]]) % m_mod
                if d_alpha != beta[x][y]:
                    match_all = False
                    break
            if not match_all:
                break
        if match_all:
            is_coboundary = True
            break

    expect_nontrivial = bool(cert.get("expect_nontrivial_cohomology", True))
    if expect_nontrivial and is_coboundary:
        raise AssertionError("2-cocycle beta is a coboundary ([beta] == 0 in H^2); expected non-trivial class!")
    if (not expect_nontrivial) and (not is_coboundary):
        raise AssertionError("2-cocycle beta is cohomologically non-trivial, contradicting expect_nontrivial=False")

    # Build extension group E_beta on Z_m x Q (order m_mod * q_ord):
    ext_elems = [(s, u) for u in range(q_ord) for s in range(m_mod)]
    ext_idx = {el: idx for idx, el in enumerate(ext_elems)}
    ext_n = len(ext_elems)
    ext_cay = [[0] * ext_n for _ in range(ext_n)]
    for i, (s1, u1) in enumerate(ext_elems):
        for j, (s2, u2) in enumerate(ext_elems):
            ext_cay[i][j] = ext_idx[((s1 + s2 + beta[u1][u2]) % m_mod, q_cay[u1][u2])]
    verify_group_axioms(ext_cay)

    if "expected_quotient_group" in cert and cert["expected_quotient_group"] is not None:
        q_canon = build_canonical_group_cayley(str(cert["expected_quotient_group"]))
        if find_group_isomorphism(q_cay, q_canon) is None:
            raise AssertionError("quotient_cayley is not isomorphic to expected_quotient_group")

    if "extension_cayley" in cert and cert["extension_cayley"] is not None:
        claim_ext = assert_int_matrix(cert["extension_cayley"], expected_rows=ext_n, expected_cols=ext_n)
        if find_group_isomorphism(ext_cay, claim_ext) is None:
            raise AssertionError("extension_cayley is not isomorphic to E_beta")

    if "expected_extension_group" in cert and cert["expected_extension_group"] is not None:
        e_canon = build_canonical_group_cayley(str(cert["expected_extension_group"]))
        if find_group_isomorphism(ext_cay, e_canon) is None:
            raise AssertionError(f"E_beta is not isomorphic to {cert['expected_extension_group']}")

    return {
        "verified": True,
        "quotient_order": q_ord,
        "central_modulus": m_mod,
        "extension_order": ext_n,
        "cohomologically_nontrivial": not is_coboundary,
        "extension_cayley": ext_cay,
    }


def _verify_single_group_indicator_bounds(item: dict[str, Any], ctx: str = "group_bounds") -> dict[str, Any]:
    if "cayley" in item:
        cayley = assert_int_matrix(item["cayley"], context=f"{ctx}.cayley")
    elif "group_name" in item:
        cayley = build_canonical_group_cayley(str(item["group_name"]))
    else:
        raise AssertionError(f"{ctx}: requires `cayley` or `group_name`")

    verify_group_axioms(cayley)
    n = len(cayley)
    if "group_name" in item and item["group_name"] is not None and "cayley" in item:
        g_nm = str(item["group_name"])
        if g_nm in ("C_3", "C_4", "C_5", "C_6", "V_4", "S_3", "D_4", "Q_8", "Dic_3", "Q_16"):
            if find_group_isomorphism(cayley, build_canonical_group_cayley(g_nm)) is None:
                raise AssertionError(f"{ctx}: cayley not isomorphic to canonical {g_nm}")

    # Construct I_mult in {0,1}^{|G|^2 x |G|} directly from first principles:
    i_mult: IntMatrix = []
    for g in range(n):
        for h in range(n):
            tgt = cayley[g][h]
            i_mult.append([1 if c == tgt else 0 for c in range(n)])

    gram = mat_mul(mat_transpose(i_mult), i_mult)
    expected_gram = [[n if i == j else 0 for j in range(n)] for i in range(n)]
    if gram != expected_gram:
        raise AssertionError(f"{ctx}: I_mult^T @ I_mult != |G| * I_{{|G|}}")

    det_gram = exact_det_bareiss(gram)
    expected_det = n ** n
    if det_gram != expected_det:
        raise AssertionError(f"{ctx}: Bareiss det(I_mult^T I_mult)={det_gram} != |G|^|G|={expected_det}")

    if "expected_gram_det" in item and item["expected_gram_det"] is not None:
        if assert_strict_int(item["expected_gram_det"], f"{ctx}.expected_gram_det") != det_gram:
            raise AssertionError(f"{ctx}: expected_gram_det mismatch")

    unbiased_lb = exact_q_rank_bareiss(i_mult)
    r0 = i_mult[0]
    centered = [[i_mult[r][c] - r0[c] for c in range(n)] for r in range(1, n * n)]
    biased_lb = exact_q_rank_bareiss(centered)
    if unbiased_lb != n or biased_lb != n - 1:
        raise AssertionError(f"{ctx}: rank lower bounds ({biased_lb}, {unbiased_lb}) != ({n - 1}, {n})")

    circuits_verified: list[dict[str, Any]] = []
    for c_idx, c_cert in enumerate(item.get("circuits", [])):
        merged = dict(c_cert)
        if "cayley" not in merged:
            merged["cayley"] = cayley
        res_c = verify_group_circuit_certificate(merged)
        w_c = int(res_c["width"])
        if merged.get("zero_bias", False):
            if w_c < unbiased_lb:
                raise AssertionError(f"{ctx}.circuits[{c_idx}]: width {w_c} violated zero-bias rank lower bound {unbiased_lb}")
        else:
            if w_c < biased_lb:
                raise AssertionError(f"{ctx}.circuits[{c_idx}]: width {w_c} violated biased rank lower bound {biased_lb}")
        circuits_verified.append(res_c)

    return {
        "verified": True,
        "group_order": n,
        "gram_det": det_gram,
        "biased_rank_lower_bound": biased_lb,
        "zero_bias_rank_lower_bound": unbiased_lb,
        "circuits_verified": len(circuits_verified),
    }


def verify_group_indicator_bounds_certificate(cert: dict[str, Any]) -> dict[str, Any]:
    """Theorem D4b verifier: Bareiss `det(I_mult^T I_mult) == |G|^{|G|}`, universal rank bounds, and minimal circuits."""
    list_key = "indicator_bound_groups" if "indicator_bound_groups" in cert else ("groups" if "groups" in cert else None)
    if list_key is not None:
        grp_list = cert[list_key]
        if type(grp_list) is not list or len(grp_list) == 0:
            raise AssertionError(f"Empty {list_key} in group indicator bounds certificate")
        res_all = [_verify_single_group_indicator_bounds(g_it, f"{list_key}[{i}]") for i, g_it in enumerate(grp_list)]
        return {"verified": True, "kind": "group_indicator_bounds_batch", "groups_verified": len(res_all), "results": res_all}
    return _verify_single_group_indicator_bounds(cert, "group_indicator_bounds")


def verify_ledger_certificate(
    cert: Any,
    claim_id: str = "",
    epistemic_tag: str | None = None,
) -> dict[str, Any]:
    """Universal zero-trust certificate verifier dispatching any `CERTIFICATE_SCHEMA_V1` / `V2` object."""
    if type(cert) is not dict or len(cert) == 0:
        raise AssertionError(f"Claim `{claim_id}` missing non-empty `certificate` dict")

    # 1. Recursive composite bundle (`sub_certificates` list or dict)
    if "sub_certificates" in cert:
        subs = cert["sub_certificates"]
        if type(subs) is list:
            if len(subs) == 0:
                raise AssertionError(f"Claim `{claim_id}` has empty sub_certificates list")
            sub_res = [
                verify_ledger_certificate(
                    sc,
                    f"{claim_id}[{i}]",
                    epistemic_tag=sc.get("epistemic_tag", epistemic_tag) if type(sc) is dict else epistemic_tag,
                )
                for i, sc in enumerate(subs)
            ]
            return {"verified": True, "kind": "composite_list", "count": len(sub_res)}
        if type(subs) is dict:
            if len(subs) == 0:
                raise AssertionError(f"Claim `{claim_id}` has empty sub_certificates dict")
            sub_map = {
                k: verify_ledger_certificate(
                    sc,
                    f"{claim_id}.{k}",
                    epistemic_tag=sc.get("epistemic_tag", epistemic_tag) if type(sc) is dict else epistemic_tag,
                )
                for k, sc in subs.items()
            }
            return {"verified": True, "kind": "composite_dict", "count": len(sub_map)}
        raise AssertionError(f"Claim `{claim_id}` invalid sub_certificates container")

    # 2. Explicit Wave II `cert_type` dispatch
    c_type = cert.get("cert_type")
    if c_type == "zonotope_join_volume":
        return verify_zonotope_join_volume_certificate(cert)
    if c_type == "max6_z_half_primal":
        return verify_max6_primal_z_half_certificate(cert)
    if c_type == "max6_padic_dual":
        return verify_max6_dual_padic_certificate(cert, epistemic_tag=epistemic_tag)
    if c_type == "arrangement_paramid_snf":
        return verify_arrangement_paramid_snf_certificate(cert)
    if c_type == "central_extension_cocycle":
        return verify_central_extension_cocycle_certificate(cert)
    if c_type == "group_indicator_bounds":
        return verify_group_indicator_bounds_certificate(cert)
    if c_type == "group_circuit":
        return verify_group_circuit_certificate(cert)

    # 3. Structural Wave II signatures (checked BEFORE Wave I fallbacks so richer witnesses are never skipped!)
    if "join_cases" in cert or (all(k in cert for k in ("d_dim", "r1", "r2", "expected_volume"))):
        return verify_zonotope_join_volume_certificate(cert)

    if "arrangement_cases" in cert or (
        all(k in cert for k in ("A", "U", "U_inv", "S", "V", "V_inv", "hyperplanes", "gates"))
    ):
        return verify_arrangement_paramid_snf_certificate(cert)

    if ("t_exp" in cert or "pow2_denom" in cert) and "gates" in cert and "coeffs_z" in cert:
        return verify_max6_primal_z_half_certificate(cert)

    if "tiers" in cert or (
        all(k in cert for k in ("A", "b", "y", "p"))
        and "gates" in cert
        and ("row_specs" in cert or "eval_points" in cert)
    ):
        return verify_max6_dual_padic_certificate(cert, epistemic_tag=epistemic_tag)

    if "quotient_cayley" in cert and "cocycle_beta" in cert:
        return verify_central_extension_cocycle_certificate(cert)

    if "indicator_bound_groups" in cert or (
        ("cayley" in cert or "group_name" in cert) and cert.get("check_gram_det", False)
    ):
        return verify_group_indicator_bounds_certificate(cert)

    # 4. Unimodular SNF (Wave I + general)
    if all(k in cert for k in ("A", "U", "U_inv", "S", "V", "V_inv")):
        return verify_snf_certificate(
            cert["A"],
            cert["U"],
            cert["U_inv"],
            cert["S"],
            cert["V"],
            cert["V_inv"],
            cert.get("invariant_factors"),
        )

    # 5. Ghrist-Ding integer saturation projector
    if all(k in cert for k in ("A", "P_sat", "Q_free")):
        return verify_saturation_projector(
            cert["A"],
            cert["P_sat"],
            cert["Q_free"],
            u=cert.get("U"),
            u_inv=cert.get("U_inv"),
            rank=cert.get("rank"),
        )

    # 6. Farkas inequality / equality duals
    if all(k in cert for k in ("A_ub", "b_ub", "y")):
        return verify_farkas_le_certificate(cert["A_ub"], cert["b_ub"], cert["y"])
    if all(k in cert for k in ("A_eq", "b_eq")) and ("y_signed" in cert or "y" in cert):
        y_s = cert["y_signed"] if "y_signed" in cert else cert["y"]
        return verify_farkas_equality_certificate(cert["A_eq"], cert["b_eq"], y_s)

    # 7. p-adic valuation obstruction
    if all(k in cert for k in ("A", "b", "y", "p")):
        if bool(cert.get("unconstrained", False)) and epistemic_tag == "CERTIFIED_EXACT":
            raise AssertionError("Epistemic guardrail: unconstrained p-adic UNSAT without universal proof must be OPEN_BUDGET_EXCEEDED")
        return verify_padic_obstruction_certificate(
            cert["A"],
            cert["b"],
            cert["y"],
            p=cert["p"],
            s_bound=cert.get("s_bound"),
            inverted_primes=cert.get("inverted_primes", ()),
        )

    # 8. Chvatal-Gomory cuts
    if "cuts" in cert and (("A_ge" in cert and "b_ge" in cert) or ("A_ub" in cert and "b_ub" in cert)):
        return verify_cg_cuts_certificate(cert)

    # 9. Simplex triangulation volume
    if "simplices" in cert and "expected_volume" in cert:
        return verify_simplex_triangulation_volume_certificate(
            cert["simplices"],
            cert["expected_volume"],
            cert.get("modulus"),
            cert.get("expected_mod_residue"),
        )

    # 10. Poincare trajectory / counterexample
    if "segments" in cert:
        return verify_poincare_trajectory_certificate(cert)

    # 11. Finite-group ReLU circuit (Z or Q)
    if "cayley" in cert and (("W1" in cert and "W2" in cert) or ("W_in" in cert and "W_out" in cert)):
        return verify_group_circuit_certificate(cert)

    # 12. Eisenstein polynomial irreducibility
    if "poly_coeffs_low_to_high" in cert and "prime" in cert:
        return verify_eisenstein_certificate(cert["poly_coeffs_low_to_high"], cert["prime"])

    # 13. Feedforward homogeneous ReLU network universal identity
    if all(k in cert for k in ("W1", "W2", "w_out", "out_denom", "n_dim")):
        n_d = assert_strict_int(cert["n_dim"], "n_dim")
        tgt_expr = SymbolicCPWL.coord(n_d, 0)
        for idx_c in range(1, n_d):
            tgt_expr = SymbolicCPWL.max2(tgt_expr, SymbolicCPWL.coord(n_d, idx_c))
        tgt_scale = assert_strict_int(cert.get("target_scale", 1), "target_scale")
        if tgt_scale != 1:
            tgt_expr = SymbolicCPWL.scale(tgt_scale, 1, tgt_expr)
        return verify_feedforward_relu_network_homogeneous(
            cert["W1"], cert["W2"], cert["w_out"], cert["out_denom"], tgt_expr
        )

    # 14. Exact linear dictionary realization (`A @ c_num == c_den * b`)
    if all(k in cert for k in ("A", "b")) and ("c_num" in cert or "x_num" in cert):
        return verify_linear_realization_certificate(cert)

    raise AssertionError(f"Claim `{claim_id}` has unrecognized certificate schema keys: {sorted(cert.keys())}")

