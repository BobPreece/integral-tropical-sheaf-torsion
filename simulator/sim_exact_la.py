from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple


def igcd(a: int, b: int) -> int:
    return math.gcd(a, b)


def ilcm(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    return abs(a * b) // math.gcd(a, b)


def vec_gcd(v: Sequence[int]) -> int:
    g = 0
    for x in v:
        g = math.gcd(g, x)
        if g == 1:
            return 1
    return g


def prim_vec(v: Sequence[int]) -> Tuple[int, ...]:
    g = vec_gcd(v)
    if g <= 1:
        return tuple(int(x) for x in v)
    return tuple(int(x) // g for x in v)


def ext_gcd(a: int, b: int) -> Tuple[int, int, int]:
    """Return (g, x, y) with g = gcd(a, b) >= 0 and a*x + b*y = g."""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    if old_r < 0:
        return -old_r, -old_s, -old_t
    return old_r, old_s, old_t


def rat_norm(num: int, den: int) -> Tuple[int, int]:
    if den == 0:
        raise ZeroDivisionError("Zero denominator in exact rational")
    if den < 0:
        num = -num
        den = -den
    if num == 0:
        return 0, 1
    g = math.gcd(num, den)
    return num // g, den // g


def rat_str(num: int, den: int) -> str:
    n, d = rat_norm(num, den)
    if d == 1:
        return str(n)
    return f"{n}/{d}"


def ceil_div(num: int, den: int) -> int:
    """Exact ceil(num / den) using integer floor division only."""
    if den < 0:
        num = -num
        den = -den
    return -((-num) // den)


def int_bit_length(x: int) -> int:
    return abs(x).bit_length()


def matrix_max_bit_length(mat: Sequence[Sequence[int]]) -> int:
    best = 0
    for row in mat:
        for val in row:
            bl = abs(val).bit_length()
            if bl > best:
                best = bl
    return best


def mat_eye(n: int) -> List[List[int]]:
    out = [[0] * n for _ in range(n)]
    for i in range(n):
        out[i][i] = 1
    return out


def mat_transpose(A: Sequence[Sequence[int]]) -> List[List[int]]:
    if not A:
        return []
    m = len(A)
    n = len(A[0])
    return [[A[i][j] for i in range(m)] for j in range(n)]


def mat_mul(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]]) -> List[List[int]]:
    """Zero-skipping exact integer matrix multiplication."""
    if not A or not B:
        return []
    m = len(A)
    k_len = len(A[0])
    n = len(B[0])
    out = [[0] * n for _ in range(m)]
    for i in range(m):
        row_a = A[i]
        row_out = out[i]
        for k in range(k_len):
            aik = row_a[k]
            if aik != 0:
                row_b = B[k]
                for j in range(n):
                    b_kj = row_b[j]
                    if b_kj != 0:
                        row_out[j] += aik * b_kj
    return out


def mat_vec_mul(A: Sequence[Sequence[int]], x: Sequence[int]) -> List[int]:
    out: List[int] = []
    for row in A:
        acc = 0
        for a, xv in zip(row, x):
            if a != 0 and xv != 0:
                acc += a * xv
        out.append(acc)
    return out


def mat_eq(A: Sequence[Sequence[int]], B: Sequence[Sequence[int]]) -> bool:
    if len(A) != len(B):
        return False
    for ra, rb in zip(A, B):
        if len(ra) != len(rb):
            return False
        for a, b in zip(ra, rb):
            if a != b:
                return False
    return True


def is_identity(A: Sequence[Sequence[int]], n: int) -> bool:
    if len(A) != n:
        return False
    for i in range(n):
        row = A[i]
        if len(row) != n:
            return False
        for j in range(n):
            expected = 1 if i == j else 0
            if row[j] != expected:
                return False
    return True


@dataclass(frozen=True)
class SNFCertificate:
    m: int
    n: int
    rank: int
    invariant_factors: Tuple[int, ...]
    torsion_factors: Tuple[int, ...]
    S: List[List[int]]
    U: List[List[int]]
    U_inv: List[List[int]]
    V: List[List[int]]
    V_inv: List[List[int]]
    input_max_bits: int
    u_max_bits: int
    v_max_bits: int
    peak_intermediate_bits: int


def snf_unimodular(
    A_in: Sequence[Sequence[int]],
    verify: bool = True,
) -> SNFCertificate:
    """
    Compute exact unimodular Smith Normal Form U * A * V = S over Z using:
      1. DHSW Markowitz unit-pivot (+-1) peeling,
      2. Smallest-pivot Markowitz Euclidean row/col diagonalization,
      3. Exact 2x2 Bezout diagonal divisibility normalization d_1 | d_2 | ... | d_r.
    Tracks U, U_inv in GL_m(Z) and V, V_inv in GL_n(Z) and asserts exactness.
    """
    m = len(A_in)
    n = len(A_in[0]) if m > 0 else 0
    B = [[int(x) for x in row] for row in A_in]
    U = mat_eye(m)
    U_inv = mat_eye(m)
    V = mat_eye(n)
    V_inv = mat_eye(n)

    input_bits = matrix_max_bit_length(B)
    peak_bits = input_bits

    def swap_rows(i: int, j: int) -> None:
        if i == j:
            return
        B[i], B[j] = B[j], B[i]
        U[i], U[j] = U[j], U[i]
        for r in range(m):
            U_inv[r][i], U_inv[r][j] = U_inv[r][j], U_inv[r][i]

    def neg_row(i: int) -> None:
        row_b = B[i]
        for c in range(n):
            row_b[c] = -row_b[c]
        row_u = U[i]
        for c in range(m):
            row_u[c] = -row_u[c]
        for r in range(m):
            U_inv[r][i] = -U_inv[r][i]

    def add_row(dst: int, src: int, q: int) -> None:
        """B[dst] += q * B[src]"""
        if q == 0:
            return
        nonlocal peak_bits
        row_dst = B[dst]
        row_src = B[src]
        for c in range(n):
            sc = row_src[c]
            if sc != 0:
                val = row_dst[c] + q * sc
                row_dst[c] = val
                bl = abs(val).bit_length()
                if bl > peak_bits:
                    peak_bits = bl
        u_dst = U[dst]
        u_src = U[src]
        for c in range(m):
            usc = u_src[c]
            if usc != 0:
                u_dst[c] += q * usc
        for r in range(m):
            ui_dst = U_inv[r][dst]
            if ui_dst != 0:
                U_inv[r][src] -= q * ui_dst

    def swap_cols(i: int, j: int) -> None:
        if i == j:
            return
        for r in range(m):
            B[r][i], B[r][j] = B[r][j], B[r][i]
        for r in range(n):
            V[r][i], V[r][j] = V[r][j], V[r][i]
        V_inv[i], V_inv[j] = V_inv[j], V_inv[i]

    def neg_col(j: int) -> None:
        for r in range(m):
            B[r][j] = -B[r][j]
        for r in range(n):
            V[r][j] = -V[r][j]
        row_vi = V_inv[j]
        for c in range(n):
            row_vi[c] = -row_vi[c]

    def add_col(dst: int, src: int, q: int) -> None:
        """B[:, dst] += q * B[:, src]"""
        if q == 0:
            return
        nonlocal peak_bits
        for r in range(m):
            bs = B[r][src]
            if bs != 0:
                val = B[r][dst] + q * bs
                B[r][dst] = val
                bl = abs(val).bit_length()
                if bl > peak_bits:
                    peak_bits = bl
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

    k = 0
    limit = min(m, n)
    while k < limit:
        # Compute row/col nnz in active submatrix B[k:, k:]
        row_nnz = [0] * m
        col_nnz = [0] * n
        unit_best: Optional[Tuple[int, int, int]] = None
        gen_best: Optional[Tuple[int, int, int, int]] = None

        for r in range(k, m):
            rb = B[r]
            cnt = 0
            for c in range(k, n):
                if rb[c] != 0:
                    cnt += 1
                    col_nnz[c] += 1
            row_nnz[r] = cnt

        for r in range(k, m):
            if row_nnz[r] == 0:
                continue
            rb = B[r]
            rn = row_nnz[r] - 1
            for c in range(k, n):
                val = rb[c]
                if val == 0:
                    continue
                av = abs(val)
                score = rn * (col_nnz[c] - 1)
                if av == 1:
                    cand_u = (score, r, c)
                    if unit_best is None or cand_u < unit_best:
                        unit_best = cand_u
                else:
                    cand_g = (av, score, r, c)
                    if gen_best is None or cand_g < gen_best:
                        gen_best = cand_g

        if unit_best is None and gen_best is None:
            break

        if unit_best is not None:
            _, pr, pc = unit_best
            swap_rows(k, pr)
            swap_cols(k, pc)
            if B[k][k] < 0:
                neg_row(k)
            for r in range(k + 1, m):
                if B[r][k] != 0:
                    add_row(r, k, -B[r][k])
            for c in range(k + 1, n):
                if B[k][c] != 0:
                    add_col(c, k, -B[k][c])
            k += 1
            continue

        assert gen_best is not None
        _, _, pr, pc = gen_best
        swap_rows(k, pr)
        swap_cols(k, pc)
        if B[k][k] < 0:
            neg_row(k)

        # Euclidean reduction on row k and col k until both are cleared
        while True:
            changed = False
            piv = B[k][k]
            if piv < 0:
                neg_row(k)
                piv = -piv
            # Reduce column k
            for r in range(k + 1, m):
                val = B[r][k]
                if val != 0:
                    q, rem = divmod(val, piv)
                    if 2 * rem > piv:
                        q += 1
                    add_row(r, k, -q)
                    if B[r][k] != 0:
                        swap_rows(k, r)
                        if B[k][k] < 0:
                            neg_row(k)
                        piv = B[k][k]
                        changed = True
            # Reduce row k
            piv = B[k][k]
            for c in range(k + 1, n):
                val = B[k][c]
                if val != 0:
                    q, rem = divmod(val, piv)
                    if 2 * rem > piv:
                        q += 1
                    add_col(c, k, -q)
                    if B[k][c] != 0:
                        swap_cols(k, c)
                        if B[k][k] < 0:
                            neg_col(k)
                        piv = B[k][k]
                        changed = True
            if not changed:
                # Double check row k and col k are strictly zero outside (k, k)
                any_nz = False
                for r in range(k + 1, m):
                    if B[r][k] != 0:
                        any_nz = True
                        break
                if not any_nz:
                    for c in range(k + 1, n):
                        if B[k][c] != 0:
                            any_nz = True
                            break
                if not any_nz:
                    break

        if B[k][k] < 0:
            neg_row(k)
        k += 1

    rank = k
    # Phase 2: B is now strictly diagonal diag(e_0, ..., e_{rank-1}, 0).
    # Enforce divisibility e_i | e_j for all 0 <= i < j < rank via 2x2 reductions.
    for i in range(rank):
        for j in range(i + 1, rank):
            ei = B[i][i]
            ej = B[j][j]
            if ej % ei != 0:
                # Add col j to col i: now B[j][i] = ej, while only {i, j} block is nonzero
                add_col(i, j, 1)
                while B[j][i] != 0 or B[i][j] != 0:
                    if B[i][i] < 0:
                        neg_row(i)
                    if B[j][i] != 0:
                        q = B[j][i] // B[i][i]
                        add_row(j, i, -q)
                        if B[j][i] != 0:
                            swap_rows(i, j)
                            if B[i][i] < 0:
                                neg_row(i)
                    if B[i][j] != 0:
                        q = B[i][j] // B[i][i]
                        add_col(j, i, -q)
                        if B[i][j] != 0:
                            swap_cols(i, j)
                            if B[i][i] < 0:
                                neg_col(i)
                if B[i][i] < 0:
                    neg_row(i)
                if B[j][j] < 0:
                    neg_row(j)

    inv_factors = tuple(B[i][i] for i in range(rank))
    torsion = tuple(d for d in inv_factors if d > 1)
    u_bits = matrix_max_bit_length(U)
    v_bits = matrix_max_bit_length(V)

    if verify:
        uav = mat_mul(mat_mul(U, A_in), V)
        if not mat_eq(uav, B):
            raise AssertionError("SNF verification failed: U @ A @ V != S")
        if not is_identity(mat_mul(U, U_inv), m):
            raise AssertionError("SNF verification failed: U @ U_inv != I_m")
        if not is_identity(mat_mul(V, V_inv), n):
            raise AssertionError("SNF verification failed: V @ V_inv != I_n")
        for idx in range(rank):
            if B[idx][idx] <= 0:
                raise AssertionError("SNF diagonal entry must be positive")
            if idx + 1 < rank and B[idx + 1][idx + 1] % B[idx][idx] != 0:
                raise AssertionError("SNF divisibility d_i | d_{i+1} violated")

    return SNFCertificate(
        m=m,
        n=n,
        rank=rank,
        invariant_factors=inv_factors,
        torsion_factors=torsion,
        S=B,
        U=U,
        U_inv=U_inv,
        V=V,
        V_inv=V_inv,
        input_max_bits=input_bits,
        u_max_bits=u_bits,
        v_max_bits=v_bits,
        peak_intermediate_bits=peak_bits,
    )


@dataclass(frozen=True)
class DiophantineResult:
    q_sat: bool
    z_sat: bool
    x_z: Optional[Tuple[int, ...]]
    x_q_num: Optional[Tuple[int, ...]]
    x_q_den: int
    torsion_residues: Tuple[Tuple[int, int, int], ...]  # (coord_idx, rhs_val, mod_d)
    q_dual_witness: Optional[Tuple[int, ...]]  # u in Z^m with u^T A = 0, u^T b != 0


def solve_with_snf(
    A: Sequence[Sequence[int]],
    b: Sequence[int],
    cert: Optional[SNFCertificate] = None,
) -> DiophantineResult:
    """Solve A x = b over both Q and Z using unimodular SNF U A V = S."""
    if cert is None:
        cert = snf_unimodular(A, verify=True)
    ub = mat_vec_mul(cert.U, b)
    r = cert.rank
    m = cert.m
    n = cert.n

    for i in range(r, m):
        if ub[i] != 0:
            witness = tuple(cert.U[i])
            return DiophantineResult(
                q_sat=False,
                z_sat=False,
                x_z=None,
                x_q_num=None,
                x_q_den=1,
                torsion_residues=(),
                q_dual_witness=witness,
            )

    residues: List[Tuple[int, int, int]] = []
    z_ok = True
    y_z = [0] * n
    den_lcm = 1
    for i in range(r):
        di = cert.invariant_factors[i]
        rem = ub[i] % di
        if rem != 0:
            z_ok = False
            residues.append((i, ub[i], di))
        else:
            y_z[i] = ub[i] // di
        _, red_d = rat_norm(ub[i], di)
        den_lcm = ilcm(den_lcm, red_d)

    # Exact Q-solution: y_q_scaled[i] = (ub[i] * den_lcm) // di, then x_q_num = V @ y_q_scaled
    y_q_scaled = [0] * n
    for i in range(r):
        di = cert.invariant_factors[i]
        y_q_scaled[i] = (ub[i] * den_lcm) // di
    xq_raw = mat_vec_mul(cert.V, y_q_scaled)
    g_all = math.gcd(den_lcm, vec_gcd(xq_raw))
    xq_num = tuple(v // g_all for v in xq_raw)
    xq_den = den_lcm // g_all

    xz_tuple: Optional[Tuple[int, ...]] = None
    if z_ok:
        xz_raw = mat_vec_mul(cert.V, y_z)
        assert mat_vec_mul(A, xz_raw) == list(b)
        xz_tuple = tuple(xz_raw)

    return DiophantineResult(
        q_sat=True,
        z_sat=z_ok,
        x_z=xz_tuple,
        x_q_num=xq_num,
        x_q_den=xq_den,
        torsion_residues=tuple(residues),
        q_dual_witness=None,
    )


def kernel_z_basis(A: Sequence[Sequence[int]], cert: Optional[SNFCertificate] = None) -> List[List[int]]:
    """Return columns of V[:, rank:] forming a saturated Z-basis of ker_Z(A)."""
    if cert is None:
        cert = snf_unimodular(A, verify=True)
    basis: List[List[int]] = []
    for col in range(cert.rank, cert.n):
        basis.append([cert.V[row][col] for row in range(cert.n)])
    return basis


def ghrist_ding_projectors(
    A: Sequence[Sequence[int]],
    cert: Optional[SNFCertificate] = None,
) -> Dict[str, List[List[int]]]:
    """
    For A: Z^n -> Z^m with U A V = S (rank r), return exact integer idempotent projectors on Z^m:
      - P_sat = U_inv[:, :r] @ U[:r, :]  (projects onto sat(im_Z(A)) = im_Q(A) cap Z^m)
      - Q_free = U_inv[:, r:] @ U[r:, :] = I_m - P_sat  (projects onto free cokernel complement)
    """
    if cert is None:
        cert = snf_unimodular(A, verify=True)
    m = cert.m
    r = cert.rank
    u_inv_left = [[cert.U_inv[i][j] for j in range(r)] for i in range(m)]
    u_top = [list(cert.U[i]) for i in range(r)]
    p_sat = mat_mul(u_inv_left, u_top) if r > 0 else [[0] * m for _ in range(m)]

    u_inv_right = [[cert.U_inv[i][j] for j in range(r, m)] for i in range(m)]
    u_bot = [list(cert.U[i]) for i in range(r, m)]
    q_free = mat_mul(u_inv_right, u_bot) if r < m else [[0] * m for _ in range(m)]

    # Verify exact idempotency & orthogonality over Z:
    # P_sat^2 == P_sat, Q_free^2 == Q_free, P_sat @ Q_free == 0, P_sat + Q_free == I_m
    assert mat_eq(mat_mul(p_sat, p_sat), p_sat)
    assert mat_eq(mat_mul(q_free, q_free), q_free)
    zero_m = [[0] * m for _ in range(m)]
    assert mat_eq(mat_mul(p_sat, q_free), zero_m)
    sum_pq = [[p_sat[i][j] + q_free[i][j] for j in range(m)] for i in range(m)]
    assert is_identity(sum_pq, m)
    return {"P_sat": p_sat, "Q_free": q_free}


# ---------------------------------------------------------------------------
# Exact 2D & 3D Polyhedral Vertex Enumeration & Chvatal-Gomory Closure Engine
# System convention: { x in Q^d : a_i . x >= b_i  for (a_i, b_i) in ineqs }
# ---------------------------------------------------------------------------

def poly2d_vertices_exact(
    ineqs: Sequence[Tuple[int, int, int]],
) -> List[Tuple[Tuple[int, int], Tuple[int, int]]]:
    """
    Enumerate unique extreme vertices of { (x, y) in Q^2 : a*x + b*y >= c }
    represented as exact reduced rational pairs ((x_num, x_den), (y_num, y_den)).
    """
    m = len(ineqs)
    seen: dict[Tuple[Tuple[int, int], Tuple[int, int]], bool] = {}
    for i in range(m):
        a1, b1, c1 = ineqs[i]
        for j in range(i + 1, m):
            a2, b2, c2 = ineqs[j]
            det = a1 * b2 - a2 * b1
            if det == 0:
                continue
            xn_raw = c1 * b2 - c2 * b1
            yn_raw = a1 * c2 - a2 * c1
            xn, xd = rat_norm(xn_raw, det)
            yn, yd = rat_norm(yn_raw, det)
            # Check feasibility against all inequalities: a * (xn/xd) + b * (yn/yd) >= c
            # Multiply through by xd * yd > 0:
            feasible = True
            for ak, bk, ck in ineqs:
                lhs = ak * xn * yd + bk * yn * xd
                rhs = ck * xd * yd
                if lhs < rhs:
                    feasible = False
                    break
            if feasible:
                seen[((xn, xd), (yn, yd))] = True
    return sorted(seen.keys(), key=lambda pt: (pt[0][0] * pt[1][1], pt[1][0] * pt[0][1]))


def poly2d_all_integral(verts: Sequence[Tuple[Tuple[int, int], Tuple[int, int]]]) -> bool:
    return all(vx[1] == 1 and vy[1] == 1 for vx, vy in verts)


def cg_round_2d_exact(
    ineqs: Sequence[Tuple[int, int, int]],
) -> List[Tuple[int, int, int]]:
    """
    Compute one exact simultaneous elementary Chvatal-Gomory closure round P^(1)
    of a pointed 2D rational polyhedron P = { (x, y) : a_i x + b_i y >= c_i } with a_i, b_i, c_i in Z.
    Every active 2-cone (i, j) at a vertex of P has determinant D = |det[a_i, a_j]|;
    every Hilbert-basis / fundamental-parallelepiped combination lambda_1 = mu_1 / D, lambda_2 = mu_2 / D
    with 0 <= mu_1, mu_2 <= D and (mu_1 a_i + mu_2 a_j) == 0 (mod D) generates an integer valid cut
    g . x >= ceil((mu_1 c_i + mu_2 c_j) / D).
    """
    # Normalize input inequalities by gcd(a, b): if gcd(a, b) = g > 1, a'x + b'y >= ceil(c / g) is Round-1 CG!
    best_rhs: Dict[Tuple[int, int], int] = {}

    def record_cut(ca: int, cb: int, rhs_num: int, rhs_den: int) -> None:
        if ca == 0 and cb == 0:
            return
        g = math.gcd(ca, cb)
        pa = ca // g
        pb = cb // g
        cut_rhs = ceil_div(rhs_num, rhs_den * g)
        key = (pa, pb)
        if key not in best_rhs or cut_rhs > best_rhs[key]:
            best_rhs[key] = cut_rhs

    for a, b, c in ineqs:
        record_cut(a, b, c, 1)

    m = len(ineqs)
    verts = poly2d_vertices_exact(ineqs)
    for vx, vy in verts:
        xn, xd = vx
        yn, yd = vy
        active: List[int] = []
        for idx, (a, b, c) in enumerate(ineqs):
            if a * xn * yd + b * yn * xd == c * xd * yd:
                active.append(idx)
        for p in range(len(active)):
            i = active[p]
            a1, b1, c1 = ineqs[i]
            for q in range(p + 1, len(active)):
                j = active[q]
                a2, b2, c2 = ineqs[j]
                det = abs(a1 * b2 - a2 * b1)
                if det == 0:
                    continue
                # Enumerate fundamental parallelepiped:
                # Notice g = gcd(a2, b2); instead of O(det^2), solve mu1*a1 + mu2*a2 == 0 (mod det)
                # For each mu2 in 0..det-1, check if a1*mu1 == -mu2*a2 (mod det) has solutions!
                g1 = math.gcd(math.gcd(a1, b1), det)
                # Number of mu1 solutions in 0..det-1 is at most g1; step is det // g1.
                step1 = det // g1
                for mu2 in range(det):
                    # Solve mu1 * a1 == -mu2 * a2 (mod det) and mu1 * b1 == -mu2 * b2 (mod det)
                    # Find one solution via ext_gcd(a1, det) if a1 != 0 else ext_gcd(b1, det)
                    if a1 != 0:
                        ga, inv_a, _ = ext_gcd(a1, det)
                        rhs_a = (-mu2 * a2) % det
                        if rhs_a % ga != 0:
                            continue
                        base = ((rhs_a // ga) * inv_a) % (det // ga)
                        sub_step = det // ga
                        mu1 = base
                        while mu1 < det:
                            if (mu1 * a1 + mu2 * a2) % det == 0 and (mu1 * b1 + mu2 * b2) % det == 0:
                                if mu1 > 0 or mu2 > 0:
                                    ca = (mu1 * a1 + mu2 * a2) // det
                                    cb = (mu1 * b1 + mu2 * b2) // det
                                    record_cut(ca, cb, mu1 * c1 + mu2 * c2, det)
                            mu1 += sub_step
                    else:
                        gb, inv_b, _ = ext_gcd(b1, det)
                        rhs_b = (-mu2 * b2) % det
                        if rhs_b % gb != 0:
                            continue
                        base = ((rhs_b // gb) * inv_b) % (det // gb)
                        sub_step = det // gb
                        mu1 = base
                        while mu1 < det:
                            if (mu1 * a1 + mu2 * a2) % det == 0 and (mu1 * b1 + mu2 * b2) % det == 0:
                                if mu1 > 0 or mu2 > 0:
                                    ca = (mu1 * a1 + mu2 * a2) // det
                                    cb = (mu1 * b1 + mu2 * b2) // det
                                    record_cut(ca, cb, mu1 * c1 + mu2 * c2, det)
                            mu1 += sub_step

    # Prune dominated cuts: keep cuts active at at least one extreme vertex OR defining extreme rays
    cand = [(a, b, c) for (a, b), c in sorted(best_rhs.items())]
    new_verts = poly2d_vertices_exact(cand)
    essential: List[Tuple[int, int, int]] = []
    # Keep original ray-defining directions + any cut tight at a vertex of P^(1)
    orig_dirs = {(a // math.gcd(a, b), b // math.gcd(a, b)) for a, b, _ in ineqs if a != 0 or b != 0}
    for a, b, c in cand:
        if (a, b) in orig_dirs:
            essential.append((a, b, c))
            continue
        tight = False
        for (xn, xd), (yn, yd) in new_verts:
            if a * xn * yd + b * yn * xd == c * xd * yd:
                tight = True
                break
        if tight:
            essential.append((a, b, c))
    return essential


def det3_exact(
    r1: Tuple[int, int, int],
    r2: Tuple[int, int, int],
    r3: Tuple[int, int, int],
) -> int:
    return (
        r1[0] * (r2[1] * r3[2] - r2[2] * r3[1])
        - r1[1] * (r2[0] * r3[2] - r2[2] * r3[0])
        + r1[2] * (r2[0] * r3[1] - r2[1] * r3[0])
    )


def poly3d_vertices_exact(
    ineqs: Sequence[Tuple[int, int, int, int]],
) -> List[Tuple[Tuple[int, int], Tuple[int, int], Tuple[int, int]]]:
    """
    Enumerate unique extreme vertices of { (x, y, z) in Q^3 : a*x + b*y + c*z >= d }.
    """
    m = len(ineqs)
    seen: dict[Tuple[Tuple[int, int], Tuple[int, int], Tuple[int, int]], bool] = {}
    for i in range(m):
        a1, b1, c1, d1 = ineqs[i]
        for j in range(i + 1, m):
            a2, b2, c2, d2 = ineqs[j]
            for k in range(j + 1, m):
                a3, b3, c3, d3 = ineqs[k]
                det = det3_exact((a1, b1, c1), (a2, b2, c2), (a3, b3, c3))
                if det == 0:
                    continue
                dx = det3_exact((d1, b1, c1), (d2, b2, c2), (d3, b3, c3))
                dy = det3_exact((a1, d1, c1), (a2, d2, c2), (a3, d3, c3))
                dz = det3_exact((a1, b1, d1), (a2, b2, d2), (a3, b3, d3))
                xn, xd = rat_norm(dx, det)
                yn, yd = rat_norm(dy, det)
                zn, zd = rat_norm(dz, det)
                common_d = ilcm(ilcm(xd, yd), zd)
                xs = xn * (common_d // xd)
                ys = yn * (common_d // yd)
                zs = zn * (common_d // zd)
                feasible = True
                for ak, bk, ck, dk in ineqs:
                    if ak * xs + bk * ys + ck * zs < dk * common_d:
                        feasible = False
                        break
                if feasible:
                    seen[((xn, xd), (yn, yd), (zn, zd))] = True
    return sorted(seen.keys())


def poly3d_all_integral(
    verts: Sequence[Tuple[Tuple[int, int], Tuple[int, int], Tuple[int, int]]],
) -> bool:
    return all(vx[1] == 1 and vy[1] == 1 and vz[1] == 1 for vx, vy, vz in verts)


def cg_round_3d_exact(
    ineqs: Sequence[Tuple[int, int, int, int]],
) -> List[Tuple[int, int, int, int]]:
    """
    Compute one exact simultaneous elementary Chvatal-Gomory closure round P^(1)
    of a pointed 3D rational polyhedron P = { x in Q^3 : A x >= d } (assuming small cone determinants).
    Uses exact adjugate inversion on every active 2-face and 3-cone at vertices of P:
    For 3-cone B = [r_i; r_j; r_k] with D = |det(B)|:
      lambda^T B = c^T in Z^3  <=>  D * lambda^T = c^T * adj(B), with 0 <= (D*lambda)_t < D!
      Instead of iterating (mu_1, mu_2, mu_3) in D^3, solve B^T mu == 0 (mod D) via SNF of B^T,
      which has AT MOST D solutions in [0, D)^3 (since |Z^3 / B^T Z^3| = |det(B)| = D!!)!
    """
    best_rhs: Dict[Tuple[int, int, int], int] = {}

    def record_cut3(ca: int, cb: int, cc: int, rhs_num: int, rhs_den: int) -> None:
        if ca == 0 and cb == 0 and cc == 0:
            return
        g = math.gcd(math.gcd(ca, cb), cc)
        pa, pb, pc = ca // g, cb // g, cc // g
        cut_rhs = ceil_div(rhs_num, rhs_den * g)
        key = (pa, pb, pc)
        if key not in best_rhs or cut_rhs > best_rhs[key]:
            best_rhs[key] = cut_rhs

    for a, b, c, d in ineqs:
        record_cut3(a, b, c, d, 1)

    verts = poly3d_vertices_exact(ineqs)
    checked_triples: set[Tuple[int, int, int]] = set()
    checked_pairs: set[Tuple[int, int]] = set()

    for vx, vy, vz in verts:
        xn, xd = vx
        yn, yd = vy
        zn, zd = vz
        cd = ilcm(ilcm(xd, yd), zd)
        xs = xn * (cd // xd)
        ys = yn * (cd // yd)
        zs = zn * (cd // zd)
        active: List[int] = []
        for idx, (a, b, c, d) in enumerate(ineqs):
            if a * xs + b * ys + c * zs == d * cd:
                active.append(idx)

        # Pairwise combinations (2-cones on edges)
        for p in range(len(active)):
            i = active[p]
            for q in range(p + 1, len(active)):
                j = active[q]
                pair_key = (i, j) if i < j else (j, i)
                if pair_key in checked_pairs:
                    continue
                checked_pairs.add(pair_key)
                a1, b1, c1, d1 = ineqs[i]
                a2, b2, c2, d2 = ineqs[j]
                cert2 = snf_unimodular([[a1, a2], [b1, b2], [c1, c2]], verify=False)
                if cert2.rank < 2:
                    continue
                s0, s1 = cert2.invariant_factors[0], cert2.invariant_factors[1]
                D2 = s1
                if D2 <= 1:
                    continue
                # B_pair * V = S => columns of V give generators of (1/s_t) lattice:
                # mu = t0 * (D2 // s0) * V[:, 0] + t1 * V[:, 1] (mod D2) for t0 in 0..s0-1, t1 in 0..s1-1!
                for t0 in range(s0):
                    for t1 in range(s1):
                        mu1 = (t0 * (D2 // s0) * cert2.V[0][0] + t1 * cert2.V[0][1]) % D2
                        mu2 = (t0 * (D2 // s0) * cert2.V[1][0] + t1 * cert2.V[1][1]) % D2
                        if mu1 == 0 and mu2 == 0:
                            continue
                        ca = (mu1 * a1 + mu2 * a2) // D2
                        cb = (mu1 * b1 + mu2 * b2) // D2
                        cc = (mu1 * c1 + mu2 * c2) // D2
                        record_cut3(ca, cb, cc, mu1 * d1 + mu2 * d2, D2)

        # 3-way combinations (vertex cones: |Z^3 / B^T Z^3| = |det(B)| = s0 * s1 * s2 elements ONLY!)
        for p in range(len(active)):
            i = active[p]
            for q in range(p + 1, len(active)):
                j = active[q]
                for r_idx in range(q + 1, len(active)):
                    k = active[r_idx]
                    t_key = tuple(sorted((i, j, k)))
                    if t_key in checked_triples:
                        continue
                    checked_triples.add(t_key)  # type: ignore[arg-type]
                    a1, b1, c1, d1 = ineqs[i]
                    a2, b2, c2, d2 = ineqs[j]
                    a3, b3, c3, d3 = ineqs[k]
                    B_T = [[a1, a2, a3], [b1, b2, b3], [c1, c2, c3]]
                    cert3 = snf_unimodular(B_T, verify=False)
                    if cert3.rank < 3:
                        continue
                    s0, s1, s2 = cert3.invariant_factors
                    D3 = s2
                    if D3 <= 1:
                        continue
                    # Exact parametrization of { mu in [0, D3)^3 : B_T * mu == 0 (mod D3) }:
                    # Write B_T * mu == 0 (mod D3) <=> S * V_inv * mu == 0 (mod D3)
                    # <=> (V_inv * mu)_t is a multiple of (D3 // s_t), i.e. V_inv * mu = diag(D3//s0, D3//s1, D3//s2) * z
                    # for z in [0, s0) x [0, s1) x [0, s2) (EXACTLY s0*s1*s2 = |det(B)| tuples instead of D3^3!!)!
                    f0, f1, f2 = D3 // s0, D3 // s1, D3 // s2
                    for z0 in range(s0):
                        for z1 in range(s1):
                            for z2 in range(s2):
                                w0, w1, w2 = z0 * f0, z1 * f1, z2 * f2
                                mu1 = (cert3.V[0][0] * w0 + cert3.V[0][1] * w1 + cert3.V[0][2] * w2) % D3
                                mu2 = (cert3.V[1][0] * w0 + cert3.V[1][1] * w1 + cert3.V[1][2] * w2) % D3
                                mu3 = (cert3.V[2][0] * w0 + cert3.V[2][1] * w1 + cert3.V[2][2] * w2) % D3
                                if mu1 == 0 and mu2 == 0 and mu3 == 0:
                                    continue
                                ca = (mu1 * a1 + mu2 * a2 + mu3 * a3) // D3
                                cb = (mu1 * b1 + mu2 * b2 + mu3 * b3) // D3
                                cc = (mu1 * c1 + mu2 * c2 + mu3 * c3) // D3
                                record_cut3(ca, cb, cc, mu1 * d1 + mu2 * d2 + mu3 * d3, D3)

    # Exact vertex-cutoff theorem: every candidate (a, b, c) = lambda^T A (lambda >= 0) satisfies
    # c . r >= 0 on rec(P). Hence if a*vx + b*vy + c*vz >= d at EVERY extreme vertex v of P,
    # then a*x + b*y + c*z >= d already holds on all of P and is 100% redundant!
    # Keep only current defining inequalities (updated to best_rhs) + cuts that strictly cut off >= 1 vertex of P.
    orig_dirs = {
        prim_vec((a, b, c))
        for a, b, c, _ in ineqs
        if a != 0 or b != 0 or c != 0
    }
    filtered_cand: List[Tuple[int, int, int, int]] = []
    for (a, b, c), d in sorted(best_rhs.items()):
        if (a, b, c) in orig_dirs:
            filtered_cand.append((a, b, c, d))
            continue
        cuts_fractional = False
        for (xn, xd), (yn, yd), (zn, zd) in verts:
            cd = ilcm(ilcm(xd, yd), zd)
            if a * xn * (cd // xd) + b * yn * (cd // yd) + c * zn * (cd // zd) < d * cd:
                cuts_fractional = True
                break
        if cuts_fractional:
            filtered_cand.append((a, b, c, d))

    new_verts = poly3d_vertices_exact(filtered_cand)
    # Minimal irredundant representation of P^(1): keep extreme-ray directions + cuts tight at >= 1 vertex of P^(1)
    essential: List[Tuple[int, int, int, int]] = []
    for a, b, c, d in filtered_cand:
        if (a, b, c) in orig_dirs and len(new_verts) <= 1:
            essential.append((a, b, c, d))
            continue
        tight_count = 0
        for (xn, xd), (yn, yd), (zn, zd) in new_verts:
            cd = ilcm(ilcm(xd, yd), zd)
            if a * xn * (cd // xd) + b * yn * (cd // yd) + c * zn * (cd // zd) == d * cd:
                tight_count += 1
        if tight_count >= 1:
            essential.append((a, b, c, d))
    return essential
