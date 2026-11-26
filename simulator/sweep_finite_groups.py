from __future__ import annotations

import itertools
import math
import time
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Sequence, Tuple

from simulator.sim_exact_la import (
    mat_mul,
    mat_vec_mul,
    snf_unimodular,
    solve_with_snf,
)


@dataclass(frozen=True)
class FiniteGroupSpec:
    name: str
    order: int
    is_abelian: bool
    elements: Tuple[str, ...]
    cayley: Tuple[Tuple[int, ...], ...]  # cayley[i][j] = index of g_i * g_j, with g_0 = identity
    inv_map: Tuple[int, ...]
    perm_degree: Optional[int]  # faithful action degree m <= |G| if used for D1(c)
    perm_images: Optional[Tuple[Tuple[int, ...], ...]]  # 0-indexed permutations of {0..m-1}, (gh)(x) = g(h(x))


def verify_group_axioms(spec: FiniteGroupSpec) -> None:
    n = spec.order
    assert len(spec.elements) == n
    assert len(spec.cayley) == n
    # Identity at 0
    for i in range(n):
        assert spec.cayley[0][i] == i
        assert spec.cayley[i][0] == i
        inv_i = spec.inv_map[i]
        assert spec.cayley[i][inv_i] == 0
        assert spec.cayley[inv_i][i] == 0
    # Latin square & associativity
    for i in range(n):
        assert sorted(spec.cayley[i]) == list(range(n))
        for j in range(n):
            ij = spec.cayley[i][j]
            for k in range(n):
                jk = spec.cayley[j][k]
                assert spec.cayley[ij][k] == spec.cayley[i][jk]
    # Check abelian flag
    ab = all(spec.cayley[i][j] == spec.cayley[j][i] for i in range(n) for j in range(n))
    assert ab == spec.is_abelian
    # Check faithful permutation action if provided: (g_i * g_j)(x) == g_i(g_j(x))
    if spec.perm_images is not None:
        assert spec.perm_degree is not None
        m = spec.perm_degree
        assert len(spec.perm_images) == n
        assert len(set(spec.perm_images)) == n  # faithfulness!
        for i in range(n):
            for j in range(n):
                ij = spec.cayley[i][j]
                for x in range(m):
                    assert spec.perm_images[ij][x] == spec.perm_images[i][spec.perm_images[j][x]]


def _build_group_from_perms(
    name: str,
    perms: Sequence[Tuple[int, ...]],
    m: int,
) -> FiniteGroupSpec:
    # Ensure identity tuple(range(m)) is at index 0
    id_p = tuple(range(m))
    ordered = [id_p] + [p for p in perms if p != id_p]
    idx_of = {p: i for i, p in enumerate(ordered)}
    n = len(ordered)
    cayley: List[Tuple[int, ...]] = []
    inv_map: List[int] = [0] * n
    for i, pi in enumerate(ordered):
        row: List[int] = []
        for j, pj in enumerate(ordered):
            comp = tuple(pi[pj[x]] for x in range(m))
            c_idx = idx_of[comp]
            row.append(c_idx)
            if c_idx == 0:
                inv_map[i] = j
        cayley.append(tuple(row))
    ab = all(cayley[i][j] == cayley[j][i] for i in range(n) for j in range(n))
    labels = tuple(f"g{i}" for i in range(n))
    spec = FiniteGroupSpec(
        name=name,
        order=n,
        is_abelian=ab,
        elements=labels,
        cayley=tuple(cayley),
        inv_map=tuple(inv_map),
        perm_degree=m,
        perm_images=tuple(ordered),
    )
    verify_group_axioms(spec)
    return spec


def make_cyclic_group(n: int) -> FiniteGroupSpec:
    cayley = tuple(tuple((i + j) % n for j in range(n)) for i in range(n))
    inv_map = tuple((-i) % n for i in range(n))
    perms = tuple(tuple((x + i) % n for x in range(n)) for i in range(n))
    spec = FiniteGroupSpec(
        name=f"C_{n}",
        order=n,
        is_abelian=True,
        elements=tuple(str(i) for i in range(n)),
        cayley=cayley,
        inv_map=inv_map,
        perm_degree=n,
        perm_images=perms,
    )
    verify_group_axioms(spec)
    return spec


def make_v4_group() -> FiniteGroupSpec:
    # V_4 = C_2 x C_2 <= S_4 acting faithfully on {0,1} + {2,3} (degree 4)
    perms = [
        (0, 1, 2, 3),
        (1, 0, 2, 3),
        (0, 1, 3, 2),
        (1, 0, 3, 2),
    ]
    return _build_group_from_perms("V_4", perms, 4)


def make_dihedral_group(n: int) -> FiniteGroupSpec:
    # D_n of order 2n acting on regular n-gon {0..n-1}
    perms: List[Tuple[int, ...]] = []
    for r in range(n):
        perms.append(tuple((x + r) % n for x in range(n)))
    for r in range(n):
        perms.append(tuple((-x + r) % n for x in range(n)))
    return _build_group_from_perms(f"D_{n}", perms, n)


def make_s3_group() -> FiniteGroupSpec:
    return _build_group_from_perms("S_3", list(itertools.permutations(range(3))), 3)


def make_s4_group() -> FiniteGroupSpec:
    return _build_group_from_perms("S_4", list(itertools.permutations(range(4))), 4)


def make_a4_group() -> FiniteGroupSpec:
    even_perms: List[Tuple[int, ...]] = []
    for p in itertools.permutations(range(4)):
        inv_cnt = sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j])
        if inv_cnt % 2 == 0:
            even_perms.append(p)
    return _build_group_from_perms("A_4", even_perms, 4)


def make_q8_group() -> FiniteGroupSpec:
    """
    Quaternion group Q_8 = {+1, -1, +i, -i, +j, -j, +k, -k} of order 8.
    Minimal faithful permutation degree is 8 (regular representation), because -1 lies in EVERY
    nontrivial subgroup of Q_8 so no proper subgroup is core-free!
    """
    elems = ("1", "-1", "i", "-i", "j", "-j", "k", "-k")
    idx = {e: t for t, e in enumerate(elems)}

    def mul_sym(a: str, b: str) -> str:
        neg = 0
        if a.startswith("-"):
            neg ^= 1
            a = a[1:]
        if b.startswith("-"):
            neg ^= 1
            b = b[1:]
        if a == "1":
            base = b
        elif b == "1":
            base = a
        elif a == b:
            neg ^= 1
            base = "1"
        elif (a, b) == ("i", "j"):
            base = "k"
        elif (a, b) == ("j", "i"):
            neg ^= 1
            base = "k"
        elif (a, b) == ("j", "k"):
            base = "i"
        elif (a, b) == ("k", "j"):
            neg ^= 1
            base = "i"
        elif (a, b) == ("k", "i"):
            base = "j"
        elif (a, b) == ("i", "k"):
            neg ^= 1
            base = "j"
        else:
            raise AssertionError("Unreachable Q_8 pair")
        return f"-{base}" if neg == 1 else base

    cayley = tuple(tuple(idx[mul_sym(a, b)] for b in elems) for a in elems)
    inv_map = tuple(next(j for j in range(8) if cayley[i][j] == 0) for i in range(8))
    reg_perms = tuple(tuple(cayley[i][x] for x in range(8)) for i in range(8))
    spec = FiniteGroupSpec(
        name="Q_8",
        order=8,
        is_abelian=False,
        elements=elems,
        cayley=cayley,
        inv_map=inv_map,
        perm_degree=8,
        perm_images=reg_perms,
    )
    verify_group_axioms(spec)
    return spec


def enumerate_all_subgroups(spec: FiniteGroupSpec) -> List[Tuple[int, ...]]:
    """Exact closure enumeration of all subgroups H <= G."""
    n = spec.order
    cay = spec.cayley

    def closure(seed: Tuple[int, ...]) -> Tuple[int, ...]:
        s = set(seed)
        s.add(0)
        changed = True
        while changed:
            changed = False
            cur = list(s)
            for a in cur:
                for b in cur:
                    ab = cay[a][b]
                    if ab not in s:
                        s.add(ab)
                        changed = True
        return tuple(sorted(s))

    subgroups: set[Tuple[int, ...]] = {closure(())}
    for g in range(n):
        subgroups.add(closure((g,)))

    # Iteratively close under adding one element to existing proper subgroups
    frontier = set(subgroups)
    while frontier:
        next_f: set[Tuple[int, ...]] = set()
        for h in frontier:
            if len(h) == n:
                continue
            # By Lagrange, any strictly larger subgroup has size dividing n and >= 2*len(h)
            if 2 * len(h) > n:
                continue
            for g in range(1, n):
                if g not in h:
                    nh = closure(h + (g,))
                    if nh not in subgroups:
                        subgroups.add(nh)
                        next_f.add(nh)
        frontier = next_f

    return sorted(subgroups, key=lambda h: (len(h), h))


def minimal_faithful_perm_degree(spec: FiniteGroupSpec, subgroups: Sequence[Tuple[int, ...]]) -> int:
    """
    Compute the exact minimal degree m of a faithful permutation representation G -> S_m:
      m(G) = min { sum_{t=1}^k [G : H_t] : cap_{t=1}^k Core_G(H_t) = {0} }.
    """
    n = spec.order
    # Compute Core_G(H) = cap_{g in G} g H g^{-1} for each subgroup H
    cores: List[Tuple[int, int]] = []  # (index [G:H], bitmask of Core_G(H) excluding identity 0)
    for h in subgroups:
        h_set = set(h)
        core = set(h)
        for g in range(n):
            ginv = spec.inv_map[g]
            conj = {spec.cayley[spec.cayley[g][x]][ginv] for x in h_set}
            core &= conj
        mask = 0
        for x in core:
            if x != 0:
                mask |= 1 << x
        idx_deg = n // len(h)
        cores.append((idx_deg, mask))

    # DP over bitmasks of non-identity elements killed so far (here n <= 24; even faster: prune dominated pairs!)
    best_cost_for_mask: Dict[int, int] = {(1 << n) - 2: 0}
    # Dedup by mask keeping minimal index degree
    min_deg_by_mask: Dict[int, int] = {}
    for deg, msk in cores:
        if msk not in min_deg_by_mask or deg < min_deg_by_mask[msk]:
            min_deg_by_mask[msk] = deg

    for msk, deg in sorted(min_deg_by_mask.items(), key=lambda kv: kv[1]):
        cur_items = list(best_cost_for_mask.items())
        for old_msk, old_cost in cur_items:
            new_msk = old_msk & msk
            new_cost = old_cost + deg
            if new_cost < n and (new_msk not in best_cost_for_mask or new_cost < best_cost_for_mask[new_msk]):
                best_cost_for_mask[new_msk] = new_cost

    return best_cost_for_mask.get(0, n)


# ---------------------------------------------------------------------------
# Trap 5 & Theorem D1 Circuit Constructions & Verifiers
# ---------------------------------------------------------------------------

def verify_trivial_w_eq_g2_circuit(spec: FiniteGroupSpec) -> int:
    """
    Trap 5: Verify exact 1-layer pure-Z {0,1}-indicator realization ReLU(x_g + y_h - 1) at W = |G|^2.
    """
    n = spec.order
    w_triv = n * n
    # Check across all n^2 input pairs (g, h)
    for g in range(n):
        for h in range(n):
            target = spec.cayley[g][h]
            out = [0] * n
            for a in range(n):
                xa = 1 if a == g else 0
                for b in range(n):
                    yb = 1 if b == h else 0
                    act = max(0, xa + yb - 1)
                    if act != 0:
                        out[spec.cayley[a][b]] += act
            for c in range(n):
                expected = 1 if c == target else 0
                assert out[c] == expected
    return w_triv


def guard_compression_width(spec: FiniteGroupSpec, requested_width: int) -> None:
    """Trap 5 mandatory ValueError guard whenever compression routine is called with W >= |G|^2."""
    if requested_width >= spec.order * spec.order:
        raise ValueError(
            f"Trivial width guard triggered for {spec.name}: W={requested_width} >= |G|^2={spec.order * spec.order}"
        )


def verify_cyclic_1layer_z_circuits(spec: FiniteGroupSpec) -> Dict[str, Any]:
    """
    Theorem D1(b): Explicit 1-layer pure-Z exact {0,1}-indicator circuits for C_n:
      - Biased width W = 2n - 2 (with integer output biases)
      - Unbiased width W = 2n - 1 (zero biases in BOTH layers!)
    """
    n = spec.order
    w_biased = 2 * n - 2
    w_unbiased = 2 * n - 1
    guard_compression_width(spec, w_biased)
    if n >= 3:
        guard_compression_width(spec, w_unbiased)

    # Unbiased 1-layer pure-Z neurons on one-hot (x_0..x_{n-1}, y_0..y_{n-1}):
    # Neuron 0: ReLU(sum_{i=0}^{n-1} x_i) == 1 on all one-hot inputs!
    # Neuron t+1 (for t = 0..2n-3): ReLU(sum_i (i - t)*x_i + sum_j j*y_j) == max(0, (i + j) - t)!
    # Evaluate feature matrix F_sum on s = i + j in 0..2n-2:
    m_grid = 2 * n - 1
    f_grid = [[0] * w_unbiased for _ in range(m_grid)]
    for s in range(m_grid):
        f_grid[s][0] = 1
        for t in range(2 * n - 2):
            f_grid[s][t + 1] = max(0, s - t)

    snf_grid = snf_unimodular(f_grid, verify=True)
    assert snf_grid.invariant_factors == tuple([1] * m_grid)

    # Solve exact integer readout weights C_out in Z^{n x (2n-1)} for all k in 0..n-1:
    readout_rows: List[Tuple[int, ...]] = []
    for k in range(n):
        target_s = [1 if (s % n) == k else 0 for s in range(m_grid)]
        sol = solve_with_snf(f_grid, target_s, snf_grid)
        assert sol.z_sat and sol.x_z is not None
        readout_rows.append(sol.x_z)

    # Exhaustively verify across all n^2 pairs (i, j) using explicit zero-bias neuron weights!
    for i in range(n):
        for j in range(n):
            hidden = [0] * w_unbiased
            # Neuron 0: sum_a 1 * x_a = 1
            hidden[0] = max(0, 1)
            for t in range(2 * n - 2):
                # sum_a (a - t) * x_a + sum_b b * y_b = (i - t) + j
                hidden[t + 1] = max(0, (i - t) + j)
            for k in range(n):
                val = sum(readout_rows[k][col] * hidden[col] for col in range(w_unbiased))
                expected = 1 if ((i + j) % n == k) else 0
                assert val == expected

    return {
        "biased_width_2nm2": w_biased,
        "unbiased_width_2nm1": w_unbiased,
        "grid_snf": list(snf_grid.invariant_factors),
        "exact_z_indicator_verified": True,
    }


def verify_permutation_biequivariant_circuit(spec: FiniteGroupSpec) -> Dict[str, Any]:
    """
    Theorem D1(c): Zero-bias pure-Z bi-equivariant permutation circuit (`arXiv:2410.07476v3`)
    with anchor vector a = (1, 2, ..., m)^T at compressed width W = m^2 << |G|^2!
    """
    assert spec.perm_degree is not None and spec.perm_images is not None
    m = spec.perm_degree
    n = spec.order
    w_perm = m * m
    if w_perm >= n * n:
        return {
            "applicable_strict_compression": False,
            "perm_degree_m": m,
            "width_m2": w_perm,
            "reason": f"m^2 = {w_perm} == |G|^2 = {n * n} (no proper faithful permutation compression)",
        }

    guard_compression_width(spec, w_perm)
    perms = spec.perm_images
    # Anchor vector a = (1, 2, ..., m)
    # For each element g, P(g) maps basis e_k to e_{g(k)}, so (P(g) a)_i = sum_{k: g(k)==i} (k+1) = g^{-1}(i) + 1.
    pa_vecs: List[Tuple[int, ...]] = []
    for g in range(n):
        vec = [0] * m
        for k in range(m):
            vec[perms[g][k]] = k + 1
        pa_vecs.append(tuple(vec))

    # Build zero-bias ReLU activation matrix M_perm in Z^{n^2 x m^2}:
    # Neuron (i, k) on one-hot (x, y):
    #   phi_{i,k}(x, y) = ReLU( sum_{h in G} (P(h) a)_k * y_h  -  m * sum_{g in G : g(k) != i} x_g )
    min_margin = 10**9
    for g in range(n):
        for h in range(n):
            target = spec.cayley[g][h]
            z_sum = [0] * m
            for i in range(m):
                acc_i = 0
                for k in range(m):
                    l_k = pa_vecs[h][k]
                    pen = 0 if perms[g][k] == i else m
                    act = max(0, l_k - pen)
                    acc_i += act
                z_sum[i] = acc_i
            assert tuple(z_sum) == pa_vecs[target]
            scores = [sum(pa_vecs[c][i] * z_sum[i] for i in range(m)) for c in range(n)]
            best_target = scores[target]
            best_other = max(scores[c] for c in range(n) if c != target)
            margin = best_target - best_other
            assert margin >= 1
            if margin < min_margin:
                min_margin = margin

    return {
        "applicable_strict_compression": True,
        "perm_degree_m": m,
        "width_m2": w_perm,
        "compression_ratio_num_den": [w_perm, n * n],
        "zero_bias_pure_z": True,
        "min_strict_argmax_margin": min_margin,
        "verified_all_g2_pairs": True,
    }


# ---------------------------------------------------------------------------
# Theorem D2: Fixed Integer Character / Irrep & Coset Readout Torsion Matrices
# ---------------------------------------------------------------------------

def build_outcome_irrep_matrix(spec: FiniteGroupSpec) -> List[List[int]]:
    """
    Build a canonical |G| x |G| integer character / Q-irrep matrix-coefficient table R_G in Z^{|G| x |G|}
    whose rows are indexed by outcome c = g*h in G and whose columns are bilinear integer irrep features
    phi_col(g*h) = sum_k rho(g)_{i,k} rho(h)_{k,j} in Z, having exact Q-rank = |G|!
    Stacking rows across all (g, h) in G^2 yields M_irrep in Z^{|G|^2 x |G|} with identical nonzero SNF!
    """
    name = spec.name
    n = spec.order

    if name == "V_4":
        # Exact 4x4 Sylvester-Hadamard character table H_4: SNF = diag(1, 2, 2, 4)
        return [
            [1, 1, 1, 1],
            [1, -1, 1, -1],
            [1, 1, -1, -1],
            [1, -1, -1, 1],
        ]

    if name in ("C_3", "C_4", "C_5"):
        # Direct sum of 1D rational characters + companion matrices of cyclotomic polynomials Phi_d(x)!
        # C_3: 1 (dim 1) (+) Phi_3 = x^2 + x + 1 (dim 2: C = [[0,-1],[1,-1]]) -> 1 + 2 = 3 cols?
        # Wait: matrix coefficients of d x d companion rep span dim d (commutant Q(zeta_d) has dim d)!
        # Specifically, first column of C^c for each divisor d | n (with d > 2), plus +-1 sign if 2 | n, plus trivial 1!
        if name == "C_3":
            # Trivial [1] + first col of C^c where C = [[0, -1], [1, -1]]? Wait: check det([[1,1,0],[1,0,1],[1,-1,-1]]) = -3!
            c_mat = [[0, -1], [1, -1]]
            p0 = [[1, 0], [0, 1]]
            p1 = c_mat
            p2 = mat_mul(c_mat, c_mat)
            ps = [p0, p1, p2]
            return [[1, ps[g][0][0], ps[g][1][0]] for g in range(3)]
        if name == "C_4":
            # Trivial [1], sign [(-1)^g], and 2D rotation J = [[0, -1], [1, 0]] first col!
            j_mat = [[0, -1], [1, 0]]
            ps = [[[1, 0], [0, 1]]]
            for _ in range(3):
                ps.append(mat_mul(ps[-1], j_mat))
            return [[1, 1 if g % 2 == 0 else -1, ps[g][0][0], ps[g][1][0]] for g in range(4)]
        if name == "C_5":
            # Trivial [1] + first col of 4D companion matrix of Phi_5 = 1 + x + x^2 + x^3 + x^4!
            comp5 = [
                [0, 0, 0, -1],
                [1, 0, 0, -1],
                [0, 1, 0, -1],
                [0, 0, 1, -1],
            ]
            ps = [[[1 if r == c else 0 for c in range(4)] for r in range(4)]]
            for _ in range(4):
                ps.append(mat_mul(ps[-1], comp5))
            return [[1, ps[g][0][0], ps[g][1][0], ps[g][2][0], ps[g][3][0]] for g in range(5)]

    if name == "S_3":
        # Trivial (1) + sign (1) + all 4 matrix entries of standard 2D integral irrep on {(x1,x2,x3): sum=0}
        # Basis e1=(1,-1,0), e2=(0,1,-1): action of perm p in S_3 in Z^{2x2}!
        assert spec.perm_images is not None
        rows: List[List[int]] = []
        for p in spec.perm_images:
            inv_cnt = sum(1 for i in range(3) for j in range(i + 1, 3) if p[i] > p[j])
            sgn = 1 if inv_cnt % 2 == 0 else -1
            # Map basis vectors v_b1 = (1, -1, 0), v_b2 = (0, 1, -1) under w_i = v_{p^{-1}(i)}, i.e. place v_k at p[k]:
            # Express w = c1*(1,-1,0) + c2*(0,1,-1) => c1 = w_0, c2 = -w_2!
            w1 = [0, 0, 0]
            w1[p[0]] = 1
            w1[p[1]] = -1
            w2 = [0, 0, 0]
            w2[p[1]] = 1
            w2[p[2]] = -1
            m00, m10 = w1[0], -w1[2]
            m01, m11 = w2[0], -w2[2]
            rows.append([1, sgn, m00, m01, m10, m11])
        return rows

    if name == "D_4":
        # Four 1D characters (+-1)^4 + all 4 entries of faithful 2D square symmetry irrep in {0, +-1}^{2x2} (total 8 cols)!
        # Elements of D_4: perms[0..3] rotations of 4-gon, perms[4..7] reflections!
        assert spec.perm_images is not None
        # Vertices of square in Z^2: v0=(1,0), v1=(0,1), v2=(-1,0), v3=(0,-1)!
        sq = [(1, 0), (0, 1), (-1, 0), (0, -1)]
        rows = []
        for p in spec.perm_images:
            # 2D matrix M maps (1,0)=v0 -> sq[p[0]] and (0,1)=v1 -> sq[p[1]]!
            m00, m10 = sq[p[0]]
            m01, m11 = sq[p[1]]
            det_m = m00 * m11 - m01 * m10  # +1 on rotations, -1 on reflections
            # Parity on diagonals {0,2} vs {1,3}: p[0] % 2 == 0 -> +1 else -1
            diag_par = 1 if (p[0] % 2 == 0) else -1
            rows.append([1, det_m, diag_par, det_m * diag_par, m00, m01, m10, m11])
        return rows

    if name == "Q_8":
        # Four 1D characters factoring through Q_8 / {+-1} ~ V_4 (Hadamard H_4)
        # PLUS first column of 4D left-regular quaternion representation on (1, i, j, k) (total 8 cols)!
        # Elements order: ("1", "-1", "i", "-i", "j", "-j", "k", "-k")
        # Cosets: {+-1}->0, {+-i}->1, {+-j}->2, {+-k}->3
        h4 = [
            [1, 1, 1, 1],
            [1, -1, 1, -1],
            [1, 1, -1, -1],
            [1, -1, -1, 1],
        ]
        quat_col = [
            [1, 0, 0, 0],
            [-1, 0, 0, 0],
            [0, 1, 0, 0],
            [0, -1, 0, 0],
            [0, 0, 1, 0],
            [0, 0, -1, 0],
            [0, 0, 0, 1],
            [0, 0, 0, -1],
        ]
        rows = []
        for g in range(8):
            coset_id = g // 2
            rows.append(h4[coset_id] + quat_col[g])
        return rows

    if name == "D_5":
        # 1D trivial (1) + 1D det sign (1) + 8 matrix-coefficient basis cols from 4D Q-irrep on {(x0..x4): sum=0}!
        # Wait: in D_5 (order 10 = 1 + 1 + 8!), End_Q(V_4) where V_4 = Q^4 (sum=0) is M_2(Q(sqrt(5))), dim_Q = 2^2 * 2 = 8!
        # Let's extract all 16 entries of the 4x4 integral representation on basis e_i = u_i - u_4 (i=0..3),
        # and pick the lexicographically first 8 linearly independent columns (so R_{D_5} is 10 x 10 of full Q-rank 10)!
        assert spec.perm_images is not None
        cand_cols_per_g: List[List[int]] = []
        for p in spec.perm_images:
            # Rotation vs reflection: check cyclic step (p[1] - p[0]) % 5 in {1,2,3,4}? Wait: det on 4D rep!
            # Build 4x4 matrix M on basis b_k = e_k - e_4 (k=0..3): image has coord i equal to w_i - w_4!
            mat4 = [[0] * 4 for _ in range(4)]
            for col_k in range(4):
                w = [0] * 5
                w[p[col_k]] += 1
                w[p[4]] -= 1
                for row_i in range(4):
                    mat4[row_i][col_k] = w[row_i]
            # Check reflection sign: p^2 == id and p != id => -1, else +1
            p2 = tuple(p[p[x]] for x in range(5))
            is_refl = (p != (0, 1, 2, 3, 4)) and (p2 == (0, 1, 2, 3, 4))
            sgn = -1 if is_refl else 1
            flat16 = [mat4[r][c] for r in range(4) for c in range(4)]
            cand_cols_per_g.append([1, sgn] + flat16)
        return _select_independent_int_columns(cand_cols_per_g, n)

    if name == "A_4":
        # Order 12: 3D standard tetrahedral irrep (all 9 matrix entries in Z^{3x3}: dim 9!)
        # + 1D trivial (1) + 2D companion rep of A_4 / V_4 ~ C_3 (dim 2)! 1 + 2 + 9 = 12!
        assert spec.perm_images is not None
        # Standard 3D tetrahedral vertices in {+-1}^3:
        # v0=(1,1,1), v1=(1,-1,-1), v2=(-1,1,-1), v3=(-1,-1,1)! Notice sum v_i = (0,0,0),
        # and EVERY even permutation of {v0,v1,v2,v3} acts as a 3x3 signed permutation matrix in SO_3(Z) subset {0, +-1}^{3x3}!!
        tet = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
        # Wait: check how e_x = (1,0,0) = (v0 + v1)/2!
        # In basis (e_x, e_y, e_z): 2*e_x = v0 + v1 -> image is tet[p[0]] + tet[p[1]], which ALWAYS has entries in {0, +-2},
        # so dividing by 2 gives an EXACT {0, +-1}^{3x3} orthogonal integer matrix!!
        c3_comp = [[0, -1], [1, -1]]
        c3_pows = [[[1, 0], [0, 1]], c3_comp, mat_mul(c3_comp, c3_comp)]
        rows = []
        for p in spec.perm_images:
            ex_img = [(tet[p[0]][d] + tet[p[1]][d]) // 2 for d in range(3)]
            ey_img = [(tet[p[0]][d] + tet[p[2]][d]) // 2 for d in range(3)]
            ez_img = [(tet[p[0]][d] + tet[p[3]][d]) // 2 for d in range(3)]
            flat9 = ex_img + ey_img + ez_img
            # Coset in A_4 / V_4 ~ C_3: trace of SO_3 matrix is 3 (id), -1 (V_4\{id}), or 0 (3-cycles)!
            # Distinguish the two C_3 cosets by cyclic order of (ex_img, ey_img, ez_img): ex_img = (0,1,0) vs (0,0,1)!
            tr = ex_img[0] + ey_img[1] + ez_img[2]
            if tr in (3, -1):
                c3_id = 0
            elif ex_img[1] != 0:
                c3_id = 1
            else:
                c3_id = 2
            rows.append([1, c3_pows[c3_id][0][0], c3_pows[c3_id][1][0]] + flat9)
        return rows

    if name == "S_4":
        # EVERY complex irrep of S_4 is realizable over Z!
        # Dimensions: 1 (triv) + 1 (sign) + 2^2 (S_4/V_4 ~ S_3 standard 2D) + 3^2 (standard 3D) + 3^2 (sign x 3D) = 1+1+4+9+9 = 24!
        assert spec.perm_images is not None
        tet = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]
        rows = []
        for p in spec.perm_images:
            inv_cnt = sum(1 for i in range(4) for j in range(i + 1, 4) if p[i] > p[j])
            sgn = 1 if inv_cnt % 2 == 0 else -1
            # On S_4, any perm of tet acts by O_3(Z) (multiplying by sgn makes odd perms flip sign if we want both 3D irreps!):
            # Wait: for odd permutation (0, 1), tet[1]+tet[0] = v1+v0 (invariant), tet[0]+tet[2] = (1,1,1)+(-1,1,-1)=(0,2,0)?
            # Wait: check (0,1) on tet: v0<->v1, v2->v2, v3->v3!
            # Linear map sending v0->v1, v1->v0, v2->v2, v3->v3:
            # 2*e_x = v0+v1 -> v1+v0 = 2*e_x; 2*e_y = v0+v2 -> v1+v2 = (0,0,-2) = -2*e_z; 2*e_z = v0+v3 -> v1+v3 = (0,-2,0) = -2*e_y!
            # IT IS STILL DIVISIBLE BY 2 FOR ALL 24 ELEMENTS OF S_4!!
            ex_img = [(tet[p[0]][d] + tet[p[1]][d]) // 2 for d in range(3)]
            ey_img = [(tet[p[0]][d] + tet[p[2]][d]) // 2 for d in range(3)]
            ez_img = [(tet[p[0]][d] + tet[p[3]][d]) // 2 for d in range(3)]
            flat9 = ex_img + ey_img + ez_img
            flat9_sgn = [sgn * v for v in flat9]
            # Quotient S_4 / V_4 ~ S_3 acts by permuting the 3 coordinate axes {x, y, z}!
            # Extract which axis 0,1,2 each of ex_img, ey_img, ez_img lands on -> permutation q in S_3!
            q_s3 = [
                next(d for d in range(3) if ex_img[d] != 0),
                next(d for d in range(3) if ey_img[d] != 0),
                next(d for d in range(3) if ez_img[d] != 0),
            ]
            w1 = [0, 0, 0]
            w1[q_s3[0]] = 1
            w1[q_s3[1]] = -1
            w2 = [0, 0, 0]
            w2[q_s3[1]] = 1
            w2[q_s3[2]] = -1
            s3_flat4 = [w1[0], w2[0], -w1[2], -w2[2]]
            rows.append([1, sgn] + s3_flat4 + flat9 + flat9_sgn)
        return rows

    raise ValueError(f"Unsupported group {name}")


def _select_independent_int_columns(mat: Sequence[Sequence[int]], target_rank: int) -> List[List[int]]:
    m = len(mat)
    total_cols = len(mat[0])
    chosen: List[int] = []
    for c in range(total_cols):
        trial = chosen + [c]
        sub = [[mat[r][j] for j in trial] for r in range(m)]
        cert = snf_unimodular(sub, verify=False)
        if cert.rank == len(trial):
            chosen.append(c)
            if len(chosen) == target_rank:
                break
    assert len(chosen) == target_rank
    return [[mat[r][j] for j in chosen] for r in range(m)]


def build_outcome_proper_coset_matrix(
    spec: FiniteGroupSpec,
    subgroups: Sequence[Tuple[int, ...]],
) -> List[List[int]]:
    """
    Build {0, 1} outcome coset indicator matrix C_G in {0, 1}^{|G| x W_cos}
    over all left cosets cH of NON-TRIVIAL subgroups H <= G (|H| >= 2, including G itself).
    """
    n = spec.order
    cols: List[Tuple[int, ...]] = []
    seen_cosets: set[Tuple[int, ...]] = set()
    for h in subgroups:
        if len(h) < 2:
            continue
        for g in range(n):
            coset = tuple(sorted(spec.cayley[g][x] for x in h))
            if coset not in seen_cosets:
                seen_cosets.add(coset)
                col = tuple(1 if r in coset else 0 for r in range(n))
                cols.append(col)
    return [[cols[c][r] for c in range(len(cols))] for r in range(n)]


def analyze_finite_group(spec: FiniteGroupSpec) -> Dict[str, Any]:
    t0 = time.perf_counter_ns()
    n = spec.order
    subgroups = enumerate_all_subgroups(spec)
    min_perm_deg = minimal_faithful_perm_degree(spec, subgroups)

    # 1. Trap 5: W = |G|^2 baseline + ValueError guard test
    w_triv = verify_trivial_w_eq_g2_circuit(spec)
    guard_raised = False
    try:
        guard_compression_width(spec, n * n)
    except ValueError:
        guard_raised = True
    assert guard_raised

    # 2. Theorem D1(b) if cyclic, Theorem D1(c) bi-equivariant permutation compression
    cyclic_res: Optional[Dict[str, Any]] = None
    if spec.name.startswith("C_"):
        cyclic_res = verify_cyclic_1layer_z_circuits(spec)

    perm_res = verify_permutation_biequivariant_circuit(spec)

    # 3. Theorem D2: SNF Readout Torsion on Integral Irrep / Character Feature Matrix M_irrep in Z^{|G|^2 x |G|}
    # Note: R_G has shape |G| x |G| on outcomes; verify that stacking R_G[cayley[g][h]] across all |G|^2 pairs
    # has the EXACT SAME rank and SNF invariant factors as R_G!
    r_irrep = build_outcome_irrep_matrix(spec)
    snf_r = snf_unimodular(r_irrep, verify=True)
    assert snf_r.rank == n  # Full Q-rank = |G| => EVERY {0,1} outcome indicator is Q-SAT!

    # Also build full |G|^2 x |G| stacked matrix M_irrep for n <= 12 (and verify SNF equality!),
    # while for S_4 (576 x 24) run fast DHSW unit-pivot SNF on M_irrep as well!
    m_irrep_full = [list(r_irrep[spec.cayley[g][h]]) for g in range(n) for h in range(n)]
    snf_m_full = snf_unimodular(m_irrep_full, verify=(n <= 12))
    assert snf_m_full.invariant_factors == snf_r.invariant_factors

    # Solve for {0, 1} identity-outcome indicator e_0 over Q vs Z on R_G (equivalent to 1[g*h == id] on M_irrep!)
    e0_target = [1 if c == 0 else 0 for c in range(n)]
    sol_irrep = solve_with_snf(r_irrep, e0_target, snf_r)
    assert sol_irrep.q_sat and not sol_irrep.z_sat  # Genuine Z vs Q readout torsion!

    # 4. Proper-Subgroup Coset Feature Matrix C_G (|H| >= 2)
    c_coset = build_outcome_proper_coset_matrix(spec, subgroups)
    snf_coset = snf_unimodular(c_coset, verify=True)
    sol_coset = solve_with_snf(c_coset, e0_target, snf_coset)

    max_bits = max(
        snf_r.u_max_bits,
        snf_r.v_max_bits,
        snf_r.peak_intermediate_bits,
        snf_m_full.peak_intermediate_bits,
        snf_coset.u_max_bits,
        snf_coset.v_max_bits,
    )
    elapsed_us = (time.perf_counter_ns() - t0) // 1000

    return {
        "name": spec.name,
        "order": n,
        "g_squared": n * n,
        "is_abelian": spec.is_abelian,
        "num_subgroups": len(subgroups),
        "minimal_faithful_perm_degree": min_perm_deg,
        "trap5_trivial_width": w_triv,
        "trap5_guard_verified": guard_raised,
        "cyclic_1layer_circuit": cyclic_res,
        "permutation_biequivariant_circuit": perm_res,
        "irrep_feature_snf": list(snf_r.invariant_factors),
        "irrep_readout_torsion": list(snf_r.torsion_factors),
        "irrep_e0_q_sat": sol_irrep.q_sat,
        "irrep_e0_z_sat": sol_irrep.z_sat,
        "irrep_e0_q_denominator": sol_irrep.x_q_den,
        "proper_coset_num_cols": len(c_coset[0]),
        "proper_coset_q_rank": snf_coset.rank,
        "proper_coset_spans_all_outcomes_q": snf_coset.rank == n,
        "proper_coset_snf": list(snf_coset.invariant_factors),
        "proper_coset_torsion": list(snf_coset.torsion_factors),
        "proper_coset_e0_q_sat": sol_coset.q_sat,
        "proper_coset_e0_z_sat": sol_coset.z_sat,
        "max_bits": max_bits,
        "runtime_us": elapsed_us,
    }


def sweep_finite_groups_stage() -> Dict[str, Any]:
    """
    Run Cycle 1 Stage 4 across all 10 required finite groups:
      C_3, V_4, C_4, C_5, S_3, D_4, D_5, A_4, S_4, Q_8.
    """
    t0 = time.perf_counter_ns()
    specs = [
        make_cyclic_group(3),
        make_v4_group(),
        make_cyclic_group(4),
        make_cyclic_group(5),
        make_s3_group(),
        make_dihedral_group(4),
        make_dihedral_group(5),
        make_a4_group(),
        make_s4_group(),
        make_q8_group(),
    ]
    rows = [analyze_finite_group(sp) for sp in specs]

    # Explicit assertion for SPEC.md Theorem D2: V_4 Hadamard SNF == [1, 2, 2, 4]
    v4_row = [r for r in rows if r["name"] == "V_4"][0]
    assert v4_row["irrep_feature_snf"] == [1, 2, 2, 4]

    total_us = (time.perf_counter_ns() - t0) // 1000
    return {
        "stage": "stage4_finite_groups",
        "groups": rows,
        "total_runtime_us": total_us,
    }
