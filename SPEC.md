Initialize the project workspace at . and launch a 4-agent adversarial research swarm (@architect, @simulator, @formalist, @inquisitor, plus stall @monitor) for Wave I (v1.0) of "Integral Tropical-Sheaf Torsion" (Pillar 5 of the Exact-Math Observatory): build a 100% zero-dependency Python 3.9+ standard-library exact Z/Q polyhedral-sheaf torsion engine, pass all 7 repaired Wave-1 Adversarial Sanity Traps, and produce machine-certified proofs and counterexample witnesses across Tracks B, C, E, and the closed-form foundations of Tracks A and D.

## 0. Constitutional Rules, Filesystem Sandbox & Anti-Stall Guardrails

1. **STRICT FILESYSTEM BOUNDARY (Immediate Startup — Zero External Scanning):**
   - Work **EXCLUSIVELY** inside `.` (and `/tmp` solely for `@inquisitor`'s final isolated `python3 -I` check).
   - **DO NOT run `find`, `ls`, or `rg` on `$HOME/` or any sibling scratch directories.** This specification is 100% self-contained. Immediately create `./{architect,simulator,formalist,inquisitor,artifacts}` and spawn the 4 workers + `@monitor` without scanning external folders.

2. **100% Pure Python 3.9+ Standard Library Only (Zero External Dependencies):**
   - Strictly `from __future__ import annotations` + Python stdlib (`math`, `sys`, `os`, `time`, `signal`, `json`, `ast`, `pathlib`, `dataclasses`, `typing`, `itertools`, `functools`, `collections`, `unittest`, `subprocess`).
   - External packages (`numpy`, `scipy`, `sympy`, `flint`, `z3`, `gurobi`, `cvxpy`, `pycddlib`, `torch`) are **STRICTLY FORBIDDEN** and must fail `@inquisitor`'s AST contraband gate. Do NOT create `pyproject.toml` external dependencies.
   - **AST `Fraction` & Float Firewall:** Ban `float` arithmetic and `fractions.Fraction` inside all inner matrix/LP/HNF/SNF solver loops (`architect/core/`). Represent vectors/rows as `math.gcd`-normalized native Python `int` tuples/dicts; confine `Fraction` strictly to outer JSON/report serialization.

3. **Mandatory Anti-Hang Operational Rules:**
   - **Enforce `signal.alarm(20)` (20-second hard wall-clock timeout)** inside every Python test/verification stage and flush per-stage JSON checkpoints to `artifacts/` immediately so no worker ever hits the ~10-12 minute turn timeout.
   - **STRICT BAN on Unreduced Full-Matrix Z-HNF Over Orbit-Expanded Gate Sets:** Never expand asymmetric gates over `S_6` (`720` permutations) into raw integer HNF. Always use (a) DHSW unimodular tree/unit-pivot (`+-1`) peeling + Pivot-Basis Modulo-`D` HNF/SNF or (b) the Local-Global `p`-adic valuation solver (`Lemma A-LocalGlobal` below).
   - **Defer SVGs to Wave II (v2.0):** Spend 0% of Wave I tokens on SVG plotting; dedicate 100% of Wave I to exact algebra, adversarial counterexample probing, `verify_all.py` (`< 30s` total runtime), `artifacts/theorem_ledger_v1.json`, `failure_log_v1.md`, and `PROOF_DOSSIER_v1.md`.

4. **Brave & Humble 3-Valued Epistemic Ledger:**
   - Every claim in `artifacts/theorem_ledger_v1.json` MUST carry an independently machine-checked certificate and one of three honest tags:
     * `CERTIFIED_EXACT`: Proven unconditionally via exact symbolic/homological algebra (`U * A * V = S` over `Z` with `U * U_inv == I` and `V * V_inv == I` over `Z`, exact integer Farkas dual witness `y >= 0, A^T y = 0, b^T y < 0`, or exhaustive chamber identity check).
     * `FALSIFIED_COUNTEREXAMPLE`: Refuted with an exact rational/integer witness evaluated at zero error (`0/1`).
     * `OPEN_BUDGET_EXCEEDED`: Unresolved outside explicitly stated finite search bounds. **Never promote a bounded-width or fixed-arrangement UNSAT to an unconditional impossibility theorem.**

---

## 1. Four-Agent Swarm Roles Across 3 Adversarial Cycles

- **`architect/` (`@architect`)**: Builds `architect/core/exact_int_la.py`, `architect/core/bareiss_farkas_lp.py`, `architect/core/padic_local_global.py`, the 5 track modules (`track_a_foundations.py`, `track_b_decomp_splines.py`, `track_c_airy_cosheaf.py`, `track_d_group_circuits.py`, `track_e_cpa_torsors.py`), `architect/test_wave1_traps.py`, and top-level `verify_all.py`.
- **`formalist/` (`@formalist`)**: Builds an independent zero-dependency verification suite (`formalist/proof_pack_v1.py`) checking unimodular SNF factorizations, integer saturation idempotents, Farkas dual certificates, and chamber-exhaustive CPWL identities without trusting `@architect`'s high-level wrappers.
- **`simulator/` (`@simulator`)**: Sweeps parameterized infinite-family templates (`r = 2..12` 3D Reeve tetrahedra, `k = 1..10` 4-ray fans of determinant `2k+3`, multi-hole spiderwebs/annuli, finite groups `C_3, V_4, C_4, C_5, S_3, D_4, D_5, A_4, S_4, Q_8`) and logs exact bit-length, SNF torsion, and runtime tables in `simulator/cycle_benchmarks.md`.
- **`inquisitor/` (`@inquisitor`)**: Runs the scope-aware AST contraband scanner (banning external imports, `float`, inner-loop `Fraction`, and `isinstance` test-bypass cheats), probes mathematical edge cases across Cycles 1-3 (`failure_log_v1.md`), and executes the Cycle 3B clean-room `/tmp` `/usr/bin/python3 -I` audit.

---

## 2. Core Stdlib Algebraic Kernel (`architect/core/`)

1. **`exact_int_la.py` (DHSW Peeling + Pivot-Basis Modulo-`D` HNF/SNF + Saturation Projectors):**
   - Exact Q-rank & maximal linearly independent row/column pivot extraction `(P, J)` via 61-bit prime pre-screening + GCD-normalized Markowitz elimination.
   - Full unimodular Smith Normal Form `U * A * V = S` over `Z` (explicitly asserting `U @ A @ V == S` and `U @ U_inv == I`, `V @ V_inv == I` over `Z`), invariant factor extraction `d_1 | d_2 | ... | d_r`, exact inhomogeneous solver `A x = b` over `Z` vs `Q` (keeping `Z` rows unscaled so fake torsion is never injected), and Ghrist-Ding exact integral saturation projectors `P_sat = U_inv[:, :r] @ U[:r, :]` in `Z^{m x m}`.
2. **`bareiss_farkas_lp.py` (Fraction-Free Bareiss Simplex with Avis Lexicographic Pivoting):**
   - Exact rational LP feasibility/optimality solver over integer-cleared `A x <= b`, immune to degenerate origin/braid cones, returning either an exact rational primal point `(x_num_tuple, denom_int)` OR an exact non-negative integer Farkas dual certificate `y in Z_{\ge 0}^m` (`y^T A = 0`, `y^T b < 0`). Include exact vertex enumeration for low-dimensional (`2D-4D`) pointed polyhedra and exact normalized lattice volume `Vol_k(P) = k! * vol_k(P) in Z`.
3. **`padic_local_global.py` (`Lemma A-LocalGlobal` — Sub-150ms `Z[1/2]` Linear Solver):**
   - Decide `exists c in (Z[1/2])^N : A c = b` (`A in Z^{M x N}, b in Z^M`) with ZERO full-matrix HNF:
     * **Step 1 (`F_3` Pre-Screen):** Fast mod-3 Gaussian elimination on `[A | b] mod 3`. If inconsistent, immediately emit an exact mod-3 dual obstruction vector `y in {0,1,2}^M` (`y^T A == 0 mod 3`, `y^T b == 1 mod 3`).
     * **Step 2 (`Q`-Pivot Solve):** Find one exact `Q`-basic solution `c_Q` on maximal pivot basis `(P, J)`. Compute the odd part `L_odd` of `lcm(denominators(c_Q))`. If `L_odd == 1`, return `CERTIFIED_EXACT` with `c_Q in (Z[1/2])^N`.
     * **Step 3 (`Z / p^k Z` Valuation Elimination):** For each odd prime `p | L_odd`, run minimum-`v_p` pivot elimination modulo `p^k` (`k = v_p(L_odd) + 2`) across all `N` columns; either reconstruct `c in (Z[1/2])^N` via CRT or emit an exact `p`-adic obstruction witness `y in Z^M` with `v_p(y^T A) >= s > v_p(y^T b)`.

---

## 3. Gate 0: Repaired Wave-1 Adversarial Sanity Traps (`architect/test_wave1_traps.py`)

All 7 traps MUST pass 100% in Cycle 1:
1. **Trap 1 (`MAX_4` over `Z` vs. `MAX_5` over `Z` and `Z[1/2]`):**
   - Verify `MAX_4(x_1..x_4) = max(max(x_1,x_2), max(x_3,x_4))` as a strict 9-neuron (`6` Layer-1, `3` Layer-2) feedforward ReLU network with weights in `{-1, 0, +1} subset Z` and zero skip connections across all `24` chambers.
   - Certify `max(0, y_1, y_2, y_3, y_4)` (`Delta_4`) is `UNSAT` in 2 hidden `Z`-layers via `Vol_4(Delta_4) = 1 == 1 (mod 2)` (`arXiv:2302.12553` Thm 16), and verify Bakaev et al.'s (`arXiv:2505.14338` Eq. 2) exact 9-term `Z[1/2]` identity across all `120` chambers of `S_5`:
     `2 * MAX_5(x) = P_1 + P_2 + P_3 + P_4 + Q - R_13 - R_14 - R_23 - R_24`, where `P_1 = max(max(2x_5, x_1+x_2), max(x_1,x_3)+max(x_1,x_4))` (symmetrically `P_2` for `x_2` vs `{3,4}`, `P_3` for `x_3` vs `{1,2}`, `P_4` for `x_4` vs `{1,2}`), `Q = max(2x_5, max(x_1+x_2, x_3+x_4))`, and `R_ij = max(max(2x_5, x_i+x_j), max(x_1+x_2, x_3+x_4))` for `(i,j) in {1,2} x {3,4}`.
2. **Trap 2 (Unrestricted Rational Biases in Modular Refuters, `arXiv:2610.38281` Thm 8.5):**
   - Feed candidate 2-layer networks for `MAX_5` with nonbias weights in `Z[1/3]` (omitting prime `2`) and non-zero fractional biases in `Q` (including denominator `2`); assert the exact asymptotic recession / modular volume refuter outputs a certified `x* in Q^5` where `N(x*) != MAX_5(x*)`.
3. **Trap 3 (Mandatory Off-Braid Spurious Hinges, `arXiv:2502.09324v2`):**
   - Certify `UNSAT` over `Q` (with exact integer Farkas witness on `{0,1}^5` indicator evaluations) for any 2-layer `B_5`-conforming network for `MAX_5`, while verifying `SAT` over `Z[1/2]` via Trap 1's off-braid hinges `2x_5 - x_i - x_j = 0` with zero net output wall jump `w_F(MAX_5) = 0` on every non-braid facet.
4. **Trap 4 (Primitive Dual-Lattice Normals & Lineality Quotient in `D_Sigma(f)`):**
   - Quotient `Aff(Z^d)` and enforce primitive covectors `eta_F in (Z^d)*` (`gcd = 1`). Certify `Weil/Cart ~ Z/2Z` on the 2D `A_1` fan `(1,0), (-1,2), (0,-1)` and `Z/rZ` (`r = 2, 3, 5`) on the 3D Reeve tetrahedron `T_r = conv{(0,0,0),(1,0,0),(0,1,0),(1,1,r)}`.
5. **Trap 5 (Trivial `W = |G|^2` Guard in Finite-Group Circuits):**
   - Verify exact 1-layer `Z`-realization `ReLU(x_g + y_h - 1)` at `W = |G|^2` (`36` for `S_3`, `25` for `C_5`), and enforce a hard `ValueError` guard whenever any Track D compression routine is called with `W >= |G|^2`.
6. **Trap 6 (Spiderweb Cokernel Torsion & Repaired Subdivided Annular Monodromy):**
   - On the 4-vertex wheel `v_0=(0,0), v_1=(2,0), v_2=(0,2), v_3=(-2,-2)` with `z_rim = 0`, certify `UNSAT` over `Z` for integer Airy face slopes at `z_0 = 1` (`Z/2Z` torsion) and `SAT` iff `z_0 in 2Z`.
   - **Repaired Annulus Geometry:** Subdivide the spokes at inner rim `u_1=(1,0), u_2=(0,1), u_3=(-1,-1)` inside outer rim `v_1=(2,0), v_2=(0,2), v_3=(-2,-2)` and delete `v_0` to form a true 2D polygonal/triangulated annulus (`b = 2` boundary components), certifying the exact rank-3 monodromy obstruction `mu_mono^Z(w) = (Delta a, Delta b, Delta c) in Z^3`.
7. **Trap 7 (Annular CPA Torsor `LOCAL_SAT` vs. Global Vertex-LP `INFEASIBLE`):**
   - On a triangulated forward-invariant annulus `A ~ S^1 x [1,2]`, certify that the global vertex-variable CPA LP returns `INFEASIBLE` with an exact Farkas cycle witness, while the decoupled 1-cocycle solver returns `LOCAL_SAT` with exact non-zero period `[eta] != 0 in H^1(A; Q)`.

---

## 4. Wave I Proof Tracks (Exact Mathematical Specifications)

### Track B: Primitive-Lattice `D_tilde_Sigma(f)_I`, Gale-Dual CG Rank & Integral BSS Splines
1. **Theorem B1 (`Weil` vs. `Cart`, Reeve Polar Torsion & Integral BSS Degree-1 Splines — `CERTIFIED_EXACT`):**
   - Prove and symbolically verify that on any complete rational fan `Sigma` with simply connected dual region graph, `w^prim(f) in Z^{Sigma_{d-1}} <=> f in Cart(Sigma) <=> f in C^0(Sigma; Z[x_1..x_d])_1` (homogeneous degree-1 integral BSS splines), so every `f in Weil(Sigma) \ Cart(Sigma)` has empty Cartier integer DC hull `D_tilde_Sigma(w(f))_I = empty`.
   - Verify on `T_r` (`r = 2..12`) BOTH the primal edge matrix `SNF = diag(1, 1, r)` (`Weil/Cart ~ Z/rZ`) AND the polar primitive facet-form matrix (`l_12 = z`, `l_13 = -ry + z`, `l_23 = rx - z`) having `SNF = diag(1, r, r)`, proving `Z/rZ` torsion in each ridge colon ideal and `(Z/rZ)^2` torsion at the apex intersection.
   - Verify that on any 3-ray 2D fan (such as `A_1` alone), `dim B_Sigma = 3 - 2 = 1` forces every balanced function to be already convex or concave (`>= 4` rays required for non-trivial DC splits).
2. **Theorem B2 (Fractional Vertices & Chvatal-Gomory Rank Inside `Cart(Sigma)` — `CERTIFIED_EXACT`):**
   - On the 4-ray 2D fan `Sigma_*` with `v_1=(1,0), v_2=(1,2), v_3=(-1,2), v_4=(-1,-3)`, verify primitive cyclic normals `eta_1=(-2,1), eta_2=(-2,-1), eta_3=(3,-1), eta_4=(0,1)` and exact unimodular `Z`-basis `w(u, t) = (3t - u, u, 2t, 2u - t)` of `B_{Sigma_*}(Z)`.
   - For the pure integer-gradient Cartier function `(u_f, t_f) = (1, 0) => w^prim(f) = (-1, 1, 0, 2)` (regional gradients `a_P1=(0,2), a_P2=(2,1), a_P3=a_P4=(0,0) in Z^2`), certify:
     * Unique fractional LP vertex `(u*, t*) = (6/5, 2/5) -> w+* = (0, 6/5, 4/5, 2)`.
     * Round-1 CG cut `t >= 1` leaves fractional vertex `(3/2, 1)`; Round-2 CG cut `u >= 2` yields the exact Klein-sail integer hull with 3 integer vertices `(3,1)->(0,3,2,5)`, `(2,1)->(1,2,2,3)`, and `(2,2)->(4,2,4,2)` (**exact CG rank = 2**).
   - Generalize to `v_4^(k) = (-1, -(2k+1))` (`k = 1..10`, LP vertex denominator `2k+3`) and test direct-sum / higher-ray complexes (`m >= 5` rays or `d = 3`) to certify higher CG ranks `>= k`.

### Track C: 2D Integral Maxwell-Cremona Airy Cosheaves & 2D Digit-SNF Dictionary
1. **Theorem C1 (Saturated Integral Airy Sequence & Non-Primitive Edge Breakdown — `CERTIFIED_EXACT`):**
   - Construct `0 -> Z_R^sat -> Aff_R -> A_R -> 0` over `Z` and `Z_(p)` on planar lattice complexes `p(v) in Z^2`. Prove stalk freeness and certify that `Z_Z^sat` is unimodularly isomorphic to the **Primitive Force Cosheaf** `F_Z^prim` (using `(dx_e/g_e, dy_e/g_e)` where `g_e = gcd(dx_e, dy_e)`), whereas `arXiv:2311.12946` Lemma 41's unnormalized geometric force cosheaf `F_Z^geom` suffers exact edge-length torsion cokernel `bigoplus_e (Z / g_e Z)`.
   - Verify exact `H_2(A_Z)` nodal-height evaluation torsion (`SNF = diag(1,2,2,2)` unclamped) on index-`m` spiderwebs (`m = 2, 3, 4, 6`), lifted Desargues/prism projections (`arXiv:2410.12729`), and `b`-boundary punctured complexes (`b = 2, 3`, `Z^{3(b-1)}` monodromy).
2. **Theorem C2 (2D Precision-Bockstein Digit-SNF Dictionary & Global `Z`-Saturation Idempotents — `CERTIFIED_EXACT`):**
   - Extract the saturated cycle basis `Z_1(A_Z) = ker(partial_1^A)` via the right unimodular SNF multiplier `V_1`, compute SNF `U * partial_tilde_2^A * V = diag(d_1..d_r, 0)` of `C_2(A_Z) -> Z_1(A_Z)`, and verify on `Z / p^k Z` truncations that the 2D Precision-Bockstein `beta_k^(2): H_2(A_{Z/p^kZ}) -> H_1(A_Z)[p^k]` (arising from `Tor_1^Z(H_1(A_Z), Z/p^kZ)`) matches `# {i : v_p(d_i) >= k}` at every scale `k`.
   - Certify orthogonal integer projectors `P_sat, Q_free in Z^{m x m}` splitting `Z_1(A_Z)` into realizable `Z`-Airy boundaries, finite `Z/d_i Z` lattice-index torsion, and free `Z^{3(b-1)}` annular monodromy.

### Track E: Sheaf-Torsor CPA Lyapunov Synthesis on Annuli & Twisted Mobius Quotients
1. **Counterexample E0 (The Outward-Spiraling Escher Waterfall — `FALSIFIED_COUNTEREXAMPLE`):**
   - Construct an explicit polyhedral annulus `A` (e.g., octagonal/square ring `1 <= ||x||_inf <= 2`) with a piecewise-affine outward-drifting rotational vector field where a closed CPA `Q`-torsor `V_tilde` satisfies strict decrease `D^+_f V_tilde <= -eps < 0` on ALL cells and Filippov creases while trajectories spiral **outward** away from the inner cycle—refuting the naive claim that a strictly decreasing annular `R`-torsor alone certifies transverse orbital contraction!
2. **Theorem E1 (Orientable Annulus Torsor Transit + Cut-Section / Pinned-Torsor Contraction — `CERTIFIED_EXACT`):**
   - Combine (i) exact Bouligand boundary positive invariance on `partial A`, (ii) flat CPA `Q`-torsor strict decrease (`d^1 eta = 0`, `[eta] != 0`, certifying zero equilibria and monotonic winding via Poincare-Bendixson), and (iii) exact 1-lap Poincare cut-section contraction on a Ghrist-Cooperband **pinned torsor** `P_{eta, beta}` (`arXiv:2507.01226v2` §6.2) to certify true asymptotic orbital stability of a rational limit cycle.
3. **Theorem E2 (Non-Orientable Mobius Quotient — Genuine `Z/2Z` Sheaf Torsion — `CERTIFIED_EXACT`):**
   - Construct a triangulated Mobius band / antipodal period-doubling quotient `M` carrying the orientation-twisted sheaf `Z_{-1}` (`R = -1`), certifying `SNF(delta_Mobius^0) = diag(1, ..., 1, 2)`, `H^1(M; Z_{-1}) ~ Z/2Z`, and `H^1(M; Q_{-1}) = 0` (every integer twisted cocycle is rationally trivial over `Q` via `1/2`, and integrally trivial over `Z` iff its signed loop sum is even).

### Track A & Track D Closed-Form Foundations (Launchpad for Wave II)
1. **Track A Foundations (`track_a_foundations.py`):**
   - **Theorem A1 (`CERTIFIED_EXACT` + Audit Report Correction):** Formulate both integral functors—the Minkowski Support Quotient `CPWL_n(Z)/ReLU_{n,2}(Z)` (`m * h_P = h_{mP}`) and the Formal Valuation Chain Complex `P_bullet^val(Z)/Lambda_bullet^val(Z)` (`[2P] = 2^k [P]`). Refute the audit prose's false claim that `3` divides the minimal annihilator for all `n >= 4`: verify annihilator `1` at `n = 4`, annihilator `2` at `n = 5`, and construct `F_2(x_1,x_2) + F_3(x_3,x_4,x_5) in ReLU_{5,2}(Z)` (`Delta_2 x Delta_3 subset R^5`) having normalized 5-volume `Vol_5(Delta_2 x Delta_3) = binom(5,2) = 10 == 1 (mod 3) != 0`, proving top-dimensional `Vol_5 mod 3` fails Minkowski additivity at non-prime-power `d = 5` (whereas `d = 3^2 = 9`, `n = 10`, restores `Vol_9 mod 3` additivity).
   - **`MAX_6` `Z[1/6]` Baseline & `Syl_2(S_6)` Engine:** Implement Brunck et al.'s (`arXiv:2610.28587v2`) explicit `MAX_6 in ReLU_{6,2}(Q)` paramid construction AND construct a `D_6`-equivariant 2-layer hexagon gate dictionary over the 15 pairwise maxima `max(x_i, x_j)` (`i < j` on `Z_6`: 3 long diagonals, 6 edges, 6 short diagonals) to verify `6 * MAX_6` over `Z` across all `720` braid chambers, plus test `padic_local_global.py` + `Syl_2(S_6)` (`|D_4 x C_2| = 16 = 2^4`, `45` braid-chamber orbit representatives) in `< 0.2s` ready for Wave II's `Z[1/2]` frontier sprint.
   - **Theorem A3 (`vrc_{2,Z}` Separation):** Certify `vrc_{2,Z}(Delta_4) = +infinity` vs `vrc_{2,Z[1/2]}(Delta_4) <= 9` zonotope-hull blocks.
2. **Track D Foundations (`track_d_group_circuits.py`):**
   - **Theorem D1 (`CERTIFIED_EXACT`):** Prove and verify (a) universal unconstrained strict-argmax width collapse `W_Z^argmax(G) = W_Q^argmax(G) = W_R^argmax(G)` via positive layer-wise LCM scaling, (b) explicit 1-layer pure-`Z` exact `{0,1}`-indicator circuits for `C_n` of width `W = 2n - 2` biased / `2n - 1` unbiased (`W = 8 << 25` on `C_5`, refuting the `sqrt(5)` barrier for unconstrained ReLU!), and (c) zero-bias pure-`Z` bi-equivariant permutation circuits (`arXiv:2410.07476v3` with `a = (1..m)^T`) at compressed widths `W = m^2 << |G|^2`: `S_3 (9 < 36)`, `D_4 (16 < 64)`, `D_5 (25 < 100)`, `A_4 (16 < 144)`, `S_4 (16 < 576)`.
   - **Theorem D2 (`CERTIFIED_EXACT`):** Certify exact `{0,1}`-indicator SNF readout torsion `Z` vs `Q` on fixed integer character/coset feature matrices `M in Z^{|G|^2 x W}` (`V_4` Hadamard `SNF = diag(1,2,2,4)`, `S_3`, `D_4`, `Q_8`).
   - **Theorem D3 (`CERTIFIED_EXACT`):** Prove and verify on prime cyclic `C_5` that enforcing strict `(C_5 x C_5)`-permutation equivariance on hidden neurons forces `W >= 25` even over `R` (`gcd(5, 2) = 1` kills non-trivial stabilizer sign characters), while linear embedding bottlenecks separate `d_emb(R) = 2` (`Q(sqrt(5))`) from `d_emb(Q) = d_emb(Z) = phi(5) = 4` (irreducible `Phi_5`).

---

## 5. Final Cycle 3B Clean-Room Gate (`verify_all.py`)
1. `/usr/bin/python3 -I verify_all.py` must execute end-to-end in `< 30 seconds` with `0` external imports, passing 100% of `architect/test_wave1_traps.py`, `formalist/proof_pack_v1.py`, `@inquisitor`'s AST scanner, and all Track A/B/C/D/E theorems.
2. Emit `artifacts/theorem_ledger_v1.json`, `failure_log_v1.md`, and `PROOF_DOSSIER_v1.md` documenting every theorem, exact matrix/witness, runtime, and clean Wave II entry points.
