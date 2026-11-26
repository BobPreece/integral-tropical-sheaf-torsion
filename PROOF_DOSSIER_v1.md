# Integral Tropical-Sheaf Torsion — Wave I (v1.0) Master Proof & Certificate Dossier

- **Project**: *Integral Tropical-Sheaf Torsion: Exact $\mathbb{Z}$ and $\mathbb{Z}[1/2]$ Cohomological Obstructions Across ReLU Expressivity, Polyhedral Difference-of-Convex Decompositions, Cellular Airy Cosheaves, Finite-Group Circuits, and CPA Lyapunov Torsors*
- **Clean-Room Gate**: `/usr/bin/python3 -I verify_all.py` (`100%` Python 3.9+ standard library, zero external imports, zero `float`, zero inner-loop `Fraction`, zero `ast.Div`, zero `isinstance`, zero JSON float tokens, hard `signal.alarm(20)` per stage, `< 30s` end-to-end runtime, `100%` path-portable to `/tmp`)
- **Epistemic Ledger**: `artifacts/theorem_ledger_v1.json` (`21` claims, `100%` machine-checked certificate coverage via `formalist.cert_kernel.verify_ledger_certificate`: `19 CERTIFIED_EXACT`, `1 FALSIFIED_COUNTEREXAMPLE`, `1 OPEN_BUDGET_EXCEEDED`)

---

## 1. Executive Architecture & 3-Valued Epistemic Ledger Summary

Rational ($\mathbb{Q}$) and real ($\mathbb{R}$) tropical/piecewise-linear analyses systematically erase finite torsion invariants by tensoring away abelian cokernels ($\operatorname{Tor}_1^{\mathbb{Z}}(M, \mathbb{Q}/\mathbb{Z}) = 0$ after $\otimes_{\mathbb{Z}} \mathbb{Q}$). Wave I (v1.0) constructs a zero-dependency exact integer ($\mathbb{Z}$), localized ($\mathbb{Z}_{(p)}$), and dyadic/S-integral ($\mathbb{Z}[1/2], \mathbb{Z}[S^{-1}]$) computational engine and independent proof verifier unifying five concrete arenas where integer lattice integrality creates exact cohomological, polyhedral, or $p$-adic obstructions.

### 1.1 Strict Clean-Room & Epistemic Guardrails (`SPEC.md` §0)

1. **Zero-Float Exact Arithmetic Firewall**: Audited statically across every workspace `.py` file and JSON artifact by `inquisitor/ast_scanner.py`. All inner linear-algebra, LP, simplex, volume, SNF, and $p$-adic solvers operate strictly over Python arbitrary-precision `int` and `(num, den)` integer tuples.
2. **Dual Independent Verification (`architect/` vs. `formalist/`)**: Every algebraic witness emitted by `architect/` is verified from scratch by `formalist/cert_kernel.py` without trusting solver flags:
   - Unimodular Smith Normal Form: $U A V = S$, $U U^{-1} = I_m$, $V V^{-1} = I_n$, $d_1 \mid d_2 \mid \dots \mid d_r$.
   - Ghrist–Ding Saturation Projectors: $P_{\text{sat}}^2 = P_{\text{sat}}$, $P_{\text{sat}} + Q_{\text{free}} = I_m$, $P_{\text{sat}} Q_{\text{free}} = 0$, $P_{\text{sat}} A = A$, $Q_{\text{free}} A = 0$.
   - Exact Integer Farkas Duals: $y \ge 0$, $y^T A_{\text{ub}} = 0$, $y^T b_{\text{ub}} < 0$ (or signed $y^T A_{\text{eq}} = 0$, $y^T b_{\text{eq}} \ne 0$).
   - $p$-Adic Valuation Obstructions: prime $p \notin S$, $v_p(y^T A) \ge s > v_p(y^T b)$.
   - Universal Sub-Chamber CPWL Identity Splitting: dynamic pointed-cone ray splitting across all $n!$ braid chambers and all internal off-braid kinks, immune to finite point-sampling spoofing.
3. **3-Valued Brave & Humble Epistemic Discipline**: Every claim in `artifacts/theorem_ledger_v1.json` carries one of `CERTIFIED_EXACT`, `FALSIFIED_COUNTEREXAMPLE`, or `OPEN_BUDGET_EXCEEDED` (never conflating fixed-dictionary UNSAT with unconstrained impossibility).

### 1.2 Master Wave I Epistemic Ledger (`21 / 21` Machine-Certified Claims)

| Claim ID | Track | Epistemic Tag | Certificate Schema | Core Mathematical Statement / Witness Highlight |
| :--- | :---: | :--- | :--- | :--- |
| `TRAP_1` | Gate 0 | `CERTIFIED_EXACT` | `composite_dict` | Strict 9-neuron $\{-1,0,+1\}$ $\mathbb{Z}$-net for $\text{MAX}_4$; $\operatorname{Vol}_4(\Delta_4)=1\equiv 1\pmod 2$; Bakaev $\frac{1}{2}$-identity for $\text{MAX}_5$ |
| `TRAP_2` | Gate 0 | `CERTIFIED_EXACT` | `simplex_triangulation_volume` | Asymptotic recession $T_0$ + $\operatorname{Vol}_4(M\Delta_4)=M^4\equiv 1\pmod 2$ refuter for rational-bias $\mathbb{Z}_{(2)}$ networks |
| `TRAP_3` | Gate 0 | `CERTIFIED_EXACT` | `farkas_eq` | 5th Boolean Möbius difference $\Delta_5$ Farkas witness refuting $B_5$-conforming 2-layer $\text{MAX}_5$ over $\mathbb{Q}$ |
| `TRAP_4` | Gate 0 | `CERTIFIED_EXACT` | `composite_dict` | Primitive dual normals $\eta_F \in (\mathbb{Z}^d)^*$ & lineality quotient: $A_1$ $\mathbb{Z}/2\mathbb{Z}$ & Reeve $T_r$ $[1,r,r]$ torsion |
| `TRAP_5` | Gate 0 | `CERTIFIED_EXACT` | `group_circuit` | Trivial $W=\lvert G\rvert^2$ 1-layer $\mathbb{Z}$-realization $\operatorname{ReLU}(x_g+y_h-1)$ + mandatory `ValueError` at $W \ge \lvert G\rvert^2$ |
| `TRAP_6` | Gate 0 | `CERTIFIED_EXACT` | `composite_dict` | Spiderweb $[1,2,2,2]$ nodal torsion + 6-triangle subdivided annulus rank-3 monodromy (`[1,1,2]`) |
| `TRAP_7` | Gate 0 | `CERTIFIED_EXACT` | `composite_dict` | Forward-invariant annulus global CPA LP Farkas cycle witness vs. closed 1-cocycle `LOCAL_SAT` |
| `B1` | B | `CERTIFIED_EXACT` | `composite_dict` | $\operatorname{Cart}(\Sigma) \cong \text{BSS}_1(\Sigma;\mathbb{Z})$, empty DC hull on $\operatorname{Weil}\setminus\operatorname{Cart}$, Reeve $T_r$ ($r=2..12$) $[1,1,r]$ & $[1,r,r]$ |
| `B2` | B | `CERTIFIED_EXACT` | `cg_cuts` | $\Sigma_*^{(k)}$ LP vertex $(\frac{6}{5},\frac{2}{5})$, Klein sail, **Seq. Gomory $=2..3$ vs. Sim. CG $=1$**; 5-ray $\Sigma_5^{(k)}$ Sim. CG $=2k+1$ |
| `C1` | C | `CERTIFIED_EXACT` | `composite_dict` | Saturated Airy sequence $0\to\mathcal{Z}_R^{\text{sat}}\to\mathcal{A}\!\mathit{ff}_R\to\mathcal{A}_R\to 0$, $\mathcal{F}_{\mathbb{Z}}^{\text{prim}}$ vs. $\mathcal{F}_{\mathbb{Z}}^{\text{geom}}$, $\mathbb{Z}^{3(b-1)}$ monodromy |
| `C2` | C | `CERTIFIED_EXACT` | `saturation_projector` | 2D Precision-Bockstein $\beta_k^{(2)}: H_2(\mathcal{A}_{\mathbb{Z}/p^k\mathbb{Z}})\to H_1(\mathcal{A}_{\mathbb{Z}})[p^k]$ & $(P_{\text{sat}}, Q_{\text{free}})$ splitting |
| `E0` | E | `FALSIFIED_COUNTEREXAMPLE` | `poincare_trajectory` | **Outward-Spiraling Escher Waterfall**: $D^+_f\widetilde{V}\le -19 < 0$ everywhere yet 1-lap return $(\frac{21}{19})^4 = \frac{194481}{130321} > 1$ |
| `E1` | E | `CERTIFIED_EXACT` | `composite_dict` | Orientable annulus Bouligand invariance + pinned-torsor 1-lap Poincaré contraction $\frac{16}{81} < 1$ to $r^*=\frac{10}{3}$ |
| `E2` | E | `CERTIFIED_EXACT` | `snf_unimodular` | Non-orientable Möbius band $M_N$ carrying $\mathbb{Z}_{-1}$: $\delta^1\delta^0=0$, $\operatorname{SNF}(\delta^0)=[1,\dots,1,2]$, $H^1(M_N;\mathbb{Z}_{-1})\cong\mathbb{Z}/2\mathbb{Z}$ |
| `A1` | A | `CERTIFIED_EXACT` | `simplex_triangulation_volume` | Minkowski vs. Valuation functors; Kummer prime-power law; $\operatorname{Vol}_5(\Delta_2\times\Delta_3)=10\equiv 1\pmod 3$ refutation |
| `A2_MAX6_Z_SIXTH_AND_SYL2_ENGINE` | A | `CERTIFIED_EXACT` | `composite_dict` | 11-orbit (`105`-gate) $D_6$ hexagon formula for $6\cdot\text{MAX}_6$ over $\mathbb{Z}$ + `< 15 ms` `Syl_2(S_6)` (`45`-orbit) engine |
| `A2_MAX6_Z_HALF_FRONTIER` | A | `OPEN_BUDGET_EXCEEDED` | `padic_obstruction` | Fixed 11-orbit $D_6$ dictionary $p=3$ obstruction over $\mathbb{Z}[1/2]$; unconstrained $\operatorname{ReLU}_{6,2}(\mathbb{Z}[1/2])$ open for Wave II |
| `A3` | A | `CERTIFIED_EXACT` | `composite_dict` | Virtual zonotope-hull complexity separation $\operatorname{vrc}_{2,\mathbb{Z}}(\Delta_4)=+\infty$ vs. $\operatorname{vrc}_{2,\mathbb{Z}[1/2]}(\Delta_4)\le 9$ |
| `D1` | D | `CERTIFIED_EXACT` | `composite_dict` | Strict-argmax LCM collapse $W_{\mathbb{Z}}=W_{\mathbb{Q}}=W_{\mathbb{R}}$; $C_n$ width $2n-2$ ($8\ll 25$ on $C_5$); $W=m^2$ perm circuits |
| `D2` | D | `CERTIFIED_EXACT` | `composite_dict` | Character & proper-coset SNF readout trichotomy ($Q_8$ rank $4<8$; $V_4,S_3,D_4$ torsion; $S_4$ Bézout $[1]^{24}$) |
| `D3` | D | `CERTIFIED_EXACT` | `composite_dict` | Strict $(C_5\times C_5)$-equivariance forces $W\ge 25$ over $\mathbb{R}$ (Farkas) vs. $\Phi_5$ Eisenstein bottleneck ($d_{\text{emb}}(\mathbb{R})=2 < 4$) |

---

## 2. Core Stdlib Exact Algebraic Kernel (`architect/core/`)

### 2.1 `exact_int_la.py`: Mersenne Pre-Screen, DHSW Peeling SNF & Saturation Idempotents

- **Rank & Pivot Extraction (`extract_pivot_basis`)**: Uses a fast modular pre-screen over the 61-bit Mersenne prime $M_{61} = 2^{61} - 1$ to identify candidate linearly independent rows/columns in $O(\text{nnz})$ machine-word operations, followed by exact GCD-normalized fraction-free Markowitz elimination over $\mathbb{Z}$. Crucially, if any entry is a nonzero multiple of $M_{61}$ (probed adversarially via $\operatorname{diag}(2^{61}-1, 1)$ in `K1.4`), the exact fallback sweeps remaining rows/columns so $\mathbb{Q}$-rank is never underestimated.
- **Unimodular Smith Normal Form (`smith_normal_form`)**: Combines Dumas–Heckenbach–Saunders–Welker (DHSW) minimum-Markowitz-cost $\pm 1$ unit-pivot peeling on sparse cellular/coset coboundary matrices with nearest-integer-quotient (`round`-free symmetric remainder $\lvert r\rvert \le \lvert d\rvert/2$) Euclidean row/column elimination and explicit divisibility restoration ($d_1 \mid d_2 \mid \dots \mid d_r$). Emits full two-sided unimodular multipliers $(U, U^{-1}, S, V, V^{-1})$.
- **Ghrist–Ding Integer Saturation Projectors (`saturation_projectors`)**: Given $U A V = \operatorname{diag}(d_1,\dots,d_r, 0)$, constructs
  $$P_{\text{sat}} = U^{-1}_{[:, :r]} U_{[:r, :]} \in \mathbb{Z}^{m \times m}, \qquad Q_{\text{free}} = I_m - P_{\text{sat}} \in \mathbb{Z}^{m \times m},$$
  certifying $P_{\text{sat}}^2 = P_{\text{sat}}$, $P_{\text{sat}} A = A$, $Q_{\text{free}} A = 0$, and splitting $\mathbb{Z}^m = \operatorname{sat}_{\mathbb{Z}}(\operatorname{im} A) \oplus \mathbb{Z}^{m-r}$ over $\mathbb{Z}$ without rational division.

### 2.2 `bareiss_farkas_lp.py`: Lexicographic Fraction-Free Simplex & Beneath-Beyond Volume

- **Anti-Cycling Exact Simplex (`solve_lp`)**: Represents every tableau $T \in \mathbb{Z}^{(m+1)\times(n+1+m)}$ with a strictly positive integer determinant denominator $D > 0$ updated by exact Bareiss division $T'_{i,j} = (T_{p,q} T_{i,j} - T_{i,q} T_{p,j}) // D_{\text{prev}}$. Degenerate polyhedral cones (such as the 5D braid cone at the origin) are resolved deterministically with zero cycling via the **Avis–Chvátal lexicographic ratio test** comparing exact integer cross-multiplied rows `(b_i, E_{i,0}, ..., E_{i,m-1}) * a_{r,q}` against `(b_r, E_{r,0}, ..., E_{r,m-1}) * a_{i,q}`. Phase I infeasibility directly extracts a primitive non-negative integer Farkas vector $y \in \mathbb{Z}_{\ge 0}^m$ satisfying $y^T A_{\text{ub}} = 0$ and $y^T b_{\text{ub}} < 0$.
- **Origin-Invariant Lattice Volume (`normalized_lattice_volume_vertices`)**: Translates any polytope $P \subset \mathbb{Z}^d$ by $-v_0$, projects onto its exact affine hull via unimodular SNF when $\dim(\operatorname{aff} P) < d$, and executes exact integer Beneath-Beyond convex-hull triangulation summing $\lvert\det(S_k)\rvert = d! \operatorname{Vol}_{\text{Eucl}}(S_k)$ (surviving translated Reeve $T_r + (5,7,11)$ where Pick/origin-cone assumptions fail).

### 2.3 `padic_local_global.py`: `Lemma A-LocalGlobal` Sub-15ms $\mathbb{Z}[1/2]$ & $S$-Integral Solver

To decide $\exists c \in \mathbb{Z}[S^{-1}]^N$ with $A c = b$ without computing catastrophic full-matrix Hermite Normal Forms over $N \gg r$ columns:
1. **Step 1 ($\mathbb{F}_3$ Fast Pre-Screen)**: When $3 \notin S$ (in particular for $R = \mathbb{Z}[1/2]$), reduces $(A \mid b) \bmod 3$. Any pivot in the augmented column immediately lifts to $y \in \{0,1,2\}^M$ with $y^T A \equiv 0 \pmod 3$ and $y^T b \equiv 1 \text{ or } 2 \pmod 3$.
2. **Step 2 (Row Compression & Cancelled-Prime Discovery)**: Extracts an exact $\mathbb{Q}$-row basis $P$ ($\lvert P\rvert = r$), checks exact consistency $A_{\bar{P}} c_{\mathbb{Q}} = b_{\bar{P}}$, and computes $D_{\text{piv}} = \lvert\det(A_{P,J})\rvert$ alongside a deterministic non-pivot rescue probing prime divisors of $D_{\text{piv}}$ (defeating the **Hidden Cancelled-Prime Trap** `K3.2`: $A = \begin{pmatrix}3&0&1\\0&5&1\end{pmatrix}, b = \begin{pmatrix}1\\5\end{pmatrix}$, where $c_{\mathbb{Q}} = (\frac{1}{3}, 1, 0)$ hides prime $5$ via $5/5 = 1$, yet true $\mathbb{Z}[1/2]$ feasibility requires shifting non-pivot $c_3 = 10$ to obtain $(-3, -1, 10) \in \mathbb{Z}^3$).
3. **Step 3 ($p$-Adic Valuation Peeling vs. CRT Reconstruction)**: Factors odd/uninverted primes via deterministic 64-bit Miller–Rabin + Brent–Pollard $\rho$, solves locally over $\mathbb{Z}/p^{e_p}\mathbb{Z}$ for free non-pivot coordinates killing all uninverted denominators, or emits an exact integer valuation witness $v_p(y^T A) \ge s > v_p(y^T b)$.

---

## 3. Gate 0: Repaired Wave-1 Adversarial Sanity Traps (`TRAP_1`–`TRAP_7`)

- **Trap 1 (`TRAP_1`, `CERTIFIED_EXACT`)**:
  1. $\text{MAX}_4(x_1,x_2,x_3,x_4) = \max(\max(x_1,x_2), \max(x_3,x_4))$ is realized by a strict zero-skip, zero-bias, $\{-1,0,+1\}$-weight 2-hidden-layer pure-$\mathbb{Z}$ ReLU network with $6 + 3 = 9$ hidden neurons (`MAX4_W1`, `MAX4_W2`, `MAX4_W3`), verified across all $24$ $S_4$ chambers and $84$ symbolic signed-braid sub-cones.
  2. $\text{MAX}_5 \notin \operatorname{ReLU}_{5,2}(\mathbb{Z})$: restricting to $x_5 = 0$ gives $\max(0, x_1, x_2, x_3, x_4)$ with Newton polytope $\Delta_4 = \operatorname{conv}\{0, e_1, e_2, e_3, e_4\}$ of normalized volume $\operatorname{Vol}_4(\Delta_4) = \lvert\det(I_4)\rvert = 1 \equiv 1 \pmod 2$. Every 2-layer $\mathbb{Z}$-neuron Newton polytope $\operatorname{conv}(Z_{k_+}, Z_{k_-}) \subset \mathbb{Z}^4$ has $\operatorname{Vol}_4$ divisible by $\gcd(4!, 3!1!, 2!2!) = \gcd(24, 6, 4) = 2$, and at prime-power $d = 4 = 2^2$ every mixed multinomial $\frac{4!}{r_1!\cdots r_t!}$ ($t \ge 2, r_j \ge 1$) lies in $\{24, 12, 6, 4\} \subset 2\mathbb{Z}$.
  3. Over $\mathbb{Z}[1/2]$, Bakaev et al.'s (`arXiv:2505.14338` Eq. 2) 9-term identity $2\cdot\text{MAX}_5 = P_1 + P_2 + P_3 + P_4 + Q - R_{13} - R_{14} - R_{23} - R_{24}$ realizes $\text{MAX}_5 \in \operatorname{ReLU}_{5,2}(\mathbb{Z}[1/2])$ across all $480$ symbolic leaf sub-chambers ($360$ dynamic off-braid splits).
- **Trap 2 (`TRAP_2`, `CERTIFIED_EXACT`)**: Refutes candidate 2-layer networks with nonbias weights in $\mathbb{Z}_{(2)}$ (e.g., $\mathbb{Z}[1/3]$) and **unrestricted rational biases including denominator $2$** (even when tuned so $N(0) = 0$ and $N\rvert_{\{0,1\}^5} \equiv \text{MAX}_5\rvert_{\{0,1\}^5}$!). Under asymptotic recession $N_{\text{rec}}(d) = \lim_{t\to+\infty} t^{-1} N(t d)$, all biases vanish identically; clearing odd nonbias weight denominator $M \equiv 1 \pmod 2$ preserves $\operatorname{Vol}_4(M\Delta_4) = M^4 \equiv 1 \pmod 2$, guaranteeing an exact ray $d \in \mathbb{Z}^5$ with $N_{\text{rec}}(d) \ne \text{MAX}_5(d)$ and an exact kink-clearing threshold $T_0 \in \mathbb{Z}_{>0}$ producing $x^* \in \{T_0 d, (T_0+1)d\}$ with $N(x^*) \ne \text{MAX}_5(x^*)$ at `0/1` error.
- **Trap 3 (`TRAP_3`, `CERTIFIED_EXACT`)**: Every $B_5$-conforming 2-layer ReLU gate depends on at most $4$ coordinates (since $\text{MAX}_3$ is not 1-layer realizable, no chamber-sign-consistent $L \in V_1$ can involve all $5$ variables non-trivially). Consequently, the 5th Boolean Möbius difference $\Delta_5(f) = \sum_{S \subseteq [5]} (-1)^{5-\lvert S\rvert} f(\mathbf{1}_S)$ annihilates every $B_5$-conforming 2-layer gate ($\Delta_5(g) = 0$) while $\Delta_5(\text{MAX}_5) = +1 \ne 0$. Bakaev's $\mathbb{Z}[1/2]$ network escapes this obstruction solely via non-zero off-braid spurious hinges along $2x_5 - x_i - x_j = 0$ and $x_1 + x_2 - x_3 - x_4 = 0$ whose primitive wall jumps cancel to $0$ in the sum.
- **Trap 4 (`TRAP_4`, `CERTIFIED_EXACT`)**: Using primitive dual-lattice normals $\eta_F \in (\mathbb{Z}^d)^*$ ($\gcd(\eta_F) = 1$) and quotienting linear space $M$ certifies $\operatorname{Weil}(\Sigma_{A_1}) / \operatorname{Cart}(\Sigma_{A_1}) \cong \mathbb{Z}/2\mathbb{Z}$ ($w^{\text{prim}} = (\frac{1}{2}, \frac{1}{2}, 1)$) and Reeve $T_r$ polar facet torsion $\mathbb{Z}^3 / L_r\mathbb{Z}^3 \cong (\mathbb{Z}/r\mathbb{Z})^2$ ($\operatorname{SNF}(L_r) = [1, r, r]$). Using unnormalized $\det = 2$ normals spuriously doubles $\frac{1}{2} \mapsto 1$, erasing torsion.
- **Trap 5 (`TRAP_5`, `CERTIFIED_EXACT`)**: For every finite group $G$, $W = \lvert G\rvert^2$ neurons $\phi_{g,h}(x,y) = \operatorname{ReLU}(x_g + y_h - 1)$ trivially realize multiplication over $\mathbb{Z}$ in 1 hidden layer. All Track D compression routines enforce a hard `ValueError` guard whenever $W \ge \lvert G\rvert^2$.
- **Trap 6 (`TRAP_6`, `CERTIFIED_EXACT`)**: On the index-2 wheel $v_0=(0,0), v_1=(2,0), v_2=(0,2), v_3=(-2,-2)$, $z_{\text{rim}}=0, z_0=1$ is $\mathbb{Q}$-SAT yet $\mathbb{Z}$-UNSAT ($\mathbb{Z}$-SAT iff $2 \mid z_0$; unclamped nodal $\operatorname{SNF} = [1,2,2,2]$). On the punctured annulus, leaving the 3 trapezoidal sectors untriangulated causes all 3 interior spokes to concur at $(0,0)$, collapsing affine monodromy rank from $3$ to $2$; subdividing into **6 counterclockwise triangles** via chords $u_1 v_2, u_2 v_3, u_3 v_1$ restores full rank $3$ ($\operatorname{SNF}(J_{\text{mono}}) = [1,1,2]$, $H_1(\mathcal{A}_{\mathbb{Z}}) \cong \mathbb{Z}^3$).
- **Trap 7 (`TRAP_7`, `CERTIFIED_EXACT`)**: On a forward-invariant triangulated annulus with strictly rotational flow, global single-valued vertex CPA synthesis $V \in C^0(A,\mathbb{R})$ is `INFEASIBLE` (certified by a non-negative integer Farkas cycle witness telescope-summing around the hole), whereas decoupled closed 1-cocycle CPA synthesis ($\eta \in Z^1(A;\mathbb{Q})$, $d^1\eta = 0$) is `LOCAL_SAT` with equal negative Stokes periods around both rims.

---

## 4. Track B: Primitive-Lattice Cartier DC Polyhedra, BSS Splines & Chvátal–Gomory Rank (`B1`, `B2`)

### 4.1 Theorem B1 (`CERTIFIED_EXACT`) — Weil vs. Cartier, Reeve Polar Torsion & BSS Splines

1. **Equivalence with Homogeneous Degree-1 Integral Billera–Schenck–Stillman Splines**: On any complete full-dimensional rational polyhedral fan $\Sigma$ in $\mathbb{R}^d$ (which is topologically $\mathbb{R}^d$, hence simply connected), $f \in \operatorname{Weil}(\Sigma)$ satisfies $w_F^{\text{prim}}(f) \in \mathbb{Z}$ for every interior wall $F$ if and only if local gradients integrate around all codimension-2 ridges with zero monodromy inside $(\mathbb{Z}^d)^*$, i.e., $f \in \operatorname{Cart}(\Sigma) \cong C^0(\Sigma; \mathbb{Z}[x_1,\dots,x_d])_1$. Whenever $f \in \operatorname{Weil}(\Sigma) \setminus \operatorname{Cart}(\Sigma)$, $w^{\text{prim}}(f) \notin \mathbb{Z}^m$; since every pair $(g, h) \in \operatorname{Cart}_+(\Sigma)^2$ satisfies $w^{\text{prim}}(g) - w^{\text{prim}}(h) \in \mathbb{Z}^m$, the Cartier DC integer hull $\widetilde{\mathcal{D}}_\Sigma(f)_{\mathbb{Z}} = \emptyset$.
2. **3-Ray 2D Collapse**: For any positively spanning 3-ray 2D fan, $\dim \mathcal{B}_\Sigma = 3 - 2 = 1$ with a strictly positive primitive generator $w_0 \in \mathbb{Z}_{>0}^3$, so every balanced function is already globally convex or globally concave.
3. **3D Reeve Tetrahedra $T_r = \operatorname{conv}\{(0,0,0),(1,0,0),(0,1,0),(1,1,r)\}$ ($r = 2..12$, plus $r=1$ control)**:
   - $\operatorname{Vol}_3(T_r) = r$, $\lvert T_r \cap \mathbb{Z}^3\rvert = 4$ (constant lattice-point count despite unbounded volume).
   - Primal apex edge matrix $E_r = \begin{pmatrix}1&0&0\\0&1&0\\1&1&r\end{pmatrix}$ has $\operatorname{SNF}(E_r) = \operatorname{diag}(1, 1, r)$, certifying $\operatorname{Weil}(\Sigma_r)/\operatorname{Cart}(\Sigma_r) \cong \mathbb{Z}/r\mathbb{Z}$.
   - Polar primitive facet-form matrix $L_r = \begin{pmatrix}0&0&1\\0&-r&1\\r&0&-1\end{pmatrix}$ ($\ell_{12}=z, \ell_{13}=-ry+z, \ell_{23}=rx-z$) has $\operatorname{SNF}(L_r) = \operatorname{diag}(1, r, r)$ ($(\mathbb{Z}/r\mathbb{Z})^2$ dual-apex torsion) and all 3 ridge colon $2\times 3$ submatrices have $\operatorname{SNF} = \operatorname{diag}(1, r)$.

### 4.2 Theorem B2 (`CERTIFIED_EXACT`) — Fractional Vertices, Klein Sail & Chvátal–Gomory Definition Split

On the 4-ray 2D complete fan family $\Sigma_*^{(k)}$ ($k = 1..10$) with $v_1=(1,0), v_2=(1,2), v_3=(-1,2), v_4^{(k)}=(-1,-(2k+1))$ ($\det = 2k+3$), the balanced integer wall-weight lattice $\mathcal{B}_{\Sigma_*^{(k)}}(\mathbb{Z}) \cong \mathbb{Z}^2$ has unimodular basis
$$w^{(k)}(u, t) = \bigl(-u + (2k+1)t,\; u,\; 2t,\; 2u - (2k-1)t\bigr).$$
For the pure integer-gradient Cartier function $f \in \operatorname{Cart}(\Sigma_*^{(k)})$ with $(u_f, t_f) = (1, 0)$, $w^{\text{prim}}(f) = (-1, 1, 0, 2) \in \mathbb{Z}^4$ (regional gradients $a_{P_4}=(0,0), a_{P_1}=(0,2), a_{P_2}=(2,1), a_{P_3}=(0,0)$):
1. **Unique Fractional LP Optimum**:Minimizing $\mathbf{1}^T w_+$ over $P_0 = \{w^{(k)}(u,t) \ge (0, 1, 0, 2)\}$ yields the unique rational vertex $(u^*, t^*) = \bigl(\frac{4k+2}{2k+3}, \frac{2}{2k+3}\bigr)$ — at $k = 1$, $(u^*, t^*) = (\frac{6}{5}, \frac{2}{5})$ and $w_+^* = (0, \frac{6}{5}, \frac{4}{5}, 2)$ ($\ell_1$-cost $4 < 6$).
2. **Exact CG Definition Split (`B2-CG-DEFINITION-SPLIT`)**:
   - **Sequential Single-Cut Gomory Rank**: At $k = 1$, Round-1 cut $t \ge \lceil 2/5\rceil = 1$ leaves fractional vertex $(\frac{3}{2}, 1)$; Round-2 cut $u \ge \lceil 3/2\rceil = 2$ yields the integral **Klein sail** $\{(3,1), (2,1), (2,2)\}$ (**2 sequential cuts**; for $k \ge 2$, axis cut $u \ge k+1$ leaves $(k+1, \frac{2k}{2k-1})$, requiring a **3rd** oblique cut $u - (k-1)t \ge 2$).
   - **Simultaneous Elementary Schrijver–Chvátal Closure Rank ($P \mapsto P^{(1)}$) $= 1$ for all $k = 1..10$**: Because $u \ge 1$ and $2t \ge 0$ are LP-redundant on $P_0$, $P_0$ is a single 2-facet planar cone; at $k = 1$, both Round-1 multipliers $\lambda^{(1)} = (\frac{2}{5}, 0, 0, \frac{1}{5})$ ($\implies t \ge 1$) and $\lambda^{(2)} = (\frac{1}{5}, 0, 0, \frac{3}{5})$ ($\implies u \ge \lceil 6/5\rceil = 2$) belong simultaneously to $P_0^{(1)}$!
3. **Genuine Unbounded Simultaneous Chvátal Rank in $\operatorname{Cart}(\Sigma)$**: Passing to the 5-ray 2D complete fan $\Sigma_5^{(k)}$ ($v_1=(1,0), v_2=(2k+1,1), v_3=(-(2k+1),1), v_4=(-1,-2), v_5=(0,-1)$, $\dim \mathcal{B} = 3$) breaks the planar 2-facet cone bound: the pure Cartier function $w^{\text{prim}}(f) = (0, 1, 0, 1, -(2k+1)) \in \mathbb{Z}^5$ has **Simultaneous Elementary Chvátal Rank $= 2k + 1$** (`3` at $k=1$, `5` at $k=2$, `7` at $k=3$, `9` at $k=4$).

---

## 5. Track C: 2D Integral Maxwell–Cremona Airy Cosheaves & Digit-SNF Dictionary (`C1`, `C2`)

### 5.1 Theorem C1 (`CERTIFIED_EXACT`) — Saturated Integral Airy Sequence & Geometric Force Torsion

On any finite connected 2D planar cell complex $K$ with integer vertices $p(v) \in \mathbb{Z}^2$ and $b \ge 1$ boundary components ($R \in \{\mathbb{Z}, \mathbb{Z}_{(p)}\}$):
1. **Stalk Freeness & Short Exact Sequence**: $0 \to \mathcal{Z}_R^{\text{sat}} \to \mathcal{A}\!\mathit{ff}_R \to \mathcal{A}_R \to 0$ is stalkwise split-exact: on each face $\sigma$, $\mathcal{Z}_R^{\text{sat}}(\sigma) = 0, \mathcal{A}_R(\sigma) \cong R^3$; on each edge $e$ with $\Delta p_e = g_e t_e$ ($\gcd(t_{e,x}, t_{e,y}) = 1$), $\mathcal{Z}_R^{\text{sat}}(e) = R \cdot (-t_{e,y}, t_{e,x}, t_{e,y} x_u - t_{e,x} y_u) \cong R^1$ and $\mathcal{A}_R(e) \cong R^2$; on each vertex $v$, $\mathcal{Z}_R^{\text{sat}}(v) \cong R^2$ and $\mathcal{A}_R(v) \cong R^1$.
2. **Primitive vs. Geometric Force Cosheaf**: Under the 90°-rotated Maxwell–Cremona map, $\mathcal{Z}_{\mathbb{Z}}^{\text{sat}} \cong \mathcal{F}_{\mathbb{Z}}^{\text{prim}}$ is unimodularly torsion-free, whereas Cooperband et al.'s (`arXiv:2311.12946` Lemma 41) unnormalized geometric edge-vector cosheaf $\mathcal{F}_{\mathbb{Z}}^{\text{geom}}(e) = \mathbb{Z}\cdot\Delta p_e$ embeds with edge-length torsion cokernel $\bigoplus_e (\mathbb{Z}/g_e\mathbb{Z})$.
3. **Nodal Evaluation Torsion & Multi-Hole Monodromy**:
   - Scaled index-$m$ spiderwebs ($m=2,3,4,6$): unclamped $H_2^{\text{int}}(\mathcal{A}_{\mathbb{Z}}) \to \mathbb{Z}^4$ has $\operatorname{SNF} = \operatorname{diag}(1, m, m, m)$; clamped $z_0 = 1, z_{\text{rim}} = 0$ is $\mathbb{Z}_{(p)}$-realizable iff $p \nmid m$.
   - Primitive-spoke twisted wheels ($m=2,4$): all interior spokes have $g_e = 1$, yet determinant shear produces genuine nodal torsion $\operatorname{SNF} = \operatorname{diag}(1, 1, 1, m)$.
   - Punctured complexes ($b = 2$ 6-triangle annulus and $b = 3$ 26-triangle double-punctured grid): free affine monodromy $\ker(\delta_{\mathbb{Z}})\text{-rank} = 3(b - 1)$ (`3` at $b=2$, `6` at $b=3$).

### 5.2 Theorem C2 (`CERTIFIED_EXACT`) — 2D Precision-Bockstein & Global Saturation Projectors

Extracting a saturated $\mathbb{Z}$-basis of $Z_1(\mathcal{A}_{\mathbb{Z}}) = \ker(\partial_1^{\mathcal{A}})$ via the trailing columns of $V_1$ in $U_1 \partial_1^{\mathcal{A}} V_1 = S_1$ reduces $\widetilde{\partial}_2^{\mathcal{A}}: C_2(\mathcal{A}_{\mathbb{Z}}) \to Z_1(\mathcal{A}_{\mathbb{Z}})$ to $U \widetilde{\partial}_2^{\mathcal{A}} V = \operatorname{diag}(d_1,\dots,d_r, 0)$. Across all tested complexes (including the composite $2^2 \cdot 3$-torsion lifted Desargues prism $m=3$, twisted wheel $m=4$, and subdivided annulus $b=2$), the 2D Precision-Bockstein rank at scale $p^k$ ($p \in \{2,3\}, k \in \{1,2,3\}$) equals $\#\{i : v_p(d_i) \ge k\}$ identically, and $(P_{\text{sat}}, Q_{\text{free}})$ orthogonally splits $Z_1(\mathcal{A}_{\mathbb{Z}})$ into $\mathbb{Z}$-realizable Airy boundaries, finite $\bigoplus_i \mathbb{Z}/d_i\mathbb{Z}$ lattice-index torsion, and free $\mathbb{Z}^{3(b-1)}$ annular monodromy.

---

## 6. Track E: Sheaf-Torsor CPA Lyapunov Synthesis, Escher Waterfall & Twisted Möbius (`E0`, `E1`, `E2`)

### 6.1 Counterexample E0 (`FALSIFIED_COUNTEREXAMPLE`) — The Outward-Spiraling Escher Waterfall

- **Claim Refuted**: *"On a triangulated annulus $A \cong S^1 \times [1,2]$, existence of a closed CPA $\mathbb{R}/\mathbb{Q}$-torsor $\widetilde{V}$ ($d^1\eta = 0, [\eta] \ne 0$) satisfying strict cell and Clarke/Filippov crease decrease $D^+_f \widetilde{V} \le -\varepsilon < 0$ everywhere certifies transverse orbital contraction."*
- **Exact Construction**: On the 8-triangle square annulus $A = \{1 \le \|x\|_\infty \le 2\}$ with sector-rotated outward rotational field $f_k = R_{90^\circ}^k(1, 20)$ and flat integer CPA torsor gradients $g_{2k} = R_{90^\circ}^k(-1, -1)$, $g_{2k+1} = R_{90^\circ}^k(2, -2)$ ($d^1\eta = 0$, period $[\eta] = -16$):
  1. Every 2D cell and all $32$ Clarke/Filippov crease pairings satisfy $\langle g_{\tau^\pm}, f_{\tau^\pm}\rangle \in \{-38, -21, -19\} \le -19 < 0$, with strictly positive transversal crease crossings ($\langle f_\pm, n\rangle > 0$, **zero sliding modes**).
  2. Yet exact `0/1`-error rational trajectory integration from $x_0 = (1, -1)$ on $\Sigma_{\text{cut}} = \{(r,-r) : 1 \le r \le 2\}$ visits $(1,-1) \to (\frac{21}{19},\frac{21}{19}) \to (-\frac{441}{361},\frac{441}{361}) \to (-\frac{9261}{6859},-\frac{9261}{6859}) \to (\frac{194481}{130321}, -\frac{194481}{130321})$, proving **strict outward 1-lap Poincaré expansion**:
     $$P(r_0) = \left(\frac{21}{19}\right)^4 r_0 = \frac{194481}{130321}\, r_0 > r_0 \qquad \left(1 < \frac{194481}{130321} < 2\right).$$
  - **Mechanism**: Angular progress consumes the negative period $[\eta] = -16$ per lap, masking positive radial expansion!

### 6.2 Theorem E1 (`CERTIFIED_EXACT`) — Orientable Annulus Torsor Transit + Pinned-Torsor Contraction

On $A = \{2 \le \|x\|_\infty \le 6\}$ with oblique-crease refraction $f_{2k} = R_{90^\circ}^k(-1, 10)$ (outer triangle) and $f_{2k+1} = R_{90^\circ}^k(1, 10)$ (inner triangle):
1. **Strict Bouligand Positive Invariance**: $\langle f, n_{\text{out}}\rangle = -1 < 0$ on all 8 outer and inner hole edges (including the non-convex $270^\circ$ reflex inner hole corners where $T_A(u_k) = \{\xi \ge 0 \lor \eta \ge 0\}$).
2. **Global CPA Infeasibility vs. Torsor Transit**: Global vertex-variable CPA LP is `INFEASIBLE` (certified by integer Farkas cycle witness), while the flat CPA torsor ($[\eta] = -96$) satisfies $D^+_f \widetilde{V} \le -8 < 0$ across all cells and creases (ruling out equilibria and proving global transit to $\Sigma_{\text{cut}}$).
3. **Exact Pinned-Torsor Poincaré Contraction**: Across each sector, diagonal refraction maps $r \mapsto \frac{2}{3} r + \frac{10}{9}$, yielding the exact 4-sector 1-lap return map
   $$P(r) - \frac{10}{3} = \left(\frac{2}{3}\right)^4 \left(r - \frac{10}{3}\right) = \frac{16}{81}\left(r - \frac{10}{3}\right),$$
   certifying contraction factor $\frac{16}{81} < 1$ on the Ghrist–Cooperband pinned torsor $\mathcal{P}_{\eta,\beta}$ (`arXiv:2507.01226v2` §6.2) onto the unique rational limit cycle $r^* = \frac{10}{3}$ ($P(2) = \frac{238}{81}$, $P(6) = \frac{938}{243}$).

### 6.3 Theorem E2 (`CERTIFIED_EXACT`) — Non-Orientable Möbius Quotient $\mathbb{Z}/2\mathbb{Z}$ Sheaf Torsion

Because $H^1(A; \mathbb{Z}) \cong \mathbb{Z}$ is torsion-free on every orientable annulus, genuine $\mathbb{Z}$ vs. $\mathbb{Q}$ sheaf cohomology torsion arises on the triangulated non-orientable Möbius band $M_N$ ($N \ge 3$ panels, single boundary cycle, $\chi = 0$) carrying the orientation-twisted local system $\mathbb{Z}_{-1}$ ($R_e = -1$ across the antipodal seam):
$$\delta^1 \circ \delta^0 = 0, \qquad \operatorname{SNF}(\delta^0_{M_N}) = \operatorname{diag}(\underbrace{1,\dots,1}_{2N-1}, 2), \qquad H^1(M_N; \mathbb{Z}_{-1}) \cong \mathbb{Z}/2\mathbb{Z}, \qquad H^1(M_N; \mathbb{Q}_{-1}) = 0.$$
Every twisted 1-cocycle is rationally trivial via half-integers ($\frac{1}{2}\mathbb{Z}$), while integral triviality holds iff the twisted loop sum around the central cycle is even.

---

## 7. Track A: Integral Functors, `MAX_6` `Syl_2(S_6)` Engine & Virtual Zonotope Complexity (`A1`, `A2`, `A3`)

### 7.1 Theorem A1 (`CERTIFIED_EXACT`) — Minkowski vs. Valuation Functors & $\operatorname{Vol}_5(\Delta_2 \times \Delta_3) = 10$

1. **Two Distinct Integral Functors**:
   - *Minkowski Support Quotient*: $\mathcal{Q}_n^{\text{Mink}}(\mathbb{Z}) = \operatorname{CPWL}_n(\mathbb{Z}) / \operatorname{ReLU}_{n,2}(\mathbb{Z})$, governed by linear support homogeneity $m \cdot h_P = h_{mP}$ (where minimal integer annihilators live: $1$ at $n=4$, $2$ at $n=5$, divisor of $6$ at $n=6$).
   - *Formal Valuation Chain Complex*: $\mathcal{P}_\bullet^{\text{val}}(\mathbb{Z}) / \Lambda_\bullet^{\text{val}}(\mathbb{Z})$, governed by polynomial dilation $[2P] = 2^k [P]$ in degree $k$.
2. **Refutation of Universal Mod-3 Annihilator Claim**: At $n = 6$ ($d = 5$, non-prime-power with respect to $p = 3$), $F(x_1,\dots,x_5) = \max(0, x_1, x_2) + \max(0, x_3, x_4, x_5) \in \operatorname{ReLU}_{5,2}(\mathbb{Z})$ has Newton polytope $\Delta_2 \times \Delta_3 \subset \mathbb{Z}^5$ ($12$ vertices), triangulated explicitly into $\binom{5}{2} = 10$ unimodular staircase 5-simplices:
   $$\operatorname{Vol}_5(\Delta_2 \times \Delta_3) = \binom{5}{2} = 10 \equiv 1 \not\equiv 0 \pmod 3.$$
   By Kummer's theorem, $\gcd_{1 \le a < d} \binom{d}{a} = p$ iff $d = p^k$ is a prime power ($1$ for composite $d = 6, 10$), so top-dimensional $\operatorname{Vol}_d \bmod 3$ is Minkowski-additive at $d = 3^1 = 3$ and $d = 3^2 = 9$ ($\gcd_{1\le a\le 8}\binom{9}{a} = 3$), **not** at $d = 5$.

### 7.2 Theorem A2 (`CERTIFIED_EXACT` on $\mathbb{Z}[1/6]$ & `Syl_2(S_6)`; `OPEN_BUDGET_EXCEEDED` on $\mathbb{Z}[1/2]$)

1. **Pure-$\mathbb{Z}$ $D_6$-Equivariant Hexagon Decomposition of $6\cdot\text{MAX}_6$ (`CERTIFIED_EXACT`)**: Over the $15$ pairwise maxima $m_{ij} = \max(x_i, x_j)$ on the regular hexagon $\mathbb{Z}_6$ ($6$ edges, $6$ short diagonals, $3$ long diagonals), $11$ $D_6$-orbits (`6` Layer-1 edge gates of weight $-2$ + `99` Layer-2 paramid gates $\max(m_{ab}+m_{cd}, m_{ef}+m_{gh})$ of weights $\in \{-2, -1, +1\}$, `105` total gates) realize $6\cdot\text{MAX}_6$ exactly over $\mathbb{Z}$, certified across `2,160` braid-chamber points, internal off-braid 2nd-difference zero probes, AND `formalist`'s universal pointed-cone symbolic sub-chamber splitter (`720` braid chambers, `13,944` leaf sub-chambers). Thus $\text{MAX}_6 \in \operatorname{ReLU}_{6,2}(\mathbb{Z}[1/6])$.
2. **Sub-200ms `Syl_2(S_6)` Local-Global Engine (`CERTIFIED_EXACT`) & Honest $\mathbb{Z}[1/2]$ Frontier (`OPEN_BUDGET_EXCEEDED`)**: Restricting $S_6$ (`720` chambers) to its Sylow 2-subgroup $\operatorname{Syl}_2(S_6) = D_4(\{0,1,2,3\}) \times C_2(\{4,5\})$ of order $16 = 2^4$ (whose order is a unit in $\mathbb{Z}_{(p)}$ for every odd prime $p$, so $\mathbb{Z}[1/2]$-averaging introduces zero odd denominators!) partitions the $720$ chambers into exactly **$45$ free orbits**. Compressing to the $92 \times 11$ `Syl_2(S_6)` system and invoking `padic_local_global.solve_z_half` completes in **`~13 ms` (`< 200 ms` gate)**:
   - Certifies $6\cdot\text{MAX}_6$ over $\mathbb{Z}$ (`c_den = 1`) and $1\cdot\text{MAX}_6$ over $\mathbb{Z}[1/6]$ (`c_den = 6`).
   - Emits an exact $p = 3$ valuation obstruction witness ($v_3(y^T A) \ge 1 > 0 = v_3(y^T b)$) proving $1\cdot\text{MAX}_6$ is UNSAT over $\mathbb{Z}[1/2]$ *within the fixed 11-orbit $D_6$ hexagon dictionary*, while keeping unconstrained $\text{MAX}_6 \in \operatorname{ReLU}_{6,2}(\mathbb{Z}[1/2])$ tagged **`OPEN_BUDGET_EXCEEDED`** for Wave II.

### 7.3 Theorem A3 (`CERTIFIED_EXACT`) — Virtual Zonotope-Hull Complexity Separation

Over $\mathbb{Z}$, $\operatorname{Vol}_4(\Delta_4) = 1 \equiv 1 \pmod 2$ while every 2-layer $\mathbb{Z}$ zonotope-hull block has even $\operatorname{Vol}_4$, certifying $\operatorname{vrc}_{2,\mathbb{Z}}(\Delta_4) = +\infty$. Over $\mathbb{Z}[1/2]$, specializing Bakaev's 9-term identity at $x_5 = 0$ expresses $h_{\Delta_4}(y_1,y_2,y_3,y_4) = \max(0, y_1, y_2, y_3, y_4)$ across all $120$ signed 4D cones as a signed Minkowski combination of $9$ $\mathbb{Z}[1/2]$-zonotope hulls, certifying $\operatorname{vrc}_{2,\mathbb{Z}[1/2]}(\Delta_4) \le 9$.

---

## 8. Track D: Finite-Group Circuits, Coset SNF Trichotomy & $C_5$ Equivariance Barrier (`D1`, `D2`, `D3`)

### 8.1 Theorem D1 (`CERTIFIED_EXACT`) — Argmax LCM Collapse, $C_n$ Width $2n-2$ & $W = m^2$ Compression

1. **Universal Unconstrained Strict-Argmax Ring Collapse**: Because strict argmax over the finite set $G \times G$ defines an open cone in weight space, $\mathbb{Q}$ is dense in $\mathbb{R}$, and positive layer-wise LCM multipliers $L_1, L_2 \in \mathbb{Z}_{>0}$ satisfy $\operatorname{ReLU}(L_1 z) = L_1 \operatorname{ReLU}(z)$ and $\operatorname{argmax}(L_1 L_2 s) = \operatorname{argmax}(s)$ at **zero neuron overhead**, $W_{\mathbb{Z}}^{\text{argmax}}(G) = W_{\mathbb{Q}}^{\text{argmax}}(G) = W_{\mathbb{R}}^{\text{argmax}}(G)$ for every finite group $G$.
2. **Unconstrained Pure-$\mathbb{Z}$ $C_n$ $\{0,1\}$-Indicator Circuits**: Using integer ramp second-differences $h_t(x,y) = \operatorname{ReLU}(\sum_g g x_g + \sum_h h y_h - t)$ ($t = 0..2n-3$), $C_n$ ($n \ge 3$) is realized exactly over $\mathbb{Z}$ at biased width $W = 2n - 2$ (**$W = 8 \ll 25$ on $C_5$**, refuting any $\mathbb{Q}(\sqrt{5})$ barrier for unconstrained ReLU!) and unbiased width $W = 2n - 1$ ($W = 9$ on $C_5$).
3. **Zero-Bias Bi-Equivariant Permutation Compression (`arXiv:2410.07476v3`)**: With anchor $a = (1, 2, \dots, m)^T \in \mathbb{Z}^m$, $W = m^2 < \lvert G\rvert^2$ realizes zero-bias pure-$\mathbb{Z}$ multiplication on $S_3$ ($9 < 36$), $D_4$ ($16 < 64$), $D_5$ ($25 < 100$), $A_4$ ($16 < 144$), and $S_4$ ($16 < 576$). On $Q_8$, the unique central involution $-1$ lies in every non-trivial subgroup, forcing minimal faithful permutation degree $m(Q_8) = 8 \implies m^2 = 64 = \lvert Q_8\rvert^2$ (triggering the mandatory `ValueError` guard).

### 8.2 Theorem D2 (`CERTIFIED_EXACT`) — Character & Proper-Subgroup Coset Readout SNF Trichotomy

Fixing an integer hidden feature dictionary $M \in \mathbb{Z}^{\lvert G\rvert^2 \times W}$ and demanding exact $\{0,1\}$-indicator readout $M w = e_{c_0}$ exposes three distinct regimes across proper-subgroup coset features ($\lvert H\rvert \ge 2, H \ne G$):
- **Regime I ($\mathbb{Q}$-Rank Deficient)**: Prime cyclic $C_3 (1<3), C_5 (1<5)$, $C_4 (2<4)$, and quaternion **$Q_8$ (`q_rank = 4 < 8`)** cannot separate $1$ from $-1$ even over $\mathbb{Q}$ (augmenting $Q_8$ with its 4D integral quaternion representation restores full rank $8$ with 2-primary SNF torsion).
- **Regime II ($\mathbb{Q}$-Complete + Genuine $\mathbb{Z}$-Torsion)**: $V_4$ (`[2]`; Sylvester–Hadamard $H_4$ has $\operatorname{SNF} = [1,2,2,4]$), $S_3$ (`[3]`), $D_4$ (`[2]`), $D_5$ (`[5]`), and $A_4$ (`[2,2]`) are $\mathbb{Q}$-SAT yet $\mathbb{Z}$-UNSAT for $e_0$.
- **Regime III ($\mathbb{Z}$-Unimodular Proper-Coset Synthesis)**: **$S_4$** (`210` proper cosets) achieves $\operatorname{SNF} = [1]^{24}$ (**zero $\mathbb{Z}$-torsion**, $e_0$ $\mathbb{Z}$-SAT!) because $S_3 \le S_4$ synthesizes $3 e_0$ and $D_4 \le S_4$ synthesizes $2 e_0$, so Bézout $1\cdot(3 e_0) - 1\cdot(2 e_0) = e_0$ over $\mathbb{Z}$!

### 8.3 Theorem D3 (`CERTIFIED_EXACT`) — $C_5$ Strict Equivariance Barrier vs. $\Phi_5$ Bottleneck

1. **Strict $(C_5 \times C_5)$-Equivariance Forces $W \ge 25$ Even Over $\mathbb{R}$**: Because $\gcd(\lvert C_5 \times C_5\rvert, 2) = \gcd(25, 2) = 1$, no subgroup $H \le C_5 \times C_5$ admits a non-trivial real sign character. Across all $6$ subgroups $H$ of order $5$, $H$-invariance forces each neuron on $\{e_g\}\times\{e_h\}$ to depend on $g$ alone ($H = \{0\}\times C_5$), $h$ alone ($H = C_5\times\{0\}$), or be constant ($4$ diagonal subgroups, where both projections onto $C_5$ are surjective!). Thus all orbits of size $< 25$ span only the **9-dimensional separable subspace** $\{f_1(g) + f_2(h)\}$, certified infeasible even for **strict argmax** ($\text{score}_{g+h}(g,h) - \text{score}_k(g,h) \ge 1$) via a 100-row Bareiss Farkas dual witness. Hence at least one free orbit of size $25$ is required ($W \ge 25$ over $\mathbb{R}, \mathbb{Q}, \mathbb{Z}$).
2. **Linear Bottleneck Separation ($2$ vs. $4$)**: Relaxing hidden permutation equivariance to a faithful linear representation bottlenecks $C_5$ at $d_{\text{emb}}(\mathbb{R}) = 2$ (real $2\pi/5$ rotation over $\mathbb{Q}(\sqrt{5})$) vs. $d_{\text{emb}}(\mathbb{Q}) = d_{\text{emb}}(\mathbb{Z}) = \varphi(5) = 4$, certified by Eisenstein's criterion at $p = 5$ on $\Phi_5(y + 1) = 5 + 10y + 10y^2 + 5y^3 + y^4$ and the order-5 companion matrix $C(\Phi_5) \in \operatorname{GL}_4(\mathbb{Z})$.

---

## 9. Empirical Scaling Benchmarks & Adversarial Audit Summary

### 9.1 Consolidated Wave I Parameterized Family Benchmarks (`simulator/cycle_benchmarks.md`)

Total runtime across all `92` parameterized instances in Stages 1–6 under `/usr/bin/python3 -I`: **`2,019 ms` (`~2.0 s`)**.

| Sweep Stage | Parameterized Family | Instances | Certified Law / Structural Invariant | Peak Bits | Runtime (`ms`) |
| :--- | :--- | :---: | :--- | :---: | :---: |
| **Stage 1 (`B1`/Trap 4)** | 2D $A_1$ + 3D Reeve $T_r$ ($r=1..12$) | `13` | Primal $[1,1,r]$, Polar $[1,r,r]$, Ridges $[1,r]$, $\operatorname{Weil}/\operatorname{Cart} \cong \mathbb{Z}/r\mathbb{Z}$ | `4` | `3.5` |
| **Stage 2 (`B2`)** | 4-Ray $\Sigma_*^{(k)}$ ($k=1..10$) & 5-Ray $\Sigma_5^{(k)}$ ($k=1..3$) | `13` | 4-ray Sim. CG $= 1$ vs. Seq. $2..3$; 5-ray Sim. CG $= 2k+1$ (`3, 5, 7`) | `8` | `1344.6` |
| **Stage 3 (`C1`/`C2`/Trap 6)** | Spiderwebs ($m=1..12$), Desargues Prisms & Annuli ($b=2,3$) | `23` | $\operatorname{ev}_V = [1,m,m,m]$, $\mathbb{Z}^{3(b-1)}$ monodromy (`3, 6`), `100%` Bockstein match | `8` | `98.1` |
| **Stage 4 (`D1`/`D2`/Trap 5)** | 10 Finite Groups ($C_3,V_4,C_4,C_5,S_3,D_4,D_5,A_4,S_4,Q_8$) | `10` | $C_n: 2n-2/2n-1$, $W=m^2$, $Q_8$ block, 3-regime coset trichotomy ($S_4$ $[1]^{24}$) | `6` | `258.3` |
| **Stage 5 (`E0`/`E1`/`E2`)** | Escher `E0` (`6`), Pinned `E1` (`6`), Möbius $M_N$ ($N=3..12$) | `22` | `E0` $(\frac{1+\delta}{1-\delta})^4 > 1$ (`FALSIFIED`), `E1` $(\frac{1-3\delta}{1+3\delta})^4 < 1$, $M_N$ $\mathbb{Z}/2\mathbb{Z}$ | `71` | `32.8` |
| **Stage 6 (`A1`/`A2`)** | $\operatorname{Vol}_d(\Delta_a\times\Delta_b)$ ($d=2..10$), $6\cdot\text{MAX}_6$ & `Syl_2(S_6)` | `11` | Kummer $\gcd$, $\operatorname{Vol}_5=10\equiv 1\pmod 3$, `Syl_2` `< 15 ms` (`OPEN_BUDGET_EXCEEDED` on $\mathbb{Z}[1/2]$) | `11` | `133.2` |

### 9.2 High-Value Adversarial Traps Inoculated (`failure_log_v1.md`)

- **Algebraic Kernel Torture Probes (`14/14 PASS`)**: Survived $M_{61} = 2^{61}-1$ modular rank-drop collision (`K1.4`), pairwise-non-coprime `[[6, 10, 15]] x = [1]` $\mathbb{Z}$-solve (`K1.2`), row-GCD torsion erasure vs. Bareiss scaling fake torsion (`K1.3`), 5D degenerate braid cycling (`K2.1`), translated $0 \notin P$ Reeve volume (`K2.2`), $3^2$ mod-3-passing obstruction `[[9,18]] c = [3]` (`K3.1`), and Hidden Cancelled-Prime `[[3,0,1],[0,5,1]] c = [1,5]` (`K3.2`).
- **Point-Sampling Spoof Defenses**: Both `MAX_4`/`MAX_5` (`2*MAX_4 + 2*MIN_4 - sum(x) == 0` on all $24$ permutations of `(0,1,2,3)`) and `6 * MAX_6` (`ReLU((x_(6)-x_(5)) - (x_(2)-x_(1))) == 0` on all $720$ permutations of `(1..6)`) are verified via universal pointed-cone sub-chamber splitting + sum-collision-free negative/Fibonacci profiles + internal off-braid 2nd-difference probes.

---

## 10. Wave II (v2.0) Research & Engineering Launchpad

With Wave I's clean-room algebraic kernel, certificate dispatcher, and sub-15ms `Syl_2(S_6)` engine locked and audited, Wave II (v2.0) enters directly at five well-conditioned entry points:

1. **Unconstrained `MAX_6` in $\operatorname{ReLU}_{6,2}(\mathbb{Z}[1/2])$ Off-Braid Dictionary Sprint (Track A)**:
   - *Entry Point*: `architect.core.padic_local_global.solve_z_half` + `architect.track_a_foundations.build_syl2_s6_and_orbit_reps`.
   - *Strategy*: Expand from the 11-orbit $D_6$ hexagon dictionary to systematic $\operatorname{Syl}_2(S_6)$-orbits (`45` chamber orbits = `256x` entry reduction vs. unreduced $S_6$) over asymmetric $2x_6 - x_i - x_j$ and $3$-sum off-braid hinges (`360 x 500..2500` multi-profile + off-braid wall-cancellation rows, projected `25..450 ms`, `<= 16` bits).
2. **`MAX_7` 2-Adic & 3-Adic Local-Global Frontier (Track A)**:
   - *Entry Point*: `architect.core.padic_local_global.solve_s_integral` over $\operatorname{Syl}_2(S_7)$ (`315` orbits, $\lvert G\rvert=16$) and $\operatorname{Syl}_3(S_7)$ (`560` orbits, $\lvert G\rvert=9$), testing prime-divisor lower bounds on the minimal integer annihilator $m_7$ (`120..1800 ms`).
3. **3D & Multi-Ray Chvátal–Gomory Rank Hierarchy in $\operatorname{Cart}(\Sigma)$ (Track B)**:
   - *Entry Point*: `architect.track_b_decomp_splines.exact_elementary_cg_round` & `simulator.sim_exact_la.cg_round_3d_exact` on Reeve $T_r$ ($r \le 100$) and 6-ray / 3D non-simplicial fans ($\dim \mathcal{B} = 4$).
4. **3D Cellular Maxwell–Cremona Stress Cosheaves & $\mathbb{RP}^2$ / Klein Bottle Twisted Sheaves (Tracks C & E)**:
   - *Entry Point*: Extend `build_airy_cosheaf_complex` and `build_twisted_mobius_complex` to $b = 4..10$ multi-hole domains ($\mathbb{Z}^{3(b-1)}$ monodromy) and closed non-orientable Klein-bottle CPA torsors.
5. **Simple & Quasisimple Finite-Group Circuits ($A_5, \operatorname{PSL}(2,7), \operatorname{SL}(2,3)$) & Publication Visuals (Track D + Visuals)**:
   - *Entry Point*: `architect.track_d_group_circuits.build_permutation_biequivariant_circuit` compressing $A_5$ ($W = 25 \ll 3600$, `144x`) and $\operatorname{PSL}(2,7)$ ($W = 49 \ll 28224$, `576x`) vs. $\operatorname{SL}(2,3)$ central-involution core-free obstruction, paired with dedicated Wave II geometric SVG diagrams (`E0` Escher waterfall vs. `E1` pinned limit cycle, Klein sail cuts, and spiderweb torsion complexes).
