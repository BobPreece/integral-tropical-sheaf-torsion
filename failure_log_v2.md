# Integral Tropical-Sheaf Torsion (Wave II / v2.0) — Master Adversarial Failure, Falsification & Trap Log (`failure_log_v2.md`)

- **Owner**: `@inquisitor`
- **Constitutional Scope**: `SPEC.md` §0–§5 & `SPEC_WAVE2.md` §0–§3 (`100%` Python 3.9+ standard library, zero external packages, zero `float` across the entire repository including `simulator/svg_atlas.py` and `inquisitor/svg_auditor.py`, inner-loop `Fraction` firewall on `architect/core/`, `0` `ast.Div`, `0` `isinstance` bypasses, `10/10` zero-OOB zero-overlap SVGs, `signal.alarm(20)` per stage)
- **Audit Checkpoint**: `artifacts/wave2_inquisitor_audit.json` (`5/5` live torture stages `PASS` in `~1.0 s` under `/usr/bin/python3 -I`)

---

## 1. Wave I Certified Foundation Anchor (`failure_log_v1.md` Baseline Preserved `100%`)

All `21/21` Wave I claims (`artifacts/theorem_ledger_v1.json`) and all `14` kernel + `7` Gate-0 + `8` Cycle-2 adversarial probes remain `100%` active and regression-tested:

| Arena | Certified Wave I Trap / Discovery | Ground-Truth Guard Preserved in v2.0 |
| :--- | :--- | :--- |
| **Algebraic Kernel (`K1`–`K3`)** | $M_{61} = 2^{61}-1$ modular rank-drop collision; pairwise-non-coprime `[[6,10,15]] x = [1]` $\mathbb{Z}$-solve; Bareiss fake torsion vs. row-GCD torsion erasure; 5D braid simplex cycling; translated $0 \notin P$ Reeve volume; $3^2$ mod-3-passing UNSAT; **Hidden Cancelled-Prime Bug** `[[3,0,1],[0,5,1]] c = [1,5]` | Exact fallback after mod-$M_{61}$ screen, DHSW unimodular SNF, Avis–Chvátal lexicographic simplex, origin-shifted SNF hull volume, and non-pivot $p$-adic denominator rescue |
| **Track B (`B1`, `B2`)** | Unnormalized $\det=2$ dual normals erasing $\operatorname{Weil}/\operatorname{Cart}$ torsion; **Sequential Single-Cut Gomory Rank (`2..3`) vs. Simultaneous Schrijver–Chvátal Closure Rank (`1` on 4-ray $\Sigma_*^{(k)}$, `2k+1` on 5-ray $\Sigma_5^{(k)}$)** | Primitive $(\mathbb{Z}^d)^*$ wall normals + explicit two-regime CG rank split (`fig03`, `fig04`, `fig05`) |
| **Track C (`C1`, `C2`)** | Concurrent-spoke untriangulated 3-quad annulus collapsing affine monodromy rank `3 -> 2`; Cooperband geometric $\mathcal{F}_{\mathbb{Z}}^{\text{geom}}$ vs. saturated $\mathcal{Z}_{\mathbb{Z}}^{\text{sat}}$ edge-GCD torsion | 6-triangle chord-subdivided annulus restoring $\mathbb{Z}^{3(b-1)}$ monodromy & 2D Precision-Bockstein $(P_{\text{sat}}, Q_{\text{free}})$ projectors (`fig06`, `fig07`) |
| **Track E (`E0`–`E2`)** | **Counterexample E0 (`FALSIFIED_COUNTEREXAMPLE` — Outward-Spiraling Escher Waterfall)**: flat CPA $\mathbb{R}/\mathbb{Q}$-torsor with strict cell & Clarke/Filippov crease decrease $\le -19 < 0$ everywhere yet outward 1-lap Poincaré expansion $(21/19)^4 = 194481/130321 > 1$; $270^\circ$ non-convex Bouligand inner-hole corner; untwisted/scaled-row Möbius spoofs | Pinned-torsor cut-section contraction $16/81 < 1$ around $r^* = 10/3$ (`E1`) + genuine 2D triangulated Möbius $\mathbb{Z}_{-1}$ cochain complex $H^1(M_N;\mathbb{Z}_{-1}) \cong \mathbb{Z}/2\mathbb{Z}$ (`E2`, `fig10`) |

---

## 2. Wave II Mathematical Adversarial Traps, Falsified Conjectures & Structural Near-Misses

### 2.1 Trap W2-1: Three Finite-Ray `MAX_6` Impostors Defeated by Motzkin–Burger Sub-Cone Splitting

A central hazard in Sprint A2 (`MAX_6` over $\mathbb{Z}[1/2]$) is solving `Syl_2(S_6)`-reduced linear systems $A c = b$ by evaluating candidate 2-layer gates only on finite interior chamber rays rather than across all polyhedral sub-cones induced by active off-braid hyperplanes:

1. **`@architect`'s Underdetermined `47`-Ray `Z[1/2]` Impostor (`c_den = 512`)**:
   - In the `615`-orbit `Syl_2(S_6)` pairwise-max `(2, 2)` dictionary (`architect/track_a_wave2_max6.py`), evaluating on `1` interior point per `Syl_2(S_6)` braid chamber plus $\pm(1,\dots,1)$ (`45 + 2 = 47` equations in `615` unknowns) yields a spurious dyadic solution with denominator $c_{\text{den}} = 512 = 2^9 \in \mathbb{Z}[1/2]$.
   - Testing at the off-braid interior point $x = (0, 4, 6, 10, 25, 40)$ immediately exposes the impostor, and expanding to the complete **`945 x 615` exact symbolic sub-chamber + off-braid wall-jump system** flips the status from fake `Z[1/2]-SAT` to certified **`UNSAT_MOD3_PRESCREEN`** ($p = 3$ obstruction), while $\mathbb{Z}[1/6]$ remains `CERTIFIED_EXACT`.
2. **`@inquisitor`'s Impostor W2-1A (`F_fake_Z` — Pure-`Z` `c_den = 1` Impostor Across All `720` `S_6` Chambers)**:
   - On any `S_6`-symmetric linear combination of pure-braid maxima $S_1, M_2, M_3, M_4$ evaluated at permutations of $(1, 2, 3, 4, 5, 6)$, Kummer's prime-$7$ congruence forces values $(21, 70, 105, 84) \equiv (0, 0, 0, 0) \pmod 7$, blocking $\text{MAX}_6 = 6 \not\equiv 0 \pmod 7$.
   - However, introducing the `60` **off-braid** 1-layer integer hinges $Q_{\text{off}}(x) = \sum_{i=0}^5 \sum_{j<k \ne i} \operatorname{ReLU}(2x_i - x_j - x_k)$ breaks prime $7$: $Q_{\text{off}}(1,\dots,1) = 0$ while $Q_{\text{off}}(\sigma(1,2,3,4,5,6)) = 60 + 36 + 16 + 4 = 116 \equiv 4 \pmod 7$, with $\gcd(116, 14) = 2$ ($-3 \cdot 116 + 25 \cdot 14 = +2$).
   - Consequently, the **pure-integer (`c_den = 1`)** homogeneous translation-equivariant 2-layer ReLU network
     $$F_{\text{fake},\mathbb{Z}}(x) = S_1(x) - 75 M_2(x) - M_3(x) + 76 M_4(x) - 9 Q_{\text{off}}(x)$$
     satisfies $F_{\text{fake},\mathbb{Z}}(\pm \mathbf{1}) = \pm 1$ and $F_{\text{fake},\mathbb{Z}}(x) = \text{MAX}_6(x)$ across **all `45` `Syl_2(S_6)` representative chambers and all `720` `S_6` permutations of $(1,2,3,4,5,6)$**, yet evaluates to **`1048 != 10`** on the open off-braid sub-cone containing $(0, 1, 2, 3, 4, 10)$!
   - Fed live into **both** `architect.track_a_wave2_max6.verify_candidate_all_syl2_subcones` and `formalist.cert_kernel.verify_max6_primal_z_half_certificate`, both engines split the braid chamber along $2x_i - x_j - x_k = 0$ and deterministically reject $F_{\text{fake},\mathbb{Z}}$ with explicit integer sub-cone witnesses (`[0, 16, 24, 28, 30, 31]`).
3. **`@inquisitor`'s Impostor W2-1B (`F_stealth_6max6_z` — Multi-Profile `2,160`-Ray Evasive Bump)**:
   - Adding $G_{\text{cone},100}(x) = \operatorname{ReLU}\bigl(\operatorname{ReLU}(x_1 - x_0) - 100\operatorname{ReLU}(x_5 - x_1) - 100\operatorname{ReLU}(x_1 - x_5)\bigr)$ to $6\cdot\text{MAX}_6(x)$ produces zero error across **all `2,160` interior points** of $(1,2,3,4,5,6)$, $(-89,-34,-13,-5,-2,-1)$, and $(-41,-13,0,7,29,103)$ (since $|x_5 - x_1| \ge 1$ and $x_1 - x_0 \le 88 < 100$ on every permutation of those profiles!), yet differs by $+100$ on the narrow $100:1$ sub-cone around $(0, 500, 501, 502, 503, 504)$. Both `@architect`'s and `@formalist`'s pointed sub-cone splitters catch it with `0/1` exactness (`verify_candidate_all_syl2_subcones` pinpointing `[0, 2060701, 2070902, 2071003, 2071004, 2081308]`, where $2060701 > 100 \times (2081308 - 2060701) = 2060700$ by exactly $1$ lattice unit!).

---

### 2.2 Sprint A2 Dichotomy: Why `(2, 2)` Zonotope Joins Escape `Vol_5 mod 3` Yet Still Hit `3`-Adic Obstructions

1. **Top-Dimensional Volume Escape at $d = 5$ (`MAX_6`) vs. Universal Restoration at $d = 6$ (`MAX_7`)**:
   - By the Cayley–Shephard / Cauchy–Binet determinant law (`Theorem A2a`, verified across `65` canonical, sheared, sublattice, and multi-generator families in `simulator/wave2_sweeps.py`), any skew lattice zonotope pair $(Z_1, Z_2)$ in $\mathbb{Z}^d$ of dimensions $r_1 + r_2 = d - 1$ satisfies $(r_1! r_2!) \mid \operatorname{Vol}_d(\operatorname{conv}(Z_1 \cup Z_2))$.
   - At $d = 5$ (`MAX_6`): $(4, 0)$ paramids give $4!0! = 24 \equiv 0 \pmod 3$ and $(3, 1)$ segment-zonotope joins give $3!1! = 6 \equiv 0 \pmod 3$, **falsifying** any naive attempt to prove $\text{MAX}_6 \notin \operatorname{ReLU}_{6,2}(\mathbb{Z}[1/2])$ via single-gate top-dimensional volume mod $3$ because **`(2, 2)` zonotope-pair joins achieve $\operatorname{Vol}_5 = 2!2! = 4 \equiv 1 \pmod 3$** ($G_5 = \gcd(24, 6, 4) = 2$).
   - At $d = 6$ (`MAX_7`): $r_1 + r_2 = 5 \implies \max(r_1, r_2) \ge 3$, so $r_1! r_2! \in \{120, 24, 12\}$ and **$G_6 = 12$ ($6 \mid \operatorname{Vol}_6$ universally)** across every convex 2-layer join!
2. **Coupled Wall-Cancellation `3`-Adic Obstruction Across Nested `Syl_2(S_6)` Dictionaries (`Theorem A2b` & `Trap W2-2`)**:
   - Even though individual `(2, 2)` gates escape $\operatorname{Vol}_5 \bmod 3$ and `Syl_2(S_6)` ($|D_4 \times C_2| = 16 = 2^4$) introduces zero $3$-torsion from orbit averaging, canceling all spurious off-braid creases across the `45` braid chambers couples gate weights globally modulo $3$:
     * `615`-orbit full `(2, 2)` pairwise-max symbolic system (`945 x 615`): $\mathbb{Z}[1/6]$-`SAT` (`den = 192 = 2^6 \cdot 3`), $\mathbb{Z}[1/2]$-`UNSAT` (compact `113 x 615` $p = 3$ witness verified independently).
     * **Tier 1** (`321` `Syl_2(S_6)` orbits, `4+2` Bakaev zonotope-pair extension): $p = 3$ obstruction (compact `109 x 321` witness, $\min_j v_3((y^T A)_j) = 1 > 0 = v_3(y^T b)$).
     * **Tier 2** (`364` `Syl_2(S_6)` orbits, nested `(2,2) + (3,1) + (4,0)` joins in $\{-2..2\}^6$): $p = 3$ obstruction (compact `134 x 364` witness).
     * **Tier 3** (`384` `Syl_2(S_6)` orbits, non-convex signed Layer-2 gates $\alpha_r \in \{\pm 1, \pm 2\}$): $p = 3$ obstruction (compact `135 x 384` witness).
   - **`Trap W2-2` Guard**: Verified deterministic rejection of `7` bogus near-miss $p$-adic witnesses (including $y^T A \equiv 0 \pmod 3, y^T b \equiv 0 \pmod 3$ with equal valuation $v_3 = 1 = 1$ on a $\mathbb{Z}$-satisfiable system, inverted $v_3 = 1 < 2$, $y^T b = 0$, final-column valuation tie leak, inflated `s_bound`, and smuggled inverted prime $p = 2$ over $\mathbb{Z}[1/2]$).
   - **`Trap W2-4` Epistemic Guard**: Synchronized `wave2_torture_tests.py`, `cycle2_adversarial_probes.py`, and `formalist/cert_kernel.py` so tier-scoped `A2_TIER123_3ADIC_OBSTRUCTION` carries `CERTIFIED_EXACT` while unconstrained $\text{MAX}_6 \in \operatorname{ReLU}_{6,2}(\mathbb{Z}[1/2])$ remains honestly tagged **`OPEN_BUDGET_EXCEEDED`**, deterministically rejecting `3/3` mock unconditional overclaims.
3. **Finite-Arrangement Paramid vs. Zonotope-Pair Quotient SNF Transitions (`Theorem A2c`)**:
   - $n = 4$ ($H_4$, `48` chambers, rank `27`): pure `(2,0)` paramids have torsion `[2,2,2,2,2]` (`MAX_4` `UNSAT_Z_TORSION`, `den = 2`), whereas adding `(1,1)` zonotope-pair joins collapses torsion to `[2,2,2]` and makes `MAX_4` **`CERTIFIED_EXACT` over $\mathbb{Z}$ (`den = 1`)**.
   - $n = 5$ ($H_5^{D_4}$, `480` chambers, $D_4$-rank `23`): pure `(3,0)` paramids have rank `14`, torsion `[4]` (`MAX_5` **`UNSAT_Q`**); adding Bakaev `(2,1)` joins raises rank to `17`, torsion `[2]`, realizing `MAX_5` with **`den = 2` ($\mathbb{Z}[1/2]$)**.
   - $n = 6$ ($H_6^{D_6}$ & $H_6^{S_6}$): pure `(4,0)` paramids leave `MAX_6` **`UNSAT_Q`** (`S_6` torsion `[3, 12]`); adding hexagon `(2,2)` joins makes `MAX_6` $\mathbb{Q}$-complete with torsion `[2, 2, 6]` and exact **`den = 6` ($\mathbb{Z}[1/6]$)**.

---

### 2.3 Sprint D4 Traps: `Dic_3` Intransitive Permutation Degree, Latin-Square Rank Falsification & Torsion Surgery

1. **The `Dic_3` Transitive vs. Intransitive Faithful Permutation Trap (`Theorem D4a`)**:
   - On dicyclic $\operatorname{Dic}_3 = \langle a, x \mid a^6 = 1, x^2 = a^3, x a x^{-1} = a^{-1}\rangle$ ($|G| = 12$), **every** non-trivial subgroup has a non-trivial normal core, so minimal *transitive* faithful degree is $m_{\text{trans}}(\operatorname{Dic}_3) = 12$ ($W_{\text{trans}} = 144 = |G|^2$, hitting the lookup wall).
   - **Subtle Trap Caught**: Unlike $2$-groups $Q_8$ ($m = 8, W_{\text{perm}} = 64$) and $Q_{16}$ ($m = 16, W_{\text{perm}} = 256$) where the unique involution $-1$ lies in *every* non-trivial subgroup, $\operatorname{Dic}_3$ has odd-order normal subgroup $\langle a^2\rangle \cong C_3$ (index `4`, core $\langle a^2\rangle$) disjoint from $\operatorname{Core}(\langle x\rangle) = \{1, a^3\} \cong C_2$ (index `3`)! Since $\langle a^2\rangle \cap \{1, a^3\} = \{1\}$, the **intransitive** action on $(\operatorname{Dic}_3/\langle x\rangle) \sqcup (\operatorname{Dic}_3/\langle a^2\rangle)$ is faithful of degree **$m(\operatorname{Dic}_3) = 3 + 4 = 7$**, giving $W_{\text{perm}}(\operatorname{Dic}_3) = 7^2 = 49 < 144$!
   - **Cohomological Breakout Beyond Both Walls**: Exploiting $1 \to C_m \to G \to C_2 \to 1$ via shifted/superposed 2-cocycle second-difference ramps compresses pure-$\mathbb{Z}$ `{0,1}`-indicator multiplication to **$W_{\mathbb{Z}}(G) \le 4m + 1 = 2|G| + 1$ (biased) / $2|G| + 2$ (zero-bias)**:
     * $Q_8$ ($m = 4, c_0 = 2$): `64` (perm wall) $\to$ `48` (Tier-1 $V_4$ cocycle) $\to$ `43`/`38` (quotient-merged $\mathbb{Z}$) $\to$ `22`/`26` (Howell–Lafon $\mathbb{Z}[1/2]$, `den = 8`) $\to$ **`17` biased / `18` zero-bias over pure $\mathbb{Z}$ (`3.76x` compression, matching split $D_4$'s `17`!)**.
     * $\operatorname{Dic}_3$ ($m = 6, c_0 = 3$): `144` (trans. wall) / `49` (intrans. perm) $\to$ `108` (Tier-1 $S_3$ cocycle) $\to$ **`25` biased / `26` zero-bias over pure $\mathbb{Z}$ (`5.76x` vs. $|G|^2$, `1.96x` below `49`!)**.
     * $Q_{16}$ ($m = 8, c_0 = 4$): `256` (perm wall) $\to$ `192` $\to$ **`33` biased / `34` zero-bias over pure $\mathbb{Z}$ (`7.76x` compression!)**.
2. **Falsification of Equality in the Universal Rank Lower Bound $W \ge |G| - 1$ (`Theorem D4b`)**:
   - While $I_{\text{mult}}^T I_{\text{mult}} = |G| I_{|G|}$ ($\det = |G|^{|G|}$) implies $W \ge |G| - 1$ (biased) and $W \ge |G|$ (zero-bias), equality $W = |G| - 1$ is **falsified over $\mathbb{R}$ for every finite group $|G| \ge 2$**!
   - **Mechanism (Latin-Square / 1-Neuron Outcome Impossibility)**: Achieving $W = |G| - 1$ with 1 bias column requires all $W$ hidden columns to lie inside the $|G|$-dimensional multiplication-outcome subspace $V_G$ ($h(g, y) = f(g \cdot y)$). Exact Bareiss LP Farkas duals certify that any ReLU neuron $\operatorname{ReLU}(u_g + v_y + b)$ constant on multiplication fibers of a group of order $\ge 2$ must be globally constant, strictly sharpening the universal real lower bound to **$W \ge |G|$ (biased) and $W \ge |G| + 1$ (zero-bias)** (and 1D quotient ray-bucket exclusion modulo $V_G$ further certifies $W \ge 4$ on $C_3$, matching constructive $W_{\mathbb{Z}}(C_3) = 4$, and $W \ge 5$ on $V_4, C_4$).
3. **`Z`-vs-`Q` Feature Torsion & Surgical Torsion-Killing (`V_4` & `Q_8`) + `Trap W2-3` Rejections**:
   - On $V_4$, symmetric `6`-neuron coset/Walsh–Hadamard XOR features yield $\operatorname{SNF} = [1,1,1,1,1,1,2]$ (`Q-SAT` with `den = 2`, `Z-UNSAT` `[2]`-torsion). Adding one pure-$\mathbb{Z}$ corner neuron resolves torsion at $W = 7$ (`architect/track_d_wave2_extensions.py`), while **asymmetric hinge surgery** (`simulator/wave2_sweeps.py`, replacing one redundant XOR hinge by $\operatorname{ReLU}([0,-1,-1,-1]_g + [1,2,2,2]_h)$) kills the `[2]` invariant factor directly ($\operatorname{SNF} = [1]^7$), certifying $W_{\mathbb{Z}}(V_4) = 6$ (`7` zero-bias)!
   - **`Trap W2-3` Live Rejections**: Both `@architect` and `@formalist` deterministically rejected (a) the $W = 16$ pure-$V_4$ sign-collapsed circuit (`64/64` cosets right in $Q_8/\{\pm 1\}$, failing $i \cdot i = -1$ by predicting $+1$), (b) smuggled `"1/2"` string weights in $W_2$, (c) integer-doubled $2 e_{g\cdot h}$ outputs masquerading with `out_denom = 2`, and (d) `ValueError` lookup-wall breaches at $W = 64$ ($Q_8$), $W = 144$ ($\operatorname{Dic}_3$), $W = 256$ ($Q_{16}$), and $W = 5 \ge 4$ ($C_2$).

---

## 3. SVG Visual Atlas Geometry Gate & Workspace AST Contraband Summary

### 3.1 `inquisitor/svg_auditor.py` (`10 / 10` Atlas Figures + `10 / 10` Adversarial Geometry Traps)

Audited via exact arbitrary-precision `fractions.Fraction` geometry (`0` floats, de Casteljau 8-way Bezier hull subdivision, Liang–Barsky segment clipping, `>= 2px` inner container clearance, and painter's `z`-order occlusion checks):

| Atlas Figure (`plots/fig01..fig10.svg`) | `viewBox` | Shapes | Texts | `OOB` | `Overlaps` | Verdict |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `fig01_paramid_torsion_and_join_dichotomy.svg` | `0 0 1400 900` | `47` | `97` | `0` | `0` | **`PASS`** |
| `fig02_max6_syl2_padic_frontier.svg` | `0 0 1400 900` | `46` | `45` | `0` | `0` | **`PASS`** |
| `fig03_klein_sail_cg_split.svg` | `0 0 1400 900` | `61` | `42` | `0` | `0` | **`PASS`** |
| `fig04_five_ray_unbounded_chvatal_rank.svg` | `0 0 1400 900` | `41` | `49` | `0` | `0` | **`PASS`** |
| `fig05_reeve_polar_bss_torsion.svg` | `0 0 1400 900` | `69` | `47` | `0` | `0` | **`PASS`** |
| `fig06_airy_spiderweb_and_chord_annulus.svg` | `0 0 1400 900` | `43` | `45` | `0` | `0` | **`PASS`** |
| `fig07_2d_precision_bockstein_snf.svg` | `0 0 1400 900` | `32` | `53` | `0` | `0` | **`PASS`** |
| `fig08_group_circuit_compression_and_q8_cocycle.svg` | `0 0 1400 900` | `49` | `53` | `0` | `0` | **`PASS`** |
| `fig09_proper_coset_snf_trichotomy.svg` | `0 0 1400 900` | `18` | `46` | `0` | `0` | **`PASS`** |
| `fig10_escher_waterfall_and_mobius_torsion.svg` | `0 0 1400 900` | `73` | `49` | `0` | `0` | **`PASS`** |
| **Atlas Totals (`149 ms` total audit time)** | **`10 / 10`** | **`479`** | **`526`** | **`0`** | **`0`** | **`100% PASS`** |

- **Adversarial Unit Self-Tests (`10 / 10 PASS`)**: Verified detection of deliberate OOB stroke half-widths, OOB cubic Bezier control points (`y = -25`), translated `<g>` OOB overflow, `<text>`-to-`<text>` collisions, `<line>` slicing `<text>`, quadratic Bezier `<path>` slicing `<text>`, thin `<rect>` bars & `z`-order card occlusion over `<text>`, malformed XML / wrong `viewBox`, and missing `fig10` in full-atlas mode.

### 3.2 `inquisitor/ast_scanner.py` (`18 / 18` Contraband Self-Tests & `100%` Zero-Float Repo)

- **Workspace-Wide Scan**: **`100% CLEAN` (`0` violations, `0` advisories, `0` JSON float tokens)** across all `architect/`, `formalist/`, `simulator/` (including **`100%` zero-float `simulator/svg_atlas.py`**, `svg_atlas_zero_float = True`), `inquisitor/`, and `verify_all.py` modules, plus all `artifacts/*.json` checkpoints.
