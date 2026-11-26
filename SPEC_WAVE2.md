# SPEC_WAVE2.md — Integral Tropical-Sheaf Torsion (Wave II / v2.0 Frontier Sprint & Production Observatory Release)

Workspace: `.`
Foundation: Build directly on the clean-room certified Wave I (`v1.0`) codebase (`architect/`, `formalist/`, `simulator/`, `inquisitor/`, `artifacts/theorem_ledger_v1.json`) already on disk.

## 0. Constitutional Rules & Operational Guardrails
1. **Strict Sandbox Boundary:** Work EXCLUSIVELY inside `.` (plus `/tmp` solely for `@inquisitor`'s isolated `/usr/bin/python3 -I` audits). Do NOT scan `$HOME/` or external folders.
2. **100% Zero-Dependency Python 3.9+ Stdlib & Zero-Float Firewall:** Zero external packages, zero `float` literals/calls/annotations in algebraic/verification modules (`float` formatting permitted strictly inside `simulator/svg_atlas.py` coordinate string rendering if isolated from `architect/` and `formalist/`, or keep 100% integer/rational scaled SVG coordinates so the entire repo stays 0-float!). Preserve all `21/21` Wave I claims intact.
3. **Hard Per-Stage Timeouts (`signal.alarm(20)`) & `< 45s` Total `verify_all.py` Budget:** Flush JSON checkpoints per stage; never run unreduced full-matrix Z-HNF over `S_6`. Always use `architect/core/padic_local_global.py` (`Syl_2(S_6)` 45-orbit engine) and DHSW Modulo-`D` SNF.
4. **Strict 3-Valued Epistemic Ledger (`CERTIFIED_EXACT`, `FALSIFIED_COUNTEREXAMPLE`, `OPEN_BUDGET_EXCEEDED`):** Never promote fixed-dictionary `UNSAT` to an unconditional `ReLU_{6,2}(Z[1/2])` impossibility claim without a universal algebraic proof holding over ALL off-braid hyperplanes.

---

## 1. Wave II Mathematical Frontier Sprints (Cycles 1 -> 2 -> 3)

### Sprint A2: Join-Volume Arithmetic Dichotomy & The `MAX_6` `Z[1/2]` `(2,2)` Zonotope-Pair Attack (`architect/track_a_wave2_max6.py`)
1. **Theorem A2a (`CERTIFIED_EXACT` — Join-Volume Arithmetic Dichotomy):**
   - Prove and symbolically verify that for any two lattice parallelepipeds/zonotopes `Z_1, Z_2 subset R^d` of dimensions `(r_1, r_2)` spanning a full `d`-dimensional join (`r_1 + r_2 = d - 1`), normalized `d`-volume satisfies `(r_1! * r_2!) | Vol_d(conv(Z_1 union Z_2))`.
   - Certify the exact dimensional threshold for prime `3`:
     * At `d = 5` (`n = 6`, `MAX_6`): `(4,0)` paramids (`4!0! = 24`) and `(3,1)` segment-zonotope joins (`3!1! = 6`) are divisible by `3`, whereas **`(2,2)` zonotope-pair joins** `max(Z_1, Z_2)` (e.g., `Pi_1 = [0,e_1]+[0,e_2]`, `Pi_2 = e_5+[0,e_3]+[0,e_4]`) achieve `Vol_5 = 2!2! = 4 == 1 (mod 3)` (escaping prime `3`!).
     * At `d = 6` (`n = 7`, `MAX_7`): `r_1 + r_2 = 5 => max(r_1, r_2) >= 3`, forcing `6 | Vol_6(conv(Z_1 union Z_2))` on EVERY single convex 2-layer join!
2. **Theorem A2b (`Syl_2(S_6)` `(2,2)` Zonotope-Pair & Signed-1-Layer Primal/Dual Hierarchy on `MAX_6`):**
   - Construct nested `Syl_2(S_6)`-reduced (`|D_4 x C_2| = 16`, `45` braid chambers + exact induced off-braid sub-cone refinement!) 2-layer `Z`-gate dictionaries that break `D_6` `3`-symmetry:
     * **Tier 1 (`4+2` Bakaev Zonotope-Pair Extension):** Generalize Bakaev's (`2505.14338`) `(2,2)` gates `max(Z_1, Z_2)` across partitions `{1,2} u {3,4} u {5,6}` using Layer-1 pairwise maxima `max(x_i, x_j)` and half-sum forms (`x_i+x_j`, `2x_k`, `x_5+x_6`, `2x_5+2x_6-x_1-x_2-x_3-x_4`).
     * **Tier 2 (Full `(2,2)` + `(3,1)` + `(4,0)` Small-Coefficient Zonotope-Pair Dictionary):** Include sums of two Layer-1 hinges `ReLU(a_1.x) + ReLU(a_2.x)` paired against `c_0.x + ReLU(a_3.x) + ReLU(a_4.x)` with zero-sum primitive integer normals in `{-2,-1,0,1,2}^6`.
     * **Tier 3 (Non-Convex Signed Layer-2 Gates `ReLU(U - V)`):** Include signed Layer-1 differences inside Layer 2 (`alpha_r in {-2,-1,+1,+2}`).
   - Test each tier via `padic_local_global.py` (making sure the linear system checks EXACT piecewise-linear equality across ALL refined polyhedral sub-cones induced by the active off-braid hyperplanes, not merely 45 interior test rays — `@inquisitor` must torture-test against finite-ray impostors!):
     * **If `SAT` over `Z[1/2]`:** Certify exact equality `2^t * MAX_6(x) = sum_k c_k g_k(x)` symbolically across 100% of refined polyhedral chambers (`0/1` error) as a world-first `CERTIFIED_EXACT` resolution!
     * **If `UNSAT` over `Z[1/2]` across Tiers 1–3:** Emit exact machine-checked `3`-adic dual obstruction witnesses `y` (`v_3(y^T A) > v_3(y^T b)`) certifying `CERTIFIED_EXACT` impossibility on each tier (`A2_TIER123_3ADIC_OBSTRUCTION`), while recording unconstrained `ReLU_{6,2}(Z[1/2])` truthfully as `OPEN_BUDGET_EXCEEDED` unless a universal invariant over all off-braid arrangements is proved.
3. **Theorem A2c (`CERTIFIED_EXACT` — Finite-Arrangement Integral Paramid Quotient SNF Tables):**
   - Compute exact unimodular SNF torsion invariant factors of the finite-arrangement quotient module `CPWL_H(Z) / Span_Z(Paramids_H)` on the canonical braid + Bakaev/hexagon arrangements `H_n` for `n = 4, 5, 6`, comparing pure `(d-1, 0)` paramids against `(2, 2)` zonotope-pair spans!

### Sprint D4: Cohomological 2-Cocycle Compression Breaking the `Q_8` Wall & Minimal `{0,1}` Widths (`architect/track_d_wave2_extensions.py`)
1. **Theorem D4a (`CERTIFIED_EXACT` — `H^2(V_4; Z_2)` 2-Cocycle Circuit Compressing `Q_8` Below `64` Over `Z`):**
   - Break Wave I's faithful-permutation wall on quaternionic `Q_8` (`W_perm = 64 == |Q_8|^2`) via the central extension `1 -> {+-1} -> Q_8 -> V_4 -> 1` classified by `[beta] in H^2(V_4; Z_2)`:
     * Construct and verify across all `64` pairs of `Q_8 x Q_8` an explicit **1-hidden-layer pure-`Z` exact `{0,1}`-indicator ReLU circuit** at `W <= 48 < 64` (using 3 `Z`-neurons per `(x_bar, y_bar) in V_4 x V_4`, and optimize further using identity/sign reductions on `Q_8` to find the tightest achievable compressed `Z`-width and `Q`-width, e.g., testing `W <= 36` or `32` via Walsh-Hadamard quotient features over `Q` vs `Z`!).
     * Generalize and verify on a second non-split / central group extension (e.g., `Q_8` vs `D_4` comparison or `Z_4` / `Dic_3` of order `12`, `W < 144`) to establish a general **Cohomological Extension Compression Theorem**.
2. **Theorem D4b (`CERTIFIED_EXACT` — Exact `{0,1}`-Indicator Width Bounds & `Z`-vs-`Q` Feature Separations):**
   - Prove and verify the universal rank lower bounds `W >= |G| - 1` (biased readout) and `W >= |G|` (zero-bias readout) for exact `{0,1}`-indicator multiplication on ALL finite groups (`det(I_mult^T I_mult) = |G|^{|G|}`).
   - Test whether exact `{0,1}`-indicator width on `C_3, V_4, C_4, C_5` closes the gap between the rank lower bound (`|G|-1`) and `2n - 2` over `Z` vs `Q` (certifying constructive minimal circuits on `C_3`, `V_4`, `C_4`).

---

## 2. Visual Atlas (`plots/` — 10 Pure-Stdlib Audited SVGs) & Clean-Room Packaging

1. **10 Publication-Grade Pure-Stdlib SVGs (`simulator/svg_atlas.py` -> `plots/fig01..fig10.svg`):**
   - Generate 10 crisp, information-dense multi-panel mathematical diagrams (`1400x900` viewBox, clean typography, exact rational/SNF annotations):
     * `fig01_paramid_torsion_and_join_dichotomy.svg`: `n=4,5,6,10` annihilator staircase + `(4,0)/(3,1)` vs `(2,2)` join volume mod 3.
     * `fig02_max6_syl2_padic_frontier.svg`: `D_6` 105-gate `6*MAX_6` identity vs `Syl_2(S_6)` 45-orbit `(2,2)` zonotope-pair `3`-adic valuation profile.
     * `fig03_klein_sail_cg_split.svg`: Track B2 4-ray `Sigma_*` LP vertex `(6/5, 2/5)`, Klein-sail hull, sequential Gomory rank 2/3 vs simultaneous closure rank 1.
     * `fig04_five_ray_unbounded_chvatal_rank.svg`: Track B2 `Sigma_5^(k)` genuine simultaneous Schrijver-Chvatal closure rank `2k + 1` (`3, 5, 7, 9`).
     * `fig05_reeve_polar_bss_torsion.svg`: Track B1 3D Reeve `T_r` (`r=2..12`) primal `[1,1,r]` Weil/Cartier vs polar `[1,r,r]` BSS colon-ideal torsion.
     * `fig06_airy_spiderweb_and_chord_annulus.svg`: Track C1 spiderweb `Z/mZ` nodal torsion + concurrent-spoke rank-2 collapse vs 6-triangle chord-subdivided rank-3 monodromy.
     * `fig07_2d_precision_bockstein_snf.svg`: Track C2 2D Airy `beta_k^(2)` `p`-adic persistence barcodes & `(P_sat, Q_free)` integral projectors.
     * `fig08_group_circuit_compression_and_q8_cocycle.svg`: Track D1/D4 `W = m^2 << |G|^2` permutation compression + `Q_8` `H^2(V_4; Z_2)` 2-cocycle circuit breaking `W = 64` + `C_5` `W = 8 << 25`.
     * `fig09_proper_coset_snf_trichotomy.svg`: Track D2/D3 proper-coset SNF trichotomy (`S_4` Bezout `[1]^24` vs `V_4` Hadamard `[1,2,2,4]`) + `C_5` `Phi_5` bottleneck `2 < 4`.
     * `fig10_escher_waterfall_and_mobius_torsion.svg`: Track E0/E1/E2 Outward-Spiraling Escher Waterfall `P(r_0)=(21/19)^4 r_0` vs `16/81` pinned-torsor contraction & Mobius `Z/2Z` torsion.
   - **Mandatory `@inquisitor` SVG Geometry & XML Gate (`inquisitor/svg_auditor.py`):** Parse every `.svg` via `xml.etree.ElementTree`, asserting `0` out-of-bounds elements (`OOB == 0` including stroke widths and cubic Bezier control-polygon hulls) and `0` text-to-text / text-to-shape bounding-box collisions (`overlaps == 0`).

2. **Self-Contained Standalone Bundle & Repository Documentation:**
   - **`standalone_integral_sheaf_torsion.py`**: Single-file zero-dependency executable bundling the core Z/Q/p-adic kernel and deterministic verification of all Wave I + Wave II theorems, runnable anywhere via `/usr/bin/python3 -I standalone_integral_sheaf_torsion.py` in `< 25s`.
   - **Updated `verify_all.py` (`< 45s` total)**, **`artifacts/theorem_ledger_v2.json`**, **`PROOF_DOSSIER_v2.md`**, **`failure_log_v2.md`**, and a flagship Exact-Math Observatory **`README.md`** (embedding all 10 `plots/fig*.svg` links, exact theorem summary table, quickstart commands, and honest complexity/open-frontier boundaries).

## 3. Final Cycle 3B Clean-Room Sign-Off
`@inquisitor` must copy BOTH the full workspace AND `standalone_integral_sheaf_torsion.py` alone into separate scrubbed `/tmp` directories and certify `exit_code == 0` under `/usr/bin/python3 -I` with `0` AST contraband violations, `10/10` zero-overlap SVGs, and `100%` `formalist/cert_kernel.py` certificate verification across `theorem_ledger_v2.json`.
