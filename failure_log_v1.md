# Integral Tropical-Sheaf Torsion (Wave I) — Adversarial Failure & Trap Log (`failure_log_v1.md`)

**Owner**: `@inquisitor`  
**Constitutional Scope**: `SPEC.md` §0–§5 (`100%` Python 3.9+ stdlib, zero external imports, zero `float`, inner-loop `Fraction` firewall on `architect/core/`, `signal.alarm(20)`).

---

## 1. AST Contraband & Firewall Scanner (`inquisitor/ast_scanner.py`)

- **Self-Test Verification**: `13 / 13` synthetic contraband vectors caught in-memory (`FORBIDDEN_EXTERNAL_IMPORT`, `FLOAT_LITERAL`, `FLOAT_IDENTIFIER`, `FLOAT_MATH_API`, `FLOAT_TIME_API`, `INNER_LOOP_FRACTION_FIREWALL`, `CORE_FLOAT_TRUE_DIV`, `ISINSTANCE_TEST_BYPASS`, `ISINSTANCE_DISPATCH_BYPASS`, `WAVE1_SVG_BANNED`, `HARDCODED_WORKSPACE_PATH`, plus outer-layer `Fraction` and internal `importlib.import_module("architect...")` allowlist checks).
- **Critical Python 3.9 Compatibility Finding**: System `/usr/bin/python3` is **Python 3.9.6** (`sys.stdlib_module_names` does not exist in 3.9). `inquisitor/ast_scanner.py` uses an explicit portable 3.9+ stdlib allowlist + `sysconfig` verification, and bans `time.perf_counter()` / `time.time()` (which return IEEE `float`) in favor of `time.perf_counter_ns()` / `time.time_ns()` + integer `//`.

---

## 2. Cycle 1 High-Value Mathematical Failure Vectors Discovered & Probed (`inquisitor/cycle1_adversarial_probes.py`)

| ID | Target Module / Trap | Adversarial Failure Mode Exposed | Exact Ground-Truth Witness / Guard |
| :--- | :--- | :--- | :--- |
| **K1.1** | `exact_int_la.py` (SNF) | Naive diagonal GCD loop halting on `diag(2, 3)` or `diag(4, 6)` without invariant divisibility $d_1 \mid d_2$ | `SNF([[2,0],[0,3]]) == [1,6]`, `SNF([[4,0],[0,6]]) == [2,12]` |
| **K1.2** | `exact_int_la.py` ($\mathbb{Z}$-solve) | Restricting inhomogeneous $\mathbb{Z}$-solve to $\mathbb{Q}$-pivot columns $J$ fails when only all columns together are coprime | `[[6, 10, 15]] x = [1]` ($\gcd(6,10)=2, \gcd(6,15)=3, \gcd(10,15)=5$, full $\gcd=1$, `x=(1,1,-1)`) |
| **K1.3** | `exact_int_la.py` ($\mathbb{Z}$-solve & $P_{\text{sat}}$) | Row-GCD normalization erases $\mathbb{Z}/2\mathbb{Z}$ torsion; Bareiss scaling injects fake torsion | `[[2,2,0],[0,2,2],[1,2,1]] x = [1,1,1]` ($\mathbb{Q}$-SAT, $\mathbb{Z}$-UNSAT; $P_{\text{sat}}^2 == P_{\text{sat}}$) |
| **K1.4** | `exact_int_la.py` (61-bit prime pre-screen) | Mod-$p_{61}$ rank drop when matrix entry is divisible by Mersenne prime $M_{61} = 2^{61} - 1$ | `diag(2^61 - 1, 1)` ($\mathbb{Q}$-rank `2`, mod-$M_{61}$ rank `1`) |
| **K2.1** | `bareiss_farkas_lp.py` | Cycling on degenerate 5D braid cone at $0 \in \mathbb{R}^5$ or negative common denominator flipping `<=` | 5D braid cycle + `-1` cut certified via $y=(1,1,1,1,1)$ |
| **K2.2** | `bareiss_farkas_lp.py` ($\text{Vol}_k$) | Volume routines assuming $0 \in P$ or counting lattice points (Pick's theorem fails in 3D!) | Translated Reeve $T_r + (5,7,11)$ ($0 \notin P$) has $\text{Vol}_3 = r$ for $r=1..12$ |
| **K3.1** | `padic_local_global.py` | Higher prime-power $3^2$ obstruction passing $F_3$ mod-3 pre-screen & $\mathbb{Q}$-solve | `[[9, 18]] c = [3]` (UNSAT, $v_3=2>1$) vs twin `[[9, 6]] c = [3]` (SAT via $c=(0, 1/2)$) |
| **K3.2** | `padic_local_global.py` (**Hidden Cancelled-Prime Bug**) | Basic $\mathbb{Q}$-solution $c_{\mathbb{Q}} = A_{P,J}^{-1} b_P$ cancels prime $5$ ($5/5=1$), so `L_odd(c_Q) = 3` misses $p=5$; solving only mod $3^k$ re-injects denominator $5$ into pivot coords | `A = [[3,0,1],[0,5,1]], b = [1,5]`: $c_{\mathbb{Q}}=(1/3,1,0)$ has $L_{\text{odd}}=3$; naive mod-3 pivot gives invalid $(0, 4/5, 1) \notin \mathbb{Z}[1/2]^3$, true solution is `c = (-3, -1, 10)` |
| **T1** | Trap 1 (`MAX_4`, `MAX_5`) | Testing only positive arithmetic-progression permutations `(1,2,3,4,5)` misses missing $-\text{ReLU}(-x)$ on negative chambers and sits directly on off-braid hinges $2 x_5 = x_i + x_j$ | Verified on `(-34,-13,-5,-2)` & `(1,2,5,13,34)` + off-braid wall jump `0` across $2x_5 - x_1 - x_3 = 0$ |
| **T2** | Trap 2 (Modular Refuter) | Biased $\mathbb{Z}[1/3]$ network matching `MAX_5` on **all 32 vertices of $\{0,1\}^5$** fools finite $\{0,1\}^5$-sampling refuters | $N(x) = \text{ReLU}(1) - \text{ReLU}(1 - \sum x_i) + \text{ReLU}(\frac{1}{3}x_1 - \frac{1}{2})$ matches $\{0,1\}^5$ 100%, refuted at $x^* = (3,0,0,0,0)$ |
| **T3** | Trap 3 ($B_5$-Conforming) | Every $B_5$-conforming 2-layer ReLU atom depends on $\le 4$ coordinates (as `MAX_3` is not 1-layer realizable) | Exact 64-row `{0,1}` Farkas witness (5th Mobius difference $\Delta_5$) annihilates all 96 $B_5$-atoms, $\Delta_5(\text{MAX}_5) = 1$ |
| **T4** | Trap 4 ($D_\Sigma(f)$) | Using unnormalized $\det=2$ normal $(4,2)$ instead of primitive $\eta=(2,1)$ multiplies half-integer jump $1/2 \to 1$, erasing $\text{Weil}/\text{Cart} \cong \mathbb{Z}/2\mathbb{Z}$ | Certified primitive jump $1/2$, $\text{Aff}(\mathbb{Z}^d)$ tilt invariance, and Reeve $T_r$ at $r=1$ (unimodular) & $r=2,3,5,6$ |
| **T5** | Trap 5 (Group Guard) | Off-by-one `W > \|G\|^2` vs `W >= \|G\|^2` guard check | Hard `ValueError` required at both $W = \lvert G \rvert^2$ and $W = \lvert G \rvert^2 + 1$ |
| **T6** | Trap 6 (Repaired Annulus) | **Concurrent-Spoke Degeneracy**: untriangulated 3-quad annulus has 3 spokes concurrent at $(0,0)$, collapsing monodromy rank from `3` to `2`! | Triangulating with 3 chords `u1-v2, u2-v3, u3-v1` restores full **rank 3** and certifies pure Escher height-shift monodromy `(0, 0, -2)` with zero slope jump |
| **T7** | Trap 7 (Annular CPA) | Discontinuous per-triangle gradients masquerading as a 1-cocycle without tangential edge matching | Certified 8-triangle flat CPA 1-cocycle matching all 8 interior edges with strict decrease $\le -1$ and Stokes-invariant period `-16` on both inner & outer rims |

---

## 3. Critical Structural Discovery Ahead of Cycle 2 (Track B2 — Sequential Gomory Rank vs. Simultaneous Schrijver-Chvatal Rank)

- **Discovery (`B2-CG-DEFINITION-SPLIT`)**: Testing `simulator/sim_exact_la.py`'s simultaneous Chvatal-Gomory closure `cg_round_2d_exact` on the 4-ray fan family $\Sigma_*^{(k)}$ ($k = 1..10$, determinant $2k + 3$, $P_0 = \{-u + (2k+1)t \ge 0,\; u \ge 1,\; 2t \ge 0,\; 2u - (2k-1)t \ge 2\}$) revealed that:
  1. **Sequential Single-Cut Gomory Rank = 2** at $k = 1$ (matching `SPEC.md` §4 Theorem B2 verbatim: Round-1 cut $t \ge \lceil 2/5 \rceil = 1$ leaves fractional vertex $(3/2, 1)$; Round-2 cut $u \ge \lceil 3/2 \rceil = 2$ yields the Klein sail $\{(3,1), (2,1), (2,2)\}$).
  2. **Simultaneous Elementary Schrijver-Chvatal Closure Rank ($P \mapsto P^{(1)}$) = 1 for ALL $k = 1..10$** on 4-ray $\Sigma_*^{(k)}$! Proof: the valid Round-1 multiplier $\lambda = \bigl(\frac{2k-1}{2k+3},\, 0,\, 0,\, \frac{2k+1}{2k+3}\bigr) \ge 0$ already combines $(-u + (2k+1)t \ge 0)$ and $(2u - (2k-1)t \ge 2)$ directly in $P_0$ to yield $1 \cdot u + 0 \cdot t \ge \frac{4k+2}{2k+3} \implies u \ge \lceil 2 - \frac{4}{2k+3} \rceil = 2$ (and $\frac{1}{2k+3}(-u + (2k+1)t) + \frac{k+1}{2k+3}(2u - (2k-1)t)$ yields $u - (k-1)t \ge 2$) **inside $P_0^{(1)}$**! Geometrically, $u \ge 1$ and $2t \ge 0$ are strictly redundant on $P_0$, so $P_0$ is a single translated 2D cone whose entire Klein sail lies in $P_0^{(1)}$.
  3. **Actionable Rule for Cycle 2**: Theorem B2 must explicitly distinguish **Sequential Gomory Cut Count (= 2 on $\Sigma_*$)** from **Simultaneous Chvatal Closure Rank (= 1 on single-cone 4-ray fans; achieving simultaneous Chvatal rank $\ge 2$ requires opposing cones in $m \ge 5$ rays or $d = 3$)**.

---

## 4. Live Peer Audit Log — Cycle 1 Final Status (`PASS`)

- **Workspace-Wide AST Contraband & JSON Float Scan (`inquisitor/ast_scanner.py`)**: **`PASS` (`18` Python files + `4` Cycle 1 JSON checkpoints, `0` violations, `0` advisories, `12/12` scanner self-tests)**.
- **`architect/core/` (`exact_int_la.py`, `bareiss_farkas_lp.py`, `padic_local_global.py`)**: **`PASS` (`14/14` Live Adversarial Torture Checks)** — Passed $M_{61} = 2^{61}-1$ pre-screen collision, pairwise-non-coprime `[[6,10,15]] x = [1]` $\mathbb{Z}$-solve, row-dependent $\mathbb{Q}$-SAT/$\mathbb{Z}$-UNSAT torsion & $P_{\text{sat}}$ idempotence, 5D degenerate braid Farkas witness, translated Reeve $T_r + (5,7,11)$, 4D hypercube (`Vol_4 = 24`), 5D $\Delta_2 \times \Delta_3$ (`Vol_5 = 10`), 4D redundant-edge-midpoint Beneath-Beyond invariance, $3^2$ mod-3-passing obstruction `[[9,18]] c = [3]`, and Hidden Cancelled-Prime `[[3,0,1],[0,5,1]] c = [1,5]`.
- **`architect/test_wave1_traps.py` + `artifacts/cycle1_architect_traps.json`**: **`PASS`** — Verified `0` exit code under `/usr/bin/python3 -I`, plus live adversarial injection of the 32-point $\{0,1\}^5$-matching Boolean-cube impostor network into `refute_z_local_2_biased_max5_network(...)` (successfully refuted via asymptotic recession threshold $T_0$) and `W = |G|^2, |G|^2 + 1` `ValueError` guard checks.
- **`formalist/cert_kernel.py` + `formalist/proof_pack_v1.py` + `artifacts/cycle1_formalist_audit.json`**: **`PASS`** — Verified `0` exit code under `/usr/bin/python3 -I` and independent symbolic sub-chamber verification (`84` leaf subchambers on `MAX_4`, `480` leaf subchambers / `360` off-braid splits on Bakaev `2*MAX_5`). *(Cycle 1 transient bugs caught during live monitoring and resolved by `@formalist`: Trap 3 nullspace sign-cone check and Trap 6 monodromy sign orientation.)*
- **`simulator/` (`sim_exact_la.py`, `sweep_reeve_fans.py`, `sweep_airy_spiderwebs.py`, `sweep_finite_groups.py`, `run_cycle1_sweeps.py`) + `artifacts/cycle1_simulator_sweeps.json`**: **`PASS`** — Verified `0` AST/JSON float violations, `M_61` & 3-col SNF checks, 5-ray simultaneous CG rank `2k+1`, and proper-subgroup coset torsion trichotomy (`Q_8` core-free obstruction vs `S_4` unimodular `[1]^24` proper cosets).

---

## 5. Cycle 2 Adversarial Failure Vectors & Live Track A–E Probes (`inquisitor/cycle2_adversarial_probes.py`)

| ID | Target Track | Adversarial Failure Mode Exposed | Exact Ground-Truth Witness / Guard |
| :--- | :--- | :--- | :--- |
| **E0-FILIPPOV** | Track E0 (Escher Waterfall) | Missing Clarke-subgradient $\times$ Filippov-crease decrease check or sliding-mode tangency check on switching rays | 8-triangle square ring CPA cocycle (`d^1 eta = 0`, period `-16`) with all 4 cross-pairings $g_{\tau^\pm} \cdot f_{\tau^\pm} < 0$ & exact outward 1-lap Poincare expansion `83521/50625 > 1` (`FALSIFIED_COUNTEREXAMPLE`) |
| **E-BOULIGAND** | Track E0 / E1 (Inner Corners) | Confusing non-convex $270^\circ$ inner Bouligand cone $T_A(1,1) = \{\xi \ge 0 \lor \eta \ge 0\}$ with $90^\circ$ intersection $\{\xi \ge 0 \land \eta \ge 0\}$, or missing continuous circular hole-leak $(1, 1-\epsilon)$ | Filippov midpoint $(-1/2, +1/2) \in T_A(1,1) \setminus \{\xi \ge 0 \land \eta \ge 0\}$; circular flow $(-y,x)$ leaks into hole at $(1, 99/100)$ ($n_{\text{hole}} \cdot f = +99/100 > 0$) |
| **E1-PINNED** | Track E1 (Pinned Torsor) | Claiming orbital stability from local torsor decrease without 1-lap cut-section contraction | Pinned torsor jump $\Delta_{\text{lap}} V_{\text{pinned}}(r) = -\frac{1}{2}\lvert r - 3/2 \rvert < 0$ ($r \ne 3/2$) |
| **E2-MOBIUS** | Track E2 ($\mathbb{Z}_{-1}$ Torsion) | Spoofing `SNF = diag(1,...,1,2)` via scaled untwisted circle/cylinder rows where $\delta^1 \delta^0 \ne 0$, $b_{\partial} = 2$, or $H^1(M; \mathbb{Q}) \ne 0$ | Genuine $N=3$ 2D triangulated Mobius band ($V=6, E=12, F=6$, single 6-cycle boundary $b_{\partial}=1$, $\delta^1 \delta^0 = 0$, $\text{rank}(\delta^0)=6=V$, $H^1(M;\mathbb{Z}_{-1}) \cong \mathbb{Z}/2\mathbb{Z}$, $H^1(M;\mathbb{Q}_{-1}) = 0$) |
| **A1-MOD3** | Track A1 (Integral Functors) | False universal mod-3 annihilator prose at non-prime-power $d = 5$ | `Vol_5(Delta_2 x Delta_3) = 10 == 1 (mod 3) != 0` in `ReLU_{5,2}(Z)`, vs prime-power $d = 3^2 = 9$ where $\binom{9}{a} \equiv 0 \pmod 3$ for all $1 \le a \le 8$ |
| **A2-MAX6-SPOOF** | Track A (`6*MAX_6` & `Syl_2`) | Checking `6*MAX_6` only at `720` permutations of `(1,2,3,4,5,6)` misses off-braid kinks (`6*x_(6) + ReLU((x_(6)-x_(5)) - (x_(2)-x_(1)))` vanishes on all `720` standard perms!) | `verify_6max6_beyond_720_rays` tests `720` negative Fibonacci + `720` sum-collision-free chambers + explicit 2nd-difference zero checks across internal off-braid hinges |
| **D-GUARDS** | Track D (`Q_8` & Compression) | Passing `Q_8` minimal faithful permutation degree $m = 8 \implies W = m^2 = 64 == \lvert Q_8 \rvert^2$ into permutation compression without `ValueError` | Enforces `ValueError` at `W >= \|G\|^2` across all Track D compression entry points + verifies pure-$\mathbb{Z}$ `C_5` `{0,1}` circuit at $W = 8 \ll 25$ |
| **EPISTEMIC** | `theorem_ledger_v1.json` | Promoting bounded-dictionary `MAX_6` `Z[1/2]` UNSAT to `CERTIFIED_EXACT`, omitting `FALSIFIED_COUNTEREXAMPLE` on E0, or emitting JSON floats | `audit_epistemic_ledger` enforces strict 3-valued epistemic tags and zero float tokens |

---

## 6. Live Peer Audit Log — Cycle 2 Track A–E & Ledger Status

- **`verify_all.py` + `architect/track_{a,b,c,d,e}_*.py` + `artifacts/theorem_ledger_v1.json`**: **`PASS` (`10,386 ms` total under `/usr/bin/python3 -I`, `< 30s` budget)** —
  * **Track A (`track_a_foundations.py`)**: Verified all 4 exported `6 * MAX_6` evaluators (`eval_6max6_hexagon`, `eval_6max6`, `eval_brunck_6max6`, `eval_d6_6max6`) through `verify_6max6_beyond_720_rays` (`1,440` negative/collision-free chambers + explicit 2nd-difference off-braid hinge checks), `Syl_2(S_6)` (`16` elements, `45` orbits, `< 50 ms`), `Vol_5(Delta_2 x Delta_3) = 10 == 1 (mod 3)`, and `vrc_{2,Z}(Delta_4) = +infinity` vs `<= 9` over `Z[1/2]`.
  * **Track B (`track_b_decomp_splines.py`) & Track C (`track_c_airy_cosheaf.py`)**: Verified Reeve `T_r` (`r = 1..12`), 4-ray (`k = 1..10`) vs 5-ray (`k = 1..3`, simultaneous CG rank `3, 5, 7`) CG split, `F_Z^prim` vs `F_Z^geom` torsion, `b = 2, 3` free `Z^{3(b-1)}` monodromy, and 2D Precision-Bockstein `Z/p^kZ` dictionary.
  * **Track D (`track_d_group_circuits.py`)**: Verified `ValueError` guards at `W >= |G|^2` across `validate_group_compression_width`, `build_cyclic_1layer_z_circuit` (`C_5` at `W = 25, 26`), and `build_permutation_biequivariant_circuit` (`Q_8` at `m = 8 => W = 64, 65`), plus `C_5` strict `(C_5 x C_5)`-equivariance `W >= 25` Farkas proof and `Phi_5` Eisenstein irreducibility (`d_emb(R)=2 < 4=d_emb(Q)=d_emb(Z)`).
  * **Track E (`track_e_cpa_torsors.py`)**: Verified E0 outward Poincare return `194481/130321 > 1` (`FALSIFIED_COUNTEREXAMPLE`) with all Clarke/Filippov crease derivatives `<= -19 < 0`, E1 Bouligand positive invariance + `16/81 < 1` pinned-torsor contraction around `r* = 10/3`, and E2 `M_3, M_4, M_6` twisted `Z_{-1}` `delta^1 @ delta^0 == 0` with `SNF(delta^0) = (1,...,1,2)`, `H^1(M; Z_{-1}) ~ Z/2Z`, `H^1(M; Q_{-1}) = 0`.
  * **Epistemic Ledger (`artifacts/theorem_ledger_v1.json`)**: **`PASS` (`15` claims: `13 CERTIFIED_EXACT`, `1 FALSIFIED_COUNTEREXAMPLE` [E0], `1 OPEN_BUDGET_EXCEEDED` [`A2_MAX6_Z_HALF_FRONTIER`], `0` float tokens)**. *(Internal scanner substring bug matching `"E0"` inside `"GATE0_WAVE1_TRAPS_1_TO_7"` caught and fixed in `inquisitor/cycle2_adversarial_probes.py`.)*
- **`formalist/{tracks_bc_proofs,tracks_ade_proofs,proof_pack_v1}.py`**: **`PASS` (`16/16` stages under `/usr/bin/python3 -I`, `0` AST/JSON violations)**.
- **`simulator/{sweep_track_e_torsors,sweep_track_a_max6,run_cycle2_sweeps}.py` + `artifacts/cycle2_simulator_sweeps.json`**: **`PASS` (`0` AST/JSON float violations across all `30` workspace `.py` files)**.

---

## 7. Cycle 3B Isolated `/tmp` Clean-Room Gate & Final Wave I Signoff (`inquisitor/cycle3_cleanroom_audit.py`)

- **Stage 1 — Workspace-Wide AST, Portability & Zero-Float Firewall**: **`PASS` (`32` Python modules + all `artifacts/*.json` checkpoints, `13 / 13` synthetic contraband self-tests, `0` violations, `0` advisories, `0` JSON float tokens, `0` hardcoded host paths, `0` Wave I SVGs)**.
  * *Cycle 3 Portability Audit Refinements*: Added `HARDCODED_WORKSPACE_PATH` AST check ensuring every `.py` module resolves paths strictly via `Path(__file__).resolve()` while allowing bare prefix tokens used inside portability self-checks.
- **Stage 2 — Isolated `/tmp` Clean-Room Execution (`/usr/bin/python3 -I verify_all.py`)**: **`PASS` (`exit_code = 0`, `~12.8 s` clean-room wall-clock `< 30.0 s` budget)** —
  * Copied `36` clean source files (`SPEC.md`, `verify_all.py`, `PROOF_DOSSIER_v1.md`, `failure_log_v1.md`, `architect/`, `formalist/`, `simulator/`, `inquisitor/`, strictly excluding `__pycache__`, `.pyc`, and all pre-existing `artifacts/*.json`) into an isolated `tempfile.TemporaryDirectory` inside `/tmp`.
  * Executed `/usr/bin/python3 -I verify_all.py` with scrubbed environment (`PATH=/usr/bin:/bin`, `HOME=<tmp>`, `TMPDIR=<tmp>`, `PYTHONDONTWRITEBYTECODE=1`), confirming all `10` verification stages passed under `signal.alarm(20)`, fresh `artifacts/theorem_ledger_v1.json` was regenerated from scratch inside `/tmp`, `0` AST/JSON float violations appeared in `/tmp`, and the temporary directory was completely removed on exit (`tmp_directory_cleaned_up = True`).
- **Stage 3 — 100% Epistemic Ledger Certificate Coverage & Dossier Completeness**: **`PASS`** —
  * Verified **`21 / 21` (`100%`)** claims in `artifacts/theorem_ledger_v1.json` carry explicit machine-checked `certificate` objects verified independently by `formalist.cert_kernel.verify_ledger_certificate`: `19 CERTIFIED_EXACT` (`TRAP_1`..`TRAP_7`, `B1`, `B2`, `C1`, `C2`, `E1`, `E2`, `A1`, `A2_MAX6_Z_SIXTH_AND_SYL2_ENGINE`, `A3`, `D1`, `D2`, `D3`), `1 FALSIFIED_COUNTEREXAMPLE` (`E0`), and `1 OPEN_BUDGET_EXCEEDED` (`A2_MAX6_Z_HALF_FRONTIER`), with `0` JSON float tokens.
  * Verified presence, coverage markers (`B1, B2, C1, C2, E0, E1, E2, A1, MAX_6, A3, D1, D2, D3, WAVE II`), and non-SVG purity across `PROOF_DOSSIER_v1.md`, `failure_log_v1.md`, and `simulator/cycle_benchmarks.md`.
- **Final Wave I Inquisitor Verdict**: **`CLEAN-ROOM CERTIFIED PASS`** (`artifacts/cycle3_inquisitor_cleanroom.json`).

