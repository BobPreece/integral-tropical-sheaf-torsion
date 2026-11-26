# Cycle 1 Exact Parameterized Family & Finite-Group Sweep Benchmarks (`@simulator`)

- **Execution Mode**: `/usr/bin/python3 -I` (100% Python 3.9+ stdlib, zero external imports, zero `float`, zero `Fraction`, zero `/`)
- **Total Cycle 1 Sweep Wall-Clock Runtime**: `1759.980 ms` (`signal.alarm(20)` enforced per stage)
- **Simulator AST Self-Audit**: `PASSED` across `12` modules (`0` violations)

## 1. 3D Reeve Tetrahedra `T_r` (`r = 2..12`, plus `r = 1` & `A_1` Controls) — Trap 4 & Track B1

- **2D `A_1` Control `(1,0), (-1,2), (0,-1)`**: `dim B_{A_1} = 1` (non-trivial DC splits: `False`), `Cone_12 SNF = [1, 2]`, `Weil/Cart = Z/2Z`, witness `h = [0, 1, 0]` primitive wall jumps `['1/2', '1/2', '1']` (`0.073 ms`).

| `r` | `Vol_3(T_r)` | `\|T_r cap Z^3\|` | Primal Edge SNF | Polar Facet SNF (`z, -ry+z, rx-z`) | Ridge Colon SNFs (x3) | `Weil / Cart` | Reeve Wall Jumps | Peak Bits | Runtime (`ms`) |
|---:|---:|---:|---|---|---|---|---|---:|---:|
| `1` | `1` | `4` | `[1, 1, 1]` | `[1, 1, 1]` | `[1, 1]` | `0` | `(1, 1, 1)` | `1` | `0.265` |
| `2` | `2` | `4` | `[1, 1, 2]` | `[1, 2, 2]` | `[1, 2]` | `Z/2Z` | `(1/2, 1/2, 1/2)` | `2` | `0.261` |
| `3` | `3` | `4` | `[1, 1, 3]` | `[1, 3, 3]` | `[1, 3]` | `Z/3Z` | `(1/3, 1/3, 1/3)` | `2` | `0.274` |
| `4` | `4` | `4` | `[1, 1, 4]` | `[1, 4, 4]` | `[1, 4]` | `Z/4Z` | `(1/4, 1/4, 1/4)` | `3` | `0.267` |
| `5` | `5` | `4` | `[1, 1, 5]` | `[1, 5, 5]` | `[1, 5]` | `Z/5Z` | `(1/5, 1/5, 1/5)` | `3` | `0.277` |
| `6` | `6` | `4` | `[1, 1, 6]` | `[1, 6, 6]` | `[1, 6]` | `Z/6Z` | `(1/6, 1/6, 1/6)` | `3` | `0.270` |
| `7` | `7` | `4` | `[1, 1, 7]` | `[1, 7, 7]` | `[1, 7]` | `Z/7Z` | `(1/7, 1/7, 1/7)` | `3` | `0.301` |
| `8` | `8` | `4` | `[1, 1, 8]` | `[1, 8, 8]` | `[1, 8]` | `Z/8Z` | `(1/8, 1/8, 1/8)` | `4` | `0.269` |
| `9` | `9` | `4` | `[1, 1, 9]` | `[1, 9, 9]` | `[1, 9]` | `Z/9Z` | `(1/9, 1/9, 1/9)` | `4` | `0.291` |
| `10` | `10` | `4` | `[1, 1, 10]` | `[1, 10, 10]` | `[1, 10]` | `Z/10Z` | `(1/10, 1/10, 1/10)` | `4` | `0.277` |
| `11` | `11` | `4` | `[1, 1, 11]` | `[1, 11, 11]` | `[1, 11]` | `Z/11Z` | `(1/11, 1/11, 1/11)` | `4` | `0.295` |
| `12` | `12` | `4` | `[1, 1, 12]` | `[1, 12, 12]` | `[1, 12]` | `Z/12Z` | `(1/12, 1/12, 1/12)` | `4` | `0.284` |

## 2. 4-Ray 2D Fans `v_4^(k) = (-1, -(2k+1))` (`k = 1..10`) & 5-Ray Simultaneous CG Sweep — Track B2

> **Key Cycle 1 Discovery (Sequential Axis Cuts vs. Simultaneous Elementary CG Rank)**:
> 1. On ALL 4-ray 2D fans `Sigma^(k)` (`k = 1..10`), Jensen's inequality on `max(0, .)` makes `w_2 >= max(0, w_2(f))` and `w_3 >= max(0, w_3(f))` redundant over `R`, collapsing `D_tilde_{Sigma^(k)}(w(f))` to a **2-facet cone in `R^2`**. Consequently, **Simultaneous Elementary Chvatal-Gomory Rank = `1`** for every `k = 1..10` (`t >= 1` and `u - (k-1)t >= 2` are both Round-1 Hilbert-parallelepiped cuts!).
> 2. Under **sequential axis-aligned 1-cut Gomory rounds** (`t >= 1`, then `u >= k+1`): `k = 1` terminates in **`2` rounds** (`(6/5, 2/5) -> (3/2, 1) -> {(2,1),(2,2),(3,1)}`), whereas for **`k >= 2`** `u = k+1` meets `2u - (2k-1)t = 2` at the **still-fractional vertex `(k+1, 2k/(2k-1))`**, requiring a **`3`rd** cut (`u - (k-1)t >= 2`)!
> 3. Moving to **`m = 5` primitive rays** (`Sigma_5^(k)`, `dim B = 3`) breaks the 2-facet planar cone ceiling: pure Cartier `w(f) = (0, 1, 0, 1, -(2k+1))` achieves **Simultaneous Elementary CG Rank = `2k + 1`** (`3` at `k=1`, `5` at `k=2`, `7` at `k=3`; `9` at `k=4` on extended sweep)!

### 2A. 4-Ray 2D Fans `Sigma^(k)` (`k = 1..10`, Determinant `2k + 3`)

| `k` | Det `2k+3` | LP Vertex `(u*, t*)` | After `t >= 1` | After `u >= k+1` | Seq. Axis Rounds | Sim. Elem. CG Rank | Klein Sail `(u, t)` Vertices | Max Bits | Runtime (`ms`) |
|---:|---:|---|---|---|---:|---:|---|---:|---:|
| `1` | `5` | `(6/5, 2/5)` | `(3,1), (3/2,1)` | `(2,1), (2,2), (3,1)` | `2` | `1` | `(2,1), (2,2), (3,1)` | `3` | `0.165` |
| `2` | `7` | `(10/7, 2/7)` | `(5,1), (5/2,1)` | `(3,1), (5,1), (3,4/3)` | `3` | `1` | `(3,1), (4,2), (5,1)` | `4` | `0.178` |
| `3` | `9` | `(14/9, 2/9)` | `(7,1), (7/2,1)` | `(4,1), (7,1), (4,6/5)` | `3` | `1` | `(4,1), (6,2), (7,1)` | `4` | `0.178` |
| `4` | `11` | `(18/11, 2/11)` | `(9,1), (9/2,1)` | `(5,1), (9,1), (5,8/7)` | `3` | `1` | `(5,1), (8,2), (9,1)` | `5` | `0.187` |
| `5` | `13` | `(22/13, 2/13)` | `(11,1), (11/2,1)` | `(6,1), (11,1), (6,10/9)` | `3` | `1` | `(6,1), (10,2), (11,1)` | `6` | `0.186` |
| `6` | `15` | `(26/15, 2/15)` | `(13,1), (13/2,1)` | `(7,1), (13,1), (7,12/11)` | `3` | `1` | `(7,1), (12,2), (13,1)` | `7` | `0.209` |
| `7` | `17` | `(30/17, 2/17)` | `(15,1), (15/2,1)` | `(8,1), (15,1), (8,14/13)` | `3` | `1` | `(8,1), (14,2), (15,1)` | `7` | `0.207` |
| `8` | `19` | `(34/19, 2/19)` | `(17,1), (17/2,1)` | `(9,1), (17,1), (9,16/15)` | `3` | `1` | `(9,1), (16,2), (17,1)` | `7` | `0.208` |
| `9` | `21` | `(38/21, 2/21)` | `(19,1), (19/2,1)` | `(10,1), (19,1), (10,18/17)` | `3` | `1` | `(10,1), (18,2), (19,1)` | `8` | `0.224` |
| `10` | `23` | `(42/23, 2/23)` | `(21,1), (21/2,1)` | `(11,1), (21,1), (11,20/19)` | `3` | `1` | `(11,1), (20,2), (21,1)` | `8` | `0.224` |

### 2B. 5-Ray 2D Fans `Sigma_5^(k)` (`k = 1..3`) — Unbounded Simultaneous Elementary CG Rank `2k + 1`

| `k` | Rays `(1,0), (2k+1,1), (-2k-1,1), (-1,-2), (0,-1)` | Cartier `w(f)` | Initial Max Denom | Sim. Elementary CG Rank | Final Integer Hull Vertices `(w1,w2,w3)` | Runtime (`ms`) |
|---:|---|---|---:|---:|---|---:|
| `1` | `m = 3` | `[0, 1, 0, 1, -3]` | `7` | **`3`** | `(1,1,0), (2,1,1), (3,4,3)` | `11.941` |
| `2` | `m = 5` | `[0, 1, 0, 1, -5]` | `11` | **`5`** | `(1,1,0), (2,1,1), (5,6,5)` | `156.583` |
| `3` | `m = 7` | `[0, 1, 0, 1, -7]` | `15` | **`7`** | `(1,1,0), (2,1,1), (7,8,7)` | `1156.241` |

## 3. 2D Integral Maxwell-Cremona Airy Cosheaves, Spiderwebs & Punctured Annuli — Trap 6 & Track C

| Complex | `(V, E, F)` | `b` | `F^geom` Edge Torsion | Unclamped `ev_V` SNF on `H_2^int(A_Z)` | `H_1^int(A_Z)` Torsion | `H_1^all(A_Z)` Torsion | `Aff` Monodromy Rank `3(b-1)` | Bockstein `Z/p^kZ` Match | Max Bits | Runtime (`ms`) |
|---|---|---:|---|---|---|---|---:|---|---:|---:|
| `spiderweb_scaled_m1` | `(4,6,3)` | `1` | `[]` | `[1, 1, 1, 1]` | `[]` | `[]` | `0` | `True` | `2` | `1.017` |
| `spiderweb_scaled_m2` | `(4,6,3)` | `1` | `[2, 2, 2, 2, 2, 2]` | `[1, 2, 2, 2]` | `[]` | `[]` | `0` | `True` | `2` | `1.001` |
| `spiderweb_scaled_m3` | `(4,6,3)` | `1` | `[3, 3, 3, 3, 3, 3]` | `[1, 3, 3, 3]` | `[]` | `[]` | `0` | `True` | `2` | `0.995` |
| `spiderweb_scaled_m4` | `(4,6,3)` | `1` | `[4, 4, 4, 4, 4, 4]` | `[1, 4, 4, 4]` | `[]` | `[]` | `0` | `True` | `3` | `0.997` |
| `spiderweb_scaled_m5` | `(4,6,3)` | `1` | `[5, 5, 5, 5, 5, 5]` | `[1, 5, 5, 5]` | `[]` | `[]` | `0` | `True` | `3` | `1.023` |
| `spiderweb_scaled_m6` | `(4,6,3)` | `1` | `[6, 6, 6, 6, 6, 6]` | `[1, 6, 6, 6]` | `[]` | `[]` | `0` | `True` | `3` | `1.010` |
| `spiderweb_scaled_m8` | `(4,6,3)` | `1` | `[8, 8, 8, 8, 8, 8]` | `[1, 8, 8, 8]` | `[]` | `[]` | `0` | `True` | `4` | `1.004` |
| `spiderweb_scaled_m9` | `(4,6,3)` | `1` | `[9, 9, 9, 9, 9, 9]` | `[1, 9, 9, 9]` | `[]` | `[]` | `0` | `True` | `4` | `0.996` |
| `spiderweb_scaled_m12` | `(4,6,3)` | `1` | `[12, 12, 12, 12, 12, 12]` | `[1, 12, 12, 12]` | `[]` | `[]` | `0` | `True` | `4` | `0.990` |
| `spiderweb_prim_twist_m2` | `(4,6,3)` | `1` | `[2]` | `[1, 1, 1, 2]` | `[]` | `[]` | `0` | `True` | `2` | `0.986` |
| `spiderweb_prim_twist_m3` | `(4,6,3)` | `1` | `[]` | `[1, 1, 1, 3]` | `[]` | `[]` | `0` | `True` | `4` | `0.998` |
| `spiderweb_prim_twist_m4` | `(4,6,3)` | `1` | `[2]` | `[1, 1, 1, 4]` | `[]` | `[]` | `0` | `True` | `4` | `0.985` |
| `spiderweb_prim_twist_m6` | `(4,6,3)` | `1` | `[2]` | `[1, 1, 1, 6]` | `[]` | `[]` | `0` | `True` | `5` | `1.018` |
| `spiderweb_prim_twist_m8` | `(4,6,3)` | `1` | `[2]` | `[1, 1, 1, 8]` | `[]` | `[]` | `0` | `True` | `6` | `0.989` |
| `spiderweb_prim_twist_m9` | `(4,6,3)` | `1` | `[]` | `[1, 1, 1, 9]` | `[]` | `[]` | `0` | `True` | `7` | `0.996` |
| `spiderweb_prim_twist_m12` | `(4,6,3)` | `1` | `[2]` | `[1, 1, 1, 12]` | `[]` | `[]` | `0` | `True` | `7` | `0.982` |
| `desargues_prism_m1` | `(6,12,7)` | `1` | `[2, 2, 2]` | `[1, 1, 1, 1, 2, 6]` | `[2]` | `[]` | `0` | `True` | `4` | `4.521` |
| `desargues_prism_m2` | `(6,12,7)` | `1` | `[2, 2, 2, 3, 3, 3]` | `[1, 1, 1, 6, 6, 6]` | `[3]` | `[]` | `0` | `True` | `4` | `4.510` |
| `desargues_prism_m3` | `(6,12,7)` | `1` | `[3, 3, 3, 4, 4, 4]` | `[1, 1, 3, 3, 12, 12]` | `[4]` | `[3]` | `0` | `True` | `6` | `4.410` |
| `desargues_prism_m4` | `(6,12,7)` | `1` | `[4, 4, 4, 5, 5, 5]` | `[1, 1, 1, 4, 20, 60]` | `[5]` | `[]` | `0` | `True` | `8` | `4.434` |
| `punctured_annulus_b2_s1` | `(6,12,6)` | `2` | `[2, 2, 2]` | `[1, 1, 1, 1, 2, 2]` | `[2]` | `[]` | `3` | `True` | `4` | `3.391` |
| `punctured_annulus_b2_s2` | `(6,12,6)` | `2` | `[2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4]` | `[1, 2, 2, 2, 4, 4]` | `[4]` | `[2]` | `3` | `True` | `5` | `3.418` |
| `double_punctured_b3` | `(24,51,26)` | `3` | `[]` | `[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]` | `[]` | `[]` | `6` | `True` | `3` | `55.403` |

## 4. Finite-Group Multiplication, Permutation Compression & SNF Readout Torsion — Trap 5 & Track D

> **Key Cycle 1 Group Edge Cases & Exact 3-Regime Coset Trichotomy**:
> 1. **Faithful Permutation Compression (`m^2 < |G|^2`) vs. Core-Free Obstruction (`m^2 == |G|^2`)**: `S_3 (9 < 36)`, `D_4 (16 < 64)`, `D_5 (25 < 100)`, `A_4 (16 < 144)`, and `S_4 (16 < 576)` compress strictly via zero-bias pure-`Z` permutation circuits (`arXiv:2410.07476v3`), whereas `C_3, V_4, C_4, C_5` and non-abelian **`Q_8`** have `m(G) = |G|` (`m^2 == |G|^2`; for `Q_8`, `-1` lies in every nontrivial subgroup so no proper core-free subgroup exists!).
> 2. **Exact 3-Regime Proper-Subgroup Coset (`|H| >= 2`) Readout Trichotomy**:
>    - **Regime I (`Q`-Rank Deficient, `rank_Q < |G|`)**: `C_3 (1<3)`, `C_4 (2<4)`, `C_5 (1<5)`, and **`Q_8 (4<8)`** fail to span `e_0` even over `Q` (unique minimal subgroup blocks separation; adding the 4D integral quaternion representation on `Q_8` restores full `Q`-rank `8` with SNF `[1, 1, 1, 1, 2, 4, 4, 8]`).
>    - **Regime II (`Q`-Complete + Genuine `Z`-Torsion)**: `V_4` (`[2]`), `S_3` (`[3]`), `D_4` (`[2]`), `D_5` (`[5]`), and `A_4` (`[2, 2]`) span all outcomes over `Q` (`e_0` `Q`-SAT) but suffer exact subgroup-Mobius SNF torsion over `Z` (`e_0` `Z`-UNSAT)!
>    - **Regime III (`Z`-Unimodular Coset Synthesis!)**: **`S_4`** (`210` proper-subgroup cosets) achieves `SNF = [1]^24` (**zero `Z`-torsion**, `e_0` `Z`-SAT!) because `S_3 <= S_4` yields `3*e_0` and `D_4 <= S_4` yields `2*e_0`, so Bezout `1*(3*e_0) - 1*(2*e_0) = e_0` over `Z`!

| Group | `\|G\|` | `\|G\|^2` | Min Faithful `m` | `D1(b)` `C_n` Width (`b/u`) | `D1(c)` Perm Width `m^2` (Margin) | Irrep Feature SNF (`Z^{\|G\|^2 x \|G\|}`) | Proper Coset `(Cols, Q-Rank, Z-Torsion, e0_Z)` | Max Bits | Runtime (`ms`) |
|---|---:|---:|---:|---|---|---|---|---:|---:|
| `C_3` | `3` | `9` | `3` | `4 / 5` | `9 == \|G\|^2` (blocked) | `[1, 1, 3]` | `(1, 1, [], False)` | `2` | `0.324` |
| `V_4` | `4` | `16` | `4` | `—` | `16 == \|G\|^2` (blocked) | `[1, 2, 2, 4]` | `(7, 4, [2], False)` | `3` | `0.436` |
| `C_4` | `4` | `16` | `4` | `6 / 7` | `16 == \|G\|^2` (blocked) | `[1, 1, 2, 4]` | `(3, 2, [], False)` | `3` | `0.586` |
| `C_5` | `5` | `25` | `5` | `8 / 9` | `25 == \|G\|^2` (blocked) | `[1, 1, 1, 1, 5]` | `(1, 1, [], False)` | `3` | `0.986` |
| `S_3` | `6` | `36` | `3` | `—` | `9` (`>=1`) | `[1, 1, 1, 3, 3, 6]` | `(12, 6, [3], False)` | `3` | `1.469` |
| `D_4` | `8` | `64` | `4` | `—` | `16` (`>=2`) | `[1, 1, 2, 2, 2, 4, 4, 8]` | `(27, 8, [2], False)` | `4` | `3.718` |
| `D_5` | `10` | `100` | `5` | `—` | `25` (`>=5`) | `[1, 1, 1, 1, 1, 1, 1, 5, 5, 10]` | `(28, 10, [5], False)` | `6` | `9.322` |
| `A_4` | `12` | `144` | `4` | `—` | `16` (`>=2`) | `[1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4, 12]` | `(38, 12, [2, 2], False)` | `4` | `13.034` |
| `S_4` | `24` | `576` | `4` | `—` | `16` (`>=1`) | `[1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 8, 8, 24, 24, 24]` | `(210, 24, [], True)` | `6` | `216.915` |
| `Q_8` | `8` | `64` | `8` | `—` | `64 == \|G\|^2` (blocked) | `[1, 1, 1, 1, 2, 4, 4, 8]` | `(11, 4, [], False)` | `4` | `2.636` |

---

# Cycle 2 Track E & Track A Exact Sweep Benchmarks (`@simulator`)

- **Cycle 2 Sweep Wall-Clock Runtime**: `242.611 ms` (`signal.alarm(20)` enforced per stage)
- **Simulator AST Self-Audit**: `PASSED` across `12` modules (`0` violations)

## 5. Track E — Escher Waterfall (`E0`) vs. Pinned-Torsor Contraction (`E1`) & Twisted Mobius (`E2`)

### 5A. Counterexample E0 — Outward-Spiraling Escher Waterfall Family (`FALSIFIED_COUNTEREXAMPLE`)

| Drift `delta` | Worst Cell/Filippov `D^+_f V_tilde` | 1-Lap Torsor Drop | Poincare Multiplier `((1+d)/(1-d))^4` | Full In-Annulus Laps | Escape Lap (`r > 2`) | Sample Radii from `r_0 = 1` | Max Bits | Runtime (`ms`) |
|---|---|---|---|---:|---:|---|---:|---:|
| `1/41` | `-10/41 < 0` | `-4` | `194481/160000 > 1` | `3` | `4` | `1 -> 194481/160000 -> 37822859361/25600000000 -> 7355827511386641/4096000000000000` | `71` | `0.237` |
| `1/21` | `-5/21 < 0` | `-4` | `14641/10000 > 1` | `1` | `2` | `1 -> 14641/10000 -> 214358881/100000000` | `28` | `0.126` |
| `1/16` | `-15/64 < 0` | `-4` | `83521/50625 > 1` | `1` | `2` | `1 -> 83521/50625 -> 6975757441/2562890625` | `33` | `0.116` |
| `1/12` | `-11/48 < 0` | `-4` | `28561/14641 > 1` | `1` | `2` | `1 -> 28561/14641 -> 815730721/214358881` | `30` | `0.108` |
| `1/9` | `-2/9 < 0` | `-4` | `625/256 > 1` | `0` | `1` | `1 -> 625/256` | `10` | `0.084` |
| `1/5` | `-1/5 < 0` | `-4` | `81/16 > 1` | `0` | `1` | `1 -> 81/16` | `7` | `0.074` |

### 5B. Theorem E1 — Orientable Annulus Bouligand + Pinned-Torsor Contraction (`CERTIFIED_EXACT`)

| Restore `delta` | Bouligand (incl. `270`-deg Corners) | Worst `D^+_f V_tilde` | Limit Cycle `r*` | 1-Lap Pinned Contraction Factor | Inner Rim `1` -> 2 Laps | Outer Rim `2` -> 2 Laps | Max Bits | Runtime (`ms`) |
|---|---|---|---|---|---|---|---:|---:|
| `1/27` | `True` | `-13/54 < 0` | `18/13` | **`256/625`** | `1 -> 1994/1625 -> 1340714/1015625` | `2 -> 13298/8125 -> 7555538/5078125` | `29` | `0.297` |
| `1/18` | `True` | `-17/72 < 0` | `24/17` | **`625/2401`** | `1 -> 7607/5831 -> 1139671/823543` | `2 -> 63874/40817 -> 8368322/5764801` | `39` | `0.306` |
| `1/12` | `True` | `-11/48 < 0` | `16/11` | **`81/625`** | `1 -> 1919/1375 -> 1243439/859375` | `2 -> 10486/6875 -> 6289366/4296875` | `32` | `0.312` |
| `1/9` | `True` | `-2/9 < 0` | `3/2` | **`1/16`** | `1 -> 47/32 -> 767/512` | `2 -> 49/32 -> 769/512` | `14` | `0.270` |
| `1/6` | `True` | `-5/24 < 0` | `8/5` | **`1/81`** | `1 -> 43/27 -> 3499/2187` | `2 -> 130/81 -> 10498/6561` | `20` | `0.277` |
| `2/9` | `True` | `-7/36 < 0` | `12/7` | **`1/625`** | `1 -> 1499/875 -> 937499/546875` | `2 -> 7502/4375 -> 4687502/2734375` | `29` | `0.285` |

### 5C. Theorem E2 — Twisted Mobius Quotient `M_N` (`N = 3..12`) Carrying `Z_{-1}` (`CERTIFIED_EXACT`)

| `N` Panels | `(V, E, F)` | `chi` | Single Boundary Cycle | `rank(delta^0)` | `SNF(delta^0)` Torsion | `H^1(M_N; Z_{-1})` | `H^1(M_N; Q_{-1})` | Odd/Even Cocycle `(Q-den, Z-SAT)` | Max Bits | Runtime (`ms`) |
|---:|---|---:|---|---:|---|---|---|---|---:|---:|
| `3` | `(6,12,6)` | `0` | `True` | `6` | `[2]` | `Z/2Z` | `0` | `(2, False) / (1, True)` | `2` | `0.559` |
| `4` | `(8,16,8)` | `0` | `True` | `8` | `[2]` | `Z/2Z` | `0` | `(2, False) / (1, True)` | `2` | `0.844` |
| `5` | `(10,20,10)` | `0` | `True` | `10` | `[2]` | `Z/2Z` | `0` | `(2, False) / (1, True)` | `2` | `1.238` |
| `6` | `(12,24,12)` | `0` | `True` | `12` | `[2]` | `Z/2Z` | `0` | `(2, False) / (1, True)` | `2` | `1.730` |
| `7` | `(14,28,14)` | `0` | `True` | `14` | `[2]` | `Z/2Z` | `0` | `(2, False) / (1, True)` | `2` | `2.284` |
| `8` | `(16,32,16)` | `0` | `True` | `16` | `[2]` | `Z/2Z` | `0` | `(2, False) / (1, True)` | `2` | `2.892` |
| `9` | `(18,36,18)` | `0` | `True` | `18` | `[2]` | `Z/2Z` | `0` | `(2, False) / (1, True)` | `2` | `3.705` |
| `10` | `(20,40,20)` | `0` | `True` | `20` | `[2]` | `Z/2Z` | `0` | `(2, False) / (1, True)` | `2` | `4.706` |
| `11` | `(22,44,22)` | `0` | `True` | `22` | `[2]` | `Z/2Z` | `0` | `(2, False) / (1, True)` | `2` | `5.590` |
| `12` | `(24,48,24)` | `0` | `True` | `24` | `[2]` | `Z/2Z` | `0` | `(2, False) / (1, True)` | `2` | `6.656` |

## 6. Track A — `Vol_d(Delta_a x Delta_b)` (`d = 2..10`) & `MAX_6` `Syl_2(S_6)` `< 0.2s` Engine

### 6A. Kummer Prime-Power vs. Composite Minkowski Product Volume Table (`d = 2..10`)

| `d` (`MAX_{d+1}`) | Prime-Power Status | `gcd_{1<=a<d} binom(d,a)` | `Vol_d mod 2` Additive | `Vol_d mod 3` Additive | Staircase-Certified Splits `(a,b): Vol_d` | Runtime (`ms`) |
|---:|---|---:|---|---|---|---:|
| `2` (`MAX_3`) | `2^1` | **`2`** | `True` | `False` | `(1,1):2` | `0.016` |
| `3` (`MAX_4`) | `3^1` | **`3`** | `False` | `True` | `(1,2):3` | `0.013` |
| `4` (`MAX_5`) | `2^2` | **`2`** | `True` | `False` | `(1,3):4, (2,2):6` | `0.053` |
| `5` (`MAX_6`) | `5^1` | **`5`** | `False` | `False` | `(1,4):5, (2,3):10` | `0.114` |
| `6` (`MAX_7`) | `composite` | **`1`** | `False` | `False` | `(1,5):6, (2,4):15, (3,3):20` | `0.440` |
| `7` (`MAX_8`) | `7^1` | **`7`** | `False` | `False` | `(1,6):7, (2,5):21, (3,4):35` | `0.935` |
| `8` (`MAX_9`) | `2^3` | **`2`** | `True` | `False` | `(1,7):8, (2,6):28, (3,5):56, (4,4):70` | `3.270` |
| `9` (`MAX_10`) | `3^2` | **`3`** | `False` | `True` | `(1,8):9, (2,7):36, (3,6):84, (4,5):126` | `6.751` |
| `10` (`MAX_11`) | `composite` | **`1`** | `False` | `False` | `(1,9):10, (2,8):45, (3,7):120, (4,6):210, (5,5):252` | `22.159` |

### 6B. `6 * MAX_6` `D_6` Hexagon Dictionary & `Syl_2(S_6)` (`45`-Orbit) `Z[1/2]` Engine (`< 0.2s` Gate)

- **`6 * MAX_6` Pure-`Z` `D_6` Hexagon Formula (`CERTIFIED_EXACT`)**: `6` Layer-1 edge gates + `99` Layer-2 `max(m_ab+m_cd, m_ef+m_gh)` gates (weights `[-2, -1, 1]`) over the `15` pairwise maxima (`6` edges, `6` short diags, `3` long diags); verified across `2160` chamber points (`3 x 720` profiles) + `3` internal off-braid 2nd-difference zero probes in **`86.275 ms`**.
- **`Syl_2(S_6) = D_4 x C_2` (`|G| = 16 = 2^4`, `45` Free Braid-Chamber Orbits)**: Compresses `1440 x 105` chamber-gate system to `92 x 11` (max entry `11` bits). Total orbit-compression + `padic_local_global.solve_z_half` runtime: **`12.666 ms` (`< 200 ms` budget PASS; solver-only `8.486 ms`)**:
  * `6 * MAX_6` target: `CERTIFIED_EXACT` (`c_den = 1`, max coeff `2` bits).
  * `1 * MAX_6` over fixed `105`-gate hexagon dictionary: `UNSAT_MOD3_PRESCREEN` (exact `p = 3` dual obstruction witness; unconstrained `ReLU_{6,2}(Z[1/2])` logged as **`OPEN_BUDGET_EXCEEDED`** per `SPEC.md` §0.4).

---

# Cycle 3 Executive Summary & Wave II (v2.0) Scaling Projections (`@simulator`)

- **Clean-Room Path Portability Audit**: `PASSED` (`12` files, `0` hardcoded paths; 100% `Path(__file__).resolve()` relative)
- **End-to-End Cycle 1 + Cycle 2 Exact Sweep Runtime**: `2145.687 ms` (`< 2.5 s`, `< 8%` of `30 s` master clean-room budget)

## 7A. Wave I (v1.0) Master Sweep Executive Summary (Stages 1–6)

| Stage | Family / Track Scope | Instances Swept | Certified Exact Law / Edge Case | Peak Bits | Runtime (`ms`) |
|---|---|---:|---|---:|---:|
| `Stage 1 (B1/Trap 4)` | 2D `A_1` + 3D Reeve Tetrahedra `T_r` (`r=1..12`) | `13` | Primal `[1,1,r]`, Polar `[1,r,r]`, Ridges `[1,r]`, `Weil/Cart ~ Z/rZ` | `4` | `3.461` |
| `Stage 2 (B2)` | 4-Ray `v_4^(k)` (`k=1..10`) & 5-Ray `Sigma_5^(k)` (`k=1..3`) | `13` | 4-ray Sim. CG `= 1` vs Seq. `2..3`; 5-ray Sim. CG `= 2k+1` (`3, 5, 7`) | `8` | `1326.824` |
| `Stage 3 (C1/C2/Trap 6)` | Spiderwebs (`m=1..12`), Desargues Prisms & Annuli (`b=2,3`) | `23` | `ev_V = [1,m,m,m]`, `Z^{3(b-1)}` monodromy (`3, 6`), `100%` Bockstein match | `8` | `96.513` |
| `Stage 4 (D1/D2/Trap 5)` | 10 Finite Groups (`C_3,V_4,C_4,C_5,S_3,D_4,D_5,A_4,S_4,Q_8`) | `10` | `C_n: 2n-2/2n-1`, `W=m^2`, `Q_8` `m=8` block, 3-regime coset trichotomy (`S_4` Bezout `[1]^24`) | `6` | `254.089` |
| `Stage 5 (E0/E1/E2)` | Escher `E0` (`6` params), Pinned `E1` (`6` params), Mobius `M_N` (`N=3..12`) | `22` | `E0` `((1+d)/(1-d))^4 > 1` (`FALSIFIED`), `E1` `((1-3d)/(1+3d))^4 < 1`, `M_N` `Z/2Z` | `71` | `33.030` |
| `Stage 6 (A1/A2)` | `Vol_d(Delta_a x Delta_b)` (`d=2..10`), `6*MAX_6` & `Syl_2(S_6)` (`45` orbits) | `11` | Kummer prime-power `gcd`, `Vol_5=10==1 mod 3`, `Syl_2` `<15ms` (`OPEN_BUDGET_EXCEEDED` on `Z[1/2]`) | `11` | `132.893` |

## 7B. Wave II (v2.0) Exact Algorithmic & Bit-Length Scaling Projections

| Wave II Target | Track | Symmetry / Peeling Reduction | Projected Matrix / Problem Size | Peak Bits | Est. Runtime (`ms`) | Entry Point |
|---|---|---|---|---:|---:|---|
| **MAX_6 Z[1/2] Off-Braid Dictionary Sprint** | `A` | Syl_2(S_6) (|G|=16, 45 chamber orbits vs 720) | `360 x 500..2500 (multi-profile + off-braid 2nd-diff rows)` | `16` | `25..450` | `architect.core.padic_local_global.solve_z_half` |
| **MAX_7 2-adic & 3-adic Local-Global Frontier** | `A` | Syl_2(S_7): 315 orbits (|G|=16); Syl_3(S_7): 560 orbits (|G|=9) | `945 x 1200 (Syl_2) / 1680 x 1200 (Syl_3)` | `20` | `120..1800` | `architect.core.padic_local_global.solve_s_integral` |
| **3D Reeve T_r (r=13..100) & 3D/6-Ray Chvatal-Gomory Cones** | `B` | DHSW +-1 unit-pivot peeling + SNF Hilbert-parallelepiped vertex cutoff | `r <= 100 (SNF); dim B = 4, CG rank <= 15` | `12` | `10..900` | `simulator.sim_exact_la.cg_round_3d_exact` |
| **Multi-Hole 2D/3D Maxwell-Cremona Airy & RP^2 / Klein Twisted Sheaves** | `C & E` | Saturated Z_1 via V_1 + modulo-p^k Precision-Bockstein | `b = 4..10 holes (Z^{3(b-1)} = Z^9..Z^27 monodromy); N <= 50 panels` | `8` | `15..250` | `simulator.sweep_airy_spiderwebs.build_airy_operators` |
| **Non-Soluble & Quasisimple Group Circuits (A_5, PSL(2,7), SL(2,3))** | `D` | A_5: W=25 << 3600 (144x); PSL(2,7): W=49 << 28224 (576x); SL(2,3): Z={+-I} obstruction | `\|G\|^2 up to 28224, outcome irrep/coset SNF \|G\| <= 168` | `14` | `30..600` | `simulator.sweep_finite_groups.analyze_finite_group` |

