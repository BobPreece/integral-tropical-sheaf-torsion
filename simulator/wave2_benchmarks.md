# Wave II (v2.0) Exact Parameter Sweep Benchmarks (`@simulator`)

- **Execution Mode**: `python3 -I` (100% Python 3.9+ stdlib, zero external imports, zero `float`, zero `Fraction`, zero `ast.Div`)
- **Total Wave II Sweep Runtime**: `3797.747 ms` (`signal.alarm(20)` enforced per stage)
- **Simulator AST & Path-Portability Audit**: `PASSED` across `12` files (`0` violations)

## 1. Join-Volume Arithmetic Dichotomy Sweep (`d = 3..7`, Sprint A2a)

> **Exact Law Verified Across All `65` Canonical, Sheared, Sublattice & Multi-Generator Zonotope Joins**:
> For any two lattice zonotopes `Z_1, Z_2 subset Z^d` of dimensions `(r_1, r_2)` with `r_1 + r_2 = d - 1`,
> `Vol_d(conv(Z_1 union Z_2)) = r_1! * r_2! * sum_{|I|=r_1, |J|=r_2} |det[U_I, V_J, p_2 - p_1]|`,
> achieving exact family `gcd == r_1! * r_2!`:
> - **`d = 5` (`MAX_6`)**: `(4,0) -> 24`, `(3,1) -> 6` (both `0 mod 3`), whereas **`(2,2) -> 4 == 1 (mod 3)`** (escapes prime `3`!).
> - **`d = 6` (`MAX_7`)**: `(5,0) -> 120`, `(4,1) -> 24`, `(3,2) -> 12` (`gcd = 12 == 0 mod 6` across ALL convex 2-layer joins!).

| Ambient `d` (`MAX_{d+1}`) | Split `(r_1, r_2)` | `r_1! * r_2!` | Observed Family `gcd` | `mod 2` | `mod 3` | `mod 6` | Escapes Prime `3` | All-Splits `gcd(d)` | Runtime (`ms`) |
|---:|---|---:|---:|---:|---:|---:|---|---:|---:|
| `3` (`MAX_4`) | `(2,0)` | `2` | **`2`** | `0` | `2` | `2` | **`YES (2 mod 3)`** | **`1`** | `1.138` |
| `3` (`MAX_4`) | `(1,1)` | `1` | **`1`** | `1` | `1` | `1` | **`YES (1 mod 3)`** | `—` | `—` |
| `4` (`MAX_5`) | `(3,0)` | `6` | **`6`** | `0` | `0` | `0` | `No (0 mod 3)` | **`2`** | `5.776` |
| `4` (`MAX_5`) | `(2,1)` | `2` | **`2`** | `0` | `2` | `2` | **`YES (2 mod 3)`** | `—` | `—` |
| `5` (`MAX_6`) | `(4,0)` | `24` | **`24`** | `0` | `0` | `0` | `No (0 mod 3)` | **`2`** | `37.544` |
| `5` (`MAX_6`) | `(3,1)` | `6` | **`6`** | `0` | `0` | `0` | `No (0 mod 3)` | `—` | `—` |
| `5` (`MAX_6`) | `(2,2)` | `4` | **`4`** | `0` | `1` | `4` | **`YES (1 mod 3)`** | `—` | `—` |
| `6` (`MAX_7`) | `(5,0)` | `120` | **`120`** | `0` | `0` | `0` | `No (0 mod 3)` | **`12`** | `292.953` |
| `6` (`MAX_7`) | `(4,1)` | `24` | **`24`** | `0` | `0` | `0` | `No (0 mod 3)` | `—` | `—` |
| `6` (`MAX_7`) | `(3,2)` | `12` | **`12`** | `0` | `0` | `0` | `No (0 mod 3)` | `—` | `—` |
| `7` (`MAX_8`) | `(6,0)` | `720` | **`720`** | `0` | `0` | `0` | `No (0 mod 3)` | **`12`** | `2993.917` |
| `7` (`MAX_8`) | `(5,1)` | `120` | **`120`** | `0` | `0` | `0` | `No (0 mod 3)` | `—` | `—` |
| `7` (`MAX_8`) | `(4,2)` | `48` | **`48`** | `0` | `0` | `0` | `No (0 mod 3)` | `—` | `—` |
| `7` (`MAX_8`) | `(3,3)` | `36` | **`36`** | `0` | `0` | `0` | `No (0 mod 3)` | `—` | `—` |

## 2. Cohomological Extension Compression Breaking the Faithful-Permutation Wall (Sprint D4a)

> **Key Wave II Breakthrough (`W = 2|G| + 1` Pure-`Z` Superposed 2-Cocycle Ramp Theorem)**:
> - On 2-primary generalized quaternion groups `Q_8` (`|G|=8`) and `Q_16` (`|G|=16`), the unique involution `-1` lies in every nontrivial subgroup, forcing `m(G) = |G|` (`m^2 = 64, 256`); on `Dic_3` (`|G|=12`), every transitive action < 12 is unfaithful while intransitive `Dic_3/<x> + Dic_3/<a^2>` gives `m(Dic_3) = 3 + 4 = 7` (`m^2 = 49` argmax).
> - **Tier I (`H^2(Q; Z_2)` Block 2-Cocycle)**: `3` pure-`Z` neurons per `(a_bar, b_bar) in Q x Q` achieve `W = 3|Q|^2` (`48 < 64` on `Q_8`, `108 < 144` on `Dic_3`).
> - **Tier II (`V_4`-Quotient Merge & Howell-Lafon 8-Product Quaternion)**: Compresses `Q_8` to `W = 38` over `Z` and **`W = 26` over `Q` (`Z[1/2]`, `c_den = 8`)**.
> - **Tier III (Superposed 2-Cocycle Second-Difference Ramp over Pure `Z`)**: Exploiting `1 -> C_m -> G -> C_2 -> 1` (`x^2 = a^s`, `x a x^{-1} = a^{-1}`) by placing opposite-coset cross-blocks simultaneously into strictly negative (`ReLU = 0`) and strictly affine (`2nd-diff = 0`) regimes achieves **`W = 4m + 1 = 2|G| + 1` (biased) / `W = 4m + 2` (zero-bias) OVER PURE `Z` (`c_den = 1`)** — compressing **`Q_8` to `W = 17` (`3.76x`)**, **`Dic_3` to `W = 25` (`5.76x`)**, and **`Q_16` to `W = 33` (`7.76x`)**!

| Group `G` | `\|G\|` | `\|G\|^2` | Min Faithful `m` (`m^2`) | Extension Structure | Tier I `H^2(Q;Z_2)` `W_Z` | Tier II `W_Z / W_Q` | **Tier III Superposed Pure-`Z` (`b / u`)** | Compression vs `\|G\|^2` | Formalist Certified |
|---|---:|---:|---|---|---|---|---|---|---|
| `S_3` | `6` | `36` | `3` (`9`) | `1 -> C_3 -> S_3 -> C_2 -> 1 (split, s=0)` | — | — | **`13 / 14`** | `13/36` | `True` |
| `D_4` | `8` | `64` | `4` (`16`) | `1 -> C_4 -> D_4 -> C_2 -> 1 (split, s=0)` | — | — | **`17 / 18`** | `17/64` | `True` |
| `Q_8` | `8` | `64` | `8` (`64`) | `1 -> C_4 -> Q_8 -> C_2 -> 1 (non-split, s=2)` | `48` | `38 (Z) / 26 (Q)` | **`17 / 18`** | `17/64` | `True` |
| `Dic_3` | `12` | `144` | `7` (`49`) | `1 -> C_6 -> Dic_3 -> C_2 -> 1 (non-split, s=3)` | `108` | — | **`25 / 26`** | `25/144` | `True` |
| `Q_16` | `16` | `256` | `16` (`256`) | `1 -> C_8 -> Q_16 -> C_2 -> 1 (non-split, s=4)` | `192` | — | **`33 / 34`** | `33/256` | `True` |

## 3. Exact `{0,1}`-Indicator Lower Bounds & Small-Group Widths (`C_3, V_4, C_4, C_5`, Sprint D4b)

> **Universal Strict Sharpening & `V_4` Torsion-Killing Surgery**:
> 1. **Rank Bound**: `I_mult^T I_mult = |G| I_{|G|}` (`det = |G|^{|G|}`) forces `W >= |G| - 1` (biased) and `W >= |G|` (zero-bias).
> 2. **1-Neuron Outcome Impossibility Lemma**: Zero non-constant single ReLU neurons `ReLU(u(g)+v(h))` depend purely on `g*h` (`0` found across `2,904` columns on `C_3` and `2,670+` on `V_4, C_4`), strictly sharpening the universal bound over `R` to **`W >= |G|` (biased) and `W >= |G| + 1` (zero-bias)** for every `|G| >= 2`!
> 3. **Quotient Ray-Bucket Exclusion (`W = |G|`)**: By Rank-Nullity on `pi_perp: R^{G^2} -> R^{G^2}/V_out`, `W = |G|` forces all `|G|` neurons into a single 1D ray bucket modulo `V_out` — certified `Q-UNSAT` across all buckets on `C_3, V_4, C_4` (`W >= 4` on `C_3`, `W >= 5` on `V_4, C_4`).
> 4. **`V_4` `Z`-vs-`Q` Dictionary Torsion & Surgical Collapse**: Symmetric 6-neuron Walsh-Hadamard XOR features have `SNF = [1^6, 2]` (`Q-SAT` with `den = 2`, `Z-UNSAT`), while replacing 1 redundant XOR hinge with `ReLU([0,-1,-1,-1]_g + [1,2,2,2]_h)` collapses SNF to `[1]^7`, certifying **`W_Z = W_Q = 6` (`7` zero-bias) on `V_4`**!

| Group | `\|G\|` | `det(I^T I)` | Rank Bound (`b/u`) | 1-Neuron Bound (`b/u`) | Ray-Bucket Pool Bound (`b`) | Best Certified Pure-`Z` (`b/u`) | Fixed-Dict `Z` vs `Q` Phenomenon |
|---|---:|---:|---|---|---|---|---|
| `C_3` | `3` | `27` | `2 / 3` | `3 / 4` | `>= 4` | **`4 / 5`** | Exact match `W_Z = 4` to pool bound (`0` single/pair `V_out` features) |
| `V_4` | `4` | `256` | `3 / 4` | `4 / 5` | `>= 5` | **`6 / 7`** | Sym. Walsh-Hadamard `W=6` is `Q-SAT (den=2)` / `Z-UNSAT ([2])`; surgical `W=6` is `Z-SAT`! |
| `C_4` | `4` | `256` | `3 / 4` | `4 / 5` | `>= 5` | **`6 / 7`** | `2n-2 = 6` unimodular ramp second-difference pure-`Z` circuit |
| `C_5` | `5` | `3125` | `4 / 5` | `5 / 6` | `—` | **`8 / 9`** | `2n-2 = 8 << 25` pure-`Z` ramp circuit (bypasses `Phi_5` equivariance barrier) |

