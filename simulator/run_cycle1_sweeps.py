from __future__ import annotations

import ast
import json
import os
from pathlib import Path
import signal
import sys
import time
from typing import Any, Callable, Dict, List

# Ensure top-level workspace root is importable under `python3 -I` via Path(__file__).resolve()
_SIM_DIR = str(Path(__file__).resolve().parent)
_ROOT_DIR = str(Path(__file__).resolve().parent.parent)
if _ROOT_DIR not in sys.path:
    sys.path.insert(0, _ROOT_DIR)

from simulator.sweep_airy_spiderwebs import sweep_airy_stage
from simulator.sweep_finite_groups import sweep_finite_groups_stage
from simulator.sweep_reeve_fans import sweep_fans_cg_stage, sweep_reeve_stage


ALLOWED_STDLIB_MODULES = {
    "__future__",
    "math",
    "sys",
    "os",
    "time",
    "signal",
    "json",
    "ast",
    "pathlib",
    "dataclasses",
    "typing",
    "itertools",
    "functools",
    "collections",
    "unittest",
    "subprocess",
    "xml",
    "html",
    "re",
    "simulator",
    "architect",
}


class StageTimeoutError(RuntimeError):
    pass


def _alarm_handler(signum: int, frame: Any) -> None:
    raise StageTimeoutError(f"Sweep stage exceeded 20-second hard wall-clock timeout (signal {signum})")


def run_stage_with_alarm_and_checkpoint(
    stage_name: str,
    fn: Callable[[], Dict[str, Any]],
    checkpoint_dir: str,
) -> Dict[str, Any]:
    prev_handler = signal.signal(signal.SIGALRM, _alarm_handler)
    prev_remaining = signal.alarm(20)
    try:
        result = fn()
    finally:
        signal.alarm(prev_remaining if prev_remaining > 0 else 0)
        signal.signal(signal.SIGALRM, prev_handler)

    os.makedirs(checkpoint_dir, exist_ok=True)
    ckpt_path = os.path.join(checkpoint_dir, f"cycle1_sim_{stage_name}.json")
    with open(ckpt_path, "w", encoding="utf-8") as fh:
        json.dump(result, fh, indent=2, sort_keys=True)
    return result


def self_audit_simulator_ast() -> Dict[str, Any]:
    """
    Verify simulator/*.py strictly obeys SPEC.md §0 Constitutional Guardrails:
      - Zero non-stdlib imports
      - Zero float literals, float(...) calls, or float annotations
      - Zero fractions.Fraction usage
      - Zero ast.Div ('/') true-division operators
      - Zero isinstance(...) calls
    """
    violations: List[str] = []
    scanned_files: List[str] = []
    for fname in sorted(os.listdir(_SIM_DIR)):
        if not fname.endswith(".py"):
            continue
        fpath = os.path.join(_SIM_DIR, fname)
        scanned_files.append(fname)
        with open(fpath, "r", encoding="utf-8") as fh:
            src = fh.read()
        tree = ast.parse(src, filename=fname)
        for node in ast.walk(tree):
            if type(node) is ast.Import:
                for alias in node.names:
                    top = alias.name.split(".")[0]
                    if top not in ALLOWED_STDLIB_MODULES:
                        violations.append(f"{fname}:{node.lineno}: forbidden import '{alias.name}'")
            elif type(node) is ast.ImportFrom:
                if node.module is not None:
                    top = node.module.split(".")[0]
                    if top not in ALLOWED_STDLIB_MODULES:
                        violations.append(f"{fname}:{node.lineno}: forbidden from-import '{node.module}'")
            elif type(node) is ast.Constant:
                if type(node.value).__name__ == "float":
                    violations.append(f"{fname}:{node.lineno}: float literal {node.value!r}")
            elif type(node) is ast.Div:
                violations.append(f"{fname}:{node.lineno}: true division '/' (ast.Div) forbidden")
            elif type(node) is ast.Name:
                if node.id in ("float", "Fraction", "isinstance"):
                    violations.append(f"{fname}:{node.lineno}: forbidden identifier '{node.id}'")
    assert not violations, f"Simulator AST self-audit failed: {violations}"
    return {
        "passed": True,
        "scanned_files": scanned_files,
        "violations": violations,
    }


def _fmt_ms(us: int) -> str:
    return f"{us // 1000}.{us % 1000:03d}"


def write_cycle_benchmarks_markdown(
    out_path: str,
    payload: Dict[str, Any],
) -> None:
    s1 = payload["stages"]["stage1_reeve"]
    s2 = payload["stages"]["stage2_fans_cg"]
    s3 = payload["stages"]["stage3_airy"]
    s4 = payload["stages"]["stage4_groups"]

    lines: List[str] = []
    lines.append("# Cycle 1 Exact Parameterized Family & Finite-Group Sweep Benchmarks (`@simulator`)")
    lines.append("")
    lines.append("- **Execution Mode**: `/usr/bin/python3 -I` (100% Python 3.9+ stdlib, zero external imports, zero `float`, zero `Fraction`, zero `/`)")
    lines.append(f"- **Total Cycle 1 Sweep Wall-Clock Runtime**: `{_fmt_ms(payload['total_runtime_us'])} ms` (`signal.alarm(20)` enforced per stage)")
    lines.append(f"- **Simulator AST Self-Audit**: `PASSED` across `{len(payload['ast_self_audit']['scanned_files'])}` modules (`0` violations)")
    lines.append("")

    # Table 1: Reeve Tetrahedra
    lines.append("## 1. 3D Reeve Tetrahedra `T_r` (`r = 2..12`, plus `r = 1` & `A_1` Controls) — Trap 4 & Track B1")
    lines.append("")
    a1 = s1["a1_2d_control"]
    lines.append(
        f"- **2D `A_1` Control `(1,0), (-1,2), (0,-1)`**: `dim B_{{A_1}} = {a1['dim_balanced_space']}` "
        f"(non-trivial DC splits: `{a1['nontrivial_dc_splits_possible']}`), `Cone_12 SNF = {a1['cone_12_snf']}`, "
        f"`Weil/Cart = Z/2Z`, witness `h = {a1['weil_witness_h']}` primitive wall jumps `{a1['primitive_wall_jumps_q']}` (`{_fmt_ms(a1['runtime_us'])} ms`)."
    )
    lines.append("")
    lines.append("| `r` | `Vol_3(T_r)` | `|T_r cap Z^3|` | Primal Edge SNF | Polar Facet SNF (`z, -ry+z, rx-z`) | Ridge Colon SNFs (x3) | `Weil / Cart` | Reeve Wall Jumps | Peak Bits | Runtime (`ms`) |")
    lines.append("|---:|---:|---:|---|---|---|---|---|---:|---:|")
    for row in [s1["unimodular_r1_control"]] + s1["reeve_sweep_r_2_to_12"]:
        r = row["r"]
        jumps = ", ".join(row["weil_generator_reeve_wall_jumps"])
        lines.append(
            f"| `{r}` | `{row['normalized_vol3']}` | `{row['lattice_point_count']}` | "
            f"`{row['primal_edge_snf']}` | `{row['polar_facet_snf']}` | "
            f"`{row['ridge_colon_snfs'][0]}` | `{row['complete_fan_weil_mod_cart']}` | "
            f"`({jumps})` | `{row['bit_metrics']['peak_bits']}` | `{_fmt_ms(row['runtime_us'])}` |"
        )
    lines.append("")

    # Table 2: 4-Ray and 5-Ray 2D Fans & Chvatal-Gomory Rank
    lines.append("## 2. 4-Ray 2D Fans `v_4^(k) = (-1, -(2k+1))` (`k = 1..10`) & 5-Ray Simultaneous CG Sweep — Track B2")
    lines.append("")
    lines.append("> **Key Cycle 1 Discovery (Sequential Axis Cuts vs. Simultaneous Elementary CG Rank)**:")
    lines.append("> 1. On ALL 4-ray 2D fans `Sigma^(k)` (`k = 1..10`), Jensen's inequality on `max(0, .)` makes `w_2 >= max(0, w_2(f))` and `w_3 >= max(0, w_3(f))` redundant over `R`, collapsing `D_tilde_{Sigma^(k)}(w(f))` to a **2-facet cone in `R^2`**. Consequently, **Simultaneous Elementary Chvatal-Gomory Rank = `1`** for every `k = 1..10` (`t >= 1` and `u - (k-1)t >= 2` are both Round-1 Hilbert-parallelepiped cuts!).")
    lines.append("> 2. Under **sequential axis-aligned 1-cut Gomory rounds** (`t >= 1`, then `u >= k+1`): `k = 1` terminates in **`2` rounds** (`(6/5, 2/5) -> (3/2, 1) -> {(2,1),(2,2),(3,1)}`), whereas for **`k >= 2`** `u = k+1` meets `2u - (2k-1)t = 2` at the **still-fractional vertex `(k+1, 2k/(2k-1))`**, requiring a **`3`rd** cut (`u - (k-1)t >= 2`)!")
    lines.append("> 3. Moving to **`m = 5` primitive rays** (`Sigma_5^(k)`, `dim B = 3`) breaks the 2-facet planar cone ceiling: pure Cartier `w(f) = (0, 1, 0, 1, -(2k+1))` achieves **Simultaneous Elementary CG Rank = `2k + 1`** (`3` at `k=1`, `5` at `k=2`, `7` at `k=3`; `9` at `k=4` on extended sweep)!")
    lines.append("")
    lines.append("### 2A. 4-Ray 2D Fans `Sigma^(k)` (`k = 1..10`, Determinant `2k + 3`)")
    lines.append("")
    lines.append("| `k` | Det `2k+3` | LP Vertex `(u*, t*)` | After `t >= 1` | After `u >= k+1` | Seq. Axis Rounds | Sim. Elem. CG Rank | Klein Sail `(u, t)` Vertices | Max Bits | Runtime (`ms`) |")
    lines.append("|---:|---:|---|---|---|---:|---:|---|---:|---:|")
    for row in s2["four_ray_sweep_k_1_to_10"]:
        ks_verts = ", ".join(f"({v['ut'][0]},{v['ut'][1]})" for v in row["klein_sail_integer_vertices"])
        r1_str = ", ".join(f"({v[0]},{v[1]})" for v in row["seq_round1_verts_after_t_ge_1"])
        r2_str = ", ".join(f"({v[0]},{v[1]})" for v in row["seq_round2_verts_after_u_ge_kp1"])
        lines.append(
            f"| `{row['k']}` | `{row['cone_determinant']}` | `({row['lp_vertex_ut'][0]}, {row['lp_vertex_ut'][1]})` | "
            f"`{r1_str}` | `{r2_str}` | `{row['sequential_axis_gomory_rounds']}` | "
            f"`{row['simultaneous_elementary_cg_rank']}` | `{ks_verts}` | `{row['max_bits']}` | `{_fmt_ms(row['runtime_us'])}` |"
        )
    lines.append("")
    lines.append("### 2B. 5-Ray 2D Fans `Sigma_5^(k)` (`k = 1..3`) — Unbounded Simultaneous Elementary CG Rank `2k + 1`")
    lines.append("")
    lines.append("| `k` | Rays `(1,0), (2k+1,1), (-2k-1,1), (-1,-2), (0,-1)` | Cartier `w(f)` | Initial Max Denom | Sim. Elementary CG Rank | Final Integer Hull Vertices `(w1,w2,w3)` | Runtime (`ms`) |")
    lines.append("|---:|---|---|---:|---:|---|---:|")
    for row in s2["five_ray_higher_cg_sweep"]:
        final_v = ", ".join(f"({v[0]},{v[1]},{v[2]})" for v in row["rounds_trace"][-1]["vertices"])
        lines.append(
            f"| `{row['k']}` | `m = {row['odd_slope_param']}` | `{row['cartier_wf']}` | "
            f"`{row['initial_max_denominator']}` | **`{row['simultaneous_elementary_cg_rank']}`** | "
            f"`{final_v}` | `{_fmt_ms(row['runtime_us'])}` |"
        )
    lines.append("")

    # Table 3: Airy Cosheaves, Spiderwebs, Desargues, Annuli
    lines.append("## 3. 2D Integral Maxwell-Cremona Airy Cosheaves, Spiderwebs & Punctured Annuli — Trap 6 & Track C")
    lines.append("")
    lines.append("| Complex | `(V, E, F)` | `b` | `F^geom` Edge Torsion | Unclamped `ev_V` SNF on `H_2^int(A_Z)` | `H_1^int(A_Z)` Torsion | `H_1^all(A_Z)` Torsion | `Aff` Monodromy Rank `3(b-1)` | Bockstein `Z/p^kZ` Match | Max Bits | Runtime (`ms`) |")
    lines.append("|---|---|---:|---|---|---|---|---:|---|---:|---:|")
    all_airy_rows = (
        s3["scaled_spiderwebs"]
        + s3["primitive_twisted_spiderwebs"]
        + s3["desargues_prisms"]
        + s3["punctured_annuli"]
    )
    for row in all_airy_rows:
        geom_t = str(row["geom_vs_prim_edge_torsion"]) if row["geom_vs_prim_edge_torsion"] else "[]"
        lines.append(
            f"| `{row['name']}` | `({row['num_vertices']},{row['num_edges']},{row['num_faces']})` | `{row['num_boundary_components']}` | "
            f"`{geom_t}` | `{row['nodal_eval_snf']}` | `{row['h1_int_torsion']}` | `{row['h1_all_torsion']}` | "
            f"`{row['aff_monodromy_free_rank_3_bm1']}` | `{row['bockstein_checks_passed']}` | "
            f"`{row['max_bits']}` | `{_fmt_ms(row['runtime_us'])}` |"
        )
    lines.append("")

    # Table 4: Finite Groups
    lines.append("## 4. Finite-Group Multiplication, Permutation Compression & SNF Readout Torsion — Trap 5 & Track D")
    lines.append("")
    lines.append("> **Key Cycle 1 Group Edge Cases & Exact 3-Regime Coset Trichotomy**:")
    lines.append("> 1. **Faithful Permutation Compression (`m^2 < |G|^2`) vs. Core-Free Obstruction (`m^2 == |G|^2`)**: `S_3 (9 < 36)`, `D_4 (16 < 64)`, `D_5 (25 < 100)`, `A_4 (16 < 144)`, and `S_4 (16 < 576)` compress strictly via zero-bias pure-`Z` permutation circuits (`arXiv:2410.07476v3`), whereas `C_3, V_4, C_4, C_5` and non-abelian **`Q_8`** have `m(G) = |G|` (`m^2 == |G|^2`; for `Q_8`, `-1` lies in every nontrivial subgroup so no proper core-free subgroup exists!).")
    lines.append("> 2. **Exact 3-Regime Proper-Subgroup Coset (`|H| >= 2`) Readout Trichotomy**:")
    lines.append(">    - **Regime I (`Q`-Rank Deficient, `rank_Q < |G|`)**: `C_3 (1<3)`, `C_4 (2<4)`, `C_5 (1<5)`, and **`Q_8 (4<8)`** fail to span `e_0` even over `Q` (unique minimal subgroup blocks separation; adding the 4D integral quaternion representation on `Q_8` restores full `Q`-rank `8` with SNF `[1, 1, 1, 1, 2, 4, 4, 8]`).")
    lines.append(">    - **Regime II (`Q`-Complete + Genuine `Z`-Torsion)**: `V_4` (`[2]`), `S_3` (`[3]`), `D_4` (`[2]`), `D_5` (`[5]`), and `A_4` (`[2, 2]`) span all outcomes over `Q` (`e_0` `Q`-SAT) but suffer exact subgroup-Mobius SNF torsion over `Z` (`e_0` `Z`-UNSAT)!")
    lines.append(">    - **Regime III (`Z`-Unimodular Coset Synthesis!)**: **`S_4`** (`210` proper-subgroup cosets) achieves `SNF = [1]^24` (**zero `Z`-torsion**, `e_0` `Z`-SAT!) because `S_3 <= S_4` yields `3*e_0` and `D_4 <= S_4` yields `2*e_0`, so Bezout `1*(3*e_0) - 1*(2*e_0) = e_0` over `Z`!")
    lines.append("")
    lines.append("| Group | `|G|` | `|G|^2` | Min Faithful `m` | `D1(b)` `C_n` Width (`b/u`) | `D1(c)` Perm Width `m^2` (Margin) | Irrep Feature SNF (`Z^{|G|^2 x |G|}`) | Proper Coset `(Cols, Q-Rank, Z-Torsion, e0_Z)` | Max Bits | Runtime (`ms`) |")
    lines.append("|---|---:|---:|---:|---|---|---|---|---:|---:|")
    for row in s4["groups"]:
        cyc = row["cyclic_1layer_circuit"]
        cyc_str = f"`{cyc['biased_width_2nm2']} / {cyc['unbiased_width_2nm1']}`" if cyc else "`—`"
        perm = row["permutation_biequivariant_circuit"]
        if perm["applicable_strict_compression"]:
            perm_str = f"`{perm['width_m2']}` (`>={perm['min_strict_argmax_margin']}`)"
        else:
            perm_str = f"`{perm['width_m2']} == |G|^2` (blocked)"
        cos_str = (
            f"`({row['proper_coset_num_cols']}, {row['proper_coset_q_rank']}, "
            f"{row['proper_coset_torsion']}, {row['proper_coset_e0_z_sat']})`"
        )
        lines.append(
            f"| `{row['name']}` | `{row['order']}` | `{row['g_squared']}` | `{row['minimal_faithful_perm_degree']}` | "
            f"{cyc_str} | {perm_str} | `{row['irrep_feature_snf']}` | "
            f"{cos_str} | `{row['max_bits']}` | `{_fmt_ms(row['runtime_us'])}` |"
        )
    lines.append("")

    with open(out_path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")


def run_all_cycle1_sweeps() -> Dict[str, Any]:
    t0 = time.perf_counter_ns()
    artifacts_dir = os.path.join(_ROOT_DIR, "artifacts")
    ckpt_dir = os.path.join(artifacts_dir, "checkpoints")
    os.makedirs(ckpt_dir, exist_ok=True)

    ast_audit = self_audit_simulator_ast()

    s1 = run_stage_with_alarm_and_checkpoint("stage1_reeve", sweep_reeve_stage, ckpt_dir)
    s2 = run_stage_with_alarm_and_checkpoint("stage2_fans_cg", sweep_fans_cg_stage, ckpt_dir)
    s3 = run_stage_with_alarm_and_checkpoint("stage3_airy", sweep_airy_stage, ckpt_dir)
    s4 = run_stage_with_alarm_and_checkpoint("stage4_groups", sweep_finite_groups_stage, ckpt_dir)

    total_us = (time.perf_counter_ns() - t0) // 1000
    payload: Dict[str, Any] = {
        "cycle": 1,
        "agent": "simulator",
        "ast_self_audit": ast_audit,
        "total_runtime_us": total_us,
        "stages": {
            "stage1_reeve": s1,
            "stage2_fans_cg": s2,
            "stage3_airy": s3,
            "stage4_groups": s4,
        },
    }

    main_json_path = os.path.join(artifacts_dir, "cycle1_simulator_sweeps.json")
    with open(main_json_path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=2, sort_keys=True)

    md_path = os.path.join(_SIM_DIR, "cycle_benchmarks.md")
    write_cycle_benchmarks_markdown(md_path, payload)
    return payload


if __name__ == "__main__":
    summary = run_all_cycle1_sweeps()
    print(
        f"Cycle 1 simulator sweeps PASSED in {summary['total_runtime_us'] // 1000}."
        f"{summary['total_runtime_us'] % 1000:03d} ms | AST audit={summary['ast_self_audit']['passed']}"
    )
