from __future__ import annotations

"""Scope-aware AST contraband & constitutional firewall scanner (SPEC.md §0–§1 & SPEC_WAVE2.md §0.2).

Enforces across the workspace:
1. 100% pure Python 3.9+ stdlib imports only (zero external dependencies; bans ctypes, cmath, unittest.mock).
2. Strict `from __future__ import annotations` in all non-empty Python modules.
3. Workspace-wide `float`/`complex` ban in `architect/`, `formalist/`, `inquisitor/`, `verify_all.py`,
   `standalone_integral_sheaf_torsion.py`, and non-atlas `simulator/` modules (literals, calls, annotations,
   float-returning `math.*` & `time.*` APIs, integer-literal `/` true division, non-Path `/` inside `architect/core/`,
   and float tokens in `artifacts/*.json`), while auditing `simulator/svg_atlas.py` isolation per `SPEC_WAVE2.md` §0.2.
4. Scope-aware `Fraction` firewall: zero `fractions`/`Fraction` inside `architect/core/`.
5. Anti-cheat & guardrail checks: bans `isinstance` test-bypass cheats, mock/stub bodies, caller-sniffing
   (`_getframe`/`inspect.stack`), `eval`/`exec`, SVG leakage into algebraic/proof modules, and stray SVGs outside `plots/`.
"""

import ast
import json
import os
import signal
from pathlib import Path
import sys
import sysconfig
import time
from typing import Any

WORKSPACE_ROOT = str(Path(__file__).resolve().parent.parent)
HARDCODED_USERS_PREFIX = "/" + "Users/"

WORKSPACE_INTERNAL_ROOTS = frozenset({
    "architect",
    "formalist",
    "simulator",
    "inquisitor",
    "verify_all",
    "standalone_integral_sheaf_torsion",
})

# Portable Python 3.9+ standard library module allowlist (excluding banned modules below).
PORTABLE_STDLIB_MODULES = frozenset({
    "__future__",
    "abc",
    "argparse",
    "array",
    "ast",
    "atexit",
    "base64",
    "bisect",
    "builtins",
    "bz2",
    "calendar",
    "cmd",
    "code",
    "codecs",
    "collections",
    "compileall",
    "concurrent",
    "configparser",
    "contextlib",
    "contextvars",
    "copy",
    "copyreg",
    "csv",
    "dataclasses",
    "datetime",
    "difflib",
    "dis",
    "doctest",
    "enum",
    "errno",
    "faulthandler",
    "fcntl",
    "filecmp",
    "fileinput",
    "fnmatch",
    "fractions",
    "functools",
    "gc",
    "genericpath",
    "getopt",
    "getpass",
    "gettext",
    "glob",
    "graphlib",
    "gzip",
    "hashlib",
    "heapq",
    "hmac",
    "html",
    "http",
    "importlib",
    "inspect",
    "io",
    "ipaddress",
    "itertools",
    "json",
    "keyword",
    "linecache",
    "locale",
    "logging",
    "lzma",
    "marshal",
    "math",
    "mmap",
    "modulefinder",
    "multiprocessing",
    "numbers",
    "operator",
    "optparse",
    "os",
    "pathlib",
    "pdb",
    "pickle",
    "pkgutil",
    "platform",
    "plistlib",
    "posix",
    "posixpath",
    "pprint",
    "profile",
    "pstats",
    "py_compile",
    "pyclbr",
    "pydoc",
    "queue",
    "random",
    "re",
    "reprlib",
    "resource",
    "runpy",
    "sched",
    "secrets",
    "select",
    "selectors",
    "shelve",
    "shlex",
    "shutil",
    "signal",
    "site",
    "socket",
    "sqlite3",
    "stat",
    "string",
    "struct",
    "subprocess",
    "symtable",
    "sys",
    "sysconfig",
    "tabnanny",
    "tarfile",
    "tempfile",
    "textwrap",
    "threading",
    "time",
    "timeit",
    "token",
    "tokenize",
    "trace",
    "traceback",
    "tracemalloc",
    "types",
    "typing",
    "unicodedata",
    "unittest",
    "urllib",
    "uuid",
    "warnings",
    "weakref",
    "xml",
    "zipapp",
    "zipfile",
    "zipimport",
    "zlib",
    "zoneinfo",
})

EXPLICIT_FORBIDDEN_IMPORTS = frozenset({
    "numpy",
    "scipy",
    "sympy",
    "flint",
    "python_flint",
    "z3",
    "gurobi",
    "gurobipy",
    "cvxpy",
    "pycddlib",
    "cdd",
    "torch",
    "networkx",
    "matplotlib",
    "pandas",
    "ortools",
    "pulp",
    "sage",
    "gmpy2",
    "mpmath",
    "cython",
    "numba",
    "jax",
    "sklearn",
    "ctypes",
    "cmath",
    "decimal",
    "statistics",
})

FLOAT_TYPE_NAMES = frozenset({"fl" + "oat", "comp" + "lex"})

BANNED_FLOAT_MATH_ATTRS = frozenset({
    "sqrt",
    "sin",
    "cos",
    "tan",
    "asin",
    "acos",
    "atan",
    "atan2",
    "sinh",
    "cosh",
    "tanh",
    "asinh",
    "acosh",
    "atanh",
    "exp",
    "expm1",
    "log",
    "log1p",
    "log2",
    "log10",
    "pow",
    "fabs",
    "fmod",
    "frexp",
    "fsum",
    "hypot",
    "isclose",
    "isfinite",
    "isinf",
    "isnan",
    "ldexp",
    "modf",
    "nextafter",
    "radians",
    "degrees",
    "erf",
    "erfc",
    "gamma",
    "lgamma",
    "ulp",
    "pi",
    "e",
    "tau",
    "inf",
    "nan",
})

BANNED_FLOAT_TIME_ATTRS = frozenset({
    "time",
    "perf_counter",
    "monotonic",
    "process_time",
    "thread_time",
})

PRIMITIVE_GUARD_TYPES = frozenset({
    "int",
    "str",
    "bytes",
    "bool",
    "list",
    "tuple",
    "dict",
    "set",
    "frozenset",
})

SVG_TAG_TOKEN = "<" + "svg"
SVG_EXT_TOKEN = ".s" + "vg"


def _build_runtime_stdlib_set() -> frozenset[str]:
    mods = set(PORTABLE_STDLIB_MODULES)
    for bname in sys.builtin_module_names:
        if bname not in EXPLICIT_FORBIDDEN_IMPORTS:
            mods.add(bname)
    stdlib_dir = sysconfig.get_path("stdlib")
    if stdlib_dir and os.path.isdir(stdlib_dir):
        for entry in os.listdir(stdlib_dir):
            if entry.endswith(".py"):
                stem = entry[:-3]
                if stem not in EXPLICIT_FORBIDDEN_IMPORTS:
                    mods.add(stem)
            elif os.path.isdir(os.path.join(stdlib_dir, entry)) and entry not in (
                "site-packages",
                "lib-dynload",
                "test",
                "idlelib",
                "tkinter",
                "turtledemo",
            ):
                if entry not in EXPLICIT_FORBIDDEN_IMPORTS:
                    mods.add(entry)
    return frozenset(mods - EXPLICIT_FORBIDDEN_IMPORTS)


ALLOWED_STDLIB_ROOTS = _build_runtime_stdlib_set()


def _is_int_literal_expr(node: ast.AST) -> bool:
    if type(node) is ast.Constant and type(node.value) is int:
        return True
    if type(node) is ast.UnaryOp and type(node.op) in (ast.UAdd, ast.USub):
        return _is_int_literal_expr(node.operand)
    return False


def _is_path_like_expr(node: ast.AST, path_names: set[str]) -> bool:
    if type(node) is ast.Constant and type(node.value) is str:
        return True
    if type(node) is ast.Name and (
        node.id in path_names
        or "path" in node.id.lower()
        or "dir" in node.id.lower()
        or "root" in node.id.lower()
    ):
        return True
    if type(node) is ast.Call:
        if type(node.func) is ast.Name and node.func.id in path_names:
            return True
        if type(node.func) is ast.Attribute and node.func.attr in ("Path", "resolve", "parent"):
            return True
    if type(node) is ast.Attribute and node.attr in ("parent", "root"):
        return True
    if type(node) is ast.BinOp and type(node.op) is ast.Div:
        return _is_path_like_expr(node.left, path_names) or _is_path_like_expr(node.right, path_names)
    return False


def _is_canned_literal_expr(node: ast.AST | None) -> bool:
    if node is None:
        return False
    if type(node) in (ast.Constant, ast.Dict, ast.List, ast.Tuple, ast.Set):
        return True
    if type(node) is ast.UnaryOp and type(node.op) in (ast.UAdd, ast.USub, ast.Not):
        return _is_canned_literal_expr(node.operand)
    return False


def _extract_isinstance_type_names(node: ast.AST) -> list[str]:
    if type(node) is ast.Name:
        return [node.id]
    if type(node) is ast.Attribute:
        return [node.attr]
    if type(node) is ast.Tuple:
        out: list[str] = []
        for elt in node.elts:
            out.extend(_extract_isinstance_type_names(elt))
        return out
    return ["<complex_type_expr>"]


def _annotation_contains_banned_float(node: ast.AST | None) -> bool:
    if node is None:
        return False
    for sub in ast.walk(node):
        if type(sub) is ast.Name and sub.id in FLOAT_TYPE_NAMES:
            return True
        if type(sub) is ast.Attribute and sub.attr in FLOAT_TYPE_NAMES:
            return True
        if type(sub) is ast.Constant and type(sub.value) is str:
            tokens = (
                sub.value.replace("[", " ")
                .replace("]", " ")
                .replace(",", " ")
                .replace("|", " ")
                .replace("(", " ")
                .replace(")", " ")
                .split()
            )
            for tok in tokens:
                if tok.split(".")[-1] in FLOAT_TYPE_NAMES:
                    return True
    return False


def _has_non_docstring_statements(tree: ast.Module) -> bool:
    for idx, stmt in enumerate(tree.body):
        if idx == 0 and type(stmt) is ast.Expr and type(stmt.value) is ast.Constant and type(stmt.value.value) is str:
            continue
        return True
    return False


def _has_future_annotations(tree: ast.Module) -> bool:
    for stmt in tree.body:
        if type(stmt) is ast.ImportFrom and stmt.module == "__future__":
            for alias in stmt.names:
                if alias.name == "annotations":
                    return True
    return False


def _is_architect_core_path(rel_path: str) -> bool:
    norm = rel_path.replace("\\", "/")
    return norm.startswith("architect/core/") or norm == "architect/core"


def _is_test_or_verifier_path(rel_path: str) -> bool:
    norm = rel_path.replace("\\", "/")
    base = os.path.basename(norm)
    return (
        base.startswith("test_")
        or base.startswith("proof_pack")
        or base == "verify_all.py"
        or base == "standalone_integral_sheaf_torsion.py"
    )


def _is_svg_atlas_path(rel_path: str) -> bool:
    norm = rel_path.replace("\\", "/")
    return norm == "simulator/svg_atlas.py"


def _is_algebraic_or_proof_path(rel_path: str) -> bool:
    norm = rel_path.replace("\\", "/")
    return (
        norm.startswith("architect/")
        or norm.startswith("formalist/")
        or norm == "standalone_integral_sheaf_torsion.py"
    )


def scan_source_string(
    source: str,
    rel_path: str,
    sibling_stems: frozenset[str] = frozenset(),
) -> dict[str, list[dict[str, Any]]]:
    """Scan a single Python source string under scope-aware rules for `rel_path`."""
    violations: list[dict[str, Any]] = []
    advisories: list[dict[str, Any]] = []
    in_svg_atlas = _is_svg_atlas_path(rel_path)
    in_algebraic_or_proof = _is_algebraic_or_proof_path(rel_path)

    def add_violation(rule: str, line: int, col: int, detail: str) -> None:
        violations.append({
            "file": rel_path,
            "line": line,
            "col": col,
            "rule": rule,
            "detail": detail,
        })

    def add_advisory(rule: str, line: int, col: int, detail: str) -> None:
        advisories.append({
            "file": rel_path,
            "line": line,
            "col": col,
            "rule": rule,
            "detail": detail,
        })

    def add_float_finding(rule: str, line: int, col: int, detail: str, is_complex: bool = False) -> None:
        if in_svg_atlas and not is_complex:
            add_advisory(
                "SVG_ATLAS_CONFINED_FLOAT",
                line,
                col,
                f"[{rule}] Confined inside `simulator/svg_atlas.py` coordinate rendering (SPEC_WAVE2.md §0.2): {detail}",
            )
        else:
            add_violation(rule, line, col, detail)

    try:
        tree = ast.parse(source, filename=rel_path)
    except SyntaxError as exc:
        add_violation("SYNTAX_ERROR", exc.lineno or 1, exc.offset or 0, f"SyntaxError: {exc.msg}")
        return {"violations": violations, "advisories": advisories}

    in_core = _is_architect_core_path(rel_path)
    in_verifier = _is_test_or_verifier_path(rel_path)

    # Rule 0: `from __future__ import annotations` in non-empty modules
    if _has_non_docstring_statements(tree) and not _has_future_annotations(tree):
        add_violation(
            "MISSING_FUTURE_ANNOTATIONS",
            1,
            0,
            "Non-empty module must include `from __future__ import annotations` (SPEC.md §0.2).",
        )

    math_aliases: set[str] = set()
    direct_banned_math_funcs: set[str] = set()
    time_aliases: set[str] = set()
    direct_banned_time_funcs: set[str] = set()
    path_names: set[str] = {"Path"}
    has_signal_alarm = False

    # Pass 1: Scan imports & module-level aliases
    for node in ast.walk(tree):
        if type(node) is ast.Import:
            for alias in node.names:
                full_name = alias.name
                root_mod = full_name.split(".")[0]
                bound_name = alias.asname or root_mod
                if full_name == "unittest.mock" or root_mod == "mock":
                    add_violation(
                        "MOCK_IMPORT_BANNED",
                        node.lineno,
                        node.col_offset,
                        f"Mock framework import `{full_name}` is strictly forbidden.",
                    )
                elif root_mod in EXPLICIT_FORBIDDEN_IMPORTS:
                    add_violation(
                        "FORBIDDEN_EXTERNAL_IMPORT",
                        node.lineno,
                        node.col_offset,
                        f"Forbidden import `{full_name}` violates zero-dependency/exact-math guardrail.",
                    )
                elif (
                    root_mod not in ALLOWED_STDLIB_ROOTS
                    and root_mod not in WORKSPACE_INTERNAL_ROOTS
                    and root_mod not in sibling_stems
                ):
                    add_violation(
                        "NON_STDLIB_IMPORT",
                        node.lineno,
                        node.col_offset,
                        f"Non-stdlib import `{full_name}` is forbidden (Python 3.9+ stdlib only).",
                    )
                if root_mod == "fractions" and in_core:
                    add_violation(
                        "INNER_LOOP_FRACTION_FIREWALL",
                        node.lineno,
                        node.col_offset,
                        "`fractions` import is banned inside `architect/core/` (SPEC.md §0.2).",
                    )
                if in_algebraic_or_proof and (full_name == "simulator.svg_atlas" or full_name == "svg_atlas"):
                    add_violation(
                        "SVG_ATLAS_ISOLATION_BREACH",
                        node.lineno,
                        node.col_offset,
                        f"`{rel_path}` must remain strictly isolated from `simulator/svg_atlas.py` (SPEC_WAVE2.md §0.2).",
                    )
                if root_mod == "math":
                    math_aliases.add(bound_name)
                if root_mod == "time":
                    time_aliases.add(bound_name)
                if root_mod == "pathlib":
                    path_names.add(bound_name)

        elif type(node) is ast.ImportFrom:
            mod_name = node.module or ""
            root_mod = mod_name.split(".")[0] if mod_name else ""
            if node.level == 0:
                if mod_name == "unittest.mock" or root_mod == "mock":
                    add_violation(
                        "MOCK_IMPORT_BANNED",
                        node.lineno,
                        node.col_offset,
                        f"Mock framework import `from {mod_name} import ...` is strictly forbidden.",
                    )
                elif root_mod in EXPLICIT_FORBIDDEN_IMPORTS:
                    add_violation(
                        "FORBIDDEN_EXTERNAL_IMPORT",
                        node.lineno,
                        node.col_offset,
                        f"Forbidden import `from {mod_name} import ...` violates zero-dependency/exact-math guardrail.",
                    )
                elif (
                    root_mod not in ALLOWED_STDLIB_ROOTS
                    and root_mod not in WORKSPACE_INTERNAL_ROOTS
                    and root_mod not in sibling_stems
                ):
                    add_violation(
                        "NON_STDLIB_IMPORT",
                        node.lineno,
                        node.col_offset,
                        f"Non-stdlib import `from {mod_name} import ...` is forbidden.",
                    )
            if root_mod == "fractions" and in_core:
                add_violation(
                    "INNER_LOOP_FRACTION_FIREWALL",
                    node.lineno,
                    node.col_offset,
                    "`from fractions import ...` is banned inside `architect/core/` (SPEC.md §0.2).",
                )
            if in_algebraic_or_proof and (mod_name == "simulator.svg_atlas" or mod_name == "svg_atlas"):
                add_violation(
                    "SVG_ATLAS_ISOLATION_BREACH",
                    node.lineno,
                    node.col_offset,
                    f"`{rel_path}` must remain strictly isolated from `simulator/svg_atlas.py` (SPEC_WAVE2.md §0.2).",
                )
            for alias in node.names:
                bound = alias.asname or alias.name
                if in_algebraic_or_proof and root_mod in ("simulator", "") and alias.name == "svg_atlas":
                    add_violation(
                        "SVG_ATLAS_ISOLATION_BREACH",
                        node.lineno,
                        node.col_offset,
                        f"`{rel_path}` must remain strictly isolated from `simulator/svg_atlas.py` (SPEC_WAVE2.md §0.2).",
                    )
                if mod_name == "unittest" and alias.name == "mock":
                    add_violation(
                        "MOCK_IMPORT_BANNED",
                        node.lineno,
                        node.col_offset,
                        "`from unittest import mock` is strictly forbidden.",
                    )
                if root_mod == "math" and alias.name in BANNED_FLOAT_MATH_ATTRS:
                    direct_banned_math_funcs.add(bound)
                    add_float_finding(
                        "FLOAT_MATH_IMPORT",
                        node.lineno,
                        node.col_offset,
                        f"`from math import {alias.name}` imports a floating-point symbol.",
                    )
                if root_mod == "time" and alias.name in BANNED_FLOAT_TIME_ATTRS:
                    direct_banned_time_funcs.add(bound)
                    add_float_finding(
                        "FLOAT_TIME_IMPORT",
                        node.lineno,
                        node.col_offset,
                        f"`from time import {alias.name}` returns float; use `{alias.name}_ns`.",
                    )
                if root_mod == "pathlib" and alias.name in ("Path", "PurePath", "PosixPath"):
                    path_names.add(bound)
                if alias.name == "alarm" and root_mod == "signal":
                    has_signal_alarm = True

    # Pass 2: Full AST contraband, float, Fraction, anti-cheat & stub checks
    for node in ast.walk(tree):
        # 2a. Float/complex literals & algebraic-module SVG strings
        if type(node) is ast.Constant:
            vtype_name = type(node.value).__name__
            if vtype_name in FLOAT_TYPE_NAMES:
                add_float_finding(
                    "FLOAT_LITERAL",
                    node.lineno,
                    node.col_offset,
                    f"Floating-point/complex literal `{node.value!r}` is banned across algebraic/verification modules.",
                    is_complex=(vtype_name == ("comp" + "lex")),
                )
            elif type(node.value) is str:
                low = node.value.lower()
                if in_algebraic_or_proof and (SVG_TAG_TOKEN in low or low.endswith(SVG_EXT_TOKEN)):
                    add_violation(
                        "SVG_IN_ALGEBRAIC_MODULE_BANNED",
                        node.lineno,
                        node.col_offset,
                        f"SVG generation/markup is forbidden inside algebraic/proof module `{rel_path}` (SPEC_WAVE2.md §0.2).",
                    )
                if HARDCODED_USERS_PREFIX in node.value and node.value != HARDCODED_USERS_PREFIX:
                    add_violation(
                        "HARDCODED_WORKSPACE_PATH",
                        node.lineno,
                        node.col_offset,
                        "Hardcoded host user-home path breaks `/tmp` clean-room portability; use `Path(__file__).resolve()`.",
                    )

        # 2b. Direct `float` / `complex` / inner-loop `Fraction` identifiers
        elif type(node) is ast.Name:
            if node.id in FLOAT_TYPE_NAMES:
                add_float_finding(
                    "FLOAT_IDENTIFIER",
                    node.lineno,
                    node.col_offset,
                    f"Identifier `{node.id}` (call/annotation/type reference) is banned.",
                    is_complex=(node.id == ("comp" + "lex")),
                )
            elif node.id == "Fraction" and in_core:
                add_violation(
                    "INNER_LOOP_FRACTION_FIREWALL",
                    node.lineno,
                    node.col_offset,
                    "`Fraction` reference inside `architect/core/` is banned (SPEC.md §0.2).",
                )
            elif node.id in ("MagicMock", "Mock"):
                add_violation(
                    "MOCK_IDENTIFIER_BANNED",
                    node.lineno,
                    node.col_offset,
                    f"Mock class `{node.id}` is strictly forbidden.",
                )

        # 2c. Attribute checks (`builtins.float`, `fractions.Fraction`, `math.sqrt`, `time.perf_counter`, `_getframe`)
        elif type(node) is ast.Attribute:
            if node.attr in FLOAT_TYPE_NAMES:
                add_float_finding(
                    "FLOAT_IDENTIFIER",
                    node.lineno,
                    node.col_offset,
                    f"Attribute `.{node.attr}` is banned.",
                    is_complex=(node.attr == ("comp" + "lex")),
                )
            elif node.attr == "Fraction" and in_core:
                add_violation(
                    "INNER_LOOP_FRACTION_FIREWALL",
                    node.lineno,
                    node.col_offset,
                    "`.Fraction` attribute inside `architect/core/` is banned (SPEC.md §0.2).",
                )
            elif type(node.value) is ast.Name and node.value.id in math_aliases and node.attr in BANNED_FLOAT_MATH_ATTRS:
                add_float_finding(
                    "FLOAT_MATH_API",
                    node.lineno,
                    node.col_offset,
                    f"`{node.value.id}.{node.attr}` uses IEEE float arithmetic; use exact integer stdlib equivalents (`isqrt`, `gcd`, `lcm`, `comb`).",
                )
            elif type(node.value) is ast.Name and node.value.id in time_aliases and node.attr in BANNED_FLOAT_TIME_ATTRS:
                add_float_finding(
                    "FLOAT_TIME_API",
                    node.lineno,
                    node.col_offset,
                    f"`{node.value.id}.{node.attr}()` returns `float`; use `{node.value.id}.{node.attr}_ns()` with integer `//`.",
                )
            elif node.attr in ("_getframe", "currentframe") or (
                type(node.value) is ast.Name and node.value.id == "inspect" and node.attr == "stack"
            ):
                add_violation(
                    "CALLER_SNIFFING_CHEAT",
                    node.lineno,
                    node.col_offset,
                    f"Stack/caller inspection `.{node.attr}` is banned as a test-bypass vector.",
                )
            elif node.attr == "alarm":
                has_signal_alarm = True

        # 2d. String annotations containing `float` / `complex`
        elif type(node) in (ast.FunctionDef, ast.AsyncFunctionDef):
            if _annotation_contains_banned_float(node.returns):
                add_float_finding(
                    "FLOAT_ANNOTATION",
                    node.lineno,
                    node.col_offset,
                    f"Function `{node.name}` return annotation references float/complex.",
                    is_complex=("comp" + "lex") in ast.dump(node.returns),
                )
            all_args = (
                list(node.args.posonlyargs)
                + list(node.args.args)
                + list(node.args.kwonlyargs)
            )
            if node.args.vararg is not None:
                all_args.append(node.args.vararg)
            if node.args.kwarg is not None:
                all_args.append(node.args.kwarg)
            for arg in all_args:
                if _annotation_contains_banned_float(arg.annotation):
                    add_float_finding(
                        "FLOAT_ANNOTATION",
                        arg.lineno,
                        arg.col_offset,
                        f"Argument `{arg.arg}` in `{node.name}` annotation references float/complex.",
                        is_complex=(arg.annotation is not None and ("comp" + "lex") in ast.dump(arg.annotation)),
                    )

            # Check stub functions (`pass`, `...`, `raise NotImplementedError`)
            body_non_doc = [
                s
                for idx, s in enumerate(node.body)
                if not (
                    idx == 0
                    and type(s) is ast.Expr
                    and type(s.value) is ast.Constant
                    and type(s.value.value) is str
                )
            ]
            if len(body_non_doc) == 1:
                only_stmt = body_non_doc[0]
                if type(only_stmt) is ast.Pass:
                    add_violation(
                        "UNIMPLEMENTED_STUB",
                        only_stmt.lineno,
                        only_stmt.col_offset,
                        f"Function `{node.name}` has an empty `pass` stub body.",
                    )
                elif (
                    type(only_stmt) is ast.Expr
                    and type(only_stmt.value) is ast.Constant
                    and only_stmt.value.value is Ellipsis
                ):
                    add_violation(
                        "UNIMPLEMENTED_STUB",
                        only_stmt.lineno,
                        only_stmt.col_offset,
                        f"Function `{node.name}` has an unimplemented `...` stub body.",
                    )
                elif type(only_stmt) is ast.Raise and only_stmt.exc is not None:
                    exc = only_stmt.exc
                    if (type(exc) is ast.Name and exc.id == "NotImplementedError") or (
                        type(exc) is ast.Call
                        and type(exc.func) is ast.Name
                        and exc.func.id == "NotImplementedError"
                    ):
                        add_violation(
                            "UNIMPLEMENTED_STUB",
                            only_stmt.lineno,
                            only_stmt.col_offset,
                            f"Function `{node.name}` raises `NotImplementedError`.",
                        )

            # Check test/verify functions for shallow `assert isinstance(...)` bypasses
            fname_low = node.name.lower()
            if fname_low.startswith(("test_", "verify_", "check_")):
                has_algebraic_assert = False
                isinstance_assert_lines: list[int] = []
                for sub in ast.walk(node):
                    if type(sub) is ast.Assert:
                        if (
                            type(sub.test) is ast.Call
                            and type(sub.test.func) is ast.Name
                            and sub.test.func.id == "isinstance"
                        ):
                            isinstance_assert_lines.append(sub.lineno)
                        else:
                            has_algebraic_assert = True
                for ln in isinstance_assert_lines:
                    add_violation(
                        "ISINSTANCE_TEST_BYPASS",
                        ln,
                        0,
                        f"Test/verifier `{node.name}` uses `assert isinstance(...)`; tests must assert exact algebraic equations.",
                    )
                if isinstance_assert_lines and not has_algebraic_assert:
                    add_violation(
                        "SHALLOW_MOCK_TEST",
                        node.lineno,
                        node.col_offset,
                        f"Test/verifier `{node.name}` contains no algebraic assertions beyond `isinstance`.",
                    )

        elif type(node) is ast.AnnAssign:
            if _annotation_contains_banned_float(node.annotation):
                add_float_finding(
                    "FLOAT_ANNOTATION",
                    node.lineno,
                    node.col_offset,
                    "Variable type annotation references float/complex.",
                    is_complex=(("comp" + "lex") in ast.dump(node.annotation)),
                )

        # 2e. True division `/` (`ast.Div`) checks
        elif type(node) is ast.BinOp and type(node.op) is ast.Div:
            if _is_int_literal_expr(node.left) and _is_int_literal_expr(node.right):
                add_float_finding(
                    "FLOAT_TRUE_DIV",
                    node.lineno,
                    node.col_offset,
                    "Integer literal `/` integer literal evaluates to IEEE `float` in Python 3; use `//` or `(num, den)`.",
                )
            elif in_core and not (
                _is_path_like_expr(node.left, path_names) or _is_path_like_expr(node.right, path_names)
            ):
                add_violation(
                    "CORE_FLOAT_TRUE_DIV",
                    node.lineno,
                    node.col_offset,
                    "True division `/` inside `architect/core/` (where `Fraction` is banned) produces `float`; use exact `//` or `divmod`.",
                )

        elif type(node) is ast.AugAssign and type(node.op) is ast.Div:
            if in_core:
                add_violation(
                    "CORE_FLOAT_TRUE_DIV",
                    node.lineno,
                    node.col_offset,
                    "Augmented true division `/=` inside `architect/core/` produces `float`.",
                )

        # 2f. Dynamic import / eval / exec / isinstance cheat checks
        elif type(node) is ast.Call:
            if type(node.func) is ast.Name:
                fn = node.func.id
                if fn in ("__import__", "eval", "exec"):
                    add_violation(
                        "DYNAMIC_EXEC_OR_IMPORT_BYPASS",
                        node.lineno,
                        node.col_offset,
                        f"Dynamic `{fn}(...)` call is forbidden as a sandbox/AST-firewall bypass.",
                    )
                elif fn == "isinstance":
                    if len(node.args) >= 2:
                        tnames = _extract_isinstance_type_names(node.args[1])
                        non_prim = [t for t in tnames if t not in PRIMITIVE_GUARD_TYPES]
                        if non_prim:
                            add_violation(
                                "ISINSTANCE_DISPATCH_BYPASS",
                                node.lineno,
                                node.col_offset,
                                f"`isinstance(..., {tnames})` dispatches on non-primitive type(s) {non_prim}; banned by anti-bypass policy.",
                            )
                        else:
                            add_advisory(
                                "PRIMITIVE_ISINSTANCE_NOTE",
                                node.lineno,
                                node.col_offset,
                                f"Primitive `isinstance(..., {tnames})` noted (beware `isinstance(True, int) == True`; `type(x) is int` is exact).",
                            )
            elif type(node.func) is ast.Attribute:
                if (
                    type(node.func.value) is ast.Name
                    and node.func.value.id == "importlib"
                    and node.func.attr == "import_module"
                ):
                    allowed_internal = False
                    if (
                        len(node.args) == 1
                        and len(node.keywords) == 0
                        and type(node.args[0]) is ast.Constant
                        and type(node.args[0].value) is str
                    ):
                        target_root = node.args[0].value.split(".")[0]
                        if target_root in WORKSPACE_INTERNAL_ROOTS:
                            allowed_internal = True
                    if not allowed_internal:
                        add_violation(
                            "DYNAMIC_EXEC_OR_IMPORT_BYPASS",
                            node.lineno,
                            node.col_offset,
                            "`importlib.import_module(...)` is forbidden unless strictly auditing known internal packages.",
                        )

        # 2g. `if isinstance(...): return <canned literal>` bypass detector
        elif type(node) is ast.If:
            has_isinstance_cond = False
            for sub in ast.walk(node.test):
                if type(sub) is ast.Call and type(sub.func) is ast.Name and sub.func.id == "isinstance":
                    has_isinstance_cond = True
                    break
            if has_isinstance_cond:
                for stmt in node.body:
                    if type(stmt) is ast.Return and _is_canned_literal_expr(stmt.value):
                        # Allow pure input-normalization idioms only if returning raised error, never canned dict/bool/int witness!
                        if type(stmt.value) in (ast.Dict, ast.Constant):
                            add_violation(
                                "ISINSTANCE_CANNED_RETURN_BYPASS",
                                stmt.lineno,
                                stmt.col_offset,
                                "`if isinstance(...): return <literal/dict>` matches canned-witness test-bypass pattern.",
                            )

    if in_verifier and _has_non_docstring_statements(tree) and not has_signal_alarm:
        add_violation(
            "MISSING_SIGNAL_ALARM",
            1,
            0,
            f"Verification entrypoint `{rel_path}` must enforce `signal.alarm(20)` (SPEC.md §0.3).",
        )

    return {"violations": violations, "advisories": advisories}


def scan_json_artifacts_for_floats(root_path: str = WORKSPACE_ROOT) -> list[dict[str, Any]]:
    """Verify that zero IEEE floating-point numbers appear in `artifacts/*.json`."""
    violations: list[dict[str, Any]] = []
    artifacts_dir = os.path.join(root_path, "artifacts")
    if not os.path.isdir(artifacts_dir):
        return violations

    for dirpath, _dirnames, filenames in os.walk(artifacts_dir):
        for fname in sorted(filenames):
            if not fname.endswith(".json"):
                continue
            fpath = os.path.join(dirpath, fname)
            rel = os.path.relpath(fpath, root_path)
            found_floats: list[str] = []

            def _reject_float(token: str) -> int:
                found_floats.append(token)
                return 0

            try:
                with open(fpath, "r", encoding="utf-8") as fh:
                    raw = fh.read()
                json.loads(raw, parse_float=_reject_float)
            except Exception as exc:
                violations.append({
                    "file": rel,
                    "line": 1,
                    "col": 0,
                    "rule": "INVALID_JSON_ARTIFACT",
                    "detail": f"JSON parse error: {exc}",
                })
                continue

            if found_floats:
                sample = ", ".join(found_floats[:5])
                violations.append({
                    "file": rel,
                    "line": 1,
                    "col": 0,
                    "rule": "JSON_ARTIFACT_FLOAT_TOKEN",
                    "detail": f"JSON artifact contains {len(found_floats)} float token(s) (sample: {sample}); serialize exact `int` or rational strings `'p/q'`.",
                })
    return violations


def scan_workspace(root_path: str = WORKSPACE_ROOT) -> dict[str, Any]:
    """Scan all Python, JSON, and SVG files inside `root_path` and return full Wave II audit report."""
    t0_ns = time.perf_counter_ns()
    py_files: list[str] = []
    plots_svg_files: list[str] = []
    config_violations: list[dict[str, Any]] = []

    banned_dep_files = {"pyproject.toml", "requirements.txt", "setup.py", "Pipfile"}

    for dirpath, dirnames, filenames in os.walk(root_path):
        dirnames[:] = sorted(
            d for d in dirnames if d not in ("__pycache__", ".git", ".pytest_cache", ".mypy_cache")
        )
        for fname in sorted(filenames):
            full = os.path.join(dirpath, fname)
            rel = os.path.relpath(full, root_path)
            rel_norm = rel.replace("\\", "/")
            if fname in banned_dep_files:
                config_violations.append({
                    "file": rel,
                    "line": 1,
                    "col": 0,
                    "rule": "EXTERNAL_DEPENDENCY_CONFIG",
                    "detail": f"External packaging/dependency file `{rel}` is forbidden (SPEC_WAVE2.md §0.2).",
                })
            elif fname.lower().endswith(SVG_EXT_TOKEN):
                if rel_norm.startswith("plots/") and ("/" not in rel_norm[len("plots/"):]):
                    plots_svg_files.append(rel_norm)
                else:
                    config_violations.append({
                        "file": rel,
                        "line": 1,
                        "col": 0,
                        "rule": "STRAY_SVG_FILE_OUTSIDE_PLOTS",
                        "detail": f"SVG file `{rel}` outside `plots/` is forbidden (SPEC_WAVE2.md §2.1).",
                    })
            elif fname.endswith(".py"):
                py_files.append(full)

    all_violations: list[dict[str, Any]] = list(config_violations)
    all_advisories: list[dict[str, Any]] = []
    per_file_summary: list[dict[str, Any]] = []
    svg_atlas_present = False
    svg_atlas_confined_floats = 0

    # Precompute sibling module stems per directory so local imports within a folder resolve cleanly.
    dir_stems: dict[str, frozenset[str]] = {}
    for full in py_files:
        d = os.path.dirname(full)
        stems = set(dir_stems.get(d, frozenset()))
        stems.add(os.path.basename(full)[:-3])
        dir_stems[d] = frozenset(stems)

    for full in py_files:
        rel = os.path.relpath(full, root_path)
        rel_norm = rel.replace("\\", "/")
        with open(full, "r", encoding="utf-8") as fh:
            src = fh.read()
        res = scan_source_string(src, rel, sibling_stems=dir_stems.get(os.path.dirname(full), frozenset()))
        v_list = res["violations"]
        a_list = res["advisories"]
        if rel_norm == "simulator/svg_atlas.py":
            svg_atlas_present = True
            svg_atlas_confined_floats = sum(1 for a in a_list if a["rule"] == "SVG_ATLAS_CONFINED_FLOAT")
        all_violations.extend(v_list)
        all_advisories.extend(a_list)
        per_file_summary.append({
            "file": rel,
            "status": "CLEAN" if len(v_list) == 0 else "VIOLATION",
            "violation_count": len(v_list),
            "advisory_count": len(a_list),
        })

    json_violations = scan_json_artifacts_for_floats(root_path)
    all_violations.extend(json_violations)

    elapsed_ns = time.perf_counter_ns() - t0_ns
    return {
        "scanner": "inquisitor.ast_scanner",
        "workspace_root": root_path,
        "scanned_python_files": len(py_files),
        "plots_svg_files_detected": len(plots_svg_files),
        "svg_atlas_present": svg_atlas_present,
        "svg_atlas_zero_float": (svg_atlas_confined_floats == 0),
        "svg_atlas_confined_float_advisories": svg_atlas_confined_floats,
        "status": "PASS" if len(all_violations) == 0 else "FAIL",
        "total_violations": len(all_violations),
        "total_advisories": len(all_advisories),
        "elapsed_ns": elapsed_ns,
        "elapsed_ms": elapsed_ns // 1_000_000,
        "per_file": per_file_summary,
        "violations": all_violations,
        "advisories": all_advisories,
    }


def run_scanner_self_tests() -> dict[str, Any]:
    """Verify the AST scanner catches every single forbidden contraband pattern in-memory."""
    cases = [
        (
            "external_numpy_import",
            "from __future__ import annotations\nimport numpy as np\n",
            "architect/core/exact_int_la.py",
            "FORBIDDEN_EXTERNAL_IMPORT",
        ),
        (
            "unknown_third_party_import",
            "from __future__ import annotations\nfrom pycddlib import Polyhedron\n",
            "architect/track_b_decomp_splines.py",
            "FORBIDDEN_EXTERNAL_IMPORT",
        ),
        (
            "float_literal_contraband",
            "from __future__ import annotations\nx = 1" + ".25\n",
            "simulator/sweep.py",
            "FLOAT_LITERAL",
        ),
        (
            "float_call_and_annotation",
            "from __future__ import annotations\ndef f(x: " + "fl" + "oat) -> int:\n    return 0\n",
            "formalist/helper.py",
            "FLOAT_IDENTIFIER",
        ),
        (
            "float_math_sqrt",
            "from __future__ import annotations\nimport math\ny = math.sqrt(4)\n",
            "simulator/sweep.py",
            "FLOAT_MATH_API",
        ),
        (
            "float_time_perf_counter",
            "from __future__ import annotations\nimport time\nt = time.perf_counter()\n",
            "architect/track_a_foundations.py",
            "FLOAT_TIME_API",
        ),
        (
            "core_fraction_firewall",
            "from __future__ import annotations\nfrom fractions import Fraction\nx = Fraction(1, 2)\n",
            "architect/core/bareiss_farkas_lp.py",
            "INNER_LOOP_FRACTION_FIREWALL",
        ),
        (
            "core_true_division_float",
            "from __future__ import annotations\ndef div_bad(a: int, b: int) -> int:\n    return a / b\n",
            "architect/core/exact_int_la.py",
            "CORE_FLOAT_TRUE_DIV",
        ),
        (
            "outer_fraction_allowed_outside_core",
            "from __future__ import annotations\nfrom fractions import Fraction\nf = Fraction(3, 5)\n",
            "architect/track_b_decomp_splines.py",
            None,
        ),
        (
            "isinstance_test_bypass",
            "from __future__ import annotations\nimport signal\nsignal.alarm(20)\ndef test_cheat(x: object) -> None:\n    assert isinstance(x, dict)\n",
            "architect/test_wave1_traps.py",
            "ISINSTANCE_TEST_BYPASS",
        ),
        (
            "isinstance_custom_dispatch_bypass",
            "from __future__ import annotations\ndef solve(p: object) -> dict[str, str]:\n    if isinstance(p, SpecialTrap):\n        return {'status': 'CERTIFIED_EXACT'}\n    return {'status': 'OPEN'}\n",
            "architect/core/padic_local_global.py",
            "ISINSTANCE_DISPATCH_BYPASS",
        ),
        (
            "svg_in_algebraic_module_ban",
            "from __future__ import annotations\ns = '" + SVG_TAG_TOKEN + " width=\"100\">'\n",
            "architect/track_a_foundations.py",
            "SVG_IN_ALGEBRAIC_MODULE_BANNED",
        ),
        (
            "svg_allowed_in_svg_atlas_and_auditor",
            "from __future__ import annotations\ns = '" + SVG_TAG_TOKEN + " viewBox=\"0 0 1400 900\">'\n",
            "simulator/svg_atlas.py",
            None,
        ),
        (
            "svg_atlas_isolation_breach",
            "from __future__ import annotations\nfrom simulator import svg_atlas\n",
            "architect/track_a_wave2_max6.py",
            "SVG_ATLAS_ISOLATION_BREACH",
        ),
        (
            "standalone_bundle_float_ban",
            "from __future__ import annotations\nimport signal\nsignal.alarm(20)\nx = 0" + ".5\n",
            "standalone_integral_sheaf_torsion.py",
            "FLOAT_LITERAL",
        ),
        (
            "inquisitor_float_ban",
            "from __future__ import annotations\nx = " + "fl" + "oat(1)\n",
            "inquisitor/svg_auditor.py",
            "FLOAT_IDENTIFIER",
        ),
        (
            "svg_atlas_external_import_ban",
            "from __future__ import annotations\nimport matplotlib\n",
            "simulator/svg_atlas.py",
            "FORBIDDEN_EXTERNAL_IMPORT",
        ),
        (
            "hardcoded_user_path_ban",
            "from __future__ import annotations\np = '" + HARDCODED_USERS_PREFIX + "someone/proj'\n",
            "architect/track_a_foundations.py",
            "HARDCODED_WORKSPACE_PATH",
        ),
    ]

    passed = 0
    details: list[dict[str, Any]] = []
    for name, snippet, fake_path, expected_rule in cases:
        res = scan_source_string(snippet, fake_path)
        rules_hit = [v["rule"] for v in res["violations"]]
        if expected_rule is None:
            ok = len(rules_hit) == 0
        else:
            ok = expected_rule in rules_hit
        if ok:
            passed += 1
        details.append({
            "case": name,
            "expected_rule": expected_rule or "CLEAN",
            "rules_hit": rules_hit,
            "passed": ok,
        })
        if not ok:
            raise AssertionError(
                f"AST scanner self-test `{name}` failed: expected `{expected_rule}`, got `{rules_hit}`"
            )

    return {
        "total_cases": len(cases),
        "passed_cases": passed,
        "status": "PASS",
        "details": details,
    }


def assert_clean_workspace(root_path: str = WORKSPACE_ROOT) -> dict[str, Any]:
    """Run self-tests and workspace AST scan; raise AssertionError if any violation exists."""
    run_scanner_self_tests()
    report = scan_workspace(root_path)
    if report["status"] != "PASS":
        formatted = "\n".join(
            f"  - {v['file']}:{v['line']}:{v['col']} [{v['rule']}] {v['detail']}"
            for v in report["violations"]
        )
        raise AssertionError(f"AST Contraband & Firewall Audit FAILED ({report['total_violations']} violations):\n{formatted}")
    return report


def main(argv: list[str] | None = None) -> int:
    signal.alarm(20)
    try:
        args = argv if argv is not None else sys.argv[1:]
        target_root = args[0] if len(args) >= 1 else WORKSPACE_ROOT
        self_test_report = run_scanner_self_tests()
        report = scan_workspace(target_root)
        report["self_tests"] = {
            "total_cases": self_test_report["total_cases"],
            "passed_cases": self_test_report["passed_cases"],
            "status": self_test_report["status"],
        }
        print(json.dumps(report, indent=2))
        return 0 if report["status"] == "PASS" else 1
    finally:
        signal.alarm(0)


if __name__ == "__main__":
    raise SystemExit(main())
