from __future__ import annotations

"""Wave II (v2.0) 10-SVG Publication Visual Atlas Generator (`simulator/svg_atlas.py`).

Generates all 10 required `1400x900` (`viewBox="0 0 1400 900"`) multi-panel mathematical SVGs
inside `plots/`:
  1. `fig01_paramid_torsion_and_join_dichotomy.svg`
  2. `fig02_max6_syl2_padic_frontier.svg`
  3. `fig03_klein_sail_cg_split.svg`
  4. `fig04_five_ray_unbounded_chvatal_rank.svg`
  5. `fig05_reeve_polar_bss_torsion.svg`
  6. `fig06_airy_spiderweb_and_chord_annulus.svg`
  7. `fig07_2d_precision_bockstein_snf.svg`
  8. `fig08_group_circuit_compression_and_q8_cocycle.svg`
  9. `fig09_proper_coset_snf_trichotomy.svg`
 10. `fig10_escher_waterfall_and_mobius_torsion.svg`

Strict Constitutional & `@inquisitor` Compliance:
- 100% Python 3.9+ stdlib only (`from __future__ import annotations`).
- 100% `float`-free, `Fraction`-free, `ast.Div`-free (`/`), and `isinstance`-free:
  all SVG coordinates and bounding-box checks use exact integer (`int`) arithmetic!
- Two-layer z-order architecture (all geometric primitives emitted BEFORE all `<text>` labels)
  guaranteeing zero shape-over-text occlusion, paired with an exact `100x`-scaled integer
  bounding-box & Liang-Barsky segment self-auditor enforcing `OOB == 0` and `overlaps == 0`.
"""

from dataclasses import dataclass
import html
import json
import math
import os
from pathlib import Path
import signal
import sys
import time
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple
import xml.etree.ElementTree as ET

_SIM_DIR = str(Path(__file__).resolve().parent)
_ROOT_DIR = str(Path(__file__).resolve().parent.parent)
_PLOTS_DIR = os.path.join(_ROOT_DIR, "plots")

VIEW_W = 1400
VIEW_H = 900
SAFE_MIN_X = 20
SAFE_MIN_Y = 16
SAFE_MAX_X = 1380
SAFE_MAX_Y = 886

FONT_SANS = "Helvetica, Arial, sans-serif"
FONT_MONO = "Menlo, Consolas, monospace"

# Observatory Academic Color Palette
COL_BG = "#F8FAFC"
COL_HEADER = "#0F172A"
COL_HEADER_SUB = "#CBD5E1"
COL_FOOTER_BG = "#EEF2F6"
COL_PANEL_BG = "#FFFFFF"
COL_PANEL_HDR = "#F1F5F9"
COL_BORDER = "#CBD5E1"
COL_HAIRLINE = "#E2E8F0"
COL_INK = "#0F172A"
COL_SLATE = "#334155"
COL_MUTED = "#64748B"

COL_INDIGO = "#1E3A8A"
COL_INDIGO_FILL = "#DBEAFE"
COL_BLUE = "#2563EB"
COL_BLUE_SOFT = "#EFF6FF"
COL_TEAL = "#0D9488"
COL_TEAL_DARK = "#0F766E"
COL_TEAL_FILL = "#CCFBF1"
COL_TEAL_SOFT = "#F0FDFA"
COL_EMERALD = "#059669"
COL_EMERALD_FILL = "#D1FAE5"
COL_AMBER = "#D97706"
COL_AMBER_FILL = "#FEF3C7"
COL_AMBER_SOFT = "#FFFBEB"
COL_CRIMSON = "#DC2626"
COL_CRIMSON_FILL = "#FEE2E2"
COL_CRIMSON_SOFT = "#FEF2F2"
COL_VIOLET = "#7C3AED"
COL_VIOLET_FILL = "#EDE9FE"
COL_VIOLET_SOFT = "#F5F3FF"

# Clean parameterization of Sprint A2b/A2c frontier metrics synchronized 1-to-1 with checkpoint_a2_wave2.json!
A2_FRONTIER_CONFIG: Dict[str, Any] = {
    "d6_orbits": 11,
    "d6_total_gates": 105,
    "d6_l1_gates": 6,
    "d6_l2_gates": 99,
    "s6_chambers": 720,
    "syl2_order": 16,
    "syl2_orbits": 45,
    "leaf_subchambers": 13944,
    "syl2_solve_ms": 13,
    "pairwise_m2_shape": "945 x 615",
    "impostor_47ray_den": 512,
    "impostor_refuter_pt": "(0,4,6,10,25,40)",
    "tier0_d6_status": "UNSAT_MOD3 (11 orbits, p=3: v_3=1 > 0)",
    "tier1_4plus2_label": "Tier 1: 4+2 Bakaev (2,2) [321 Orbits, 362 Rows]",
    "tier1_status": "CERTIFIED_EXACT UNSAT (p=3, |supp y| = 103)",
    "tier2_zonotope_label": "Tier 2: Small-Coeff (2,2)+(3,1)+(4,0) [364 Orbits]",
    "tier2_status": "CERTIFIED_EXACT UNSAT (p=3, |supp y| = 118)",
    "tier3_signed_label": "Tier 3: Non-Convex Signed L2 ReLU(U-V) [384 Orbits]",
    "tier3_status": "CERTIFIED_EXACT UNSAT (p=3, |supp y| = 131)",
    "unconstrained_tag": "OPEN_BUDGET_EXCEEDED",
}


class SVGTimeoutError(RuntimeError):
    pass


def _alarm_handler(signum: int, frame: Any) -> None:
    _ = frame
    raise SVGTimeoutError(f"SVG Atlas generation exceeded 20s timeout (signal {signum})")


# ---------------------------------------------------------------------------
# Exact `100x`-Scaled Integer Bounding-Box & Zero-Collision Canvas Engine
# ---------------------------------------------------------------------------

_NARROW_SET = frozenset("ilI1.,:;!|'()[]{} `")
_WIDE_SET = frozenset("MWmw@%#&QGO0")


def _text_width_100(text: str, font_size: int, is_mono: bool) -> int:
    """Conservative `100x` pixel width upper-bounding both `0.62*F*N` and `inquisitor/svg_auditor.py`."""
    norm = " ".join(text.split())
    if not norm:
        return 0
    if is_mono:
        w_aud = 60 * font_size * len(norm)
    else:
        acc_20 = 0
        for ch in norm:
            if ch in _NARROW_SET:
                acc_20 += 7
            elif ch in _WIDE_SET or ord(ch) > 127:
                acc_20 += 13
            else:
                acc_20 += 11
        w_aud = acc_20 * 5 * font_size
    w_cons = 62 * font_size * len(norm)
    return w_aud if w_aud >= w_cons else w_cons


@dataclass(frozen=True)
class _ShapeAuditRec:
    shape_id: str
    kind: str  # "rect" | "circle" | "line" | "poly" | "path"
    oob_box100: Tuple[int, int, int, int]
    inner_rect100: Optional[Tuple[int, int, int, int]]
    circle100: Optional[Tuple[int, int, int, int]]  # (cx100, cy100, r100, pad100)
    segments100: Tuple[Tuple[Tuple[int, int], Tuple[int, int]], ...]
    pad100: int
    is_closed: bool


@dataclass(frozen=True)
class _TextAuditRec:
    text_id: str
    content: str
    box100: Tuple[int, int, int, int]


def _boxes_overlap_closed(a: Tuple[int, int, int, int], b: Tuple[int, int, int, int]) -> bool:
    x0 = a[0] if a[0] >= b[0] else b[0]
    y0 = a[1] if a[1] >= b[1] else b[1]
    x1 = a[2] if a[2] <= b[2] else b[2]
    y1 = a[3] if a[3] <= b[3] else b[3]
    return x0 <= x1 and y0 <= y1


def _seg_hits_box100(
    seg: Tuple[Tuple[int, int], Tuple[int, int]],
    box: Tuple[int, int, int, int],
) -> bool:
    """Exact pure-`int` cross-multiplied Liang-Barsky segment-vs-box intersection check."""
    (x0, y0), (x1, y1) = seg
    bx0, by0, bx1, by1 = box
    dx = x1 - x0
    dy = y1 - y0
    # Represent t_min = n_min / d_min, t_max = n_max / d_max with positive denominators
    n_min, d_min = 0, 1
    n_max, d_max = 1, 1
    for p_val, q_val in ((-dx, x0 - bx0), (dx, bx1 - x0), (-dy, y0 - by0), (dy, by1 - y0)):
        if p_val == 0:
            if q_val < 0:
                return False
        elif p_val < 0:
            rn, rd = -q_val, -p_val
            if rn * d_max > n_max * rd:
                return False
            if rn * d_min > n_min * rd:
                n_min, d_min = rn, rd
        else:
            rn, rd = q_val, p_val
            if rn * d_min < n_min * rd:
                return False
            if rn * d_max < n_max * rd:
                n_max, d_max = rn, rd
    return n_min * d_max <= n_max * d_min


class SVGCanvas:
    """Strict 0-float SVG builder with two-pass non-occluding z-order and built-in collision verifier."""

    def __init__(self, filename: str, title: str, subtitle: str, footer: str) -> None:
        self.filename = filename
        self.shape_elems: List[str] = []
        self.text_elems: List[str] = []
        self.shape_recs: List[_ShapeAuditRec] = []
        self.text_recs: List[_TextAuditRec] = []
        self._counter = 0

        # Background canvas + header banner + footer provenance bar
        self.add_rect(0, 0, VIEW_W, VIEW_H, fill=COL_BG, stroke="none", stroke_width=0, role="canvas-bg", check_safe=False)
        self.add_rect(24, 18, 1352, 64, rx=10, fill=COL_HEADER, stroke="none", stroke_width=0, role="panel")
        self.add_text(44, 46, title, size=19, weight="bold", fill="#F8FAFC", anchor="start")
        self.add_text(44, 69, subtitle, size=12, weight="normal", fill=COL_HEADER_SUB, anchor="start", mono=True)

        self.add_rect(24, 852, 1352, 30, rx=6, fill=COL_FOOTER_BG, stroke=COL_BORDER, stroke_width=1, role="panel")
        self.add_text(40, 871, footer, size=11, weight="normal", fill=COL_SLATE, anchor="start", mono=True)

    def _next_id(self, prefix: str) -> str:
        self._counter += 1
        return f"{prefix}_{self._counter}"

    def add_panel(self, x: int, y: int, w: int, h: int, heading: str, badge: str = "", badge_fill: str = COL_INDIGO_FILL, badge_ink: str = COL_INDIGO) -> None:
        """Draw an academic observatory panel card with header strip and optional right-aligned status pill."""
        self.add_rect(x, y, w, h, rx=10, fill=COL_PANEL_BG, stroke=COL_BORDER, stroke_width=2, role="panel")
        self.add_rect(x + 2, y + 2, w - 4, 38, rx=8, fill=COL_PANEL_HDR, stroke="none", stroke_width=0, role="panel")
        self.add_line(x + 2, y + 40, x + w - 2, y + 40, stroke=COL_BORDER, stroke_width=1)
        self.add_text(x + 16, y + 26, heading, size=13, weight="bold", fill=COL_INK, anchor="start")
        if badge:
            bw = ((62 * 11 * len(badge)) // 100) + 24
            bx = x + w - bw - 14
            self.add_rect(bx, y + 8, bw, 24, rx=6, fill=badge_fill, stroke="none", stroke_width=0, role="badge-bg")
            self.add_text(bx + (bw // 2), y + 24, badge, size=11, weight="bold", fill=badge_ink, anchor="middle", mono=True)

    def add_badge(
        self,
        x: int,
        y: int,
        w: int,
        h: int,
        label: str,
        fill: str = COL_BLUE_SOFT,
        stroke: str = COL_BLUE,
        ink: str = COL_INDIGO,
        size: int = 12,
        mono: bool = True,
        bold: bool = True,
    ) -> None:
        self.add_rect(x, y, w, h, rx=6, fill=fill, stroke=stroke, stroke_width=1, role="badge-bg")
        ty = y + (h // 2) + (size // 3)
        self.add_text(x + (w // 2), ty, label, size=size, weight="bold" if bold else "normal", fill=ink, anchor="middle", mono=mono)

    def add_callout_card(
        self,
        x: int,
        y: int,
        w: int,
        h: int,
        title: str,
        lines: Sequence[str],
        fill: str = "#F8FAFC",
        stroke: str = COL_BORDER,
        title_ink: str = COL_INDIGO,
        body_ink: str = COL_SLATE,
        size: int = 11,
        line_step: int = 18,
        mono_body: bool = True,
    ) -> None:
        self.add_rect(x, y, w, h, rx=8, fill=fill, stroke=stroke, stroke_width=1, role="panel")
        self.add_text(x + 14, y + 22, title, size=size + 1, weight="bold", fill=title_ink, anchor="start")
        for idx, ln in enumerate(lines):
            self.add_text(x + 14, y + 42 + idx * line_step, ln, size=size, fill=body_ink, anchor="start", mono=mono_body)

    def add_rect(
        self,
        x: int,
        y: int,
        w: int,
        h: int,
        fill: str = COL_PANEL_BG,
        stroke: str = COL_BORDER,
        stroke_width: int = 1,
        rx: int = 0,
        role: str = "shape",
        check_safe: bool = True,
    ) -> str:
        sid = self._next_id("rect")
        rx_attr = f' rx="{rx}"' if rx > 0 else ""
        sw_attr = f' stroke-width="{stroke_width}"' if stroke != "none" and stroke_width > 0 else ""
        role_attr = f' data-role="{role}"' if role else ""
        self.shape_elems.append(
            f'  <rect id="{sid}" x="{x}" y="{y}" width="{w}" height="{h}"{rx_attr} fill="{fill}" stroke="{stroke}"{sw_attr}{role_attr} />'
        )
        pad100 = (stroke_width * 50) if (stroke != "none" and stroke_width > 0) else 0
        oob = (x * 100 - pad100, y * 100 - pad100, (x + w) * 100 + pad100, (y + h) * 100 + pad100)
        if not check_safe:
            oob = (0, 0, VIEW_W * 100, VIEW_H * 100)
        inner = (x * 100 + pad100, y * 100 + pad100, (x + w) * 100 - pad100, (y + h) * 100 - pad100)
        c0, c1, c2, c3 = (x * 100, y * 100), ((x + w) * 100, y * 100), ((x + w) * 100, (y + h) * 100), (x * 100, (y + h) * 100)
        self.shape_recs.append(
            _ShapeAuditRec(
                shape_id=sid,
                kind="rect",
                oob_box100=oob,
                inner_rect100=inner,
                circle100=None,
                segments100=((c0, c1), (c1, c2), (c2, c3), (c3, c0)),
                pad100=pad100,
                is_closed=True,
            )
        )
        return sid

    def add_circle(
        self,
        cx: int,
        cy: int,
        r: int,
        fill: str = COL_BLUE,
        stroke: str = "#FFFFFF",
        stroke_width: int = 2,
        dash: str = "",
    ) -> str:
        sid = self._next_id("circ")
        sw_attr = f' stroke-width="{stroke_width}"' if stroke != "none" and stroke_width > 0 else ""
        dash_attr = f' stroke-dasharray="{dash}"' if dash else ""
        self.shape_elems.append(
            f'  <circle id="{sid}" cx="{cx}" cy="{cy}" r="{r}" fill="{fill}" stroke="{stroke}"{sw_attr}{dash_attr} />'
        )
        pad100 = (stroke_width * 50) if (stroke != "none" and stroke_width > 0) else 0
        oob = ((cx - r) * 100 - pad100, (cy - r) * 100 - pad100, (cx + r) * 100 + pad100, (cy + r) * 100 + pad100)
        self.shape_recs.append(
            _ShapeAuditRec(
                shape_id=sid,
                kind="circle",
                oob_box100=oob,
                inner_rect100=None,
                circle100=(cx * 100, cy * 100, r * 100, pad100),
                segments100=(),
                pad100=pad100,
                is_closed=True,
            )
        )
        return sid

    def add_line(
        self,
        x1: int,
        y1: int,
        x2: int,
        y2: int,
        stroke: str = COL_SLATE,
        stroke_width: int = 2,
        dash: str = "",
    ) -> str:
        sid = self._next_id("line")
        dash_attr = f' stroke-dasharray="{dash}"' if dash else ""
        self.shape_elems.append(
            f'  <line id="{sid}" x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{stroke}" stroke-width="{stroke_width}"{dash_attr} />'
        )
        pad100 = stroke_width * 50
        oob = (
            min(x1, x2) * 100 - pad100,
            min(y1, y2) * 100 - pad100,
            max(x1, x2) * 100 + pad100,
            max(y1, y2) * 100 + pad100,
        )
        self.shape_recs.append(
            _ShapeAuditRec(
                shape_id=sid,
                kind="line",
                oob_box100=oob,
                inner_rect100=None,
                circle100=None,
                segments100=(((x1 * 100, y1 * 100), (x2 * 100, y2 * 100)),),
                pad100=pad100,
                is_closed=False,
            )
        )
        return sid

    def add_arrow(
        self,
        x1: int,
        y1: int,
        x2: int,
        y2: int,
        stroke: str = COL_SLATE,
        stroke_width: int = 2,
        head_len: int = 9,
        head_half: int = 4,
        dash: str = "",
    ) -> None:
        """Draw an exact integer line + filled triangular arrowhead without `<marker>` OOB quirks."""
        self.add_line(x1, y1, x2, y2, stroke=stroke, stroke_width=stroke_width, dash=dash)
        dx = x2 - x1
        dy = y2 - y1
        dist_sq = dx * dx + dy * dy
        if dist_sq == 0:
            return
        dist = math.isqrt(dist_sq)
        if dist == 0:
            return
        bx = x2 - (dx * head_len) // dist
        by = y2 - (dy * head_len) // dist
        px = (-dy * head_half) // dist
        py = (dx * head_half) // dist
        self.add_polygon([(x2, y2), (bx + px, by + py), (bx - px, by - py)], fill=stroke, stroke="none", stroke_width=0)

    def add_polyline(
        self,
        pts: Sequence[Tuple[int, int]],
        stroke: str = COL_BLUE,
        stroke_width: int = 2,
        dash: str = "",
    ) -> str:
        sid = self._next_id("pline")
        pts_str = " ".join(f"{px},{py}" for px, py in pts)
        dash_attr = f' stroke-dasharray="{dash}"' if dash else ""
        self.shape_elems.append(
            f'  <polyline id="{sid}" points="{pts_str}" fill="none" stroke="{stroke}" stroke-width="{stroke_width}"{dash_attr} />'
        )
        pad100 = stroke_width * 50
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        oob = (min(xs) * 100 - pad100, min(ys) * 100 - pad100, max(xs) * 100 + pad100, max(ys) * 100 + pad100)
        segs = tuple(((pts[i][0] * 100, pts[i][1] * 100), (pts[i + 1][0] * 100, pts[i + 1][1] * 100)) for i in range(len(pts) - 1))
        self.shape_recs.append(
            _ShapeAuditRec(
                shape_id=sid,
                kind="poly",
                oob_box100=oob,
                inner_rect100=None,
                circle100=None,
                segments100=segs,
                pad100=pad100,
                is_closed=False,
            )
        )
        return sid

    def add_polygon(
        self,
        pts: Sequence[Tuple[int, int]],
        fill: str = COL_BLUE_SOFT,
        stroke: str = COL_BLUE,
        stroke_width: int = 2,
        fill_opacity_pct: int = 100,
    ) -> str:
        sid = self._next_id("poly")
        pts_str = " ".join(f"{px},{py}" for px, py in pts)
        sw_attr = f' stroke-width="{stroke_width}"' if stroke != "none" and stroke_width > 0 else ""
        op_attr = ""
        if fill_opacity_pct < 100:
            # Format exact rational decimal e.g. 25 -> "0.25" using integer formatting only (zero float!)
            op_attr = f' fill-opacity="0.{fill_opacity_pct:02d}"'
        self.shape_elems.append(
            f'  <polygon id="{sid}" points="{pts_str}" fill="{fill}"{op_attr} stroke="{stroke}"{sw_attr} />'
        )
        pad100 = (stroke_width * 50) if (stroke != "none" and stroke_width > 0) else 0
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        oob = (min(xs) * 100 - pad100, min(ys) * 100 - pad100, max(xs) * 100 + pad100, max(ys) * 100 + pad100)
        segs_list = [((pts[i][0] * 100, pts[i][1] * 100), (pts[i + 1][0] * 100, pts[i + 1][1] * 100)) for i in range(len(pts) - 1)]
        if pts[-1] != pts[0]:
            segs_list.append(((pts[-1][0] * 100, pts[-1][1] * 100), (pts[0][0] * 100, pts[0][1] * 100)))
        self.shape_recs.append(
            _ShapeAuditRec(
                shape_id=sid,
                kind="poly",
                oob_box100=oob,
                inner_rect100=None,
                circle100=None,
                segments100=tuple(segs_list),
                pad100=pad100,
                is_closed=True,
            )
        )
        return sid

    def add_cubic_bezier(
        self,
        p0: Tuple[int, int],
        p1: Tuple[int, int],
        p2: Tuple[int, int],
        p3: Tuple[int, int],
        stroke: str = COL_VIOLET,
        stroke_width: int = 2,
        dash: str = "",
    ) -> str:
        sid = self._next_id("bez")
        dash_attr = f' stroke-dasharray="{dash}"' if dash else ""
        d_str = f"M {p0[0]} {p0[1]} C {p1[0]} {p1[1]}, {p2[0]} {p2[1]}, {p3[0]} {p3[1]}"
        self.shape_elems.append(
            f'  <path id="{sid}" d="{d_str}" fill="none" stroke="{stroke}" stroke-width="{stroke_width}"{dash_attr} />'
        )
        pad100 = stroke_width * 50
        xs = [p0[0], p1[0], p2[0], p3[0]]
        ys = [p0[1], p1[1], p2[1], p3[1]]
        oob = (min(xs) * 100 - pad100, min(ys) * 100 - pad100, max(xs) * 100 + pad100, max(ys) * 100 + pad100)
        # Approximate curve conservatively by 8 de-Casteljau chords + control hull check
        pts8: List[Tuple[int, int]] = []
        for step in range(9):
            # Exact Bernstein evaluation at t = step / 8 (denom 8^3 = 512)
            u = 8 - step
            t = step
            b0 = u * u * u
            b1 = 3 * u * u * t
            b2 = 3 * u * t * t
            b3 = t * t * t
            qx = (b0 * p0[0] * 100 + b1 * p1[0] * 100 + b2 * p2[0] * 100 + b3 * p3[0] * 100) // 512
            qy = (b0 * p0[1] * 100 + b1 * p1[1] * 100 + b2 * p2[1] * 100 + b3 * p3[1] * 100) // 512
            pts8.append((qx, qy))
        segs = tuple((pts8[i], pts8[i + 1]) for i in range(8))
        self.shape_recs.append(
            _ShapeAuditRec(
                shape_id=sid,
                kind="path",
                oob_box100=oob,
                inner_rect100=None,
                circle100=None,
                segments100=segs,
                pad100=pad100 + 200,
                is_closed=False,
            )
        )
        return sid

    def add_text(
        self,
        x: int,
        y: int,
        text: str,
        size: int = 12,
        weight: str = "normal",
        fill: str = COL_INK,
        anchor: str = "start",
        mono: bool = False,
    ) -> str:
        tid = self._next_id("txt")
        fam = FONT_MONO if mono else FONT_SANS
        esc = html.escape(text, quote=False)
        wt_attr = f' font-weight="{weight}"' if weight != "normal" else ""
        self.text_elems.append(
            f'  <text id="{tid}" x="{x}" y="{y}" font-family="{fam}" font-size="{size}"{wt_attr} text-anchor="{anchor}" fill="{fill}">{esc}</text>'
        )
        w100 = _text_width_100(text, size, mono)
        bx100 = x * 100
        by100 = y * 100
        if anchor == "middle":
            x0 = bx100 - (w100 // 2)
            x1 = bx100 + ((w100 + 1) // 2)
        elif anchor == "end":
            x0 = bx100 - w100
            x1 = bx100
        else:
            x0 = bx100
            x1 = bx100 + w100
        # Conservative vertical bounds strictly enclosing `svg_auditor` [-0.75*F, +0.20*F]
        y0 = by100 - 78 * size
        y1 = by100 + 24 * size
        self.text_recs.append(_TextAuditRec(text_id=tid, content=text, box100=(x0, y0, x1, y1)))
        return tid

    def audit_self(self) -> Dict[str, Any]:
        """Run strict `100x` integer OOB & collision checks (`0` OOB inside `[0,1400]x[0,900]`, `0` overlaps)."""
        oob_errs: List[str] = []
        ov_errs: List[str] = []

        for srec in self.shape_recs:
            x0, y0, x1, y1 = srec.oob_box100
            if x0 < 0 or y0 < 0 or x1 > VIEW_W * 100 or y1 > VIEW_H * 100:
                oob_errs.append(f"Shape OOB {srec.shape_id}: {srec.oob_box100}")

        for trec in self.text_recs:
            x0, y0, x1, y1 = trec.box100
            if x0 < SAFE_MIN_X * 100 or y0 < SAFE_MIN_Y * 100 or x1 > SAFE_MAX_X * 100 or y1 > SAFE_MAX_Y * 100:
                oob_errs.append(f"Text OOB {trec.text_id} ({trec.content!r}): {trec.box100}")

        # Text-to-text collisions
        nt = len(self.text_recs)
        for i in range(nt):
            ta = self.text_recs[i]
            for j in range(i + 1, nt):
                tb = self.text_recs[j]
                if _boxes_overlap_closed(ta.box100, tb.box100):
                    ov_errs.append(f"Text-Text overlap: {ta.content!r} {ta.box100} vs {tb.content!r} {tb.box100}")

        # Text-to-shape collisions (matching & slightly strengthening `inquisitor/svg_auditor.py`)
        margin100 = 250  # 2.5px > 2.0px requirement
        for trec in self.text_recs:
            tx0, ty0, tx1, ty1 = trec.box100
            for srec in self.shape_recs:
                if not _boxes_overlap_closed(trec.box100, srec.oob_box100):
                    continue
                if srec.kind == "rect" and srec.inner_rect100 is not None:
                    ix0, iy0, ix1, iy1 = srec.inner_rect100
                    if ix0 + margin100 <= tx0 and tx1 <= ix1 - margin100 and iy0 + margin100 <= ty0 and ty1 <= iy1 - margin100:
                        continue
                    ov_errs.append(f"Text-Rect collision: {trec.content!r} {trec.box100} vs {srec.shape_id} {srec.inner_rect100}")
                elif srec.kind == "circle" and srec.circle100 is not None:
                    cx, cy, r, pad = srec.circle100
                    qx = min(max(cx, tx0), tx1)
                    qy = min(max(cy, ty0), ty1)
                    d_min_sq = (qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)
                    r_out = r + pad + 100
                    if d_min_sq > r_out * r_out:
                        continue
                    dx_f = max(abs(tx0 - cx), abs(tx1 - cx))
                    dy_f = max(abs(ty0 - cy), abs(ty1 - cy))
                    r_in = r - pad - margin100
                    if r_in > 0 and (dx_f * dx_f + dy_f * dy_f) <= r_in * r_in:
                        continue
                    ov_errs.append(f"Text-Circle collision: {trec.content!r} vs {srec.shape_id}")
                else:
                    sp = srec.pad100 + (margin100 if srec.is_closed else 100)
                    pbox = (tx0 - sp, ty0 - sp, tx1 + sp, ty1 + sp)
                    for seg in srec.segments100:
                        if _seg_hits_box100(seg, pbox):
                            ov_errs.append(f"Text-{srec.kind} segment collision: {trec.content!r} {trec.box100} vs {srec.shape_id} {seg}")
                            break

        if oob_errs or ov_errs:
            detail = "; ".join((oob_errs + ov_errs)[:8])
            raise AssertionError(f"[{self.filename}] Self-audit FAILED (OOB={len(oob_errs)}, OV={len(ov_errs)}): {detail}")

        xml_out = self.render_xml()
        ET.fromstring(xml_out)
        return {
            "file": self.filename,
            "shape_count": len(self.shape_recs),
            "text_count": len(self.text_recs),
            "oob_count": 0,
            "overlap_count": 0,
            "status": "PASS",
        }

    def render_xml(self) -> str:
        lines = [
            f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {VIEW_W} {VIEW_H}" width="{VIEW_W}" height="{VIEW_H}">',
            '  <g id="layer_shapes">',
        ]
        lines.extend(self.shape_elems)
        lines.append("  </g>")
        lines.append('  <g id="layer_labels">')
        lines.extend(self.text_elems)
        lines.append("  </g>")
        lines.append("</svg>")
        return "\n".join(lines) + "\n"

    def save(self, out_dir: str) -> Dict[str, Any]:
        audit = self.audit_self()
        os.makedirs(out_dir, exist_ok=True)
        out_path = os.path.join(out_dir, self.filename)
        with open(out_path, "w", encoding="utf-8") as fh:
            fh.write(self.render_xml())
        return audit


# ---------------------------------------------------------------------------
# Figure 01: Paramid Torsion Staircase & Join-Volume Arithmetic Dichotomy
# ---------------------------------------------------------------------------

def build_fig01() -> SVGCanvas:
    cv = SVGCanvas(
        "fig01_paramid_torsion_and_join_dichotomy.svg",
        "Fig 01 — Join-Volume GCD Staircase, (2,2) Escape & Arrangement Quotient SNF",
        "Track A (Theorems A1, A2a, A2c, A3) | G_3=1, G_4=2, G_5=2, G_6=12 & Finite-Arrangement Paramid vs Zonotope SNFs",
        "Certified Exact | d=5: (4,0)->24, (3,1)->6, (2,2)->4 == 1 mod 3 | d=6: 120,24,12 == 0 mod 6 | H_4, H_5^{D_4}, H_6^{D_6} SNFs",
    )

    # Panel A (Left): Kummer Prime-Power Product GCD & MAX_n Annihilator Staircase
    cv.add_panel(24, 96, 660, 744, "A. Kummer Product GCD & MAX_n Annihilator Staircase", "THEOREMS A1 & A3", COL_INDIGO_FILL, COL_INDIGO)

    # Bar chart of Kummer gcd_{1<=a<d} binom(d,a) for d = 2..10 (MAX_3..MAX_11)
    ax_x0, ax_y0, ax_x1, ax_y1 = 88, 430, 650, 175
    cv.add_line(ax_x0, ax_y0, ax_x1, ax_y0, stroke=COL_SLATE, stroke_width=2)
    cv.add_line(ax_x0, ax_y1, ax_x0, ax_y0, stroke=COL_SLATE, stroke_width=2)
    cv.add_text(52, 162, "Kummer gcd", size=11, weight="bold", fill=COL_SLATE)

    for g_val in (1, 2, 3, 5, 7):
        gy = ax_y0 - g_val * 32
        cv.add_line(ax_x0 - 5, gy, ax_x0, gy, stroke=COL_SLATE, stroke_width=1)
        cv.add_text(ax_x0 - 10, gy + 4, str(g_val), size=11, fill=COL_SLATE, anchor="end", mono=True)

    kummer_data = [
        (2, "MAX_3", 2, "2^1", COL_BLUE_SOFT, COL_BLUE),
        (3, "MAX_4", 3, "3^1", COL_TEAL_FILL, COL_TEAL),
        (4, "MAX_5", 2, "2^2", COL_CRIMSON_FILL, COL_CRIMSON),
        (5, "MAX_6", 5, "5^1", COL_AMBER_FILL, COL_AMBER),
        (6, "MAX_7", 1, "comp", "#F1F5F9", COL_MUTED),
        (7, "MAX_8", 7, "7^1", COL_VIOLET_FILL, COL_VIOLET),
        (8, "MAX_9", 2, "2^3", COL_BLUE_SOFT, COL_BLUE),
        (9, "MAX_10", 3, "3^2", COL_TEAL_FILL, COL_TEAL),
        (10, "MAX_11", 1, "comp", "#F1F5F9", COL_MUTED),
    ]
    for idx, (d_val, m_lbl, kgcd, pp_lbl, bfill, bstroke) in enumerate(kummer_data):
        bx = 104 + idx * 60
        bw = 38
        bh = kgcd * 32
        by = ax_y0 - bh
        cv.add_rect(bx, by, bw, bh, rx=4, fill=bfill, stroke=bstroke, stroke_width=2)
        cv.add_text(bx + 19, by - 10, str(kgcd), size=12, weight="bold", fill=bstroke, anchor="middle", mono=True)
        cv.add_text(bx + 19, ax_y0 + 18, f"d={d_val}", size=10, weight="bold", fill=COL_INK, anchor="middle", mono=True)
        cv.add_text(bx + 19, ax_y0 + 34, m_lbl, size=9, fill=COL_MUTED, anchor="middle", mono=True)
        cv.add_text(bx + 19, ax_y0 + 48, pp_lbl, size=9, fill=bstroke, anchor="middle", mono=True)

    # Certified Annihilator & Counterexample Cards in bottom half of Panel A
    cv.add_callout_card(
        46, 498, 616, 152,
        "Certified Ring Realizations & Minkowski Support Quotient Q_n^Mink(Z)",
        [
            "n=4 (d=3): MAX_4 in ReLU_{4,2}(Z) via strict 9-neuron {-1,0,+1} net (m_4 = 1).",
            "n=5 (d=4=2^2): Vol_4(Delta_4)=1 (mod 2) => not in Z; Bakaev 9-term => m_5 = 2.",
            "n=6 (d=5): D_6 105-gate hexagon identity => 6*MAX_6 in ReLU_{6,2}(Z) (m_6 | 6).",
            "n=6 (d=5): Vol_5(Delta_2 x Delta_3) = binom(5,2) = 10 == 1 (mod 3) [not 0 mod 3!].",
            "n=10 (d=9=3^2): Prime power 3^2 restores gcd_{1<=a<=8} binom(9,a) = 3.",
        ],
        fill="#F8FAFC", stroke=COL_BORDER, title_ink=COL_INDIGO, size=10, line_step=21,
    )

    cv.add_callout_card(
        46, 666, 616, 154,
        "Virtual Zonotope-Hull Complexity Separation (Theorem A3)",
        [
            "Over Z:      vrc_{2,Z}(Delta_4) = +infinity  (every 2-layer Z-join has even Vol_4).",
            "Over Z[1/2]: vrc_{2,Z[1/2]}(Delta_4) <= 9    (2*h_{Delta_4} = P_1..4 + Q - R_{13..24}).",
            "Trap 2: Asymptotic recession N_rec(d) kills arbitrary rational biases b in Q,",
            "        preserving Vol_4(M * Delta_4) = M^4 == 1 (mod 2) for all odd M in Z_(2).",
        ],
        fill=COL_CRIMSON_SOFT, stroke=COL_CRIMSON, title_ink=COL_CRIMSON, size=11, line_step=23,
    )

    # Panel B (Right): Join-Volume Arithmetic Dichotomy (d = 3..7, Sprint A2a)
    cv.add_panel(704, 96, 672, 744, "B. Join-Volume Arithmetic Dichotomy (d = 3..7)", "THEOREM A2a", COL_TEAL_FILL, COL_TEAL_DARK)

    # Visual comparison of d = 5 (MAX_6) 3 splits vs d = 6 (MAX_7) 3 splits
    cv.add_rect(726, 152, 304, 240, rx=8, fill=COL_TEAL_SOFT, stroke=COL_TEAL, stroke_width=2, role="panel")
    cv.add_text(878, 176, "d = 5 (MAX_6): Prime 3 Escaped!", size=13, weight="bold", fill=COL_TEAL_DARK, anchor="middle")
    d5_bars = [
        ("(4,0)", 24, "0 mod 3", COL_CRIMSON_FILL, COL_CRIMSON, 112),
        ("(3,1)", 6, "0 mod 3", COL_AMBER_FILL, COL_AMBER, 44),
        ("(2,2)", 4, "1 mod 3!", COL_EMERALD_FILL, COL_EMERALD, 32),
    ]
    cv.add_line(748, 336, 1008, 336, stroke=COL_SLATE, stroke_width=2)
    for idx, (slbl, v_num, mod_lbl, bf, bs, bh) in enumerate(d5_bars):
        bx = 762 + idx * 84
        by = 336 - bh
        cv.add_rect(bx, by, 52, bh, rx=4, fill=bf, stroke=bs, stroke_width=2)
        cv.add_text(bx + 26, by - 24, f"Vol={v_num}", size=11, weight="bold", fill=bs, anchor="middle", mono=True)
        cv.add_text(bx + 26, by - 9, mod_lbl, size=10, weight="bold", fill=bs, anchor="middle", mono=True)
        cv.add_text(bx + 26, 356, slbl, size=11, weight="bold", fill=COL_INK, anchor="middle", mono=True)
    cv.add_text(878, 380, "Pi_1=[0,e1]+[0,e2], Pi_2=e5+[0,e3]+[0,e4]", size=10, fill=COL_TEAL_DARK, anchor="middle", mono=True)

    cv.add_rect(1048, 152, 306, 240, rx=8, fill=COL_CRIMSON_SOFT, stroke=COL_CRIMSON, stroke_width=2, role="panel")
    cv.add_text(1201, 176, "d = 6 (MAX_7): All 0 mod 6!", size=13, weight="bold", fill=COL_CRIMSON, anchor="middle")
    d6_bars = [
        ("(5,0)", 120, "0 mod 6", COL_CRIMSON_FILL, COL_CRIMSON, 116),
        ("(4,1)", 24, "0 mod 6", COL_CRIMSON_FILL, COL_CRIMSON, 56),
        ("(3,2)", 12, "0 mod 6", COL_CRIMSON_FILL, COL_CRIMSON, 36),
    ]
    cv.add_line(1070, 336, 1332, 336, stroke=COL_SLATE, stroke_width=2)
    for idx, (slbl, v_num, mod_lbl, bf, bs, bh) in enumerate(d6_bars):
        bx = 1084 + idx * 84
        by = 336 - bh
        cv.add_rect(bx, by, 52, bh, rx=4, fill=bf, stroke=bs, stroke_width=2)
        cv.add_text(bx + 26, by - 24, f"Vol={v_num}", size=11, weight="bold", fill=bs, anchor="middle", mono=True)
        cv.add_text(bx + 26, by - 9, mod_lbl, size=10, weight="bold", fill=bs, anchor="middle", mono=True)
        cv.add_text(bx + 26, 356, slbl, size=11, weight="bold", fill=COL_INK, anchor="middle", mono=True)
    cv.add_text(1201, 380, "r1+r2=5 => max>=3 => gcd(120,24,12)=12", size=10, fill=COL_CRIMSON, anchor="middle", mono=True)

    # Exact Table of Swept Splits d = 3..7 + Theorem A2c Arrangement Quotient SNFs
    tbl_x, tbl_y, tbl_w = 726, 406, 628
    cv.add_rect(tbl_x, tbl_y, tbl_w, 418, rx=8, fill="#FFFFFF", stroke=COL_BORDER, stroke_width=1, role="panel")
    cv.add_rect(tbl_x + 2, tbl_y + 2, tbl_w - 4, 32, rx=6, fill=COL_PANEL_HDR, stroke="none", stroke_width=0, role="panel")
    cv.add_text(tbl_x + 14, tbl_y + 23, "d  | MAX_{d+1} | Splits (r1,r2): r1!r2!              | G_d=GCD | Prime-3 Status", size=10, weight="bold", fill=COL_INK, mono=True)

    join_table_rows = [
        ("3", "MAX_4", "(2,0):2,  (1,1):1", "G_3=1", "ESCAPES (1 mod 6)", COL_EMERALD),
        ("4", "MAX_5", "(3,0):6,  (2,1):2", "G_4=2", "ESCAPES 3 (2 mod 3)", COL_BLUE),
        ("5", "MAX_6", "(4,0):24, (3,1):6,  (2,2):4", "G_5=2", "(2,2) ESCAPES (1 mod 3)", COL_TEAL_DARK),
        ("6", "MAX_7", "(5,0):120,(4,1):24, (3,2):12", "G_6=12", "LOCKED (all 0 mod 6)", COL_CRIMSON),
        ("7", "MAX_8", "(6,0):720,(5,1):120,(4,2):48,(3,3):36", "G_7=12", "LOCKED (all 0 mod 6)", COL_CRIMSON),
    ]
    for r_i, (dv, m_str, sp_s, g_s, st_s, st_col) in enumerate(join_table_rows):
        ry = tbl_y + 40 + r_i * 42
        row_bg = "#F8FAFC" if r_i % 2 == 0 else "#FFFFFF"
        cv.add_rect(tbl_x + 8, ry, tbl_w - 16, 34, rx=4, fill=row_bg, stroke=COL_HAIRLINE, stroke_width=1, role="panel")
        cv.add_text(tbl_x + 18, ry + 22, f"{dv}  | {m_str:7s} | {sp_s:37s} | {g_s:7s} |", size=10, fill=COL_INK, mono=True)
        cv.add_text(tbl_x + 448, ry + 22, st_s, size=10, weight="bold", fill=st_col, mono=True)

    cv.add_callout_card(
        736, 658, 608, 154,
        "Theorem A2c — Finite-Arrangement SNF: Pure Paramids -> Zonotope-Pair Span",
        [
            "H_4 (48 ch, rk 27):  [1^22, 2^5] (MAX_4 den=2)  -> [1^24, 2^3]   (Z-SAT, den=1!)",
            "H_5^{D_4} (480 ch):  [1^13, 4]   (MAX_5 Q-UNSAT)-> [1^16, 2]     (Z[1/2]-SAT, den=2!)",
            "H_6^{D_6} (hexagon): [1^26, 2]   (MAX_6 Q-UNSAT)-> [1^34, 2,2,6] (Z[1/6]-SAT, den=6!)",
            "H_6^{S_6} (canon.):  [1^10,3,12] (rk 12)        -> [1^14,2,2,6,6,60,180] (rk 20)",
        ],
        fill=COL_INDIGO_FILL, stroke=COL_INDIGO, title_ink=COL_INDIGO, size=10, line_step=24,
    )
    return cv


# ---------------------------------------------------------------------------
# Figure 02: MAX_6 D_6 105-Gate Identity vs Syl_2(S_6) 3-Adic Frontier
# ---------------------------------------------------------------------------

def build_fig02(cfg: Optional[Dict[str, Any]] = None) -> SVGCanvas:
    c = dict(A2_FRONTIER_CONFIG)
    if cfg is not None:
        c.update(cfg)

    cv = SVGCanvas(
        "fig02_max6_syl2_padic_frontier.svg",
        "Fig 02 — D_6 105-Gate 6*MAX_6 Identity vs Syl_2(S_6) 45-Orbit 3-Adic Frontier",
        "Track A (Theorems A2, A2b, A2c) | Regular Z_6 Hexagon Pairwise-Max Orbits & Sylow-2 Local-Global Engine",
        f"Certified Exact: 6*MAX_6 in ReLU_{{6,2}}(Z) ({c['leaf_subchambers']} leaf cones) | Syl_2(S_6) ({c['syl2_orbits']} orbits) solves in ~{c['syl2_solve_ms']} ms",
    )

    # Panel A (Left): Regular Z_6 Hexagon 15 Pairwise Maxima & 11-Orbit Formula
    cv.add_panel(24, 96, 656, 744, "A. D_6 Hexagon 15 Pairwise Maxima & 105-Gate Identity", "6 * MAX_6 IN Z", COL_EMERALD_FILL, COL_EMERALD)

    # Hexagon center (352, 316), radius ~ 130 using exact integer coords:
    # v0=(352,186), v1=(465,251), v2=(465,381), v3=(352,446), v4=(239,381), v5=(239,251)
    hex_pts = [(352, 186), (465, 251), (465, 381), (352, 446), (239, 381), (239, 251)]
    # 3 long diagonals (teal dashed)
    for i in range(3):
        cv.add_line(hex_pts[i][0], hex_pts[i][1], hex_pts[i + 3][0], hex_pts[i + 3][1], stroke=COL_TEAL, stroke_width=2, dash="6,4")
    # 6 short diagonals (royal blue)
    for i in range(6):
        j = (i + 2) % 6
        if i < j:
            cv.add_line(hex_pts[i][0], hex_pts[i][1], hex_pts[j][0], hex_pts[j][1], stroke=COL_BLUE, stroke_width=2)
    # 6 outer edges (crimson thick, L1 weight = -2)
    for i in range(6):
        j = (i + 1) % 6
        cv.add_line(hex_pts[i][0], hex_pts[i][1], hex_pts[j][0], hex_pts[j][1], stroke=COL_CRIMSON, stroke_width=4)

    for px, py in hex_pts:
        cv.add_circle(px, py, 8, fill=COL_HEADER, stroke="#FFFFFF", stroke_width=2)

    # Exterior vertex labels strictly outside the hexagon with generous clearance
    lbl_pos = [
        (352, 166, "x_0", "middle"),
        (486, 250, "x_1", "start"),
        (486, 392, "x_2", "start"),
        (352, 474, "x_3", "middle"),
        (218, 392, "x_4", "end"),
        (218, 250, "x_5", "end"),
    ]
    for lx, ly, ltxt, lanc in lbl_pos:
        cv.add_text(lx, ly, ltxt, size=13, weight="bold", fill=COL_INK, anchor=lanc, mono=True)

    # Legend badges beside/below hexagon
    cv.add_badge(56, 494, 186, 30, "6 Edges: m_{i,i+1} (w=-2)", fill=COL_CRIMSON_FILL, stroke=COL_CRIMSON, ink=COL_CRIMSON, size=10)
    cv.add_badge(256, 494, 196, 30, "6 Short Diags: m_{i,i+2}", fill=COL_BLUE_SOFT, stroke=COL_BLUE, ink=COL_INDIGO, size=10)
    cv.add_badge(466, 494, 190, 30, "3 Long Diags: m_{i,i+3}", fill=COL_TEAL_FILL, stroke=COL_TEAL, ink=COL_TEAL_DARK, size=10)

    cv.add_callout_card(
        46, 540, 612, 280,
        f"D_6 {c['d6_total_gates']}-Gate Identity & 47-Ray Impostor Trap Refutation",
        [
            f"D_6 Baseline ({c['d6_orbits']} orbits): -2*sum m_{{i,i+1}} + 99 paramids = 6*MAX_6 over Z",
            f"  -> Certified across {c['s6_chambers']} S_6 chambers & {c['leaf_subchambers']} leaf sub-cones!",
            f"47-Ray Impostor Trap: finite 47-ray test yields fake Z[1/2] hit (c_den={c['impostor_47ray_den']}),",
            f"  EXPOSED & REFUTED at off-braid point x* = {c['impostor_refuter_pt']}!",
            f"Full Pairwise-M2 Sub-Chamber System ({c['pairwise_m2_shape']} Syl_2 matrix):",
            "  -> Z[1/6]-SAT (den=192), while Z[1/2] is UNSAT_MOD3_PRESCREEN (p=3)!",
            "Moral: True CPWL verification MUST split all induced off-braid sub-cones.",
        ],
        fill="#F8FAFC", stroke=COL_BORDER, title_ink=COL_INDIGO, size=10, line_step=31,
    )

    # Panel B (Right): Syl_2(S_6) Compression Funnel & 3-Adic Tier Hierarchy
    cv.add_panel(700, 96, 676, 744, "B. Syl_2(S_6) 45-Orbit Hierarchy & p=3 Obstructions", "TIERS 1-3 CERTIFIED", COL_AMBER_FILL, COL_AMBER)

    # Compression funnel boxes + arrows
    cv.add_badge(724, 156, 192, 54, "S_6: 720 Chambers", fill="#F1F5F9", stroke=COL_SLATE, ink=COL_INK, size=12)
    cv.add_arrow(924, 183, 962, 183, stroke=COL_INDIGO, stroke_width=2)
    cv.add_badge(970, 156, 196, 54, "Syl_2: 45 Free Orbits", fill=COL_INDIGO_FILL, stroke=COL_INDIGO, ink=COL_INDIGO, size=12)
    cv.add_arrow(1174, 183, 1210, 183, stroke=COL_TEAL_DARK, stroke_width=2)
    cv.add_badge(1218, 156, 136, 54, "945x615 Exact", fill=COL_TEAL_FILL, stroke=COL_TEAL, ink=COL_TEAL_DARK, size=11)

    cv.add_text(1038, 232, "Syl_2(S_6) = D_4({0,1,2,3}) x C_2({4,5}), |G| = 16 = 2^4 in Z_(3)^x (zero odd-prime averaging loss!)", size=10, fill=COL_SLATE, anchor="middle", mono=True)

    # Tier cards for Sprint A2b
    tiers = [
        ("Pairwise-M2 Sub-Chamber Base (615 Syl_2 Orbits, 945 Rows)", "CERTIFIED_EXACT UNSAT (p=3, Z[1/6] den=192)", "Exposes & refutes 47-ray impostor (c_den=512) at (0,4,6,10,25,40)", COL_CRIMSON_SOFT, COL_CRIMSON),
        (c["tier1_4plus2_label"], c["tier1_status"], "4+2 Bakaev (2,2) joins (Vol_5=4 == 1 mod 3) across 362 exact rows", COL_BLUE_SOFT, COL_BLUE),
        (c["tier2_zonotope_label"], c["tier2_status"], "Primitive {-2..2}^6 (2,2)+(3,1)+(4,0) joins across 362 exact rows", COL_TEAL_SOFT, COL_TEAL_DARK),
        (c["tier3_signed_label"], c["tier3_status"], "Signed Layer-2 ReLU(U - V) differences across 362 exact rows", COL_VIOLET_SOFT, COL_VIOLET),
    ]
    for idx, (t_name, t_stat, t_desc, t_bg, t_col) in enumerate(tiers):
        cy = 252 + idx * 102
        cv.add_rect(724, cy, 628, 88, rx=8, fill=t_bg, stroke=t_col, stroke_width=2, role="panel")
        cv.add_text(740, cy + 26, t_name, size=12, weight="bold", fill=t_col, mono=False)
        cv.add_text(740, cy + 50, f"Status: {t_stat}", size=11, weight="bold", fill=COL_INK, mono=True)
        cv.add_text(740, cy + 72, t_desc, size=10, fill=COL_SLATE, mono=True)

    # Epistemic discipline card at bottom right
    cv.add_callout_card(
        724, 668, 628, 152,
        f"3-Valued Epistemic Guardrail: {c['unconstrained_tag']}",
        [
            "1. Fixed-dictionary p=3 valuation witness y (v_3(y^T A) > v_3(y^T b)) is",
            "   machine-checked as CERTIFIED_EXACT on each explicit finite gate tier.",
            "2. Unconstrained ReLU_{6,2}(Z[1/2]) over ALL off-braid hyperplanes remains",
            "   tagged OPEN_BUDGET_EXCEEDED unless a universal invariant or SAT net is proved.",
        ],
        fill=COL_AMBER_SOFT, stroke=COL_AMBER, title_ink=COL_AMBER, size=10, line_step=23,
    )
    return cv


# ---------------------------------------------------------------------------
# Figure 03: Klein Sail & Chvatal-Gomory Sequential vs Simultaneous Split
# ---------------------------------------------------------------------------

def build_fig03() -> SVGCanvas:
    cv = SVGCanvas(
        "fig03_klein_sail_cg_split.svg",
        "Fig 03 — Track B2: 4-Ray Sigma_*^(k) Fractional Vertex (6/5, 2/5), Klein Sail & CG Split",
        "Track B (Theorem B2) | Sequential Axis Gomory Rank = 2..3 vs Simultaneous Schrijver-Chvatal Rank = 1",
        "Certified Exact | w^(1)(u,t) = (-u+3t, u, 2t, 2u-t) >= (0,1,0,2) | LP Opt (6/5, 2/5) | Klein Sail {(2,1),(2,2),(3,1)}",
    )

    # Panel A (Left): Exact (u, t) Coordinate Plane for k = 1
    cv.add_panel(24, 96, 684, 744, "A. Exact (u, t) Cone & Klein Sail Hull on Sigma_*^(1)", "LP VERTEX (6/5, 2/5)", COL_INDIGO_FILL, COL_INDIGO)

    # Map u in [0, 4] -> x in [110, 630] (130 px per unit), t in [0, 3] -> y in [710, 200] (170 px per unit)
    ox, oy = 110, 710
    ux_step, ty_step = 130, 170

    def pt_ut(u_num: int, u_den: int, t_num: int, t_den: int) -> Tuple[int, int]:
        px = ox + (u_num * ux_step) // u_den
        py = oy - (t_num * ty_step) // t_den
        return (px, py)

    # Shaded LP relaxation cone P_0 clipped to u <= 4, t <= 3:
    # Active boundary 1: -u + 3t = 0 => from (6/5, 2/5) to (4, 4/3)
    # Active boundary 2: 2u - t = 2 => from (6/5, 2/5) to (5/2, 3)
    p_lp = pt_ut(6, 5, 2, 5)          # (266, 642)
    p_ray1 = pt_ut(4, 1, 4, 3)        # (630, 483)
    p_corner = pt_ut(4, 1, 3, 1)      # (630, 200)
    p_ray2 = pt_ut(5, 2, 3, 1)        # (435, 200)
    cv.add_polygon([p_lp, p_ray1, p_corner, p_ray2], fill=COL_AMBER_FILL, stroke="none", stroke_width=0, fill_opacity_pct=45)

    # Shaded Klein Sail integer hull {(u,t) in P_0 : t >= 1, u >= 2} clipped to u <= 4, t <= 3:
    # Vertices: (2,1), (3,1), (4, 4/3), (4, 3), (5/2, 3), (2, 2)
    p_21 = pt_ut(2, 1, 1, 1)          # (370, 540)
    p_31 = pt_ut(3, 1, 1, 1)          # (500, 540)
    p_22 = pt_ut(2, 1, 2, 1)          # (370, 370)
    cv.add_polygon([p_21, p_31, p_ray1, p_corner, p_ray2, p_22], fill=COL_EMERALD_FILL, stroke=COL_EMERALD, stroke_width=3, fill_opacity_pct=65)

    # Axes
    cv.add_arrow(ox, oy, 650, oy, stroke=COL_INK, stroke_width=2)
    cv.add_arrow(ox, oy, ox, 175, stroke=COL_INK, stroke_width=2)
    cv.add_text(656, oy + 5, "u", size=13, weight="bold", fill=COL_INK, mono=True)
    cv.add_text(ox - 6, 162, "t", size=13, weight="bold", fill=COL_INK, anchor="end", mono=True)

    for u_i in range(0, 5):
        tx = ox + u_i * ux_step
        cv.add_line(tx, oy, tx, oy + 6, stroke=COL_SLATE, stroke_width=2)
        cv.add_text(tx, oy + 24, str(u_i), size=11, fill=COL_SLATE, anchor="middle", mono=True)
    for t_i in range(0, 4):
        ty = oy - t_i * ty_step
        cv.add_line(ox - 6, ty, ox, ty, stroke=COL_SLATE, stroke_width=2)
        cv.add_text(ox - 14, ty + 4, str(t_i), size=11, fill=COL_SLATE, anchor="end", mono=True)

    # Active LP facet rays + sequential cuts
    cv.add_line(p_lp[0], p_lp[1], p_ray1[0], p_ray1[1], stroke=COL_CRIMSON, stroke_width=2)
    cv.add_line(p_lp[0], p_lp[1], p_ray2[0], p_ray2[1], stroke=COL_CRIMSON, stroke_width=2)
    # Cut 1: t = 1 (from u = 3/2 to u = 3)
    p_32_1 = pt_ut(3, 2, 1, 1)        # (305, 540)
    cv.add_line(140, 540, 630, 540, stroke=COL_AMBER, stroke_width=2, dash="6,4")
    # Cut 2: u = 2 (from t = 1 to t = 2)
    cv.add_line(370, 690, 370, 200, stroke=COL_BLUE, stroke_width=2, dash="6,4")

    # Integer lattice grid dots inside [1..4] x [1..3] (only where no text sits!)
    for ui in range(1, 5):
        for ti in range(1, 4):
            gx, gy = pt_ut(ui, 1, ti, 1)
            cv.add_circle(gx, gy, 4, fill=COL_MUTED, stroke="none", stroke_width=0)

    # Key vertices
    cv.add_circle(p_lp[0], p_lp[1], 7, fill=COL_CRIMSON, stroke="#FFFFFF", stroke_width=2)
    cv.add_circle(p_32_1[0], p_32_1[1], 7, fill=COL_AMBER, stroke="#FFFFFF", stroke_width=2)
    for px, py in (p_21, p_22, p_31):
        cv.add_circle(px, py, 8, fill=COL_EMERALD, stroke="#FFFFFF", stroke_width=2)

    # Clean non-overlapping exterior/interior labels (strictly away from lines!)
    cv.add_badge(132, 654, 214, 28, "LP Opt (6/5, 2/5), ||w+||=4", fill=COL_CRIMSON_FILL, stroke=COL_CRIMSON, ink=COL_CRIMSON, size=10)
    cv.add_badge(126, 496, 170, 28, "Seq R1: (3/2, 1)", fill=COL_AMBER_FILL, stroke=COL_AMBER, ink=COL_AMBER, size=10)
    cv.add_badge(446, 336, 172, 34, "Klein Sail P_I", fill="#FFFFFF", stroke=COL_EMERALD, ink=COL_EMERALD, size=12)
    cv.add_text(388, 522, "(2,1) Opt=6", size=11, weight="bold", fill=COL_EMERALD, mono=True)
    cv.add_text(514, 566, "(3,1)", size=11, weight="bold", fill=COL_EMERALD, mono=True)
    cv.add_text(386, 366, "(2,2)", size=11, weight="bold", fill=COL_EMERALD, mono=True)
    cv.add_text(136, 232, "Cut u >= 2", size=11, weight="bold", fill=COL_BLUE, mono=True)

    cv.add_text(366, 776, "Simultaneous Round 1 applies BOTH lambda^(1)=(2/5,0,0,1/5) => t>=1", size=11, fill=COL_INDIGO, anchor="middle", mono=True)
    cv.add_text(366, 798, "AND lambda^(2)=(1/5,0,0,3/5) => u>=2 in P_0^(1) -> Sim. CG Rank = 1!", size=11, weight="bold", fill=COL_EMERALD, anchor="middle", mono=True)

    # Panel B (Right): Family Sweep k = 1..10 & CG Definition Split Table
    cv.add_panel(728, 96, 648, 744, "B. CG Definition Split Across Sigma_*^(k) (k=1..10)", "SIM=1 VS SEQ=2..3", COL_AMBER_FILL, COL_AMBER)

    cv.add_callout_card(
        748, 152, 608, 138,
        "Why Simultaneous Schrijver-Chvatal = 1 While Sequential Gomory = 2..3",
        [
            "1. Jensen's inequality makes w_2 >= 1 and w_3 >= 0 redundant on P_0,",
            "   collapsing P_0 to a planar 2-facet cone of determinant D = 2k + 3.",
            "2. Every Hilbert-basis generator of the active 2-cone belongs to P_0^(1) -> Rank 1!",
            "3. Sequential axis cuts (t >= 1, then u >= k+1) leave residual fractional",
            "   vertex (k+1, 2k/(2k-1)) for ALL k >= 2, requiring a 3rd oblique cut!",
        ],
        fill="#F8FAFC", stroke=COL_BORDER, title_ink=COL_INDIGO, size=10, line_step=20,
    )

    # Table of k = 1..8
    tx, ty, tw = 748, 306, 608
    cv.add_rect(tx, ty, tw, 514, rx=8, fill="#FFFFFF", stroke=COL_BORDER, stroke_width=1, role="panel")
    cv.add_rect(tx + 2, ty + 2, tw - 4, 34, rx=6, fill=COL_PANEL_HDR, stroke="none", stroke_width=0, role="panel")
    cv.add_text(tx + 14, ty + 24, "k  | Det | LP Opt (u*, t*) | After u>=k+1   | Seq | Sim | Klein Sail", size=10, weight="bold", fill=COL_INK, mono=True)

    k_rows = [
        (1, 5, "(6/5, 2/5)", "(2,1) INT!", 2, 1, "(2,1),(2,2),(3,1)"),
        (2, 7, "(10/7, 2/7)", "(3, 4/3) FRAC", 3, 1, "(3,1),(4,2),(5,1)"),
        (3, 9, "(14/9, 2/9)", "(4, 6/5) FRAC", 3, 1, "(4,1),(6,2),(7,1)"),
        (4, 11, "(18/11, 2/11)", "(5, 8/7) FRAC", 3, 1, "(5,1),(8,2),(9,1)"),
        (5, 13, "(22/13, 2/13)", "(6, 10/9) FRAC", 3, 1, "(6,1),(10,2),(11,1)"),
        (6, 15, "(26/15, 2/15)", "(7, 12/11) FRAC", 3, 1, "(7,1),(12,2),(13,1)"),
        (8, 19, "(34/19, 2/19)", "(9, 16/15) FRAC", 3, 1, "(9,1),(16,2),(17,1)"),
        (10, 23, "(42/23, 2/23)", "(11,20/19) FRAC", 3, 1, "(11,1),(20,2),(21,1)"),
    ]
    for idx, (kv, detv, lp_s, r2_s, seq_r, sim_r, ks_s) in enumerate(k_rows):
        ry = ty + 44 + idx * 56
        bg = "#F0FDFA" if kv == 1 else ("#FFFBEB" if idx % 2 == 1 else "#F8FAFC")
        cv.add_rect(tx + 8, ry, tw - 16, 46, rx=4, fill=bg, stroke=COL_HAIRLINE, stroke_width=1, role="panel")
        cv.add_text(
            tx + 16, ry + 28,
            f"{kv:2d} | {detv:3d} | {lp_s:15s} | {r2_s:14s} |  {seq_r}  |  {sim_r}  | {ks_s}",
            size=10, fill=COL_INK, mono=True,
        )
    return cv


# ---------------------------------------------------------------------------
# Figure 04: 5-Ray Sigma_5^(k) Unbounded Simultaneous Chvatal Rank = 2k + 1
# ---------------------------------------------------------------------------

def build_fig04() -> SVGCanvas:
    cv = SVGCanvas(
        "fig04_five_ray_unbounded_chvatal_rank.svg",
        "Fig 04 — Track B2: 5-Ray Fan Sigma_5^(k) Genuine Simultaneous Chvatal Rank = 2k + 1",
        "Track B (Theorem B2) | Escaping Planar 2-Cone Collapse via dim B_Sigma = 3 in R^3 (Ranks 3, 5, 7, 9)",
        "Certified Exact | Rays (1,0), (2k+1,1), (-(2k+1),1), (-1,-2), (0,-1) | Pure Cartier w(f) = (0, 1, 0, 1, -(2k+1))",
    )

    # Panel A (Left): 5-Ray Complete Planar Fan Sigma_5^(k) Geometry
    cv.add_panel(24, 96, 628, 744, "A. 5-Ray Complete Fan Sigma_5^(k) (dim B = 3)", "ESCAPES 2D CEILING", COL_VIOLET_FILL, COL_VIOLET)

    cx, cy = 338, 340
    # Draw subtle fan sectors around (cx, cy)
    r_v1 = (cx + 190, cy)             # (1, 0)
    r_v2 = (cx + 186, cy - 62)        # (3, 1) -> y up in screen coords
    r_v3 = (cx - 186, cy - 62)        # (-3, 1)
    r_v4 = (cx - 88, cy + 176)        # (-1, -2)
    r_v5 = (cx, cy + 186)             # (0, -1)

    cv.add_polygon([ (cx, cy), r_v1, r_v2 ], fill=COL_BLUE_SOFT, stroke="none", stroke_width=0)
    cv.add_polygon([ (cx, cy), r_v2, r_v3 ], fill=COL_VIOLET_SOFT, stroke="none", stroke_width=0)
    cv.add_polygon([ (cx, cy), r_v3, r_v4 ], fill=COL_TEAL_SOFT, stroke="none", stroke_width=0)
    cv.add_polygon([ (cx, cy), r_v4, r_v5 ], fill=COL_AMBER_SOFT, stroke="none", stroke_width=0)

    cv.add_arrow(cx, cy, r_v1[0], r_v1[1], stroke=COL_BLUE, stroke_width=3)
    cv.add_arrow(cx, cy, r_v2[0], r_v2[1], stroke=COL_VIOLET, stroke_width=3)
    cv.add_arrow(cx, cy, r_v3[0], r_v3[1], stroke=COL_VIOLET, stroke_width=3)
    cv.add_arrow(cx, cy, r_v4[0], r_v4[1], stroke=COL_TEAL, stroke_width=3)
    cv.add_arrow(cx, cy, r_v5[0], r_v5[1], stroke=COL_CRIMSON, stroke_width=3)
    cv.add_circle(cx, cy, 6, fill=COL_INK, stroke="#FFFFFF", stroke_width=2)

    # Exterior ray labels
    cv.add_text(r_v1[0] + 10, r_v1[1] + 5, "v_1=(1,0) [w=0]", size=11, weight="bold", fill=COL_BLUE, mono=True)
    cv.add_text(r_v2[0] - 10, r_v2[1] - 14, "v_2=(2k+1,1) [w=1]", size=11, weight="bold", fill=COL_VIOLET, anchor="middle", mono=True)
    cv.add_text(r_v3[0] + 10, r_v3[1] - 14, "v_3=(-(2k+1),1) [w=0]", size=11, weight="bold", fill=COL_VIOLET, anchor="middle", mono=True)
    cv.add_text(r_v4[0] - 12, r_v4[1] + 18, "v_4=(-1,-2) [w=1]", size=11, weight="bold", fill=COL_TEAL_DARK, anchor="end", mono=True)
    cv.add_text(r_v5[0] + 14, r_v5[1] + 8, "v_5=(0,-1) [w=-(2k+1)]", size=11, weight="bold", fill=COL_CRIMSON, mono=True)

    cv.add_callout_card(
        46, 568, 584, 250,
        "Structural Mechanism of Unbounded Rank inside Cart(Sigma)",
        [
            "1. With m = 5 primitive rays in R^2, balanced wall space has",
            "   dimension dim B_{Sigma_5^(k)} = 5 - 2 = 3 (3D polyhedral cone!).",
            "2. Pure integer-gradient Cartier target w^prim(f) = (0, 1, 0, 1, -(2k+1))",
            "   induces a narrow 3-facet spike with initial vertex denominator 4k + 3.",
            "3. Each simultaneous elementary Chvatal closure P -> P^(1) shaves",
            "   spike height by exactly 1 unit, forcing EXACT rank = 2k + 1!",
        ],
        fill="#F8FAFC", stroke=COL_BORDER, title_ink=COL_VIOLET, size=11, line_step=31,
    )

    # Panel B (Right): Staircase Bar Chart of Sim. Chvatal Rank = 2k + 1 & Peeling Trace
    cv.add_panel(672, 96, 704, 744, "B. Simultaneous Elementary Chvatal Rank = 2k + 1", "EXACT 3, 5, 7, 9", COL_EMERALD_FILL, COL_EMERALD)

    ax0_x, ax0_y = 744, 434
    cv.add_line(ax0_x, ax0_y, 1340, ax0_y, stroke=COL_SLATE, stroke_width=2)
    cv.add_line(ax0_x, 168, ax0_x, ax0_y, stroke=COL_SLATE, stroke_width=2)
    cv.add_text(756, 162, "Sim. CG Rank", size=11, weight="bold", fill=COL_SLATE, anchor="start")

    for r_tick in (1, 3, 5, 7, 9):
        ty = ax0_y - r_tick * 26
        cv.add_line(ax0_x - 6, ty, ax0_x, ty, stroke=COL_SLATE, stroke_width=1)
        cv.add_text(ax0_x - 12, ty + 4, str(r_tick), size=11, fill=COL_SLATE, anchor="end", mono=True)

    # Dashed reference line at 4-ray ceiling Rank = 1
    y_ceil1 = ax0_y - 26
    cv.add_line(ax0_x + 4, y_ceil1, 1336, y_ceil1, stroke=COL_AMBER, stroke_width=2, dash="6,4")
    cv.add_badge(776, 184, 240, 26, "4-Ray Ceiling: Sim. Rank = 1", fill=COL_AMBER_FILL, stroke=COL_AMBER, ink=COL_AMBER, size=10)

    bars_5ray = [
        (1, 3, 7, 3, "(3,4,3)", COL_BLUE_SOFT, COL_BLUE),
        (2, 5, 11, 5, "(5,6,5)", COL_TEAL_FILL, COL_TEAL_DARK),
        (3, 7, 15, 7, "(7,8,7)", COL_VIOLET_FILL, COL_VIOLET),
        (4, 9, 19, 9, "(9,10,9)", COL_CRIMSON_FILL, COL_CRIMSON),
    ]
    for idx, (kv, m_odd, d_init, cg_rk, apex_v, bf, bs) in enumerate(bars_5ray):
        bx = 788 + idx * 136
        bw = 74
        bh = cg_rk * 26
        by = ax0_y - bh
        cv.add_rect(bx, by, bw, bh, rx=6, fill=bf, stroke=bs, stroke_width=2)
        cv.add_text(bx + 37, by - 24, f"Rank = {cg_rk}", size=12, weight="bold", fill=bs, anchor="middle", mono=True)
        cv.add_text(bx + 37, by - 9, f"den={d_init}", size=10, fill=COL_SLATE, anchor="middle", mono=True)
        cv.add_text(bx + 37, ax0_y + 20, f"k={kv} (m={m_odd})", size=11, weight="bold", fill=COL_INK, anchor="middle", mono=True)
        cv.add_text(bx + 37, ax0_y + 38, f"apex {apex_v}", size=10, fill=COL_MUTED, anchor="middle", mono=True)

    # Exact Closure Peeling Summary Card
    cv.add_callout_card(
        696, 496, 656, 322,
        "Certified Exact 3D Hilbert-Parallelepiped Closure Summary",
        [
            "k=1 (m=3): P^(0) max_den=7  -> P^(1) -> P^(2) -> P^(3) INT {(1,1,0),(2,1,1),(3,4,3)}",
            "k=2 (m=5): P^(0) max_den=11 -> ... (5 exact rounds) ... -> P^(5) INT {(1,1,0),(2,1,1),(5,6,5)}",
            "k=3 (m=7): P^(0) max_den=15 -> ... (7 exact rounds) ... -> P^(7) INT {(1,1,0),(2,1,1),(7,8,7)}",
            "k=4 (m=9): P^(0) max_den=19 -> ... (9 exact rounds) ... -> P^(9) INT {(1,1,0),(2,1,1),(9,10,9)}",
            "",
            "General Law: rank_CG^sim(D_tilde_{Sigma_5^(k)}(w(f))) = 2k + 1 -> +infinity as k -> +inf,",
            "proving arbitrarily high simultaneous Chvatal-Gomory rank even on pure Cartier functions!",
        ],
        fill="#F8FAFC", stroke=COL_BORDER, title_ink=COL_EMERALD, size=10, line_step=34,
    )
    return cv


# ---------------------------------------------------------------------------
# Figure 05: 3D Reeve Tetrahedra Primal [1,1,r] vs Polar [1,r,r] BSS Torsion
# ---------------------------------------------------------------------------

def build_fig05() -> SVGCanvas:
    cv = SVGCanvas(
        "fig05_reeve_polar_bss_torsion.svg",
        "Fig 05 — Track B1: 3D Reeve Tetrahedra T_r Primal [1,1,r] vs Polar [1,r,r] BSS Torsion",
        "Track B (Trap 4 & Theorem B1) | Cart(Sigma) ~= BSS_1(Sigma; Z), |T_r cap Z^3| = 4 vs Vol_3(T_r) = r (r = 2..12)",
        "Certified Exact | Primal SNF(E_r) = [1,1,r] (Weil/Cart ~= Z/rZ) | Polar SNF(L_r) = [1,r,r] ((Z/rZ)^2 dual-apex torsion)",
    )

    # Panel A (Left): Isometric 3D Reeve Tetrahedron T_r & Polar Facet Normals
    cv.add_panel(24, 96, 636, 744, "A. 3D Reeve Tetrahedron T_r & Polar Dual Normals", "WEIL VS CARTIER", COL_BLUE_SOFT, COL_BLUE)

    # Axonometric vertices of T_r:
    # O=(0,0,0)->(290, 420), A=(1,0,0)->(170, 485), B=(0,1,0)->(440, 485), P_r=(1,1,r)->(315, 195)
    p_o = (290, 420)
    p_a = (170, 485)
    p_b = (440, 485)
    p_apex = (315, 195)

    cv.add_polygon([p_a, p_o, p_apex], fill=COL_BLUE_SOFT, stroke="none", stroke_width=0, fill_opacity_pct=55)
    cv.add_polygon([p_o, p_b, p_apex], fill=COL_TEAL_FILL, stroke="none", stroke_width=0, fill_opacity_pct=45)
    cv.add_line(p_a[0], p_a[1], p_b[0], p_b[1], stroke=COL_SLATE, stroke_width=3)
    cv.add_line(p_o[0], p_o[1], p_a[0], p_a[1], stroke=COL_INDIGO, stroke_width=2, dash="5,4")
    cv.add_line(p_o[0], p_o[1], p_b[0], p_b[1], stroke=COL_INDIGO, stroke_width=2, dash="5,4")
    cv.add_line(p_o[0], p_o[1], p_apex[0], p_apex[1], stroke=COL_CRIMSON, stroke_width=3)
    cv.add_line(p_a[0], p_a[1], p_apex[0], p_apex[1], stroke=COL_SLATE, stroke_width=2)
    cv.add_line(p_b[0], p_b[1], p_apex[0], p_apex[1], stroke=COL_SLATE, stroke_width=2)

    for px, py, col in ((p_o[0], p_o[1], COL_INDIGO), (p_a[0], p_a[1], COL_INK), (p_b[0], p_b[1], COL_INK), (p_apex[0], p_apex[1], COL_CRIMSON)):
        cv.add_circle(px, py, 7, fill=col, stroke="#FFFFFF", stroke_width=2)

    # Exterior vertex labels
    cv.add_text(315, 173, "v_3 = (1, 1, r)  [Apex height r]", size=12, weight="bold", fill=COL_CRIMSON, anchor="middle", mono=True)
    cv.add_text(154, 502, "v_1=(1,0,0)", size=11, weight="bold", fill=COL_INK, anchor="end", mono=True)
    cv.add_text(456, 502, "v_2=(0,1,0)", size=11, weight="bold", fill=COL_INK, anchor="start", mono=True)
    cv.add_text(290, 522, "v_0=(0,0,0)  [Only 4 Z^3 points for ALL r >= 1!]", size=11, weight="bold", fill=COL_INDIGO, anchor="middle", mono=True)

    cv.add_callout_card(
        46, 548, 592, 270,
        "Primal Edge Lattice vs Polar Primitive Facet-Form Spline Module",
        [
            "Primal Edge Matrix: E_r = [[1,0,0], [0,1,0], [1,1,r]]",
            "  -> SNF(E_r) = diag(1, 1, r)  =>  Weil(Sigma_r) / Cart(Sigma_r) ~= Z/rZ",
            "  -> Fractional wall jumps: (1/r, 1/r, 1/r) => Cartier DC hull = EMPTY!",
            "Polar Primitive Facet Forms: l_12 = z,  l_13 = -r*y + z,  l_23 = r*x - z",
            "  -> L_r = [[0,0,1], [0,-r,1], [r,0,-1]]  =>  SNF(L_r) = diag(1, r, r)!",
            "  -> Dual-apex quotient Z^3 / L_r Z^3 ~= (Z/rZ)^2  (order r^2)",
            "  -> All three 2x3 ridge colon ideals have SNF = diag(1, r).",
        ],
        fill="#F8FAFC", stroke=COL_BORDER, title_ink=COL_INDIGO, size=10, line_step=30,
    )

    # Panel B (Right): Sweep r = 1..12 Scaling Plot & Table
    cv.add_panel(680, 96, 696, 744, "B. Reeve Family T_r (r=1..12): Torsion vs Lattice Pts", "ORDER r VS r^2", COL_CRIMSON_FILL, COL_CRIMSON)

    # Plot polar torsion index r^2 (max 144) vs primal r vs constant |T_r cap Z^3| = 4
    ax_x, ax_y = 752, 418
    cv.add_line(ax_x, ax_y, 1344, ax_y, stroke=COL_SLATE, stroke_width=2)
    cv.add_line(ax_x, 166, ax_x, ax_y, stroke=COL_SLATE, stroke_width=2)
    cv.add_text(740, 158, "Index", size=11, weight="bold", fill=COL_SLATE, anchor="end")

    for y_val in (0, 36, 72, 108, 144):
        py = ax_y - (y_val * 230) // 144
        cv.add_line(ax_x - 5, py, ax_x, py, stroke=COL_SLATE, stroke_width=1)
        cv.add_text(ax_x - 10, py + 4, str(y_val), size=10, fill=COL_SLATE, anchor="end", mono=True)

    pts_r2: List[Tuple[int, int]] = []
    pts_r1: List[Tuple[int, int]] = []
    pts_lat: List[Tuple[int, int]] = []
    for r_val in range(1, 13):
        px = ax_x + 22 + (r_val - 1) * 48
        py_r2 = ax_y - (r_val * r_val * 230) // 144
        py_r1 = ax_y - (r_val * 230) // 144
        py_lat = ax_y - (4 * 230) // 144
        pts_r2.append((px, py_r2))
        pts_r1.append((px, py_r1))
        pts_lat.append((px, py_lat))
        cv.add_text(px, ax_y + 18, str(r_val), size=10, fill=COL_INK, anchor="middle", mono=True)

    cv.add_polyline(pts_lat, stroke=COL_EMERALD, stroke_width=2, dash="5,3")
    cv.add_polyline(pts_r1, stroke=COL_BLUE, stroke_width=3)
    cv.add_polyline(pts_r2, stroke=COL_CRIMSON, stroke_width=3)
    for px, py in pts_r2:
        cv.add_circle(px, py, 4, fill=COL_CRIMSON, stroke="#FFFFFF", stroke_width=1)
    for px, py in pts_r1:
        cv.add_circle(px, py, 4, fill=COL_BLUE, stroke="#FFFFFF", stroke_width=1)

    # Legend badges in upper-left open sky of chart (r=1..5 has low r^2 <= 25, so y < 320 is wide open!)
    cv.add_badge(774, 174, 246, 26, "Polar |Z^3 / L_r Z^3| = r^2", fill=COL_CRIMSON_FILL, stroke=COL_CRIMSON, ink=COL_CRIMSON, size=10)
    cv.add_badge(774, 208, 246, 26, "Primal |Weil / Cart| = Vol = r", fill=COL_BLUE_SOFT, stroke=COL_BLUE, ink=COL_INDIGO, size=10)
    cv.add_badge(774, 242, 246, 26, "Lattice Points |T_r cap Z^3| = 4", fill=COL_EMERALD_FILL, stroke=COL_EMERALD, ink=COL_EMERALD, size=10)

    # Compact exact table for selected r = 1, 2, 3, 5, 8, 12
    tx, ty, tw = 704, 456, 648
    cv.add_rect(tx, ty, tw, 362, rx=8, fill="#FFFFFF", stroke=COL_BORDER, stroke_width=1, role="panel")
    cv.add_rect(tx + 2, ty + 2, tw - 4, 34, rx=6, fill=COL_PANEL_HDR, stroke="none", stroke_width=0, role="panel")
    cv.add_text(tx + 16, ty + 24, "r  | Vol_3 | |T_r n Z^3| | Primal SNF  | Polar SNF    | Ridge SNF | Weil/Cart", size=10, weight="bold", fill=COL_INK, mono=True)
    sample_r = [1, 2, 3, 5, 8, 12]
    for idx, rv in enumerate(sample_r):
        ry = ty + 44 + idx * 50
        bg = "#F8FAFC" if idx % 2 == 0 else "#FFFFFF"
        wc = "0 (Smooth)" if rv == 1 else f"Z/{rv}Z"
        cv.add_rect(tx + 8, ry, tw - 16, 40, rx=4, fill=bg, stroke=COL_HAIRLINE, stroke_width=1, role="panel")
        cv.add_text(
            tx + 16, ry + 25,
            f"{rv:2d} |  {rv:2d}   |      4      | [1, 1, {rv:2d}] | [1, {rv:2d}, {rv:2d}] | [1, {rv:2d}]   | {wc}",
            size=10, fill=COL_INK, mono=True,
        )
    return cv


# ---------------------------------------------------------------------------
# Figure 06: Airy Spiderweb Z/mZ Torsion & 6-Triangle Chord Annulus Monodromy
# ---------------------------------------------------------------------------

def build_fig06() -> SVGCanvas:
    cv = SVGCanvas(
        "fig06_airy_spiderweb_and_chord_annulus.svg",
        "Fig 06 — Track C1: Maxwell-Cremona Spiderweb Z/mZ Torsion & 6-Triangle Annulus Monodromy",
        "Track C (Trap 6 & Theorem C1) | Saturated Airy Cosheaf A_Z vs F_Z^geom & Repaired Rank-3 Annular Monodromy",
        "Certified Exact | Spiderweb ev_V SNF = [1,m,m,m] | Concurrent Spokes Collapse Rank 3->2 | 6-Tri Chords Restore Z^{3(b-1)}",
    )

    # Panel A (Left): Scaled Index-m Spiderweb vs Primitive-Spoke Twisted Wheel
    cv.add_panel(24, 96, 660, 744, "A. Spiderweb [1,m,m,m] & Twisted Wheel [1,1,1,m]", "NODAL Z/mZ TORSION", COL_TEAL_FILL, COL_TEAL_DARK)

    # Draw spiderweb complex on top-left of Panel A: center (210, 300), v1=(330, 300), v2=(210, 185), v3=(115, 395)
    sw_c = (210, 300)
    sw_1 = (335, 300)
    sw_2 = (210, 180)
    sw_3 = (110, 400)
    cv.add_polygon([sw_1, sw_2, sw_3], fill=COL_TEAL_SOFT, stroke=COL_SLATE, stroke_width=2)
    for vx, vy in (sw_1, sw_2, sw_3):
        cv.add_line(sw_c[0], sw_c[1], vx, vy, stroke=COL_CRIMSON, stroke_width=3)
        cv.add_circle(vx, vy, 6, fill=COL_SLATE, stroke="#FFFFFF", stroke_width=2)
    cv.add_circle(sw_c[0], sw_c[1], 7, fill=COL_CRIMSON, stroke="#FFFFFF", stroke_width=2)

    cv.add_text(210, 162, "v_2=(0, m)", size=11, weight="bold", fill=COL_INK, anchor="middle", mono=True)
    cv.add_text(348, 304, "v_1=(m, 0)", size=11, weight="bold", fill=COL_INK, mono=True)
    cv.add_text(110, 424, "v_3=(-m,-m)", size=11, weight="bold", fill=COL_INK, anchor="middle", mono=True)
    cv.add_badge(262, 392, 146, 28, "v_0: m | z_0!", fill=COL_CRIMSON_FILL, stroke=COL_CRIMSON, ink=COL_CRIMSON, size=10)

    # Side box on top-right of Panel A: Primitive-Spoke Twisted Wheel
    cv.add_callout_card(
        438, 156, 224, 276,
        "Primitive Twisted Wheel",
        [
            "All 3 spokes gcd = 1!",
            "F_Z^geom edge torsion:",
            "  m=3,9 -> [] (ZERO!)",
            "Yet determinant shear",
            "forces nodal SNF:",
            "  [1, 1, 1, m]",
            "(Pure sheaf torsion,",
            "not edge-length gcd!)",
        ],
        fill=COL_VIOLET_SOFT, stroke=COL_VIOLET, title_ink=COL_VIOLET, size=10, line_step=26,
    )

    cv.add_callout_card(
        46, 456, 616, 362,
        "Saturated Integral Airy Sequence & Geometric Force Comparison",
        [
            "Short Exact Sequence:  0 -> Z_R^sat -> Aff_R -> A_R -> 0   (R in {Z, Z_(p)})",
            "Stalk Ranks:  Face sigma: (0, 3, 3) | Edge e: (1, 3, 2) | Vertex v: (2, 3, 1)",
            "",
            "1. Scaled Spiderweb (m = 2,3,4,6,8,9,12): unclamped ev_V SNF = [1, m, m, m];",
            "   clamped tent (z_0 = 1, z_rim = 0) is Q-SAT (1/m) yet Z_(p)-SAT iff p !| m!",
            "2. Maxwell-Cremona 90-deg Rotation: Z_Z^sat ~= F_Z^prim is torsion-free,",
            "   whereas unnormalized F_Z^geom embeds with cokernel oplus_e (Z / g_e Z).",
            "3. Multi-Hole Domains: b=2 annulus -> Z^3; b=3 double-punctured grid -> Z^6.",
        ],
        fill="#F8FAFC", stroke=COL_BORDER, title_ink=COL_TEAL_DARK, size=10, line_step=34,
    )

    # Panel B (Right): Trap 6 Annulus Degeneracy vs 6-Triangle Chord Subdivision
    cv.add_panel(704, 96, 672, 744, "B. Concurrent Spokes (Rk 2) vs 6-Tri Chords (Rk 3)", "H_1(A_Z) ~= Z^3", COL_INDIGO_FILL, COL_INDIGO)

    # Top Sub-card: Degenerate 3-Trapezoid Annulus (Rank 2 Collapse)
    cv.add_rect(726, 152, 628, 296, rx=8, fill=COL_CRIMSON_SOFT, stroke=COL_CRIMSON, stroke_width=2, role="panel")
    cv.add_text(744, 178, "BROKEN: Untriangulated 3-Sector Annulus (Spokes Concur at Origin)", size=12, weight="bold", fill=COL_CRIMSON)

    b_cx, b_cy = 876, 314
    out_tri = [(996, 314), (816, 210), (816, 418)]
    in_tri = [(936, 314), (846, 262), (846, 366)]
    cv.add_polygon(out_tri, fill="#FFFFFF", stroke=COL_SLATE, stroke_width=2)
    cv.add_polygon(in_tri, fill=COL_CRIMSON_FILL, stroke=COL_CRIMSON, stroke_width=2)
    for k in range(3):
        cv.add_line(in_tri[k][0], in_tri[k][1], out_tri[k][0], out_tri[k][1], stroke=COL_CRIMSON, stroke_width=3)
        cv.add_line(b_cx, b_cy, in_tri[k][0], in_tri[k][1], stroke=COL_MUTED, stroke_width=1, dash="3,3")
    cv.add_circle(b_cx, b_cy, 4, fill=COL_CRIMSON, stroke="none", stroke_width=0)

    cv.add_callout_card(
        1026, 204, 308, 218,
        "Concurrency Rank Drop!",
        [
            "All 3 interior spoke lines",
            "pass through (0, 0)!",
            "-> Cross-edge hinge jumps",
            "   satisfy sum n_k x (0,0) = 0.",
            "-> Monodromy rank collapses",
            "   from 3(b-1)=3 down to 2!",
        ],
        fill="#FFFFFF", stroke=COL_CRIMSON, title_ink=COL_CRIMSON, size=10, line_step=25,
    )

    # Bottom Sub-card: Repaired 6-Triangle Chord-Subdivided Annulus (Full Rank 3!)
    cv.add_rect(726, 468, 628, 350, rx=8, fill=COL_EMERALD_FILL, stroke=COL_EMERALD, stroke_width=2, role="panel")
    cv.add_text(744, 494, "CERTIFIED: 6-Triangle CCW Chord-Subdivided Annulus (Full Rank 3)", size=12, weight="bold", fill=COL_EMERALD)

    g_out = [(996, 646), (816, 542), (816, 750)]
    g_in = [(936, 646), (846, 594), (846, 698)]
    cv.add_polygon(g_out, fill="#FFFFFF", stroke=COL_SLATE, stroke_width=2)
    cv.add_polygon(g_in, fill=COL_PANEL_HDR, stroke=COL_SLATE, stroke_width=2)
    for k in range(3):
        # 3 radial spokes + 3 CCW subdividing chords u_k -> v_{k+1}
        cv.add_line(g_in[k][0], g_in[k][1], g_out[k][0], g_out[k][1], stroke=COL_INDIGO, stroke_width=2)
        kn = (k + 1) % 3
        cv.add_line(g_in[k][0], g_in[k][1], g_out[kn][0], g_out[kn][1], stroke=COL_EMERALD, stroke_width=3)

    cv.add_callout_card(
        1026, 524, 308, 270,
        "Full Affine Monodromy Z^3",
        [
            "Chords u_1 v_2, u_2 v_3, u_3 v_1",
            "break spoke concurrency!",
            "-> 3x6 jump matrix J_mono has",
            "   SNF(J_mono) = [1, 1, 2]",
            "   (exact rank = 3!).",
            "-> H_1(A_Z) ~= Z^{3(b-1)} = Z^3",
            "   (2 tilts + 1 vertical shift).",
        ],
        fill="#FFFFFF", stroke=COL_EMERALD, title_ink=COL_EMERALD, size=10, line_step=28,
    )
    return cv


# ---------------------------------------------------------------------------
# Figure 07: 2D Precision-Bockstein Barcodes & (P_sat, Q_free) Projectors
# ---------------------------------------------------------------------------

def build_fig07() -> SVGCanvas:
    cv = SVGCanvas(
        "fig07_2d_precision_bockstein_snf.svg",
        "Fig 07 — Track C2: 2D Precision-Bockstein p-Adic Barcodes & (P_sat, Q_free) Projectors",
        "Track C (Theorem C2) | rank(beta_k^(2)) == #{i : v_p(d_i) >= k} & Ghrist-Ding Integral Saturation Splitting",
        "Certified Exact | 100% Digit-SNF Barcode Match across p in {2,3}, k in {1,2,3} | P_sat^2 = P_sat, P_sat + Q_free = I",
    )

    # Panel A (Left): p-Adic Precision-Bockstein Barcodes
    cv.add_panel(24, 96, 660, 744, "A. Precision-Bockstein beta_k^(2) Barcodes", "DIGIT-SNF DICTIONARY", COL_VIOLET_FILL, COL_VIOLET)

    # Scale header for k = 1, 2, 3
    cv.add_rect(46, 152, 616, 42, rx=6, fill=COL_PANEL_HDR, stroke=COL_BORDER, stroke_width=1, role="panel")
    cv.add_text(62, 178, "Complex / Torsion Factor d_i", size=11, weight="bold", fill=COL_INK, mono=True)
    cv.add_text(380, 178, "k=1 (mod p)", size=11, weight="bold", fill=COL_INDIGO, anchor="middle", mono=True)
    cv.add_text(490, 178, "k=2 (mod p^2)", size=11, weight="bold", fill=COL_INDIGO, anchor="middle", mono=True)
    cv.add_text(600, 178, "k=3 (mod p^3)", size=11, weight="bold", fill=COL_INDIGO, anchor="middle", mono=True)

    barcode_groups = [
        ("Desargues Prism m=3 (ev SNF [1,1,3,3,12,12])", [
            ("p=2: d_5=12 (v_2=2)", 2, COL_BLUE),
            ("p=2: d_6=12 (v_2=2)", 2, COL_BLUE),
            ("p=3: d_3..6 in {3,12} (x4, v_3=1)", 1, COL_VIOLET),
        ]),
        ("Desargues Prism m=4 (ev SNF [1,1,1,4,20,60])", [
            ("p=2: d_4..6 in {4,20,60} (x3, v_2=2)", 2, COL_BLUE),
            ("p=3: d_6=60 (v_3=1)", 1, COL_VIOLET),
        ]),
        ("ScaledSpiderweb m=8 & Annulus b=2, s=2", [
            ("Spiderweb m=8: d=8 (x3, v_2=3)", 3, COL_TEAL_DARK),
            ("Annulus s=2 H_1^int: d=4 (v_2=2)", 2, COL_CRIMSON),
            ("Annulus s=2 H_1^all: d=2 (v_2=1)", 1, COL_AMBER),
        ]),
    ]

    cur_y = 210
    for grp_title, bars in barcode_groups:
        cv.add_rect(46, cur_y, 616, 28, rx=4, fill=COL_INDIGO_FILL, stroke="none", stroke_width=0, role="panel")
        cv.add_text(58, cur_y + 19, grp_title, size=11, weight="bold", fill=COL_INDIGO, mono=True)
        cur_y += 36
        for lbl, k_len, bcol in bars:
            cv.add_text(58, cur_y + 17, lbl, size=10, fill=COL_SLATE, mono=True)
            bar_x0 = 335
            bar_w = k_len * 110 - 20
            cv.add_rect(bar_x0, cur_y + 3, bar_w, 18, rx=9, fill=bcol, stroke="none", stroke_width=0)
            cur_y += 32
        cur_y += 10

    cv.add_callout_card(
        46, 624, 616, 196,
        "Exact Bockstein Connecting Homomorphism Dictionary",
        [
            "beta_k^(2) : H_2(A_{Z/p^k Z}) ---> H_1(A_Z)[p^k]",
            "1. Spurious mod-p^k Airy 2-cycles arise iff a Z-torsion invariant factor d_i",
            "   satisfies p | d_i; its persistence dies precisely at precision k > v_p(d_i)!",
            "2. Certified 100% match: rank_{Z/pZ}(im beta_k^(2)) == #{i : v_p(d_i) >= k}",
            "   across all 23 spiderweb, twisted-wheel, Desargues & annular complexes.",
        ],
        fill="#F8FAFC", stroke=COL_BORDER, title_ink=COL_VIOLET, size=10, line_step=27,
    )

    # Panel B (Right): Ghrist-Ding Orthogonal Integer Projectors (P_sat, Q_free)
    cv.add_panel(704, 96, 672, 744, "B. Global Z-Saturation Idempotents (P_sat, Q_free)", "EXACT Z-SPLITTING", COL_EMERALD_FILL, COL_EMERALD)

    # Top: Z_1(A_Z) module node splitting into P_sat and Q_free
    cv.add_badge(864, 158, 352, 50, "1-Cycle Lattice Z_1(A_Z) = ker(d_1^A)", fill=COL_INDIGO_FILL, stroke=COL_INDIGO, ink=COL_INDIGO, size=12)

    cv.add_arrow(960, 212, 860, 276, stroke=COL_EMERALD, stroke_width=3)
    cv.add_arrow(1120, 212, 1220, 276, stroke=COL_BLUE, stroke_width=3)
    cv.add_text(876, 246, "P_sat", size=12, weight="bold", fill=COL_EMERALD, anchor="end", mono=True)
    cv.add_text(1204, 246, "Q_free = I - P_sat", size=12, weight="bold", fill=COL_BLUE, anchor="start", mono=True)

    cv.add_callout_card(
        726, 284, 304, 214,
        "Saturated Boundary Lattice",
        [
            "sat_Z(im d_2^A) = im_Q n Z^m",
            "Formula: U_inv[:, :r] @ U[:r, :]",
            "Contains:",
            " * Exact Z-Airy boundaries im(d_2)",
            " * Finite torsion oplus Z/d_i Z",
            "   (detected by beta_k^(2)!)",
        ],
        fill=COL_EMERALD_FILL, stroke=COL_EMERALD, title_ink=COL_EMERALD, size=10, line_step=26,
    )

    cv.add_callout_card(
        1050, 284, 304, 214,
        "Free Monodromy Complement",
        [
            "im(Q_free) ~= Z^{3(b - 1)}",
            "Formula: U_inv[:, r:] @ U[r:, :]",
            "Satisfies Q_free @ d_2^A == 0!",
            "Captures topological holes:",
            " * b=1 disk:    rank 0",
            " * b=2 annulus: rank 3",
            " * b=3 2-hole:  rank 6",
        ],
        fill=COL_BLUE_SOFT, stroke=COL_BLUE, title_ink=COL_INDIGO, size=10, line_step=24,
    )

    cv.add_callout_card(
        726, 520, 628, 300,
        "Machine-Checked Unimodular Projector Identities (Zero Rational Division!)",
        [
            "Given unimodular SNF  U @ d_2_tilde @ V = diag(d_1, ..., d_r, 0)  with U in GL_m(Z):",
            "  [Idempotency]    P_sat @ P_sat == P_sat     and   Q_free @ Q_free == Q_free",
            "  [Orthogonality]  P_sat @ Q_free == 0        and   Q_free @ P_sat == 0",
            "  [Completeness]   P_sat + Q_free == I_m      and   trace(P_sat) == r",
            "  [Boundary]       P_sat @ d_2_tilde == d_2_tilde,  Q_free @ d_2_tilde == 0",
            "",
            "Certified on Subdivided Annulus (b=2): dim Z_1 = 9 -> r = 6 (P_sat) (+) corank = 3 (Q_free).",
        ],
        fill="#F8FAFC", stroke=COL_BORDER, title_ink=COL_INK, size=10, line_step=33,
    )
    return cv


# ---------------------------------------------------------------------------
# Figure 08: Group Circuit Compression & Q_8 / Dic_3 Superposed 2-Cocycle
# ---------------------------------------------------------------------------

def build_fig08() -> SVGCanvas:
    cv = SVGCanvas(
        "fig08_group_circuit_compression_and_q8_cocycle.svg",
        "Fig 08 — Track D1/D4: Permutation Compression & Q_8 / Dic_3 2-Cocycle Staircase",
        "Track D (Theorems D1, D4a, D4b) | Q_8: 64 -> 48 -> 43/38 -> 22(Q, den=8) -> 17/18(Z)! & Dic_3: 144 -> 49 -> 25/26(Z)!",
        "Certified Exact | C_5: W=8 << 25 | V_4: Walsh [2]-torsion vs W_Z=6/7 surgery | Q_8 & D_4 parity invariance W_Z=17/18",
    )

    # Panel A (Left): Compression Hierarchy Across Finite Groups
    cv.add_panel(24, 96, 664, 744, "A. Compression: |G|^2 vs Perm m^2 vs Wave II Z", "SHATTERS Q_8 WALL", COL_INDIGO_FILL, COL_INDIGO)

    # Horizontal bar comparison table for C_5, V_4, S_3, D_4, Q_8, Dic_3, Q_16
    groups_comp = [
        ("C_5", 25, "25 (blocked)", 8, "Ramp 2n-2 = 8/9 (3.1x)"),
        ("V_4", 16, "16 (blocked)", 6, "Walsh [2] vs Z-Surg W=6/7"),
        ("S_3", 36, "9 (argmax)", 13, "Perm 9 / Ind Z W=13/14"),
        ("D_4", 64, "16 (argmax)", 17, "Perm 16 / Ind Z W=17/18"),
        ("Q_8", 64, "64 (WALL!)", 17, "64->48->43->22(Q)->17/18(Z)!"),
        ("Dic_3", 144, "49 (intrans)", 25, "144->49->25/26(Z) (5.8x!)"),
        ("Q_16", 256, "256 (WALL!)", 33, "Cocycle Ramp Z W=33/34!"),
    ]

    y_top = 156
    for idx, (gname, g2, perm_s, w_z, summary_s) in enumerate(groups_comp):
        ry = y_top + idx * 78
        is_wall = "WALL" in perm_s or gname == "Dic_3"
        bg = COL_VIOLET_SOFT if is_wall else "#F8FAFC"
        st = COL_VIOLET if is_wall else COL_BORDER
        cv.add_rect(44, ry, 624, 66, rx=6, fill=bg, stroke=st, stroke_width=1, role="panel")
        cv.add_text(58, ry + 24, f"{gname:5s} | |G|^2={g2:3d} | Perm m^2={perm_s:13s}", size=11, weight="bold", fill=COL_INK, mono=True)
        cv.add_text(58, ry + 48, f"Wave II Pure-Z Indicator: W = {w_z:2d}  [{summary_s}]", size=11, weight="bold", fill=COL_EMERALD if not is_wall else COL_VIOLET, mono=True)
        # Compact visual compression ratio pill on right
        bar_full = 150
        bar_comp = max(14, (w_z * bar_full) // g2)
        cv.add_rect(500, ry + 14, bar_full, 14, rx=4, fill=COL_CRIMSON_FILL, stroke=COL_CRIMSON, stroke_width=1)
        cv.add_rect(500, ry + 36, bar_comp, 14, rx=4, fill=COL_EMERALD_FILL, stroke=COL_EMERALD, stroke_width=2)

    cv.add_callout_card(
        44, 708, 624, 114,
        "Universal Lower Bounds (Theorem D4b)",
        [
            "1. Rank Bound: det(I_mult^T I_mult) = |G|^{|G|} => W >= |G|-1 (biased), |G| (zero-bias).",
            "2. 1-Neuron Outcome Lemma: ZERO single ReLU neurons lie in V_out => W >= |G| (biased)!",
            "3. Ray-Bucket Rank-Nullity: W = |G| refuted across entire pool => C_3 minimal W_Z = 4.",
        ],
        fill=COL_AMBER_SOFT, stroke=COL_AMBER, title_ink=COL_AMBER, size=10, line_step=21,
    )

    # Panel B (Right): Q_8 3-Tier Compression & Superposed 2-Cocycle Architecture
    cv.add_panel(708, 96, 668, 744, "B. Q_8 2-Cocycle Architecture (64 -> 17 Over Z)", "W_Z = 2|G| + 1 = 17", COL_VIOLET_FILL, COL_VIOLET)

    # 5-step certified Q_8 compression staircase at top of Panel B
    steps_q8 = [
        ("Perm Wall", "W = 64", COL_CRIMSON_FILL, COL_CRIMSON),
        ("H^2 Fiber", "W_Z = 48", COL_AMBER_FILL, COL_AMBER),
        ("Quot-Red Z", "W_Z=43/38", "#F1F5F9", COL_SLATE),
        ("Walsh+HL Q", "W_Q = 22", COL_BLUE_SOFT, COL_BLUE),
        ("Superposed", "W_Z=17/18", COL_EMERALD_FILL, COL_EMERALD),
    ]
    for idx, (sl1, sl2, bf, bs) in enumerate(steps_q8):
        bx = 724 + idx * 129
        cv.add_rect(bx, 154, 116, 62, rx=7, fill=bf, stroke=bs, stroke_width=2, role="panel")
        cv.add_text(bx + 58, 178, sl1, size=10, weight="bold", fill=bs, anchor="middle")
        cv.add_text(bx + 58, 202, sl2, size=11, weight="bold", fill=COL_INK, anchor="middle", mono=True)
        if idx < 4:
            cv.add_arrow(bx + 117, 185, bx + 128, 185, stroke=COL_SLATE, stroke_width=2)

    # 2x2 Coset Superposition Matrix for 1 -> C_4 = <i> -> Q_8 -> C_2 = {1, j_bar} -> 1
    cv.add_rect(728, 236, 628, 286, rx=8, fill="#F8FAFC", stroke=COL_BORDER, stroke_width=1, role="panel")
    cv.add_text(1042, 260, "Superposed 2-Cocycle Regime Map on 1 -> C_4 = <i> -> Q_8 -> C_2 -> 1 (x^2 = i^2 = -1)", size=11, weight="bold", fill=COL_INDIGO, anchor="middle", mono=True)

    # 4 quadrant cards for Family 1 (Even coset <i>):
    quads = [
        (748, 278, "Block A x A  (i^r1 * i^r2)", "S_1 = r1 + r2 in [0, 6]", "ACTIVE KINKS: Delta^2 = 1[S_1=t]", COL_EMERALD_FILL, COL_EMERALD),
        (1050, 278, "Block A x Aj  (i^r1 * i^r2 j)", "S_1 = +2K + ... >= 20", "PURELY AFFINE: Delta^2 == 0!", COL_BLUE_SOFT, COL_BLUE),
        (748, 396, "Block Aj x A  (i^r1 j * i^r2)", "S_1 = -2K + ... <= -14", "CLIPPED OFF: ReLU == 0!", COL_PANEL_HDR, COL_SLATE),
        (1050, 396, "Block Aj x Aj  (x^2 = a^2 cocycle!)", "S_1 = (r1+3 mod 4)+(3-r2)", "ACTIVE KINKS: exact cocycle shift!", COL_VIOLET_FILL, COL_VIOLET),
    ]
    for qx, qy, qt, ql1, ql2, qbg, qst in quads:
        cv.add_rect(qx, qy, 286, 106, rx=6, fill=qbg, stroke=qst, stroke_width=2, role="panel")
        cv.add_text(qx + 12, qy + 24, qt, size=11, weight="bold", fill=qst, mono=True)
        cv.add_text(qx + 12, qy + 52, ql1, size=10, fill=COL_INK, mono=True)
        cv.add_text(qx + 12, qy + 78, ql2, size=10, weight="bold", fill=qst, mono=True)

    cv.add_callout_card(
        728, 540, 628, 280,
        "Cohomological Parity Invariance, Howell-Lafon W_Q=22 & V_4 Surgery",
        [
            "1. Shifted/Superposed Pure-Z Law (1 -> C_m -> G -> C_2 -> 1, |G| = 2m):",
            "     W_Z^biased = 4m + 1 = 2|G| + 1  (Q_8 & D_4: 17/18; Dic_3: 25/26 << 49 << 144)!",
            "2. Walsh + Howell-Lafon Quaternion Bilinear Rank 8 on Q_8:",
            "     W_Q = 22 dyadic indicator (den = 8) & W_Z = 22 pure-Z strict argmax!",
            "3. V_4 Z-vs-Q Separation & Torsion-Killing Surgery:",
            "     Sym. Walsh W=6 has SNF=[1^6, 2] (Q-SAT den=2, Z-UNSAT), cured to SNF=[1^7]",
            "     at W_Z = 6 (biased) / 7 (zero-bias) by 1 hinge ReLU([0,-1,-1,-1]+[1,2,2,2])!",
        ],
        fill="#FFFFFF", stroke=COL_VIOLET, title_ink=COL_VIOLET, size=10, line_step=32,
    )
    return cv


# ---------------------------------------------------------------------------
# Figure 09: Proper-Coset SNF Trichotomy & C_5 Equivariance vs Phi_5 Bottleneck
# ---------------------------------------------------------------------------

def build_fig09() -> SVGCanvas:
    cv = SVGCanvas(
        "fig09_proper_coset_snf_trichotomy.svg",
        "Fig 09 — Track D2/D3: Proper-Coset SNF Readout Trichotomy & C_5 Phi_5 Bottleneck",
        "Track D (Theorems D2 & D3) | 3-Regime Coset Readout Classification (S_4 Bezout [1]^24) & C_5 Equivariance Barrier",
        "Certified Exact | S_4: 3*e_0 - 2*e_0 = e_0 over Z | V_4 Hadamard [1,2,2,4] | C_5 Equiv W>=25 vs Unconstrained W=8",
    )

    # Panel A (Left): 3-Regime Proper-Subgroup Coset Readout Trichotomy
    cv.add_panel(24, 96, 700, 744, "A. Proper-Subgroup Coset (|H| >= 2) Readout SNF Trichotomy", "THEOREM D2", COL_TEAL_FILL, COL_TEAL_DARK)

    # Regime I Card
    cv.add_callout_card(
        46, 152, 656, 188,
        "Regime I — Q-Rank Deficient (rank_Q(C_G) < |G| => e_0 UNSAT Even Over Q)",
        [
            " * Prime Cyclic C_3 (1 col, rank 1 < 3) & C_5 (1 col, rank 1 < 5): only H = G exists.",
            " * Cyclic C_4 (3 cols, rank 2 < 4): unique nontrivial H = {0, 2} cannot separate 0 from 2.",
            " * Quaternion Q_8 (11 cols, rank 4 < 8): central -1 lies in EVERY H != {1}, forcing",
            "   identical rows on {+g, -g}! (Adding 4D Z-quaternions restores rank 8, SNF [1^4,2,4,4,8].)",
        ],
        fill=COL_CRIMSON_SOFT, stroke=COL_CRIMSON, title_ink=COL_CRIMSON, size=10, line_step=30,
    )

    # Regime II Card
    cv.add_callout_card(
        46, 358, 656, 224,
        "Regime II — Q-Complete + Genuine Z-Torsion (e_0 Q-SAT, Z-UNSAT!)",
        [
            " * Klein V_4  (7 cols, rank 4):  Proper-coset torsion = [2]    | Sylvester H_4 SNF = [1, 2, 2, 4]",
            " * Symm S_3   (12 cols, rank 6): Proper-coset torsion = [3]    | Irrep SNF = [1, 1, 1, 3, 3, 6]",
            " * Dihed D_4  (27 cols, rank 8): Proper-coset torsion = [2]    | Irrep SNF = [1, 1, 2, 2, 2, 4, 4, 8]",
            " * Dihed D_5  (28 cols, rank 10):Proper-coset torsion = [5]    | Irrep SNF = [1^7, 5, 5, 10]",
            " * Alt A_4    (38 cols, rank 12):Proper-coset torsion = [2, 2] | Irrep SNF = [1^3, 2^6, 4, 4, 12]",
        ],
        fill=COL_AMBER_SOFT, stroke=COL_AMBER, title_ink=COL_AMBER, size=10, line_step=32,
    )

    # Regime III Card (S_4 Unimodular Synthesis!)
    cv.add_callout_card(
        46, 600, 656, 220,
        "Regime III — Z-Unimodular Proper-Coset Synthesis: S_4 Achieves SNF = [1]^24!",
        [
            "Across all 210 proper-subgroup cosets of S_4 (|G| = 24), C_{S_4} has ZERO Z-torsion:",
            "  * Stabilizer S_3 <= S_4 synthesizes 3 * e_0 in Span_Z(cosets of S_3 & subgroups).",
            "  * Sylow-2 D_4 <= S_4 synthesizes 2 * e_0 in Span_Z(cosets of D_4 & subgroups).",
            "  * Exact Bezout Identity over Z:   1 * (3 * e_0)  -  1 * (2 * e_0)  =  1 * e_0 !",
            "Result: e_0 is Z-SAT on S_4 using ONLY proper-subgroup coset indicators (det = 1)!",
        ],
        fill=COL_EMERALD_FILL, stroke=COL_EMERALD, title_ink=COL_EMERALD, size=10, line_step=31,
    )

    # Panel B (Right): C_5 Equivariance Barrier vs Phi_5 Linear Bottleneck
    cv.add_panel(744, 96, 632, 744, "B. C_5 Equivariance Barrier vs Phi_5 Bottleneck", "THEOREM D3", COL_INDIGO_FILL, COL_INDIGO)

    # Top comparison: Strict (C_5 x C_5)-equivariance W >= 25 vs Unconstrained W = 8
    cv.add_rect(766, 152, 588, 310, rx=8, fill="#F8FAFC", stroke=COL_BORDER, stroke_width=1, role="panel")
    cv.add_text(1060, 178, "Strict (C_5 x C_5) Hidden Permutation Equivariance vs Unconstrained Z", size=12, weight="bold", fill=COL_INK, anchor="middle")

    # Two contrasting pillars
    cv.add_rect(796, 200, 244, 146, rx=8, fill=COL_CRIMSON_FILL, stroke=COL_CRIMSON, stroke_width=2, role="panel")
    cv.add_text(918, 228, "Strict Equivariant", size=12, weight="bold", fill=COL_CRIMSON, anchor="middle")
    cv.add_text(918, 258, "W >= 25 (Even Over R!)", size=13, weight="bold", fill=COL_INK, anchor="middle", mono=True)
    cv.add_text(918, 286, "gcd(25,2)=1: zero sign chars", size=10, fill=COL_SLATE, anchor="middle", mono=True)
    cv.add_text(918, 308, "Short orbits -> 9D f1(g)+f2(h)", size=10, fill=COL_SLATE, anchor="middle", mono=True)
    cv.add_text(918, 330, "100-row Bareiss Farkas UNSAT", size=10, weight="bold", fill=COL_CRIMSON, anchor="middle", mono=True)

    cv.add_rect(1080, 200, 244, 146, rx=8, fill=COL_EMERALD_FILL, stroke=COL_EMERALD, stroke_width=2, role="panel")
    cv.add_text(1202, 228, "Unconstrained Pure-Z", size=12, weight="bold", fill=COL_EMERALD, anchor="middle")
    cv.add_text(1202, 258, "W = 8 << 25!", size=14, weight="bold", fill=COL_INK, anchor="middle", mono=True)
    cv.add_text(1202, 286, "h_t = ReLU(g + h - t)", size=10, fill=COL_SLATE, anchor="middle", mono=True)
    cv.add_text(1202, 308, "t = 0..7 ramp 2nd-diffs", size=10, fill=COL_SLATE, anchor="middle", mono=True)
    cv.add_text(1202, 330, "No Q(sqrt(5)) barrier!", size=10, weight="bold", fill=COL_EMERALD, anchor="middle", mono=True)

    cv.add_text(1060, 380, "Symmetry-Breaking Gain: 25 -> 8 (3.125x fewer neurons by dropping equivariance!)", size=11, weight="bold", fill=COL_INDIGO, anchor="middle", mono=True)
    cv.add_text(1060, 404, "Strict-Argmax Ring Collapse (D1a): W_Z^argmax(G) == W_Q^argmax(G) == W_R^argmax(G).", size=10, fill=COL_SLATE, anchor="middle", mono=True)
    cv.add_text(1060, 428, "(Positive LCM layer scaling preserves ReLU & strict argmax at zero neuron overhead.)", size=10, fill=COL_MUTED, anchor="middle", mono=True)

    # Bottom sub-panel: Faithful Linear Representation Bottleneck d_emb(R)=2 vs d_emb(Q)=d_emb(Z)=4
    cv.add_callout_card(
        766, 480, 588, 340,
        "Linear Bottleneck Separation: d_emb(R) = 2 vs d_emb(Q) = d_emb(Z) = 4",
        [
            "Over R (Irrational 2*pi/5 Rotation in Q(sqrt(5))):",
            "  d_emb(R) = 2   via  cos(2*pi/5) = (sqrt(5) - 1) / 4.",
            "",
            "Over Q and Z (5th Cyclotomic Polynomial Phi_5(x) = 1 + x + x^2 + x^3 + x^4):",
            "  Shifted Eisenstein at p = 5:",
            "    Phi_5(y + 1) = y^4 + 5*y^3 + 10*y^2 + 10*y + 5",
            "    (5 | 5, 10, 10, 5  and  25 !| 5  =>  Phi_5 irreducible of degree 4 over Q!)",
            "  Companion Matrix C(Phi_5) in GL_4(Z) realizes exact minimum d_emb(Q) = d_emb(Z) = 4.",
        ],
        fill=COL_BLUE_SOFT, stroke=COL_BLUE, title_ink=COL_INDIGO, size=10, line_step=34,
    )
    return cv


# ---------------------------------------------------------------------------
# Figure 10: Escher Waterfall, Pinned-Torsor Contraction & Mobius Z/2Z Torsion
# ---------------------------------------------------------------------------

def build_fig10() -> SVGCanvas:
    cv = SVGCanvas(
        "fig10_escher_waterfall_and_mobius_torsion.svg",
        "Fig 10 — Track E: Outward Escher Waterfall, Pinned Contraction & Mobius Z/2Z Torsion",
        "Track E (Counterexample E0 & Theorems E1, E2) | Closed CPA Torsors vs Pinned Return Map & Twisted Sheaf Z_{-1}",
        "Certified Exact | E0: D^+ V_tilde <= -19 yet P(r)=(21/19)^4 r > r | E1: Factor 16/81 -> r*=10/3 | E2: H^1(M_N;Z_{-1})=Z/2Z",
    )

    # Panel A (Left): Counterexample E0 — Outward-Spiraling Escher Waterfall
    cv.add_panel(24, 96, 436, 744, "A. E0: Escher Waterfall", "FALSIFIED", COL_CRIMSON_FILL, COL_CRIMSON)

    # Square annulus {1 <= ||x||_inf <= 2} centered at (242, 310), scale 76 px per unit (r=2 -> 152, r=1 -> 76)
    e0_cx, e0_cy = 242, 310
    cv.add_rect(e0_cx - 152, e0_cy - 152, 304, 304, fill=COL_CRIMSON_SOFT, stroke=COL_SLATE, stroke_width=2, role="shape")
    cv.add_rect(e0_cx - 76, e0_cy - 76, 152, 152, fill=COL_PANEL_BG, stroke=COL_SLATE, stroke_width=2, role="shape")
    # 4 corner diagonals
    cv.add_line(e0_cx + 76, e0_cy + 76, e0_cx + 152, e0_cy + 152, stroke=COL_BORDER, stroke_width=1, dash="4,3")
    cv.add_line(e0_cx + 76, e0_cy - 76, e0_cx + 152, e0_cy - 152, stroke=COL_BORDER, stroke_width=1, dash="4,3")
    cv.add_line(e0_cx - 76, e0_cy - 76, e0_cx - 152, e0_cy - 152, stroke=COL_BORDER, stroke_width=1, dash="4,3")
    cv.add_line(e0_cx - 76, e0_cy + 76, e0_cx - 152, e0_cy + 152, stroke=COL_BORDER, stroke_width=1, dash="4,3")

    # Exact 1-lap outward spiral from r0=1 (76px) -> 21/19 (~84px) -> 441/361 (~93px) -> 9261/6859 (~103px) -> 194481/130321 (~113px)
    # Note: in screen coords, y is inverted (y_math = -1 -> e0_cy + 76)
    sp_e0 = [
        (e0_cx + 76, e0_cy + 76),
        (e0_cx + 84, e0_cy - 84),
        (e0_cx - 93, e0_cy - 93),
        (e0_cx - 103, e0_cy + 103),
        (e0_cx + 113, e0_cy + 113),
    ]
    for i in range(4):
        cv.add_arrow(sp_e0[i][0], sp_e0[i][1], sp_e0[i + 1][0], sp_e0[i + 1][1], stroke=COL_CRIMSON, stroke_width=3)
    cv.add_circle(sp_e0[0][0], sp_e0[0][1], 5, fill=COL_INK, stroke="#FFFFFF", stroke_width=1)
    cv.add_circle(sp_e0[4][0], sp_e0[4][1], 6, fill=COL_CRIMSON, stroke="#FFFFFF", stroke_width=2)

    cv.add_text(242, 490, "Start r_0 = 1 -> 1-Lap r_1 = 194481/130321 > 1!", size=11, weight="bold", fill=COL_CRIMSON, anchor="middle", mono=True)

    cv.add_callout_card(
        42, 514, 400, 306,
        "Why Unpinned Closed Torsors Fail",
        [
            "Annulus: {1 <= ||x||_inf <= 2} (8 cells)",
            "Flow:    f_k = R_{90}^k(1, 20) (outward!)",
            "Torsor:  [eta] = -16 != 0, d^1 eta = 0",
            "Every cell & all 32 Filippov creases:",
            "  <g, f> in {-38, -21, -19} <= -19 < 0!",
            "Zero sliding modes (<f_+- , n> > 0).",
            "Yet Poincare map EXPANDS outward:",
            "  P(r_0) = (21/19)^4 r_0 > r_0!",
            "Angular drop -16 masks radial drift!",
        ],
        fill="#F8FAFC", stroke=COL_CRIMSON, title_ink=COL_CRIMSON, size=10, line_step=28,
    )

    # Panel B (Center): Theorem E1 — Pinned-Torsor Poincare Contraction
    cv.add_panel(476, 96, 444, 744, "B. E1: Pinned Contraction 16/81", "CERTIFIED", COL_EMERALD_FILL, COL_EMERALD)

    # Square annulus {2 <= ||x||_inf <= 6} centered at (698, 310), scale 25 px per unit (r=6 -> 150, r=2 -> 50, r*=10/3 -> 83)
    e1_cx, e1_cy = 698, 310
    cv.add_rect(e1_cx - 150, e1_cy - 150, 300, 300, fill=COL_TEAL_SOFT, stroke=COL_SLATE, stroke_width=2, role="shape")
    cv.add_rect(e1_cx - 50, e1_cy - 50, 100, 100, fill=COL_PANEL_BG, stroke=COL_SLATE, stroke_width=2, role="shape")

    # Limit cycle square r* = 10/3 (83 px) in emerald dashed
    cv.add_rect(e1_cx - 83, e1_cy - 83, 166, 166, fill="none", stroke=COL_EMERALD, stroke_width=3, role="shape")

    # Outer trajectory from r=6 (150px) -> 1 lap r=938/243 (~97px) contracting inward
    out_pts = [
        (e1_cx + 150, e1_cy + 150),
        (e1_cx + 128, e1_cy - 128),
        (e1_cx - 113, e1_cy - 113),
        (e1_cx - 103, e1_cy + 103),
        (e1_cx + 97, e1_cy + 97),
    ]
    for i in range(4):
        cv.add_arrow(out_pts[i][0], out_pts[i][1], out_pts[i + 1][0], out_pts[i + 1][1], stroke=COL_BLUE, stroke_width=2)

    # Inner trajectory from r=2 (50px) -> 1 lap r=238/81 (~73px) expanding outward toward r*=83px
    in_pts = [
        (e1_cx + 50, e1_cy + 50),
        (e1_cx + 61, e1_cy - 61),
        (e1_cx - 68, e1_cy - 68),
        (e1_cx - 71, e1_cy + 71),
        (e1_cx + 73, e1_cy + 73),
    ]
    for i in range(4):
        cv.add_arrow(in_pts[i][0], in_pts[i][1], in_pts[i + 1][0], in_pts[i + 1][1], stroke=COL_AMBER, stroke_width=2)

    cv.add_text(698, 490, "Unique Rational Limit Cycle r* = 10/3", size=11, weight="bold", fill=COL_EMERALD, anchor="middle", mono=True)

    cv.add_callout_card(
        494, 514, 408, 306,
        "Pinned-Torsor & Bouligand Certification",
        [
            "Annulus: {2 <= ||x||_inf <= 6} (8 cells)",
            "Bouligand Invariance: <f, n_out> = -1 < 0",
            "  (incl. 270-deg reflex inner corners!)",
            "Global CPA LP: INFEASIBLE (Farkas cycle)",
            "Flat Torsor [eta] = -96: D^+ V_tilde <= -8",
            "Sector Refraction: r |-> (2/3)r + 10/9",
            "1-Lap Pinned Contraction (Ghrist §6.2):",
            "  P(r) - 10/3 = (16/81) * (r - 10/3)!",
            "  r=2 -> 238/81;   r=6 -> 938/243.",
        ],
        fill="#F8FAFC", stroke=COL_EMERALD, title_ink=COL_EMERALD, size=10, line_step=28,
    )

    # Panel C (Right): Theorem E2 — Non-Orientable Mobius Band M_N Z/2Z Sheaf Torsion
    cv.add_panel(936, 96, 440, 744, "C. E2: Mobius Z_{-1} Torsion", "H^1 ~= Z/2Z", COL_VIOLET_FILL, COL_VIOLET)

    # Fundamental N=4 triangulated Mobius strip rectangle with reversed vertical seam arrows!
    mx0, my0, mw, mh = 978, 196, 356, 176
    cv.add_rect(mx0, my0, mw, mh, fill=COL_VIOLET_SOFT, stroke="none", stroke_width=0, role="shape")
    panel_w = mw // 4
    for k in range(4):
        px = mx0 + k * panel_w
        cv.add_line(px, my0, px + panel_w, my0, stroke=COL_SLATE, stroke_width=2)
        cv.add_line(px, my0 + mh, px + panel_w, my0 + mh, stroke=COL_SLATE, stroke_width=2)
        cv.add_line(px, my0 + mh, px + panel_w, my0, stroke=COL_INDIGO, stroke_width=1, dash="4,3")
        if k > 0:
            cv.add_line(px, my0, px, my0 + mh, stroke=COL_SLATE, stroke_width=2)

    # Left seam (upward arrow, +1) vs Right antipodal seam (downward arrow, R_e = -1 in violet!)
    cv.add_arrow(mx0, my0 + mh, mx0, my0 + 10, stroke=COL_VIOLET, stroke_width=4)
    cv.add_arrow(mx0 + mw, my0, mx0 + mw, my0 + mh - 10, stroke=COL_VIOLET, stroke_width=4)

    cv.add_text(1156, 178, "Triangulated Mobius Band M_N (chi = 0)", size=11, weight="bold", fill=COL_VIOLET, anchor="middle", mono=True)
    cv.add_text(968, 288, "+1", size=12, weight="bold", fill=COL_VIOLET, anchor="end", mono=True)
    cv.add_text(1344, 288, "-1", size=12, weight="bold", fill=COL_VIOLET, anchor="start", mono=True)
    cv.add_text(1156, 404, "Antipodal Seam Twist: R_e = -1 in GL_1(Z)", size=11, weight="bold", fill=COL_VIOLET, anchor="middle", mono=True)
    cv.add_text(1156, 426, "Single Boundary Cycle (2N edges) for all N >= 3", size=10, fill=COL_SLATE, anchor="middle", mono=True)

    cv.add_callout_card(
        954, 456, 404, 364,
        "Exact Z vs Q Twisted Cohomology Split",
        [
            "Orientable Annulus: H^1(A; Z) ~= Z (free).",
            "Non-Orientable M_N carrying Z_{-1} (N=3..12):",
            "  * Exact Complex: delta^1 o delta^0 == 0",
            "  * Unimodular Coboundary SNF:",
            "      SNF(delta^0_{M_N}) = [1, ..., 1, 2]",
            "      (2N - 1 units and ONE factor of 2!)",
            "  * Integral Cohomology:",
            "      H^1(M_N; Z_{-1}) ~= Z / 2Z  (TORSION!)",
            "  * Rational Cohomology:",
            "      H^1(M_N; Q_{-1}) == 0       (TRIVIAL!)",
            "Odd loop cocycles trivialize over (1/2)Z,",
            "never over Z!",
        ],
        fill="#F8FAFC", stroke=COL_VIOLET, title_ink=COL_VIOLET, size=10, line_step=25,
    )
    return cv


# ---------------------------------------------------------------------------
# Master Atlas Runner & Self-Auditor
# ---------------------------------------------------------------------------

ATLAS_BUILDERS: Tuple[Callable[[], SVGCanvas], ...] = (
    build_fig01,
    build_fig02,
    build_fig03,
    build_fig04,
    build_fig05,
    build_fig06,
    build_fig07,
    build_fig08,
    build_fig09,
    build_fig10,
)


def generate_all_atlas_svgs(out_dir: str = _PLOTS_DIR) -> Dict[str, Any]:
    prev_handler = signal.signal(signal.SIGALRM, _alarm_handler)
    prev_rem = signal.alarm(20)
    t0 = time.perf_counter_ns()
    try:
        os.makedirs(out_dir, exist_ok=True)
        reports: List[Dict[str, Any]] = []
        for builder in ATLAS_BUILDERS:
            canvas = builder()
            rep = canvas.save(out_dir)
            reports.append(rep)
    finally:
        signal.alarm(prev_rem if prev_rem > 0 else 0)
        signal.signal(signal.SIGALRM, prev_handler)

    elapsed_ms = (time.perf_counter_ns() - t0) // 1_000_000
    return {
        "plots_dir": out_dir,
        "svg_count": len(reports),
        "total_oob": sum(int(r["oob_count"]) for r in reports),
        "total_overlaps": sum(int(r["overlap_count"]) for r in reports),
        "elapsed_ms": elapsed_ms,
        "status": "PASS",
        "files": reports,
    }


def main() -> int:
    summary = generate_all_atlas_svgs(_PLOTS_DIR)
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
