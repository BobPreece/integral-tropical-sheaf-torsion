from __future__ import annotations

"""Wave II Mandatory SVG Geometry, Bounding-Box Overlap & XML Gate (`SPEC_WAVE2.md` §2.1).

Constitutional Compliance:
- 100% Python 3.9+ stdlib only (`xml.etree.ElementTree`, `fractions.Fraction`, `re`, `os`, `signal`, `time`, `json`).
- Strictly ZERO `float` literals, ZERO `float(...)` calls, ZERO `float` annotations, ZERO `ast.Div` (`/`),
  and ZERO `isinstance` calls (`type(x) is ...` used throughout).
- Exact arbitrary-precision `fractions.Fraction` geometry for:
  1. XML well-formedness, `<svg viewBox="0 0 1400 900">`, and full 10-figure atlas completeness (`fig01..fig10`).
  2. Exact 2D affine transforms (`translate`, `scale`, `matrix`, `rotate` via exact quadrant angles + pure-rational
     Taylor trig approximation) and inherited `<g>` / inline CSS `style="..."` presentation attributes.
  3. Exact stroke-inflated & Bezier control-polygon hull bounding boxes for `<rect>`, `<circle>`, `<ellipse>`,
     `<line>`, `<polyline>`, `<polygon>`, `<path>` (`M,m,L,l,H,h,V,v,C,c,S,s,Q,q,T,t,A,a,Z,z`), and `<text>`/`<tspan>`.
  4. Strict `OOB == 0` check within `[0, 1400] x [0, 900]` (including Bezier control hulls & half `stroke-width`).
  5. Strict `overlaps == 0` check:
     - Zero `<text>`-to-`<text>` bounding-box intersections.
     - Zero `<text>`-to-shape/curve/line intersections, rigorously distinguishing valid enclosing `<rect>`
       cards/panels/cells (strictly containing `<text>` bbox on all 4 sides with `>= 2px` inner margin and
       non-occluding z-order) from `<line>`, `<path>`, `<polyline>`, `<polygon>`, `<circle>`, `<ellipse>`,
       or partial/thin/occluding `<rect>` bars & borders slicing through text.
"""

from dataclasses import dataclass
from fractions import Fraction
import json
import os
from pathlib import Path
import re
import signal
import sys
import tempfile
import time
from typing import Any
import xml.etree.ElementTree as ET

CANVAS_MIN_X = Fraction(0, 1)
CANVAS_MIN_Y = Fraction(0, 1)
CANVAS_MAX_X = Fraction(1400, 1)
CANVAS_MAX_Y = Fraction(900, 1)
CONTAINER_MIN_MARGIN_PX = Fraction(2, 1)

REQUIRED_ATLAS_FILENAMES: tuple[str, ...] = (
    "fig01_paramid_torsion_and_join_dichotomy.svg",
    "fig02_max6_syl2_padic_frontier.svg",
    "fig03_klein_sail_cg_split.svg",
    "fig04_five_ray_unbounded_chvatal_rank.svg",
    "fig05_reeve_polar_bss_torsion.svg",
    "fig06_airy_spiderweb_and_chord_annulus.svg",
    "fig07_2d_precision_bockstein_snf.svg",
    "fig08_group_circuit_compression_and_q8_cocycle.svg",
    "fig09_proper_coset_snf_trichotomy.svg",
    "fig10_escher_waterfall_and_mobius_torsion.svg",
)

NON_RENDERED_TAGS = frozenset({
    "defs",
    "clippath",
    "marker",
    "mask",
    "pattern",
    "lineargradient",
    "radialgradient",
    "style",
    "title",
    "desc",
    "metadata",
    "symbol",
    "filter",
    "script",
})

VISUAL_SHAPE_TAGS = frozenset({
    "rect",
    "circle",
    "ellipse",
    "line",
    "polyline",
    "polygon",
    "path",
})

_NUM_RE = re.compile(r"^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$")
_LEN_RE = re.compile(
    r"^\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)\s*(px|pt|pc|in|cm|mm|em|ex|%)?\s*$",
    re.IGNORECASE,
)
_COORD_TOKEN_RE = re.compile(r"[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?")
_PATH_TOKEN_RE = re.compile(r"[MmLlHhVvCcSsQqTtAaZz]|[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?")
_TRANSFORM_CALL_RE = re.compile(r"([a-zA-Z]+)\s*\(([^)]*)\)")

_NARROW_CHARS = frozenset("ilI1.,:;!|'()[]{} `")
_WIDE_CHARS = frozenset("MWmw@%#&QGO0")

# High-accuracy rational approximation to pi (104348 / 33215, accurate to ~3.3e-10) for non-quadrant SVG rotations
_PI_RAT = Fraction(104348, 33215)

# Affine 2D matrix `((a, c, e), (b, d, f))` mapping `(x, y) -> (a*x + c*y + e, b*x + d*y + f)`
Affine2D = tuple[tuple[Fraction, Fraction, Fraction], tuple[Fraction, Fraction, Fraction]]
IDENTITY_AFFINE: Affine2D = (
    (Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)),
    (Fraction(0, 1), Fraction(1, 1), Fraction(0, 1)),
)

Point2D = tuple[Fraction, Fraction]
BBox = tuple[Fraction, Fraction, Fraction, Fraction]  # (xmin, ymin, xmax, ymax)
Segment2D = tuple[Point2D, Point2D]


class _SVGAuditTimeout(RuntimeError):
    pass


def _alarm_handler(signum: int, frame: object) -> None:
    _ = (signum, frame)
    raise _SVGAuditTimeout("SVG auditor exceeded 20-second wall-clock timeout")


@dataclass(frozen=True)
class VisualShapeRecord:
    doc_index: int
    tag: str
    elem_id: str
    oob_bbox: BBox
    tight_bbox: BBox
    stroke_pad: Fraction
    has_fill: bool
    has_stroke: bool
    is_axis_aligned_rect: bool
    rect_inner_bbox: BBox | None
    circle_geom: tuple[Fraction, Fraction, Fraction] | None  # (cx, cy, r) when unrotated uniform scale
    ellipse_geom: tuple[Fraction, Fraction, Fraction, Fraction] | None  # (cx, cy, rx, ry)
    segments: tuple[Segment2D, ...]
    bezier_subhulls: tuple[BBox, ...]
    is_closed: bool


@dataclass(frozen=True)
class TextRecord:
    doc_index: int
    elem_id: str
    content: str
    bbox: BBox
    font_size: Fraction
    anchor: str


# ---------------------------------------------------------------------------
# Pure-Fraction Numeric, Unit, Style & Transform Parsers
# ---------------------------------------------------------------------------


def _rat_str(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    # Approximate to 2 decimal places as an exact string for human-readable diagnostics without float!
    neg = q.numerator < 0
    aq = -q if neg else q
    scaled100 = (aq.numerator * 100 + (aq.denominator // 2)) // aq.denominator
    whole = scaled100 // 100
    frac = scaled100 % 100
    prefix = "-" if neg else ""
    return f"{prefix}{whole}.{frac:02d} ({q.numerator}/{q.denominator})"


def _bbox_dict(b: BBox) -> dict[str, str]:
    return {
        "xmin": _rat_str(b[0]),
        "ymin": _rat_str(b[1]),
        "xmax": _rat_str(b[2]),
        "ymax": _rat_str(b[3]),
    }


def parse_svg_number(raw: str) -> Fraction:
    """Parse an integer, decimal, or scientific-notation SVG number strictly into `Fraction` (zero float)."""
    s = raw.strip()
    if not _NUM_RE.match(s):
        raise ValueError(f"Invalid SVG numeric token: {raw!r}")
    return Fraction(s)


def parse_svg_length(
    raw: str | None,
    default: Fraction = Fraction(0, 1),
    font_size: Fraction = Fraction(12, 1),
    ref_span: Fraction = CANVAS_MAX_X,
) -> Fraction:
    """Parse an SVG coordinate/length attribute (with optional px/pt/em/% unit) into exact `Fraction`."""
    if raw is None:
        return default
    s = raw.strip()
    if not s:
        return default
    m = _LEN_RE.match(s)
    if m is None:
        raise ValueError(f"Invalid SVG length value: {raw!r}")
    val = Fraction(m.group(1))
    unit = (m.group(2) or "px").lower()
    if unit == "px":
        return val
    if unit == "pt":
        return val * Fraction(4, 3)
    if unit == "pc":
        return val * Fraction(16, 1)
    if unit == "in":
        return val * Fraction(96, 1)
    if unit == "cm":
        return val * Fraction(9600, 254)
    if unit == "mm":
        return val * Fraction(960, 254)
    if unit == "em":
        return val * font_size
    if unit == "ex":
        return val * font_size * Fraction(1, 2)
    if unit == "%":
        return val * ref_span * Fraction(1, 100)
    return val


def _strip_ns(tag: str) -> str:
    if "}" in tag:
        return tag.split("}", 1)[1].lower()
    return tag.lower()


def _parse_inline_style(style_raw: str | None) -> dict[str, str]:
    out: dict[str, str] = {}
    if not style_raw:
        return out
    for part in style_raw.split(";"):
        if ":" not in part:
            continue
        k, v = part.split(":", 1)
        ks = k.strip().lower()
        vs = v.strip()
        if ks and vs:
            out[ks] = vs
    return out


def _effective_props(elem: ET.Element, parent_props: dict[str, str]) -> dict[str, str]:
    props = dict(parent_props)
    inheritable_attrs = (
        "fill",
        "fill-opacity",
        "stroke",
        "stroke-width",
        "stroke-opacity",
        "opacity",
        "font-size",
        "font-family",
        "font-weight",
        "text-anchor",
        "dominant-baseline",
        "alignment-baseline",
        "display",
        "visibility",
    )
    for k in inheritable_attrs:
        if k in elem.attrib:
            props[k] = elem.attrib[k].strip()
    inline = _parse_inline_style(elem.attrib.get("style"))
    for k, v in inline.items():
        props[k] = v
    return props


def _compose_affine(m1: Affine2D, m2: Affine2D) -> Affine2D:
    """Return `m1 @ m2` where `(m1 @ m2)(p) == m1(m2(p))`."""
    (a1, c1, e1), (b1, d1, f1) = m1
    (a2, c2, e2), (b2, d2, f2) = m2
    return (
        (a1 * a2 + c1 * b2, a1 * c2 + c1 * d2, a1 * e2 + c1 * f2 + e1),
        (b1 * a2 + d1 * b2, b1 * c2 + d1 * d2, b1 * e2 + d1 * f2 + f1),
    )


def _apply_affine(m: Affine2D, p: Point2D) -> Point2D:
    (a, c, e), (b, d, f) = m
    x, y = p
    return (a * x + c * y + e, b * x + d * y + f)


def _affine_scale_bound(m: Affine2D) -> Fraction:
    """Conservative rational upper bound on linear stroke magnification under `m`."""
    (a, c, _), (b, d, _) = m
    col1 = abs(a) + abs(b)
    col2 = abs(c) + abs(d)
    return col1 if col1 >= col2 else col2


def _rat_cos_sin_deg(deg: Fraction) -> tuple[Fraction, Fraction]:
    """Pure-Fraction cosine & sine in degrees (exact at multiples of 90 deg; 10-term Taylor elsewhere)."""
    # Normalize mod 360 into [0, 360)
    q_turns = deg.numerator // (360 * deg.denominator)
    rem = deg - Fraction(360 * q_turns, 1)
    if rem < 0:
        rem = rem + Fraction(360, 1)
    if rem == Fraction(0, 1):
        return (Fraction(1, 1), Fraction(0, 1))
    if rem == Fraction(90, 1):
        return (Fraction(0, 1), Fraction(1, 1))
    if rem == Fraction(180, 1):
        return (Fraction(-1, 1), Fraction(0, 1))
    if rem == Fraction(270, 1):
        return (Fraction(0, 1), Fraction(-1, 1))

    # Reduce into [-45, 45] around closest quadrant multiple of 90
    quad = int((rem * Fraction(1, 90) + Fraction(1, 2)).numerator // (rem * Fraction(1, 90) + Fraction(1, 2)).denominator)
    delta_deg = rem - Fraction(90 * quad, 1)
    theta = delta_deg * _PI_RAT * Fraction(1, 180)
    t2 = theta * theta

    # 6-term Taylor polynomials on |theta| <= pi/4 < 0.79 (error < 10^-10)
    cos_v = Fraction(1, 1)
    sin_v = theta
    c_term = Fraction(1, 1)
    s_term = theta
    for k in range(1, 6):
        c_term = -c_term * t2 * Fraction(1, (2 * k - 1) * (2 * k))
        cos_v = cos_v + c_term
        s_term = -s_term * t2 * Fraction(1, (2 * k) * (2 * k + 1))
        sin_v = sin_v + s_term

    q_mod = quad % 4
    if q_mod == 0:
        return (cos_v, sin_v)
    if q_mod == 1:
        return (-sin_v, cos_v)
    if q_mod == 2:
        return (-cos_v, -sin_v)
    return (sin_v, -cos_v)


def parse_svg_transform(raw: str | None) -> Affine2D:
    """Parse SVG `transform` attribute (`translate`, `scale`, `rotate`, `matrix`) into exact `Affine2D`."""
    if not raw or not raw.strip():
        return IDENTITY_AFFINE
    cur = IDENTITY_AFFINE
    for m in _TRANSFORM_CALL_RE.finditer(raw):
        kind = m.group(1).lower()
        nums = [Fraction(tok) for tok in _COORD_TOKEN_RE.findall(m.group(2))]
        if kind == "translate":
            tx = nums[0] if len(nums) >= 1 else Fraction(0, 1)
            ty = nums[1] if len(nums) >= 2 else Fraction(0, 1)
            step: Affine2D = (
                (Fraction(1, 1), Fraction(0, 1), tx),
                (Fraction(0, 1), Fraction(1, 1), ty),
            )
        elif kind == "scale":
            sx = nums[0] if len(nums) >= 1 else Fraction(1, 1)
            sy = nums[1] if len(nums) >= 2 else sx
            step = (
                (sx, Fraction(0, 1), Fraction(0, 1)),
                (Fraction(0, 1), sy, Fraction(0, 1)),
            )
        elif kind == "rotate":
            ang = nums[0] if len(nums) >= 1 else Fraction(0, 1)
            cx = nums[1] if len(nums) >= 3 else Fraction(0, 1)
            cy = nums[2] if len(nums) >= 3 else Fraction(0, 1)
            cs, sn = _rat_cos_sin_deg(ang)
            rot: Affine2D = (
                (cs, -sn, Fraction(0, 1)),
                (sn, cs, Fraction(0, 1)),
            )
            if cx != 0 or cy != 0:
                t_pos: Affine2D = ((Fraction(1, 1), Fraction(0, 1), cx), (Fraction(0, 1), Fraction(1, 1), cy))
                t_neg: Affine2D = ((Fraction(1, 1), Fraction(0, 1), -cx), (Fraction(0, 1), Fraction(1, 1), -cy))
                step = _compose_affine(t_pos, _compose_affine(rot, t_neg))
            else:
                step = rot
        elif kind == "matrix" and len(nums) == 6:
            a, b, c, d, e, f = nums
            step = ((a, c, e), (b, d, f))
        else:
            raise ValueError(f"Unsupported or malformed SVG transform `{m.group(0)}`")
        cur = _compose_affine(cur, step)
    return cur


# ---------------------------------------------------------------------------
# Pure-Fraction Bounding-Box, Bezier De Casteljau & Segment Intersection Math
# ---------------------------------------------------------------------------


def _hull_of_points(pts: list[Point2D], pad: Fraction = Fraction(0, 1)) -> BBox:
    xs = [p[0] for p in pts]
    ys = [p[1] for p in pts]
    return (min(xs) - pad, min(ys) - pad, max(xs) + pad, max(ys) + pad)


def _union_bboxes(boxes: list[BBox]) -> BBox:
    return (
        min(b[0] for b in boxes),
        min(b[1] for b in boxes),
        max(b[2] for b in boxes),
        max(b[3] for b in boxes),
    )


def _midpoint(p: Point2D, q: Point2D) -> Point2D:
    half = Fraction(1, 2)
    return ((p[0] + q[0]) * half, (p[1] + q[1]) * half)


def _subdivide_cubic_hulls(
    p0: Point2D,
    p1: Point2D,
    p2: Point2D,
    p3: Point2D,
    depth: int = 3,
    pad: Fraction = Fraction(0, 1),
) -> list[BBox]:
    """Exact de Casteljau subdivision into `2^depth` tight convex control-polygon hulls covering the cubic curve."""
    if depth <= 0:
        return [_hull_of_points([p0, p1, p2, p3], pad)]
    p01 = _midpoint(p0, p1)
    p12 = _midpoint(p1, p2)
    p23 = _midpoint(p2, p3)
    p012 = _midpoint(p01, p12)
    p123 = _midpoint(p12, p23)
    pm = _midpoint(p012, p123)
    return _subdivide_cubic_hulls(p0, p01, p012, pm, depth - 1, pad) + _subdivide_cubic_hulls(
        pm, p123, p23, p3, depth - 1, pad
    )


def _subdivide_quad_hulls(
    p0: Point2D,
    p1: Point2D,
    p2: Point2D,
    depth: int = 3,
    pad: Fraction = Fraction(0, 1),
) -> list[BBox]:
    """Exact de Casteljau subdivision into `2^depth` tight convex control-polygon hulls covering the quadratic curve."""
    if depth <= 0:
        return [_hull_of_points([p0, p1, p2], pad)]
    p01 = _midpoint(p0, p1)
    p12 = _midpoint(p1, p2)
    pm = _midpoint(p01, p12)
    return _subdivide_quad_hulls(p0, p01, pm, depth - 1, pad) + _subdivide_quad_hulls(pm, p12, p2, depth - 1, pad)


def _bboxes_intersect_open(a: BBox, b: BBox) -> bool:
    """True iff two axis-aligned boxes have strictly positive overlap area (or degenerately touch inside)."""
    x0 = a[0] if a[0] >= b[0] else b[0]
    y0 = a[1] if a[1] >= b[1] else b[1]
    x1 = a[2] if a[2] <= b[2] else b[2]
    y1 = a[3] if a[3] <= b[3] else b[3]
    return x0 < x1 and y0 < y1


def _bboxes_intersect_closed(a: BBox, b: BBox) -> bool:
    x0 = a[0] if a[0] >= b[0] else b[0]
    y0 = a[1] if a[1] >= b[1] else b[1]
    x1 = a[2] if a[2] <= b[2] else b[2]
    y1 = a[3] if a[3] <= b[3] else b[3]
    return x0 <= x1 and y0 <= y1


def _segment_intersects_bbox(seg: Segment2D, box: BBox) -> bool:
    """Exact rational Liang-Barsky test: True iff closed segment `seg` intersects closed `box`."""
    (x0, y0), (x1, y1) = seg
    bx0, by0, bx1, by1 = box
    dx = x1 - x0
    dy = y1 - y0
    t_min = Fraction(0, 1)
    t_max = Fraction(1, 1)

    checks = (
        (-dx, x0 - bx0),
        (dx, bx1 - x0),
        (-dy, y0 - by0),
        (dy, by1 - y0),
    )
    for p_val, q_val in checks:
        if p_val == 0:
            if q_val < 0:
                return False
        else:
            ratio = Fraction(q_val.numerator * p_val.denominator, q_val.denominator * p_val.numerator)
            if p_val < 0:
                if ratio > t_max:
                    return False
                if ratio > t_min:
                    t_min = ratio
            else:
                if ratio < t_min:
                    return False
                if ratio < t_max:
                    t_max = ratio
    return t_min <= t_max


def _point_in_polygon_rational(pt: Point2D, poly_segs: tuple[Segment2D, ...]) -> bool:
    """Exact rational ray-casting point-in-polygon check along horizontal ray to +infinity."""
    px, py = pt
    inside = False
    for (x1, y1), (x2, y2) in poly_segs:
        if (y1 > py) != (y2 > py):
            dy = y2 - y1
            x_int = x1 + (py - y1) * (x2 - x1) * Fraction(dy.denominator, dy.numerator)
            if px < x_int:
                inside = not inside
    return inside


# ---------------------------------------------------------------------------
# SVG `<path>` Parser (`M,m,L,l,H,h,V,v,C,c,S,s,Q,q,T,t,A,a,Z,z`)
# ---------------------------------------------------------------------------


def _parse_path_geometry(
    d_attr: str,
    ctm: Affine2D,
    stroke_pad: Fraction,
) -> tuple[BBox | None, BBox | None, list[Segment2D], list[BBox], bool]:
    """Parse SVG `<path d="...">` and return:
    `(oob_control_hull_bbox, tight_curve_bbox, line_segments, bezier_subhulls, is_closed)`.
    """
    tokens = _PATH_TOKEN_RE.findall(d_attr)
    if not tokens:
        return (None, None, [], [], False)

    idx = 0
    n_tok = len(tokens)
    cmd = ""
    cur_x = Fraction(0, 1)
    cur_y = Fraction(0, 1)
    start_x = Fraction(0, 1)
    start_y = Fraction(0, 1)
    last_ctrl_x: Fraction | None = None
    last_ctrl_y: Fraction | None = None
    last_cmd = ""

    control_pts_world: list[Point2D] = []
    segments_world: list[Segment2D] = []
    bezier_hulls_world: list[BBox] = []
    tight_boxes_world: list[BBox] = []
    is_closed = False

    def next_num() -> Fraction:
        nonlocal idx
        if idx >= n_tok:
            raise ValueError(f"Unexpected end of SVG path data in `{d_attr}`")
        val = parse_svg_number(tokens[idx])
        idx += 1
        return val

    def has_more_nums() -> bool:
        return idx < n_tok and not tokens[idx][0].isalpha()

    while idx < n_tok:
        if tokens[idx][0].isalpha():
            cmd = tokens[idx]
            idx += 1
        elif not cmd:
            raise ValueError(f"SVG path data starts without command: `{d_attr}`")

        if cmd in ("M", "m"):
            dx = next_num()
            dy = next_num()
            if cmd == "m":
                cur_x = cur_x + dx
                cur_y = cur_y + dy
            else:
                cur_x = dx
                cur_y = dy
            start_x, start_y = cur_x, cur_y
            pw = _apply_affine(ctm, (cur_x, cur_y))
            control_pts_world.append(pw)
            tight_boxes_world.append(_hull_of_points([pw], stroke_pad))
            last_ctrl_x, last_ctrl_y = None, None
            last_cmd = cmd
            # Implicit subsequent coordinate pairs after M/m are L/l per SVG 1.1 spec
            cmd = "l" if cmd == "m" else "L"

        elif cmd in ("L", "l"):
            while True:
                dx = next_num()
                dy = next_num()
                nx = (cur_x + dx) if cmd == "l" else dx
                ny = (cur_y + dy) if cmd == "l" else dy
                p0w = _apply_affine(ctm, (cur_x, cur_y))
                p1w = _apply_affine(ctm, (nx, ny))
                control_pts_world.extend([p0w, p1w])
                segments_world.append((p0w, p1w))
                tight_boxes_world.append(_hull_of_points([p0w, p1w], stroke_pad))
                cur_x, cur_y = nx, ny
                last_ctrl_x, last_ctrl_y = None, None
                last_cmd = cmd
                if not has_more_nums():
                    break

        elif cmd in ("H", "h"):
            while True:
                dx = next_num()
                nx = (cur_x + dx) if cmd == "h" else dx
                p0w = _apply_affine(ctm, (cur_x, cur_y))
                p1w = _apply_affine(ctm, (nx, cur_y))
                control_pts_world.extend([p0w, p1w])
                segments_world.append((p0w, p1w))
                tight_boxes_world.append(_hull_of_points([p0w, p1w], stroke_pad))
                cur_x = nx
                last_ctrl_x, last_ctrl_y = None, None
                last_cmd = cmd
                if not has_more_nums():
                    break

        elif cmd in ("V", "v"):
            while True:
                dy = next_num()
                ny = (cur_y + dy) if cmd == "v" else dy
                p0w = _apply_affine(ctm, (cur_x, cur_y))
                p1w = _apply_affine(ctm, (cur_x, ny))
                control_pts_world.extend([p0w, p1w])
                segments_world.append((p0w, p1w))
                tight_boxes_world.append(_hull_of_points([p0w, p1w], stroke_pad))
                cur_y = ny
                last_ctrl_x, last_ctrl_y = None, None
                last_cmd = cmd
                if not has_more_nums():
                    break

        elif cmd in ("C", "c"):
            while True:
                x1, y1 = next_num(), next_num()
                x2, y2 = next_num(), next_num()
                x3, y3 = next_num(), next_num()
                if cmd == "c":
                    x1, y1 = cur_x + x1, cur_y + y1
                    x2, y2 = cur_x + x2, cur_y + y2
                    x3, y3 = cur_x + x3, cur_y + y3
                p0w = _apply_affine(ctm, (cur_x, cur_y))
                p1w = _apply_affine(ctm, (x1, y1))
                p2w = _apply_affine(ctm, (x2, y2))
                p3w = _apply_affine(ctm, (x3, y3))
                control_pts_world.extend([p0w, p1w, p2w, p3w])
                sub_h = _subdivide_cubic_hulls(p0w, p1w, p2w, p3w, depth=3, pad=stroke_pad)
                bezier_hulls_world.extend(sub_h)
                tight_boxes_world.extend(sub_h)
                cur_x, cur_y = x3, y3
                last_ctrl_x, last_ctrl_y = x2, y2
                last_cmd = cmd
                if not has_more_nums():
                    break

        elif cmd in ("S", "s"):
            while True:
                x2, y2 = next_num(), next_num()
                x3, y3 = next_num(), next_num()
                if cmd == "s":
                    x2, y2 = cur_x + x2, cur_y + y2
                    x3, y3 = cur_x + x3, cur_y + y3
                if last_cmd in ("C", "c", "S", "s") and last_ctrl_x is not None and last_ctrl_y is not None:
                    x1 = Fraction(2, 1) * cur_x - last_ctrl_x
                    y1 = Fraction(2, 1) * cur_y - last_ctrl_y
                else:
                    x1, y1 = cur_x, cur_y
                p0w = _apply_affine(ctm, (cur_x, cur_y))
                p1w = _apply_affine(ctm, (x1, y1))
                p2w = _apply_affine(ctm, (x2, y2))
                p3w = _apply_affine(ctm, (x3, y3))
                control_pts_world.extend([p0w, p1w, p2w, p3w])
                sub_h = _subdivide_cubic_hulls(p0w, p1w, p2w, p3w, depth=3, pad=stroke_pad)
                bezier_hulls_world.extend(sub_h)
                tight_boxes_world.extend(sub_h)
                cur_x, cur_y = x3, y3
                last_ctrl_x, last_ctrl_y = x2, y2
                last_cmd = cmd
                if not has_more_nums():
                    break

        elif cmd in ("Q", "q"):
            while True:
                x1, y1 = next_num(), next_num()
                x2, y2 = next_num(), next_num()
                if cmd == "q":
                    x1, y1 = cur_x + x1, cur_y + y1
                    x2, y2 = cur_x + x2, cur_y + y2
                p0w = _apply_affine(ctm, (cur_x, cur_y))
                p1w = _apply_affine(ctm, (x1, y1))
                p2w = _apply_affine(ctm, (x2, y2))
                control_pts_world.extend([p0w, p1w, p2w])
                sub_h = _subdivide_quad_hulls(p0w, p1w, p2w, depth=3, pad=stroke_pad)
                bezier_hulls_world.extend(sub_h)
                tight_boxes_world.extend(sub_h)
                cur_x, cur_y = x2, y2
                last_ctrl_x, last_ctrl_y = x1, y1
                last_cmd = cmd
                if not has_more_nums():
                    break

        elif cmd in ("T", "t"):
            while True:
                x2, y2 = next_num(), next_num()
                if cmd == "t":
                    x2, y2 = cur_x + x2, cur_y + y2
                if last_cmd in ("Q", "q", "T", "t") and last_ctrl_x is not None and last_ctrl_y is not None:
                    x1 = Fraction(2, 1) * cur_x - last_ctrl_x
                    y1 = Fraction(2, 1) * cur_y - last_ctrl_y
                else:
                    x1, y1 = cur_x, cur_y
                p0w = _apply_affine(ctm, (cur_x, cur_y))
                p1w = _apply_affine(ctm, (x1, y1))
                p2w = _apply_affine(ctm, (x2, y2))
                control_pts_world.extend([p0w, p1w, p2w])
                sub_h = _subdivide_quad_hulls(p0w, p1w, p2w, depth=3, pad=stroke_pad)
                bezier_hulls_world.extend(sub_h)
                tight_boxes_world.extend(sub_h)
                cur_x, cur_y = x2, y2
                last_ctrl_x, last_ctrl_y = x1, y1
                last_cmd = cmd
                if not has_more_nums():
                    break

        elif cmd in ("A", "a"):
            while True:
                rx = abs(next_num())
                ry = abs(next_num())
                _xrot = next_num()
                _large_arc = next_num()
                _sweep = next_num()
                x2, y2 = next_num(), next_num()
                if cmd == "a":
                    x2, y2 = cur_x + x2, cur_y + y2
                # Conservative rational arc hull around chord midpoint inflated by max(rx, ry)
                rmax = rx if rx >= ry else ry
                p0w = _apply_affine(ctm, (cur_x, cur_y))
                p1w = _apply_affine(ctm, (x2, y2))
                mid_local = _midpoint((cur_x, cur_y), (x2, y2))
                arc_corners = [
                    _apply_affine(ctm, (mid_local[0] - rmax, mid_local[1] - rmax)),
                    _apply_affine(ctm, (mid_local[0] + rmax, mid_local[1] + rmax)),
                    p0w,
                    p1w,
                ]
                control_pts_world.extend(arc_corners)
                arc_box = _hull_of_points([p0w, p1w], stroke_pad)
                bezier_hulls_world.append(arc_box)
                tight_boxes_world.append(arc_box)
                cur_x, cur_y = x2, y2
                last_ctrl_x, last_ctrl_y = None, None
                last_cmd = cmd
                if not has_more_nums():
                    break

        elif cmd in ("Z", "z"):
            p0w = _apply_affine(ctm, (cur_x, cur_y))
            p1w = _apply_affine(ctm, (start_x, start_y))
            if p0w != p1w:
                segments_world.append((p0w, p1w))
                tight_boxes_world.append(_hull_of_points([p0w, p1w], stroke_pad))
            cur_x, cur_y = start_x, start_y
            is_closed = True
            last_ctrl_x, last_ctrl_y = None, None
            last_cmd = cmd
            cmd = ""

        else:
            raise ValueError(f"Unsupported SVG path command `{cmd}` in `{d_attr}`")

    if not control_pts_world:
        return (None, None, [], [], False)
    oob_box = _hull_of_points(control_pts_world, stroke_pad)
    tight_box = _union_bboxes(tight_boxes_world) if tight_boxes_world else oob_box
    return (oob_box, tight_box, segments_world, bezier_hulls_world, is_closed)


# ---------------------------------------------------------------------------
# `<text>` & `<tspan>` Conservative Pure-Fraction Bounding Box Model
# ---------------------------------------------------------------------------


def _estimate_text_width(text_str: str, font_size: Fraction, font_family: str) -> Fraction:
    if not text_str:
        return Fraction(0, 1)
    fam_low = font_family.lower()
    is_mono = any(tok in fam_low for tok in ("mono", "courier", "consolas", "menlo"))
    if is_mono:
        return Fraction(3, 5) * font_size * len(text_str)
    acc = Fraction(0, 1)
    for ch in text_str:
        if ch in _NARROW_CHARS:
            acc = acc + Fraction(7, 20)
        elif ch in _WIDE_CHARS or ord(ch) > 127:
            acc = acc + Fraction(13, 20)
        else:
            acc = acc + Fraction(11, 20)
    return acc * font_size


def _compute_single_text_span_bbox(
    content: str,
    x: Fraction,
    y: Fraction,
    dx: Fraction,
    dy: Fraction,
    font_size: Fraction,
    font_family: str,
    anchor: str,
    baseline: str,
    ctm: Affine2D,
) -> BBox | None:
    norm_text = " ".join(content.split())
    if not norm_text:
        return None
    w = _estimate_text_width(norm_text, font_size, font_family)
    bx = x + dx
    by = y + dy

    anc = anchor.lower().strip()
    if anc == "middle":
        x0 = bx - w * Fraction(1, 2)
        x1 = bx + w * Fraction(1, 2)
    elif anc == "end":
        x0 = bx - w
        x1 = bx
    else:
        x0 = bx
        x1 = bx + w

    bl = baseline.lower().strip()
    if bl in ("middle", "central", "mathematical"):
        y0 = by - font_size * Fraction(19, 40)
        y1 = by + font_size * Fraction(19, 40)
    elif bl in ("hanging", "text-before-edge"):
        y0 = by
        y1 = by + font_size * Fraction(19, 20)
    else:
        # Standard alphabetic baseline: 0.75 * F ascent above baseline, 0.20 * F descent below
        y0 = by - font_size * Fraction(3, 4)
        y1 = by + font_size * Fraction(1, 5)

    corners_world = [
        _apply_affine(ctm, (x0, y0)),
        _apply_affine(ctm, (x1, y0)),
        _apply_affine(ctm, (x1, y1)),
        _apply_affine(ctm, (x0, y1)),
    ]
    return _hull_of_points(corners_world)


def _extract_text_records(
    elem: ET.Element,
    props: dict[str, str],
    ctm: Affine2D,
    doc_index: int,
    elem_id: str,
) -> list[TextRecord]:
    font_size = parse_svg_length(props.get("font-size"), default=Fraction(12, 1), font_size=Fraction(12, 1))
    if font_size <= 0:
        return []
    font_family = props.get("font-family", "sans-serif")
    anchor = props.get("text-anchor", "start")
    baseline = props.get("dominant-baseline", props.get("alignment-baseline", "alphabetic"))

    base_x = parse_svg_length(elem.attrib.get("x"), default=Fraction(0, 1), font_size=font_size, ref_span=CANVAS_MAX_X)
    base_y = parse_svg_length(elem.attrib.get("y"), default=Fraction(0, 1), font_size=font_size, ref_span=CANVAS_MAX_Y)
    base_dx = parse_svg_length(elem.attrib.get("dx"), default=Fraction(0, 1), font_size=font_size, ref_span=CANVAS_MAX_X)
    base_dy = parse_svg_length(elem.attrib.get("dy"), default=Fraction(0, 1), font_size=font_size, ref_span=CANVAS_MAX_Y)

    tspans = [ch for ch in list(elem) if _strip_ns(ch.tag) == "tspan"]
    if not tspans:
        full_txt = "".join(elem.itertext())
        bb = _compute_single_text_span_bbox(
            full_txt, base_x, base_y, base_dx, base_dy, font_size, font_family, anchor, baseline, ctm
        )
        if bb is None:
            return []
        return [
            TextRecord(
                doc_index=doc_index,
                elem_id=elem_id,
                content=" ".join(full_txt.split()),
                bbox=bb,
                font_size=font_size,
                anchor=anchor,
            )
        ]

    # Multi-tspan or inline-tspan handling
    records: list[TextRecord] = []
    cur_x = base_x + base_dx
    cur_y = base_y + base_dy

    if elem.text and elem.text.strip():
        bb_lead = _compute_single_text_span_bbox(
            elem.text, cur_x, cur_y, Fraction(0, 1), Fraction(0, 1), font_size, font_family, anchor, baseline, ctm
        )
        if bb_lead is not None:
            records.append(
                TextRecord(
                    doc_index=doc_index,
                    elem_id=f"{elem_id}#lead",
                    content=" ".join(elem.text.split()),
                    bbox=bb_lead,
                    font_size=font_size,
                    anchor=anchor,
                )
            )
            cur_x = cur_x + _estimate_text_width(" ".join(elem.text.split()), font_size, font_family)

    for t_idx, ts in enumerate(tspans):
        ts_props = _effective_props(ts, props)
        ts_fs = parse_svg_length(ts_props.get("font-size"), default=font_size, font_size=font_size)
        ts_fam = ts_props.get("font-family", font_family)
        ts_anc = ts_props.get("text-anchor", anchor)
        ts_bl = ts_props.get("dominant-baseline", ts_props.get("alignment-baseline", baseline))

        has_explicit_pos = ("x" in ts.attrib) or ("y" in ts.attrib) or ("dy" in ts.attrib)
        if "x" in ts.attrib:
            cur_x = parse_svg_length(ts.attrib.get("x"), default=cur_x, font_size=ts_fs, ref_span=CANVAS_MAX_X)
        if "y" in ts.attrib:
            cur_y = parse_svg_length(ts.attrib.get("y"), default=cur_y, font_size=ts_fs, ref_span=CANVAS_MAX_Y)
        ts_dx = parse_svg_length(ts.attrib.get("dx"), default=Fraction(0, 1), font_size=ts_fs, ref_span=CANVAS_MAX_X)
        ts_dy = parse_svg_length(ts.attrib.get("dy"), default=Fraction(0, 1), font_size=ts_fs, ref_span=CANVAS_MAX_Y)
        cur_x = cur_x + ts_dx
        cur_y = cur_y + ts_dy

        ts_txt = "".join(ts.itertext())
        if ts_txt.strip():
            # If inline `<tspan>` has no explicit x/y/dy (e.g. subscript/bold inside a single phrase) and we had no splits,
            # merge inline spans on the same baseline if none of the tspans reposition x/y/dy!
            bb_ts = _compute_single_text_span_bbox(
                ts_txt, cur_x, cur_y, Fraction(0, 1), Fraction(0, 1), ts_fs, ts_fam, ts_anc, ts_bl, ctm
            )
            if bb_ts is not None:
                if not has_explicit_pos and len(tspans) > 0 and all(
                    ("x" not in c.attrib and "y" not in c.attrib and "dy" not in c.attrib) for c in tspans
                ):
                    # Pure inline formatting spans (`<text>H<tspan>1</tspan></text>`): merge as single text record!
                    merged_txt = "".join(elem.itertext())
                    bb_m = _compute_single_text_span_bbox(
                        merged_txt, base_x, base_y, base_dx, base_dy, font_size, font_family, anchor, baseline, ctm
                    )
                    if bb_m is not None:
                        return [
                            TextRecord(
                                doc_index=doc_index,
                                elem_id=elem_id,
                                content=" ".join(merged_txt.split()),
                                bbox=bb_m,
                                font_size=font_size,
                                anchor=anchor,
                            )
                        ]
                    return []
                records.append(
                    TextRecord(
                        doc_index=doc_index,
                        elem_id=f"{elem_id}#tspan{t_idx}",
                        content=" ".join(ts_txt.split()),
                        bbox=bb_ts,
                        font_size=ts_fs,
                        anchor=ts_anc,
                    )
                )
                if "x" not in ts.attrib:
                    cur_x = cur_x + _estimate_text_width(" ".join(ts_txt.split()), ts_fs, ts_fam)
        if ts.tail and ts.tail.strip():
            cur_x = cur_x + Fraction(2, 5) * ts_fs
            bb_tail = _compute_single_text_span_bbox(
                ts.tail, cur_x, cur_y, Fraction(0, 1), Fraction(0, 1), font_size, font_family, "start", baseline, ctm
            )
            if bb_tail is not None:
                records.append(
                    TextRecord(
                        doc_index=doc_index,
                        elem_id=f"{elem_id}#tail{t_idx}",
                        content=" ".join(ts.tail.split()),
                        bbox=bb_tail,
                        font_size=font_size,
                        anchor="start",
                    )
                )
    return records


# ---------------------------------------------------------------------------
# Visual Shape Extraction & Text-to-Shape Overlap Classification
# ---------------------------------------------------------------------------


def _compute_stroke_and_fill(
    tag: str,
    elem: ET.Element,
    props: dict[str, str],
    ctm: Affine2D,
) -> tuple[bool, bool, Fraction]:
    fill_val = props.get("fill", "none" if tag == "line" else "black").strip().lower()
    fill_op = parse_svg_number(props["fill-opacity"]) if "fill-opacity" in props else Fraction(1, 1)
    op = parse_svg_number(props["opacity"]) if "opacity" in props else Fraction(1, 1)
    has_fill = (fill_val != "none" and fill_val != "transparent" and fill_op > 0 and op > 0 and tag != "line")

    stroke_val = props.get("stroke", "none").strip().lower()
    has_explicit_sw = ("stroke-width" in elem.attrib) or ("stroke-width" in _parse_inline_style(elem.attrib.get("style")))
    sw_raw = props.get("stroke-width")
    sw = parse_svg_length(sw_raw, default=Fraction(1, 1))
    has_stroke = (stroke_val != "none" and stroke_val != "transparent" and sw > 0 and op > 0)
    # Conservative OOB stroke padding: include stroke half-width whenever stroke is active OR stroke-width explicitly set
    if stroke_val == "none" or sw <= 0:
        stroke_pad = Fraction(0, 1)
    elif has_stroke or has_explicit_sw:
        stroke_pad = sw * Fraction(1, 2) * _affine_scale_bound(ctm)
    else:
        stroke_pad = Fraction(0, 1)
    return (has_fill, has_stroke, stroke_pad)


def _parse_points_list(raw: str) -> list[Point2D]:
    nums = [Fraction(tok) for tok in _COORD_TOKEN_RE.findall(raw)]
    if len(nums) < 2 or (len(nums) % 2) != 0:
        return []
    return [(nums[i], nums[i + 1]) for i in range(0, len(nums), 2)]


def _extract_shape_record(
    tag: str,
    elem: ET.Element,
    props: dict[str, str],
    ctm: Affine2D,
    doc_index: int,
    elem_id: str,
) -> VisualShapeRecord | None:
    has_fill, has_stroke, stroke_pad = _compute_stroke_and_fill(tag, elem, props, ctm)
    if not has_fill and not has_stroke and stroke_pad == 0:
        return None

    (a, c, _), (b, d, _) = ctm
    is_unrotated = (b == 0 and c == 0 and a > 0 and d > 0)

    if tag == "rect":
        x = parse_svg_length(elem.attrib.get("x"), default=Fraction(0, 1), ref_span=CANVAS_MAX_X)
        y = parse_svg_length(elem.attrib.get("y"), default=Fraction(0, 1), ref_span=CANVAS_MAX_Y)
        w = parse_svg_length(elem.attrib.get("width"), default=Fraction(0, 1), ref_span=CANVAS_MAX_X)
        h = parse_svg_length(elem.attrib.get("height"), default=Fraction(0, 1), ref_span=CANVAS_MAX_Y)
        if w <= 0 or h <= 0:
            return None
        c0 = _apply_affine(ctm, (x, y))
        c1 = _apply_affine(ctm, (x + w, y))
        c2 = _apply_affine(ctm, (x + w, y + h))
        c3 = _apply_affine(ctm, (x, y + h))
        segs = ((c0, c1), (c1, c2), (c2, c3), (c3, c0))
        oob_bb = _hull_of_points([c0, c1, c2, c3], stroke_pad)
        inner_bb: BBox | None = None
        if is_unrotated:
            rx0, ry0 = c0
            rx1, ry1 = c2
            inner_bb = (rx0 + stroke_pad, ry0 + stroke_pad, rx1 - stroke_pad, ry1 - stroke_pad)
        return VisualShapeRecord(
            doc_index=doc_index,
            tag=tag,
            elem_id=elem_id,
            oob_bbox=oob_bb,
            tight_bbox=oob_bb,
            stroke_pad=stroke_pad,
            has_fill=has_fill,
            has_stroke=has_stroke,
            is_axis_aligned_rect=is_unrotated,
            rect_inner_bbox=inner_bb,
            circle_geom=None,
            ellipse_geom=None,
            segments=segs,
            bezier_subhulls=(),
            is_closed=True,
        )

    if tag == "circle":
        cx = parse_svg_length(elem.attrib.get("cx"), default=Fraction(0, 1), ref_span=CANVAS_MAX_X)
        cy = parse_svg_length(elem.attrib.get("cy"), default=Fraction(0, 1), ref_span=CANVAS_MAX_Y)
        r = parse_svg_length(elem.attrib.get("r"), default=Fraction(0, 1))
        if r <= 0:
            return None
        corners = [
            _apply_affine(ctm, (cx - r, cy - r)),
            _apply_affine(ctm, (cx + r, cy - r)),
            _apply_affine(ctm, (cx + r, cy + r)),
            _apply_affine(ctm, (cx - r, cy + r)),
        ]
        oob_bb = _hull_of_points(corners, stroke_pad)
        c_world = _apply_affine(ctm, (cx, cy))
        c_geom = (c_world[0], c_world[1], a * r) if (is_unrotated and a == d) else None
        e_geom = (c_world[0], c_world[1], a * r, d * r) if (is_unrotated and a != d) else None
        return VisualShapeRecord(
            doc_index=doc_index,
            tag=tag,
            elem_id=elem_id,
            oob_bbox=oob_bb,
            tight_bbox=oob_bb,
            stroke_pad=stroke_pad,
            has_fill=has_fill,
            has_stroke=has_stroke,
            is_axis_aligned_rect=False,
            rect_inner_bbox=None,
            circle_geom=c_geom,
            ellipse_geom=e_geom,
            segments=(),
            bezier_subhulls=(),
            is_closed=True,
        )

    if tag == "ellipse":
        cx = parse_svg_length(elem.attrib.get("cx"), default=Fraction(0, 1), ref_span=CANVAS_MAX_X)
        cy = parse_svg_length(elem.attrib.get("cy"), default=Fraction(0, 1), ref_span=CANVAS_MAX_Y)
        rx = parse_svg_length(elem.attrib.get("rx"), default=Fraction(0, 1), ref_span=CANVAS_MAX_X)
        ry = parse_svg_length(elem.attrib.get("ry"), default=Fraction(0, 1), ref_span=CANVAS_MAX_Y)
        if rx <= 0 or ry <= 0:
            return None
        corners = [
            _apply_affine(ctm, (cx - rx, cy - ry)),
            _apply_affine(ctm, (cx + rx, cy - ry)),
            _apply_affine(ctm, (cx + rx, cy + ry)),
            _apply_affine(ctm, (cx - rx, cy + ry)),
        ]
        oob_bb = _hull_of_points(corners, stroke_pad)
        c_world = _apply_affine(ctm, (cx, cy))
        e_geom = (c_world[0], c_world[1], a * rx, d * ry) if is_unrotated else None
        return VisualShapeRecord(
            doc_index=doc_index,
            tag=tag,
            elem_id=elem_id,
            oob_bbox=oob_bb,
            tight_bbox=oob_bb,
            stroke_pad=stroke_pad,
            has_fill=has_fill,
            has_stroke=has_stroke,
            is_axis_aligned_rect=False,
            rect_inner_bbox=None,
            circle_geom=None,
            ellipse_geom=e_geom,
            segments=(),
            bezier_subhulls=(),
            is_closed=True,
        )

    if tag == "line":
        x1 = parse_svg_length(elem.attrib.get("x1"), default=Fraction(0, 1), ref_span=CANVAS_MAX_X)
        y1 = parse_svg_length(elem.attrib.get("y1"), default=Fraction(0, 1), ref_span=CANVAS_MAX_Y)
        x2 = parse_svg_length(elem.attrib.get("x2"), default=Fraction(0, 1), ref_span=CANVAS_MAX_X)
        y2 = parse_svg_length(elem.attrib.get("y2"), default=Fraction(0, 1), ref_span=CANVAS_MAX_Y)
        p1 = _apply_affine(ctm, (x1, y1))
        p2 = _apply_affine(ctm, (x2, y2))
        oob_bb = _hull_of_points([p1, p2], stroke_pad)
        return VisualShapeRecord(
            doc_index=doc_index,
            tag=tag,
            elem_id=elem_id,
            oob_bbox=oob_bb,
            tight_bbox=oob_bb,
            stroke_pad=stroke_pad,
            has_fill=False,
            has_stroke=has_stroke or stroke_pad > 0,
            is_axis_aligned_rect=False,
            rect_inner_bbox=None,
            circle_geom=None,
            ellipse_geom=None,
            segments=((p1, p2),),
            bezier_subhulls=(),
            is_closed=False,
        )

    if tag in ("polyline", "polygon"):
        pts = _parse_points_list(elem.attrib.get("points", ""))
        if len(pts) < 2:
            return None
        wpts = [_apply_affine(ctm, p) for p in pts]
        segs_list = [(wpts[i], wpts[i + 1]) for i in range(len(wpts) - 1)]
        if tag == "polygon" and wpts[-1] != wpts[0]:
            segs_list.append((wpts[-1], wpts[0]))
        oob_bb = _hull_of_points(wpts, stroke_pad)
        return VisualShapeRecord(
            doc_index=doc_index,
            tag=tag,
            elem_id=elem_id,
            oob_bbox=oob_bb,
            tight_bbox=oob_bb,
            stroke_pad=stroke_pad,
            has_fill=has_fill and tag == "polygon",
            has_stroke=has_stroke,
            is_axis_aligned_rect=False,
            rect_inner_bbox=None,
            circle_geom=None,
            ellipse_geom=None,
            segments=tuple(segs_list),
            bezier_subhulls=(),
            is_closed=(tag == "polygon"),
        )

    if tag == "path":
        d_raw = elem.attrib.get("d", "")
        oob_bb_p, tight_bb_p, segs_p, bhulls_p, closed_p = _parse_path_geometry(d_raw, ctm, stroke_pad)
        if oob_bb_p is None or tight_bb_p is None:
            return None
        return VisualShapeRecord(
            doc_index=doc_index,
            tag=tag,
            elem_id=elem_id,
            oob_bbox=oob_bb_p,
            tight_bbox=tight_bb_p,
            stroke_pad=stroke_pad,
            has_fill=has_fill,
            has_stroke=has_stroke,
            is_axis_aligned_rect=False,
            rect_inner_bbox=None,
            circle_geom=None,
            ellipse_geom=None,
            segments=tuple(segs_p),
            bezier_subhulls=tuple(bhulls_p),
            is_closed=closed_p,
        )

    return None


def _check_text_shape_collision(txt: TextRecord, shp: VisualShapeRecord) -> str | None:
    """Return a non-None collision reason iff `txt` and `shp` illegally collide; `None` if disjoint or valid container."""
    tb = txt.bbox
    if not _bboxes_intersect_closed(tb, shp.tight_bbox):
        return None

    tx0, ty0, tx1, ty1 = tb
    margin = CONTAINER_MIN_MARGIN_PX
    occludes_on_top = shp.has_fill and shp.doc_index > txt.doc_index

    # 1. Axis-aligned `<rect>`: ONLY allowed as an enclosing container if:
    #    - non-occluding (drawn before `<text>` or unfilled frame), AND
    #    - inner clear box strictly contains `tb` on ALL 4 sides with `>= 2px` clearance!
    if shp.is_axis_aligned_rect and shp.rect_inner_bbox is not None:
        ix0, iy0, ix1, iy1 = shp.rect_inner_bbox
        strictly_contains = (
            ix0 + margin <= tx0
            and tx1 <= ix1 - margin
            and iy0 + margin <= ty0
            and ty1 <= iy1 - margin
        )
        if strictly_contains and not occludes_on_top:
            return None
        if strictly_contains and occludes_on_top:
            return "filled_<rect>_painted_over_<text>"
        return "<rect>_border_or_bar_intersects_<text>"

    # 2. Exact `<circle>` geometry: check exterior clearance vs perimeter intersection vs strict non-occluding node badge
    if shp.circle_geom is not None:
        cx, cy, r = shp.circle_geom
        sp = shp.stroke_pad
        qx = min(max(cx, tx0), tx1)
        qy = min(max(cy, ty0), ty1)
        d_min_sq = (qx - cx) * (qx - cx) + (qy - cy) * (qy - cy)
        r_out = r + sp
        if d_min_sq > r_out * r_out:
            return None
        dx_far = max(abs(tx0 - cx), abs(tx1 - cx))
        dy_far = max(abs(ty0 - cy), abs(ty1 - cy))
        d_max_sq = dx_far * dx_far + dy_far * dy_far
        r_in_clear = r - sp - margin
        if r_in_clear > 0 and d_max_sq <= r_in_clear * r_in_clear and not occludes_on_top:
            return None
        return "<circle>_perimeter_or_marker_intersects_<text>"

    # 3. Exact `<ellipse>` geometry: normalized rational quadratic test
    if shp.ellipse_geom is not None:
        cx, cy, rx, ry = shp.ellipse_geom
        sp = shp.stroke_pad
        qx = min(max(cx, tx0), tx1)
        qy = min(max(cy, ty0), ty1)
        rx_out = rx + sp
        ry_out = ry + sp
        lhs_min = (qx - cx) * (qx - cx) * ry_out * ry_out + (qy - cy) * (qy - cy) * rx_out * rx_out
        if lhs_min > rx_out * rx_out * ry_out * ry_out:
            return None
        rx_in = rx - sp - margin
        ry_in = ry - sp - margin
        if rx_in > 0 and ry_in > 0 and not occludes_on_top:
            dx_far = max(abs(tx0 - cx), abs(tx1 - cx))
            dy_far = max(abs(ty0 - cy), abs(ty1 - cy))
            if dx_far * dx_far * ry_in * ry_in + dy_far * dy_far * rx_in * rx_in <= rx_in * rx_in * ry_in * ry_in:
                return None
        return "<ellipse>_perimeter_or_body_intersects_<text>"

    # 4. `<line>`, `<polyline>`, `<polygon>`, `<path>`:
    #    Test EVERY line segment (against stroke-inflated text box; for closed containers require >= 2px clearance!)
    seg_pad = shp.stroke_pad if not shp.is_closed else (shp.stroke_pad + margin)
    padded_tb: BBox = (tx0 - seg_pad, ty0 - seg_pad, tx1 + seg_pad, ty1 + seg_pad)
    for seg in shp.segments:
        if _segment_intersects_bbox(seg, padded_tb):
            return f"<{shp.tag}>_segment_slices_<text>"

    # Test EVERY subdivided Bezier control-polygon sub-hull (already inflated by `stroke_pad`)
    bez_check_tb: BBox = (tx0, ty0, tx1, ty1) if not shp.is_closed else (
        tx0 - margin,
        ty0 - margin,
        tx1 + margin,
        ty1 + margin,
    )
    for bh in shp.bezier_subhulls:
        if _bboxes_intersect_closed(bez_check_tb, bh):
            return f"<{shp.tag}>_bezier_curve_slices_<text>"

    # If a closed `<polygon>` or closed `<path>` has no boundary edge near `tb`, check if `tb` is inside it
    # while `shp` is painted ON TOP of `txt` (occlusion!)
    if shp.is_closed and occludes_on_top and len(shp.segments) >= 3:
        center_pt: Point2D = ((tx0 + tx1) * Fraction(1, 2), (ty0 + ty1) * Fraction(1, 2))
        if _point_in_polygon_rational(center_pt, shp.segments):
            return f"filled_<{shp.tag}>_painted_over_<text>"

    return None


# ---------------------------------------------------------------------------
# Public Single-SVG & Full-Atlas Auditors
# ---------------------------------------------------------------------------


def audit_svg_string(xml_text: str, source_name: str = "<memory>.svg") -> dict[str, Any]:
    """Parse & audit a single SVG document string for XML validity, `1400x900` viewBox, `OOB == 0`, and `overlaps == 0`."""
    xml_errors: list[str] = []
    try:
        root = ET.fromstring(xml_text)
    except ET.ParseError as exc:
        return {
            "file": source_name,
            "status": "FAIL",
            "well_formed_xml": False,
            "viewbox_valid": False,
            "oob_count": 0,
            "overlap_count": 0,
            "xml_errors": [f"XML ParseError: {exc}"],
            "oob_violations": [],
            "overlap_violations": [],
            "shape_count": 0,
            "text_count": 0,
        }

    if _strip_ns(root.tag) != "svg":
        xml_errors.append(f"Root element must be `<svg>`, got `<{root.tag}>`")

    vb_raw = root.attrib.get("viewBox", "").strip()
    vb_nums = [Fraction(tok) for tok in _COORD_TOKEN_RE.findall(vb_raw)]
    viewbox_valid = (
        len(vb_nums) == 4
        and vb_nums[0] == CANVAS_MIN_X
        and vb_nums[1] == CANVAS_MIN_Y
        and vb_nums[2] == CANVAS_MAX_X
        and vb_nums[3] == CANVAS_MAX_Y
    )
    if not viewbox_valid:
        xml_errors.append(f"Expected `viewBox=\"0 0 1400 900\"`, got `{vb_raw!r}`")

    shapes: list[VisualShapeRecord] = []
    texts: list[TextRecord] = []
    doc_counter = 0

    def walk(elem: ET.Element, parent_props: dict[str, str], parent_ctm: Affine2D) -> None:
        nonlocal doc_counter
        tag = _strip_ns(elem.tag)
        if tag in NON_RENDERED_TAGS:
            return
        props = _effective_props(elem, parent_props)
        if props.get("display", "").lower() == "none" or props.get("visibility", "").lower() == "hidden":
            return
        local_tf = parse_svg_transform(elem.attrib.get("transform"))
        ctm = _compose_affine(parent_ctm, local_tf)

        doc_counter += 1
        cur_idx = doc_counter
        eid = elem.attrib.get("id") or f"{tag}@{cur_idx}"

        if tag in VISUAL_SHAPE_TAGS:
            rec = _extract_shape_record(tag, elem, props, ctm, cur_idx, eid)
            if rec is not None:
                shapes.append(rec)
            return

        if tag == "text":
            t_recs = _extract_text_records(elem, props, ctm, cur_idx, eid)
            texts.extend(t_recs)
            return

        for child in list(elem):
            walk(child, props, ctm)

    try:
        walk(root, {}, IDENTITY_AFFINE)
    except ValueError as exc:
        xml_errors.append(f"SVG attribute/geometry error: {exc}")

    # Require non-empty substantive SVG content (at least 1 shape and 1 text label unless already XML-invalid)
    if not xml_errors and (len(shapes) == 0 or len(texts) == 0):
        xml_errors.append(f"Degenerate/empty SVG content: shapes={len(shapes)}, texts={len(texts)}")

    # 1. Check OOB == 0 across ALL shapes (using full control-polygon hull + stroke_pad) AND ALL texts
    oob_violations: list[dict[str, Any]] = []
    for shp in shapes:
        x0, y0, x1, y1 = shp.oob_bbox
        if x0 < CANVAS_MIN_X or y0 < CANVAS_MIN_Y or x1 > CANVAS_MAX_X or y1 > CANVAS_MAX_Y:
            oob_violations.append({
                "kind": "shape_oob",
                "tag": shp.tag,
                "id": shp.elem_id,
                "bbox": _bbox_dict(shp.oob_bbox),
            })

    for txt in texts:
        x0, y0, x1, y1 = txt.bbox
        if x0 < CANVAS_MIN_X or y0 < CANVAS_MIN_Y or x1 > CANVAS_MAX_X or y1 > CANVAS_MAX_Y:
            oob_violations.append({
                "kind": "text_oob",
                "id": txt.elem_id,
                "text": txt.content[:60],
                "bbox": _bbox_dict(txt.bbox),
            })

    # 2. Check overlaps == 0:
    #    (a) Zero `<text>`-to-`<text>` intersections
    overlap_violations: list[dict[str, Any]] = []
    n_txt = len(texts)
    for i in range(n_txt):
        ti = texts[i]
        for j in range(i + 1, n_txt):
            tj = texts[j]
            if _bboxes_intersect_open(ti.bbox, tj.bbox):
                overlap_violations.append({
                    "kind": "text_to_text",
                    "text_a": ti.content[:50],
                    "id_a": ti.elem_id,
                    "bbox_a": _bbox_dict(ti.bbox),
                    "text_b": tj.content[:50],
                    "id_b": tj.elem_id,
                    "bbox_b": _bbox_dict(tj.bbox),
                })

    #    (b) Zero `<text>`-to-shape/curve/line intersections (excluding valid >=2px non-occluding containers)
    for txt in texts:
        for shp in shapes:
            reason = _check_text_shape_collision(txt, shp)
            if reason is not None:
                overlap_violations.append({
                    "kind": "text_to_shape",
                    "reason": reason,
                    "text": txt.content[:50],
                    "text_id": txt.elem_id,
                    "text_bbox": _bbox_dict(txt.bbox),
                    "shape_tag": shp.tag,
                    "shape_id": shp.elem_id,
                    "shape_bbox": _bbox_dict(shp.tight_bbox),
                })

    passed = (len(xml_errors) == 0 and len(oob_violations) == 0 and len(overlap_violations) == 0)
    return {
        "file": source_name,
        "status": "PASS" if passed else "FAIL",
        "well_formed_xml": True,
        "viewbox_valid": viewbox_valid,
        "shape_count": len(shapes),
        "text_count": len(texts),
        "oob_count": len(oob_violations),
        "overlap_count": len(overlap_violations),
        "xml_errors": xml_errors,
        "oob_violations": oob_violations,
        "overlap_violations": overlap_violations,
    }


def audit_svg_file(svg_path: str) -> dict[str, Any]:
    with open(svg_path, "r", encoding="utf-8") as fh:
        raw = fh.read()
    return audit_svg_string(raw, source_name=os.path.basename(svg_path))


def audit_plots_directory(plots_dir: str, require_full_atlas: bool = True) -> dict[str, Any]:
    """Audit all `.svg` files inside `plots_dir` (enforcing all 10 required `fig01..fig10` files in full-atlas mode)."""
    t0_ns = time.perf_counter_ns()
    if not os.path.isdir(plots_dir):
        return {
            "plots_dir": plots_dir,
            "status": "FAIL",
            "require_full_atlas": require_full_atlas,
            "svg_files_audited": 0,
            "missing_required_files": list(REQUIRED_ATLAS_FILENAMES) if require_full_atlas else [],
            "unexpected_svg_files": [],
            "total_oob": 0,
            "total_overlaps": 0,
            "total_xml_errors": 1,
            "per_file": [],
            "elapsed_ms": (time.perf_counter_ns() - t0_ns) // 1_000_000,
        }

    present_svgs = sorted(f for f in os.listdir(plots_dir) if f.lower().endswith(".svg"))
    present_set = set(present_svgs)
    req_set = set(REQUIRED_ATLAS_FILENAMES)

    missing_req = [f for f in REQUIRED_ATLAS_FILENAMES if f not in present_set] if require_full_atlas else []
    unexpected_svgs = [f for f in present_svgs if f not in req_set] if require_full_atlas else []

    per_file: list[dict[str, Any]] = []
    total_oob = 0
    total_overlaps = 0
    total_xml_errs = 0
    for fn in present_svgs:
        res = audit_svg_file(os.path.join(plots_dir, fn))
        per_file.append(res)
        total_oob += int(res["oob_count"])
        total_overlaps += int(res["overlap_count"])
        total_xml_errs += len(res["xml_errors"])

    all_files_pass = all(r["status"] == "PASS" for r in per_file) and len(per_file) > 0
    if require_full_atlas:
        ok = all_files_pass and len(missing_req) == 0 and len(unexpected_svgs) == 0
    else:
        ok = all_files_pass

    elapsed_ms = (time.perf_counter_ns() - t0_ns) // 1_000_000
    return {
        "plots_dir": plots_dir,
        "status": "PASS" if ok else "FAIL",
        "require_full_atlas": require_full_atlas,
        "svg_files_audited": len(per_file),
        "missing_required_files": missing_req,
        "unexpected_svg_files": unexpected_svgs,
        "total_oob": total_oob,
        "total_overlaps": total_overlaps,
        "total_xml_errors": total_xml_errs,
        "elapsed_ms": elapsed_ms,
        "per_file": per_file,
    }


# ---------------------------------------------------------------------------
# Mandatory Adversarial Unit Self-Tests (`SPEC_WAVE2.md` §2.1)
# ---------------------------------------------------------------------------


def run_svg_auditor_self_tests() -> dict[str, Any]:
    """Verify `svg_auditor` accepts clean multi-panel SVGs and catches deliberate OOB strokes,
    OOB Bezier control points, translated OOB groups, text-to-text collisions, lines/curves slicing
    through text, and partial/thin/occluding `<rect>` bars!
    """
    cases_summary: list[dict[str, Any]] = []

    # 1. Clean publication-style 1400x900 multi-panel SVG (cards, rotated Y-axis label, Bezier arc around text)
    clean_svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1400 900">
      <defs>
        <marker id="arrow" markerWidth="10" markerHeight="10" refX="5" refY="5">
          <path d="M -50 -50 L 10 5 L 0 10 z" fill="#000"/>
        </marker>
      </defs>
      <rect x="0" y="0" width="1400" height="900" fill="#ffffff"/>
      <rect x="30" y="30" width="640" height="840" rx="8" fill="#f8fafc" stroke="#cbd5e1" stroke-width="2"/>
      <text x="350" y="65" font-size="18" text-anchor="middle" fill="#0f172a">Panel A: Clean Exact Geometry</text>
      <text x="58" y="450" font-size="14" text-anchor="middle" transform="rotate(-90 58 450)">Vertical Axis Label</text>
      <line x1="100" y1="760" x2="620" y2="760" stroke="#334155" stroke-width="2"/>
      <line x1="100" y1="120" x2="100" y2="760" stroke="#334155" stroke-width="2"/>
      <path d="M 140 500 C 260 220, 420 220, 540 500" fill="none" stroke="#2563eb" stroke-width="3"/>
      <text x="340" y="480" font-size="14" text-anchor="middle" fill="#1e293b">Safe Interior Label Under Arc</text>
      <g transform="translate(720, 30)">
        <rect x="0" y="0" width="650" height="840" fill="#f8fafc" stroke="#cbd5e1" stroke-width="2"/>
        <circle cx="325" cy="300" r="90" fill="none" stroke="#059669" stroke-width="2"/>
        <text x="325" y="300" dy="0.35em" font-size="14" text-anchor="middle">r* = 10/3</text>
      </g>
    </svg>"""
    r_clean = audit_svg_string(clean_svg, "clean_ref.svg")
    assert r_clean["status"] == "PASS" and r_clean["oob_count"] == 0 and r_clean["overlap_count"] == 0, f"Clean SVG failed: {r_clean}"
    cases_summary.append({"case": "clean_reference_svg", "passed": True})

    # 2. Deliberate OOB stroke (`y = 4` with `stroke-width = 12` -> `ymin = 4 - 6 = -2 < 0`)
    oob_stroke_svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1400 900">
      <line x1="100" y1="4" x2="500" y2="4" stroke="#ef4444" stroke-width="12"/>
      <text x="200" y="100" font-size="14">Label</text>
    </svg>"""
    r_oob_stroke = audit_svg_string(oob_stroke_svg, "oob_stroke.svg")
    assert r_oob_stroke["status"] == "FAIL" and r_oob_stroke["oob_count"] >= 1
    cases_summary.append({"case": "deliberate_oob_stroke", "passed": True})

    # 3. Deliberate OOB cubic Bezier control point (endpoints in bounds, control point at `y = -25 < 0`)
    oob_bezier_svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1400 900">
      <path d="M 100 80 C 200 -25, 300 80, 400 80" fill="none" stroke="#000" stroke-width="2"/>
      <text x="200" y="300" font-size="14">Label</text>
    </svg>"""
    r_oob_bez = audit_svg_string(oob_bezier_svg, "oob_bezier.svg")
    assert r_oob_bez["status"] == "FAIL" and r_oob_bez["oob_count"] >= 1
    cases_summary.append({"case": "deliberate_oob_bezier_control_point", "passed": True})

    # 4. Deliberate `<g transform="translate(1250, 100)">` pushing `<text>` past `x = 1400`
    oob_group_svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1400 900">
      <rect x="20" y="20" width="200" height="200" fill="#eee"/>
      <g transform="translate(1250, 100)">
        <text x="80" y="50" font-size="18" text-anchor="start">TranslatedPastRightEdge</text>
      </g>
    </svg>"""
    r_oob_grp = audit_svg_string(oob_group_svg, "oob_group.svg")
    assert r_oob_grp["status"] == "FAIL" and r_oob_grp["oob_count"] >= 1
    cases_summary.append({"case": "deliberate_translated_group_oob", "passed": True})

    # 5. Deliberate `<text>`-to-`<text>` collision
    text_overlap_svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1400 900">
      <rect x="20" y="20" width="600" height="400" fill="#f8fafc"/>
      <text x="200" y="150" font-size="16" text-anchor="middle">First Overlapping Label</text>
      <text x="230" y="154" font-size="16" text-anchor="middle">Second Overlapping Label</text>
    </svg>"""
    r_txt_ov = audit_svg_string(text_overlap_svg, "text_overlap.svg")
    assert r_txt_ov["status"] == "FAIL" and r_txt_ov["overlap_count"] >= 1
    assert any(v["kind"] == "text_to_text" for v in r_txt_ov["overlap_violations"])
    cases_summary.append({"case": "deliberate_text_to_text_overlap", "passed": True})

    # 6. Deliberate `<line>` slicing directly through `<text>`
    line_slice_svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1400 900">
      <text x="300" y="300" font-size="16" text-anchor="middle">Target Label</text>
      <line x1="220" y1="295" x2="380" y2="295" stroke="#111" stroke-width="2"/>
    </svg>"""
    r_line_sl = audit_svg_string(line_slice_svg, "line_slice.svg")
    assert r_line_sl["status"] == "FAIL" and r_line_sl["overlap_count"] >= 1
    assert any(v["kind"] == "text_to_shape" for v in r_line_sl["overlap_violations"])
    cases_summary.append({"case": "deliberate_line_slicing_text", "passed": True})

    # 7. Deliberate `<path>` Bezier curve slicing through `<text>`
    bez_slice_svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1400 900">
      <text x="400" y="400" font-size="16" text-anchor="middle">Sliced By Curve</text>
      <path d="M 300 440 Q 400 350, 500 440" fill="none" stroke="#dc2626" stroke-width="2"/>
    </svg>"""
    r_bez_sl = audit_svg_string(bez_slice_svg, "bez_slice.svg")
    assert r_bez_sl["status"] == "FAIL" and r_bez_sl["overlap_count"] >= 1
    cases_summary.append({"case": "deliberate_bezier_slicing_text", "passed": True})

    # 8. Deliberate partial `<rect>` bar cutting across `<text>` AND occluding `<rect>` painted AFTER `<text>`
    bar_slice_svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1400 900">
      <rect x="280" y="292" width="120" height="8" fill="#3b82f6"/>
      <text x="300" y="300" font-size="16" text-anchor="middle">Bar Hits Text</text>
    </svg>"""
    r_bar_sl = audit_svg_string(bar_slice_svg, "bar_slice.svg")
    assert r_bar_sl["status"] == "FAIL" and r_bar_sl["overlap_count"] >= 1

    occlude_rect_svg = """<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1400 900">
      <text x="300" y="300" font-size="16" text-anchor="middle">Hidden Under Card</text>
      <rect x="100" y="100" width="400" height="400" fill="#ffffff" stroke="#000"/>
    </svg>"""
    r_occ = audit_svg_string(occlude_rect_svg, "occlude_rect.svg")
    assert r_occ["status"] == "FAIL" and r_occ["overlap_count"] >= 1
    cases_summary.append({"case": "deliberate_rect_bar_and_z_occlusion", "passed": True})

    # 9. Deliberate malformed XML & wrong viewBox
    bad_xml = audit_svg_string("<svg viewBox='0 0 1400 900'><text x='50' y='50'>Unclosed</svg>", "bad.svg")
    assert bad_xml["status"] == "FAIL" and bad_xml["well_formed_xml"] is False
    bad_vb = audit_svg_string(
        "<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 1200 800'>"
        "<rect x='10' y='10' width='100' height='100' fill='#eee'/><text x='30' y='50'>Hi</text></svg>",
        "bad_vb.svg",
    )
    assert bad_vb["status"] == "FAIL" and bad_vb["viewbox_valid"] is False
    cases_summary.append({"case": "deliberate_malformed_xml_and_bad_viewbox", "passed": True})

    # 10. Full-atlas 10-figure directory completeness gate (10/10 PASS vs missing fig10 FAIL) in isolated `/tmp`
    with tempfile.TemporaryDirectory(dir="/tmp", prefix="itst_svg_atlas_test_") as tmp_plots:
        for fn in REQUIRED_ATLAS_FILENAMES[:9]:
            with open(os.path.join(tmp_plots, fn), "w", encoding="utf-8") as fh:
                fh.write(clean_svg)
        r_missing = audit_plots_directory(tmp_plots, require_full_atlas=True)
        assert r_missing["status"] == "FAIL" and REQUIRED_ATLAS_FILENAMES[9] in r_missing["missing_required_files"]

        with open(os.path.join(tmp_plots, REQUIRED_ATLAS_FILENAMES[9]), "w", encoding="utf-8") as fh:
            fh.write(clean_svg)
        r_full10 = audit_plots_directory(tmp_plots, require_full_atlas=True)
        assert (
            r_full10["status"] == "PASS"
            and r_full10["svg_files_audited"] == 10
            and r_full10["total_oob"] == 0
            and r_full10["total_overlaps"] == 0
        )
    cases_summary.append({"case": "full_atlas_10_file_directory_gate", "passed": True})

    return {
        "status": "PASS",
        "total_self_tests": len(cases_summary),
        "passed_self_tests": len(cases_summary),
        "cases": cases_summary,
    }


def main(argv: list[str] | None = None) -> int:
    prev = signal.signal(signal.SIGALRM, _alarm_handler)
    signal.alarm(20)
    try:
        args = argv if argv is not None else sys.argv[1:]
        self_test_res = run_svg_auditor_self_tests()
        ws_root = str(Path(__file__).resolve().parent.parent)
        default_plots = os.path.join(ws_root, "plots")

        if len(args) >= 1:
            target = args[0]
            full_mode = "--partial" not in args
            if os.path.isfile(target):
                audit_res = audit_svg_file(target)
            else:
                audit_res = audit_plots_directory(target, require_full_atlas=full_mode)
            out = {"self_tests": self_test_res, "audit": audit_res}
            print(json.dumps(out, indent=2))
            return 0 if audit_res["status"] == "PASS" else 1

        # Default invocation: run self-tests; if `plots/` already exists on disk, audit it in partial/full report mode
        out_default: dict[str, Any] = {"self_tests": self_test_res}
        if os.path.isdir(default_plots):
            out_default["plots_audit"] = audit_plots_directory(default_plots, require_full_atlas=True)
            print(json.dumps(out_default, indent=2))
            return 0 if out_default["plots_audit"]["status"] == "PASS" else 1
        out_default["plots_status"] = "PENDING_SIMULATOR_WAVE2_ATLAS"
        print(json.dumps(out_default, indent=2))
        return 0
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, prev)


if __name__ == "__main__":
    raise SystemExit(main())
