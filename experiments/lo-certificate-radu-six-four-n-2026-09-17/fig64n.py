"""Read the geometric squares of Radu's Gamma_{6,4n} directly from the pstricks source of
Figure 'picture:64n' (arXiv:1712.01091), calibrating the reading convention on the first four
squares, which must be Gamma_{4,4}.  usage: python3 fig64n.py n"""
import re, sys, itertools
from bmw import BMW, RADU_44, parse_word, inv_word

import os
# TeX source of arXiv:1712.01091v3 (file Lattices3ALL.tex of the arXiv source tarball)
TEX = os.environ.get("RADU_TEX", "Lattices3ALL.tex")


def load():
    L = open(TEX).read().splitlines()
    s = 3126
    e = next(i for i in range(s, len(L)) if "picture:64n}" in L[i])
    squares, tris, labels, boxes = [], [], [], []
    for line in L[s:e]:
        if line.startswith("%"):
            continue
        pts = [tuple(map(float, p)) for p in re.findall(r"\((-?[\d.]+),(-?[\d.]+)\)", line)]
        if line.startswith("\\pspolygon[linestyle=dashed]"):
            boxes.append(pts)
        elif line.startswith("\\pspolygon(") and len(pts) == 4:
            squares.append(pts)
        elif "fillcolor=white" in line:
            tris.append(("h", pts))
        elif "fillcolor=black" in line:
            tris.append(("v", pts))
        elif line.startswith("\\rput"):
            m = re.match(r"\\rput\((-?[\d.]+),(-?[\d.]+)\)\{\$(.*)\$\}", line)
            labels.append((float(m.group(1)), float(m.group(2)), m.group(3)))
    return squares, tris, labels, boxes


def edges_of(sq):
    x0 = min(p[0] for p in sq); x1 = max(p[0] for p in sq)
    y0 = min(p[1] for p in sq); y1 = max(p[1] for p in sq)
    return x0, x1, y0, y1


def build(n):
    squares, tris, labels, boxes = load()
    jlabels = [l for l in labels if l[2].startswith("j \\in")]
    labels = [l for l in labels if not l[2].startswith("j \\in")]
    out = []  # list of (square index, dict side -> (letter, index, orientation), jrange)
    for si, sq in enumerate(squares):
        x0, x1, y0, y1 = edges_of(sq)
        sides = {}
        for side, typ in (("bottom", "h"), ("top", "h"), ("left", "v"), ("right", "v")):
            T = []
            for t, pts in tris:
                if t != typ:
                    continue
                cx = sum(p[0] for p in pts) / 3; cy = sum(p[1] for p in pts) / 3
                if typ == "h":
                    yy = y0 if side == "bottom" else y1
                    if abs(cy - yy) < 0.2 and x0 < cx < x1:
                        base = pts[0][0]; apex = pts[2][0]
                        T.append(1 if apex > base else -1)  # +1: points right
                else:
                    xx = x0 if side == "left" else x1
                    if abs(cx - xx) < 0.2 and y0 < cy < y1:
                        base = pts[0][1]; apex = pts[2][1]
                        T.append(1 if apex > base else -1)  # +1: points up
            assert T and len(set(T)) == 1, (si, side, T)
            idx = len(T)
            if typ == "v":
                xx = x0 if side == "left" else x1
                cand = [l for l in labels if y0 < l[1] < y1 and abs(l[0] - xx) < 0.5]
                cand = [l for l in cand if min(abs(l[0] - xx), 9) <= min(abs(l[0] - xs) for s2 in squares for xs in (edges_of(s2)[0], edges_of(s2)[1]) if edges_of(s2)[2] == y0)]
                if cand:
                    assert len(cand) == 1
                    idx = cand[0][2]
            sides[side] = (typ, idx, T[0])
        box = None
        for bi, b in enumerate(boxes):
            bx0, bx1, by0, by1 = edges_of(b)
            if bx0 <= x0 and x1 <= bx1 and by0 <= y0 and y1 <= by1:
                box = bi
        jr = None
        if box is not None:
            bx0, bx1, by0, by1 = edges_of(boxes[box])
            jl = [l for l in jlabels if by0 - 0.4 < l[1] < by1]
            assert len(jl) == 1
            hi = jl[0][2].split("\\ldots,")[1].strip(" }\\")
            jr = (2, hi)
        out.append((si, sides, jr))
    return out


def instantiate(fig, n):
    sqs = []
    for si, sides, jr in fig:
        js = [None]
        if jr:
            hi = eval(jr[1].replace("n", str(n)))
            js = list(range(2, hi + 1))
        for j in js:
            s = {}
            for side, (typ, idx, o) in sides.items():
                if isinstance(idx, str):
                    expr = idx.replace("2n", "2*%d" % n).replace("2j", "2*%d" % (j if j else 0))
                    idx = eval(expr)
                s[side] = (typ, idx, o)
            sqs.append((si, j, s))
    return sqs


def word(s, conv):
    """conv: 0 = boundary counterclockwise from bottom-left, 1 = 'a b a b' with top and left read forward."""
    B, R, Tp, Lf = s["bottom"], s["right"], s["top"], s["left"]
    if conv == 0:
        w = [("a", B[1] * B[2]), ("b", R[1] * R[2]), ("a", -Tp[1] * Tp[2]), ("b", -Lf[1] * Lf[2])]
    elif conv == 1:
        w = [("a", B[1] * B[2]), ("b", R[1] * R[2]), ("a", Tp[1] * Tp[2]), ("b", Lf[1] * Lf[2])]
    elif conv == 2:
        w = [("a", B[1] * B[2]), ("b", R[1] * R[2]), ("a", -Tp[1] * Tp[2]), ("b", Lf[1] * Lf[2])]
    else:
        w = [("a", B[1] * B[2]), ("b", R[1] * R[2]), ("a", Tp[1] * Tp[2]), ("b", -Lf[1] * Lf[2])]
    return w


def canon(w):
    forms = []
    for ww in (w, inv_word(w)):
        for k in range(4):
            forms.append(tuple(ww[k:] + ww[:k]))
    return min(forms)


def fmtw(w):
    return " ".join("%s%d%s" % (t, abs(x), "^-1" if x < 0 else "") for t, x in w)


if __name__ == "__main__":
    n = int(sys.argv[1])
    fig = build(n)
    sqs = instantiate(fig, n)
    target = {canon(parse_word(r)) for r in RADU_44}
    for conv in range(4):
        first4 = {canon(word(s, conv)) for si, j, s in sqs[:4]}
        rels = [fmtw(word(s, conv)) for si, j, s in sqs]
        ok44 = first4 == target
        try:
            G = BMW(3, 2 * n, rels)
            valid = True
        except AssertionError:
            valid = False
        print("conv", conv, "first four = Gamma_44:", ok44, "valid datum:", valid, "squares:", len(rels))
        if ok44 and valid:
            print("RELATORS", rels)
