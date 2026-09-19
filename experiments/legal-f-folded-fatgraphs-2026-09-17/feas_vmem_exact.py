"""Exact check that a mixed-memory polygon LP (lp_vmem) is FEASIBLE, from a column-generation dump.

  python3 feas_vmem_exact.py dump.json [out.json]      (dump written by vcg.py --dual; or an out.json of this script)

It keeps the polygon and window columns of the dump's primal x above 1e-7, rounds each value to a rational of
denominator <= 1024, and checks in exact arithmetic (fractions.Fraction):
  1. every kept polygon is a typed polygon of the LP: the rules of farkas_vmem_brute.walk (slot pairs, successor
     sets, 2 <= k <= maxval, distinct gates, at most one d^- dart, an f-dart only on a bigon);
  2. every row of lp_vmem.build(TY, polys) is 0 (type, pair, circulation and homology rows);
  3. the window values sum to 1 (normalisation) and all values are >= 0.
It then prints chi = sum y_P (1 - |P|/2) and the window flow.  With --save out.json it writes the rational point.
"""
import sys, json
from fractions import Fraction as Fr
import lp_vmem as VM
from ffold import inv


def is_polygon(TY, g, maxval, P):
    k = len(P)
    if not (2 <= k <= maxval):
        return "length %d" % k
    darts = [d for d, _ in P]
    for i, (d, q) in enumerate(P):
        if q not in TY.bylabel[inv(TY.label[d])]:
            return "slot label"
        if TY.kind[d] == "-" and TY.kind[q] == "-":
            return "two minus in slot"
        n = darts[(i + 1) % k]
        if n not in TY.succ[q]:
            return "successor"
    gs = [g[TY.label[d]] for d in darts]
    if len(set(gs)) != k:
        return "gates"
    if sum(1 for d in darts if TY.kind[d] == "-") > 1:
        return "minus darts"
    nf = sum(TY.fdart[d] for d in darts)
    if nf > 1 or (nf == 1 and k != 2):
        return "f-darts"
    return None


def main():
    path = sys.argv[1]
    J = json.load(open(path))
    phi, g, TY, maxval = VM.setup(J["phi0"], J["power"], J["rm"], J["rp"])
    nw = len(TY.windows)
    if "polys" in J:                       # a saved rational point
        polys = [tuple((int(d), int(q)) for d, q in P) for P in J["polys"]]
        yv = [Fr(s) for s in J["y"]]
        wv = [Fr(s) for s in J["w"]]
    else:
        x, ci, cols = J["x"], J["colidx"], J["columns"]
        polys, yv = [], []
        for k, j in enumerate(ci):
            if j < len(x) and x[j] > 1e-7:
                polys.append(tuple((int(d), int(q)) for d, q in cols[k]))
                yv.append(Fr(x[j]).limit_denominator(1024))
        wv = [Fr(x[j]).limit_denominator(1024) if x[j] > 1e-7 else Fr(0) for j in range(nw)]
    bad = [(i, is_polygon(TY, g, maxval, P)) for i, P in enumerate(polys)]
    bad = [b for b in bad if b[1]]
    nrows, pcols, ccols = VM.build(TY, polys)
    row = [Fr(0)] * nrows
    for col, v in zip(pcols, yv):
        for r, a in col.items():
            row[r] += a * v
    for col, v in zip(ccols, wv):
        for r, a in col.items():
            row[r] += a * v
    nz = [r for r in range(nrows) if row[r] != 0]
    norm = sum(wv)
    neg = sum(1 for v in yv + wv if v < 0)
    chi = sum(v * (1 - Fr(len(P), 2)) for P, v in zip(polys, yv))
    print("phi0", J["phi0"], "m", J["power"], "rm", J["rm"], "rp", J["rp"], "types", TY.N, "windows", nw,
          "maxval", maxval)
    print("polygons", len(polys), "by length", {k: sum(1 for P in polys if len(P) == k) for k in range(2, maxval + 1)},
          "non-polygons", len(bad), bad[:3])
    print("rows", nrows, "nonzero rows", len(nz), "normalisation", norm, "negative values", neg)
    print("chi", chi, "window flow", {"".join(TY.windows[j]): str(v) for j, v in enumerate(wv) if v})
    ok = not bad and not nz and norm == 1 and neg == 0
    print("EXACT FEASIBLE POINT", "VERIFIED" if ok else "FAILED", flush=True)
    if ok and len(sys.argv) > 2:
        json.dump({"phi0": J["phi0"], "power": J["power"], "rm": J["rm"], "rp": J["rp"],
                   "polys": [[list(s) for s in P] for P in polys], "y": [str(v) for v in yv],
                   "w": [str(v) for v in wv]}, open(sys.argv[2], "w"))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
