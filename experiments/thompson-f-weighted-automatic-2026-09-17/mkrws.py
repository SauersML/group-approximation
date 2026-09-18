#!/usr/bin/env python3
"""Generate KBMAG rewriting-system files for Thompson's group F and calibration groups.
Usage: mkrws.py OUTDIR   (writes one file per configuration)
Letters: lowercase generator, uppercase inverse."""
import sys, os

def rws(name, gens, rels, ordering="shortlex", weights=None, order=None):
    order = order or gens
    go = []
    for g in order:
        go += [g, g.upper()]
    inv = [x.upper() if x.islower() else x.lower() for x in go]
    def w(s):
        return "*".join(s) if s else "IdWord"
    eqs = ",\n   ".join("[%s,IdWord]" % w(r) for r in rels)
    out = "_RWS := rec(\n  isRWS := true,\n  ordering := \"%s\",\n" % ordering
    out += "  generatorOrder := [%s],\n  inverses := [%s],\n" % (",".join(go), ",".join(inv))
    if ordering == "wtlex":
        wt = []
        for g in order:
            wt += [weights[g], weights[g]]
        out += "  weight := [%s],\n" % ",".join(map(str, wt))
    out += "  equations := [\n   %s\n  ]\n);\n" % eqs
    return out

def inv(s):
    return "".join(c.swapcase() for c in reversed(s))

def comm(u, v):
    return u + v + inv(u) + inv(v)

def freered(s):
    st = []
    for c in s:
        if st and st[-1] == c.swapcase():
            st.pop()
        else:
            st.append(c)
    return "".join(st)

# F over a=x0, b=x1 (CFP): [x0 x1^-1, x0^-1 x1 x0], [x0 x1^-1, x0^-2 x1 x0^2]
F_A = [freered(comm("aB", "Aba")), freered(comm("aB", "AAbaa"))]
# F over a=x0,b=x1,c=x2 with c = x0^-1 x1 x0 : add defining relator
F_A2 = F_A + [freered("Aba" + "C")]
# F over x0..x3, d = x3 = x0^-1 x2 x0
F_A3 = F_A2 + [freered("Aca" + "D")]

CAL = {
    "z2": (["a", "b"], [comm("a", "b")]),
    "bs12": (["a", "b"], ["Abab" + "B" if False else freered("Aba" + "BB")]),  # a^-1 b a = b^2
    "trefoil": (["a", "b"], ["aba" + "BAB"]),
}

def main(outdir):
    os.makedirs(outdir, exist_ok=True)
    cfgs = {}
    for k, (g, r) in CAL.items():
        cfgs["cal_" + k] = rws(k, g, r)
    cfgs["F_A_ab"] = rws("F", ["a", "b"], F_A)
    cfgs["F_A_ba"] = rws("F", ["a", "b"], F_A, order=["b", "a"])
    for (p, q) in [(1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (3, 2), (1, 5), (5, 1)]:
        cfgs["F_A_w%d%d" % (p, q)] = rws("F", ["a", "b"], F_A, "wtlex", {"a": p, "b": q})
    cfgs["F_A2_abc"] = rws("F", ["a", "b", "c"], F_A2)
    cfgs["F_A2_cba"] = rws("F", ["a", "b", "c"], F_A2, order=["c", "b", "a"])
    cfgs["F_A3_abcd"] = rws("F", ["a", "b", "c", "d"], F_A3)
    for name, txt in cfgs.items():
        with open(os.path.join(outdir, name), "w") as f:
            f.write(txt)
    print(" ".join(sorted(cfgs)))

if __name__ == "__main__":
    main(sys.argv[1])
