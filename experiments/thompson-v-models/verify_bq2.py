"""Check the Bleak--Quick two-generator presentation data exactly inside V.

Run on MSI only:  python3 verify_bq2.py
Prints, for each orientation reading of the generators, whether every relator is
the identity of V, the orders of u and v, and whether the marked-word formulas
give the stated transpositions.  Exit code 0 iff one reading passes everything.
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import texwords
import vwords

HERE = os.path.dirname(os.path.abspath(__file__))
P = json.load(open(os.path.join(HERE, "presentation_bq2.json")))


def element_equal(w1, w2, gens, M=12):
    return vwords.is_identity(texwords._inv(w1) + w2, gens, "right", M)


def order(letter, gens, bound=24, M=12):
    for k in range(1, bound + 1):
        if vwords.is_identity([(letter, 1)] * k, gens, "right", M):
            return k
    return None


def run(gspec):
    gens = {k: vwords.parse_cycles(v) for k, v in gspec.items()}
    ok = True
    for i, r in enumerate(P["relators_tex"], 1):
        w = texwords.parse(r)
        try:
            idt = vwords.is_identity(w, gens, "right", M=12)
        except vwords.Short:
            idt = vwords.is_identity(w, gens, "right", M=16)
        print("  relator %d length %3d identity=%s" % (i, len(w), idt))
        ok &= idt
    print("  order(u)=%s order(v)=%s" % (order("u", gens), order("v", gens)))
    targets = {
        "a = t_{00,01}": "(00 01)",
        "t_{10,000}": "(10 000)",
        "t_{11,001}": "(11 001)",
    }
    base = texwords.parse("u^{3}")
    conj_s = {
        "a = t_{00,01}": [],
        "t_{10,000}": texwords.parse("vu^{-2}vu^{3}"),
        "t_{11,001}": texwords.parse("vu^{-1}vu^{3}v"),
    }
    for name, spec in targets.items():
        gens2 = dict(gens)
        gens2["t"] = vwords.parse_cycles(spec)
        w = texwords.conj(base, conj_s[name])
        eq = element_equal(w, [("t", 1)], gens2)
        print("  marked %-16s equals %s: %s" % (name, spec, eq))
        ok &= eq
    return ok


if __name__ == "__main__":
    readings = {
        "as stated": P["generators"],
        "v reversed": {"u": P["generators"]["u"], "v": "(01 11 10)"},
    }
    passed = []
    for label, g in readings.items():
        print("reading:", label, g)
        if run(g):
            passed.append(label)
    print("PASSED:", passed)
    sys.exit(0 if passed else 1)
