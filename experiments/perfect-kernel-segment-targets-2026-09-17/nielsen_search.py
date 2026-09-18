#!/usr/bin/env python3
"""Do other generating pairs of the survivor groups give certifiable Magnus hierarchies?

The certifier of experiments/one-relator-hughes-free-char-p-2026-09-17/segment_certify.py
works on one Nielsen normal form.  Here we apply automorphisms of F(a, b) (products of up to
DEPTH elementary Nielsen moves x -> x y^{+-1}, x -> y^{+-1} x) to each survivor relator, keep
the images of length <= LMAX, and run the full certifier (landed rules + rule 1) on each image
as given (certify only rotates, inverts and relabels; it re-Nielsen-reduces only when no letter
has exponent sum 0, which never happens here since H_1 = Z).

Every image presents the same group, so one certified image puts the group in H.

Usage: python3 nielsen_search.py [DEPTH] [LMAX]
"""
import os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "one-relator-hughes-free-char-p-2026-09-17"))
import segment_certify as sc  # noqa: E402
hc = sc.hc

SURV = ["A A B a b a B A A b b", "A A B B A A b a B a b",
        "A A A B B a b A b a a B", "A A A B a a b b b a a B", "A A A B a a b A b a B B",
        "A A A b b a B A B a a b", "A A A b a a B B B a a b", "A A A b a a B A B a b b",
        "A A B a B A A b a B a b", "A A B a b a B A A b a b"]


def moves():
    out = []
    for x, y in (("a", "b"), ("b", "a")):
        for e in (1, -1):
            out.append({x: ((x, 1), (y, e))})
            out.append({x: ((y, e), (x, 1))})
    return out


def main():
    depth = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    lmax = int(sys.argv[2]) if len(sys.argv) > 2 else 18
    M = moves()
    t0 = time.time()
    for s in SURV:
        w0 = hc.cred(hc.parse(s))
        seen = {hc.canon(w0)}
        frontier = [w0]
        tested = 0
        hit = None
        for d in range(depth):
            nxt = []
            for w in frontier:
                for m in M:
                    v = hc.cred(hc.subst(w, m))
                    k = hc.canon(v)
                    if k in seen or len(v) > lmax:
                        continue
                    seen.add(k)
                    nxt.append(v)
                    ok, why = hc.certify(v, "new", memo={})
                    tested += 1
                    if ok:
                        hit = (v, why)
                        break
                if hit:
                    break
            if hit:
                break
            frontier = nxt
        if hit:
            v, why = hit
            print(s, "| CERTIFIED via", " ".join(a if e == 1 else a.upper() for a, e in v), why)
        else:
            print(s, "| no certified image among", tested, "images (depth %d, len<=%d)" % (depth, lmax))
        sys.stdout.flush()
    print("time %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
