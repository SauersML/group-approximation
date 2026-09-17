"""Search and verify a legal f^m-folded fatgraph for a given multiset of d^- words.

The d^- boundary is the list of cyclic words `words`; each w comes with its own d^+
circle f(w)^{-1}.  The SAT model (sat4.build4/solve4) enforces, on the pairing p of
boundary letters: inverse labels, no backtracking, (L) at every vertex (lazily), (2), (3),
(4).  verify4 re-checks all of them from the pairing alone and unrolls X_n for n <= nunroll
(immersion check of the stacked graph, a sanity check independent of the proof).

usage: python3 find_surface.py '<phi0 json>' m nunroll out.json w1 [w2 ...]
"""
import sys, json, time
from ffold import Boundary, gate_of, certify_fully_irreducible_atoroidal, cyc_legal, apply
from search3 import power
from sat4 import solve4, verify4, orbits


def main():
    phi0 = json.loads(sys.argv[1]); m = int(sys.argv[2]); nunroll = int(sys.argv[3])
    out = sys.argv[4]; words = sys.argv[5:]
    phi = power(phi0, m)
    g = gate_of(phi)
    cert = certify_fully_irreducible_atoroidal(phi0)
    print("phi0", phi0, "m", m, "certificate", cert, "gates", "".join(g[d] for d in "abcABC"))
    for w in words:
        assert cyc_legal(g, w), ("illegal word", w)
    B = Boundary(phi, words)
    print("d^- words", words, "d^+ words", [apply(phi, w) for w in words], "darts", B.N)
    t0 = time.time()
    p, it = solve4(B, g)
    print("sat iterations", it, "time", round(time.time() - t0, 1))
    if not p:
        print("no fatgraph", p)
        return
    rep = verify4(B, p, g, nunroll=nunroll)
    vs = orbits(B, p)
    print("VERIFIED", rep)
    json.dump({"phi0": phi0, "power": m, "phi": phi, "certificate": cert,
               "minus_words": words, "boundary": B.words,
               "labels": B.label, "kind": B.kind, "fdart": B.fdart, "nxt": B.nxt,
               "pairing": [p[d] for d in range(B.N)],
               "vertices": [[(d, B.label[d]) for d in o] for o in vs], "report": rep},
              open(out, "w"), indent=1)


if __name__ == "__main__":
    main()
