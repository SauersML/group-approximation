"""Two-word boundaries {u, v^{-1}} with [u] = [v] in H_1 (so zero total homology), exact multiword LP by cg_multiword.CG.

usage: python3 scan_pairs.py '<phi0 json>' m ALPH L [--tl SEC] [--maxdarts N]
"""
import sys, json, time, itertools
from collections import defaultdict
import cg_multiword as CGmod
from ffold import gate_of, cyc_legal, inv_word
from search3 import power


def main():
    args = sys.argv[1:]
    tl, maxdarts = 60, 400
    if "--tl" in args:
        i = args.index("--tl"); tl = int(args[i + 1]); del args[i:i + 2]
    if "--maxdarts" in args:
        i = args.index("--maxdarts"); maxdarts = int(args[i + 1]); del args[i:i + 2]
    phi0 = json.loads(args[0]); m = int(args[1]); alph = args[2]; L = int(args[3])
    phi = power(phi0, m)
    g = gate_of(phi)
    gp = len({g[d] for d in "abc"}); gn = len({g[d] for d in "ABC"})
    maxval = max(2, 2 * min(gp, gn))
    def img_len(w):
        return sum(len(phi[x.lower()]) for x in w)
    ws = [w for w in CGmod.necklaces(alph, L) if cyc_legal(g, w)]
    cls = defaultdict(list)
    for w in ws:
        cls[tuple(w.count(x) - w.count(x.upper()) for x in "abc")].append(w)
    t0 = time.time()
    counts = defaultdict(int)
    for key in sorted(cls):
        for u, v in itertools.combinations_with_replacement(cls[key], 2):
            V = inv_word(v)
            if not cyc_legal(g, V):
                counts["illegal inverse"] += 1
                continue
            W = [u, V]
            nd = len(u) + len(v) + img_len(u) + img_len(v)
            if nd > maxdarts:
                counts["too big"] += 1
                continue
            c = CGmod.CG(phi, g, W, maxval)
            val, res = c.run(3000, tl, log=lambda *a, **k: None)
            tag = val if isinstance(val, str) else ("neg" if val < -1e-9 else "nonneg")
            counts[tag] += 1
            if tag not in ("infeasible",):
                print("W", W, "darts", nd, "RESULT", val, flush=True)
    print("phi0", phi0, "m", m, "alph", alph, "L", L, "words", len(ws), dict(counts),
          "t", round(time.time() - t0, 1), flush=True)


if __name__ == "__main__":
    main()
