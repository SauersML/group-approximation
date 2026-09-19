#!/usr/bin/env python3
"""Growth screen for the undecided cases: orders of short words in S, T on levels 2, 3, 4.

If some word w has ord_n(w) < ord_{n+1}(w), then H_n != H_{n+1}, so no presentation
certificate of h_present.py can succeed at level n (it needs H = H_n).  Output per case:
  stable-from-n : all screened words have equal orders on levels n..4 (candidate for h_present at n)
  growing       : some word still grows from level 3 to level 4 (with the word and its orders)
This is only a selector: it proves nothing about H itself (numpy, exact permutation orders).
Run: python3 h_growth.py NAMEFILE > h_growth.out
"""
import sys, math, itertools
import numpy as np
from bouquets import bouquets, Levels
from loopgraph import reduce, inv

def perm_order(p):
    seen = np.zeros(len(p), bool); o = 1
    for i in range(len(p)):
        if seen[i]: continue
        j, c = i, 0
        while not seen[j]: seen[j] = True; j = p[j]; c += 1
        o = o * c // math.gcd(o, c)
    return o

def words(I, maxlen=4):
    g = {"S": I["S"], "s": inv(I["S"]), "T": I["T"], "t": inv(I["T"])}
    for n in range(1, maxlen + 1):
        for w in itertools.product("SsTt", repeat=n):
            if any(a.lower() == b.lower() and a != b for a, b in zip(w, w[1:] + w[:1])): continue
            yield "".join(w), reduce(sum((g[c] for c in w), ()))

if __name__ == "__main__":
    skip = {l.split(" | ")[0].split(" ", 1)[1] for l in open("h_inf6.out") if "| infinite" in l}
    want = [l.strip() for l in open(sys.argv[1]) if l.strip() and not l.startswith(" (")]
    want = [n for n in want if n not in skip]
    cases = {name: (R, I) for name, R, I in bouquets() if name in set(want)}
    for name in want:
        R, I = cases[name]; Lv = Levels(R, 4); start = 2; bad = None
        for label, w in words(I):
            o = [perm_order(Lv.word(w, n)) for n in (2, 3, 4)]
            if o[1] < o[2]: bad = (label, o); break
            if o[0] < o[1]: start = 3
        print(name, "|", f"growing {bad[0]}: orders {bad[1]}" if bad else f"stable-from-{start}", flush=True)
