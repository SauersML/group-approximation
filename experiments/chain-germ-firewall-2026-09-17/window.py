"""Exact support of scout words on a whole delta-window W_n = delta^n [X, delta X).
usage: python3 window.py {nonaffine|affine} n word_name ...
"""
import sys
import time
from scout import *  # noqa: F401,F403


def window(kind, n, names):
    ch = nonaffine() if kind == 'nonaffine' else affine_control()
    L = letters(ch)
    a, b = ch.X, ch.dX
    for _ in range(n):
        a, b = ch.delta(a)[0], ch.delta(b)[0]
    for nm in names:
        h = word(*[L[c] for c in WORDS[nm]])
        t = time.time()
        ivs, npc = support(h, a, b)
        m = sum(y - x for x, y in ivs)
        print(f"{kind} n={n} {nm} window [{f(a)},{f(b)}) pieces {npc} comps {len(ivs)}"
              f" moved {f(m):.6g}"
              + (f" first {f(ivs[0][0]):.6g} last {f(ivs[-1][1]):.6g}" if ivs else "")
              + f" ({time.time()-t:.0f}s)")
        sys.stdout.flush()


if __name__ == '__main__':
    window(sys.argv[1], int(sys.argv[2]), sys.argv[3:])
