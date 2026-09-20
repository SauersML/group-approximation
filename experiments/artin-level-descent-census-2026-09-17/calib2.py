"""Calibrate enum2 on the decided 2x2 dead joins: members = three halves 2 and one odd."""
import sys
import time

from calib import join
from enum2 import enumerate_reps, Group

if __name__ == "__main__":
    ls = [int(x) for x in sys.argv[1].split(',')]
    hs = [tuple(int(y) for y in h.split(',')) for h in sys.argv[2:]]
    for l in ls:
        G = Group(l, 7)
        for h in hs:
            V, E, chi = join(h)
            t0 = time.time()
            st, ex, cross = enumerate_reps(V, E, chi, l, grp=G)
            print(f"l={l} halves={h} {st} ({time.time() - t0:.1f}s)", flush=True)
            for e in ex["c0_not_ct"][:1]:
                print("   c0_not_ct example:", e, flush=True)
