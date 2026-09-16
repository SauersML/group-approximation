#!/usr/bin/env python3
"""mktargets.py -- write the distinct images of presentations under the 8 signed permutations of {x, y}.

usage: mktargets.py R1 R2 [R1 R2 ...] > targets.txt
Each output line "r1 r2" is a canonical state (acverify.canon, pair sorted by (length, word)).
A MEET certificate with target line k proves the class AC-equivalent to that line, hence to the
input presentation up to a signed permutation of the generators (artifact, Lemma 2).
"""
import sys
from acverify import state


def aut(w, swap, sx, sy):
    img = {"x": ("y" if swap else "x", sx), "y": ("x" if swap else "y", sy)}
    out = []
    for c in w:
        g, s = img[c.lower()]
        e = -1 if c.isupper() else 1
        out.append(g if s * e == 1 else g.upper())
    return "".join(out)


seen = []
args = sys.argv[1:]
for k in range(0, len(args), 2):
    for swap in (0, 1):
        for sx in (1, -1):
            for sy in (1, -1):
                st = state(aut(args[k], swap, sx, sy), aut(args[k + 1], swap, sx, sy))
                if st not in seen:
                    seen.append(st)
for st in seen:
    print(st[0], st[1])
