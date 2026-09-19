"""Dump H_4 Coxeter tables and the normal forms of the generators of F (p1..p3) and N (x0..x11) for cchelly.c.
usage: python3 dumpch.py OUTPREFIX   (writes OUTPREFIX.tab, OUTPREFIX.gens)"""
import os, sys
sys.path.insert(0, '/home/user/group-approximation/experiments/h4-artin-complex-6cycles-2026-09-17')
sys.path.insert(0, '/home/user/group-approximation/experiments/h4-commutator-helly-2026-09-18')
from garside import Coxeter, Artin
W = Coxeter(4, {(0, 1): 3, (1, 2): 3, (2, 3): 5})
G = Artin(W)
FW = {'p3': [1, 1], 'p2': [1, 2, 2, -1], 'p1': [1, 2, 3, 3, -2, -1]}
NW = {'x0': [4, 4], 'x1': [3, 4, 4, -3], 'x3': [4, 3, 3, -4], 'x2': [3, 4, 3, 3, -4, -3],
      'x4': [2, 3, 4, 4, -3, -2], 'x11': [2, 4, 3, 3, -4, -2], 'x5': [2, 3, 4, 3, 3, -4, -3, -2],
      'x10': [3, 2, 4, 3, 3, -4, -2, -3], 'x6': [2, 3, 2, 4, 3, 3, -4, -2, -3, -2],
      'x9': [4, 3, 2, 4, 3, 3, -4, -2, -3, -4], 'x7': [2, 4, 3, 2, 4, 3, 3, -4, -2, -3, -4, -2],
      'x8': [3, 2, 4, 3, 2, 4, 3, 3, -4, -2, -3, -4, -2, -3]}
pre = sys.argv[1]
with open(pre + '.tab', 'w') as f:
    f.write(f"{W.n} {W.N} {W.w0} 14 7 6\n")
    for w in range(W.N):
        f.write(' '.join(map(str, [W.length[w], W.inv[w], W.ld[w], W.rd[w], W.supp[w], W.tau[w]] + W.lmul[w] + W.rmul[w]
                                    + [len(W.word[w])] + list(W.word[w]))) + '\n')
with open(pre + '.gens', 'w') as f:
    for D in (FW, NW):
        names = sorted(D, key=lambda s: int(s[1:]))
        f.write(f"{2 * len(names)}\n")
        for nm in names:
            g = G.word(D[nm])
            for (lab, h) in ((nm, g), (nm + "'", G.inv(g))):
                f.write(' '.join(map(str, [lab, h[0], len(h[1])] + list(h[1]))) + '\n')
print('dumped', W.N, flush=True)
