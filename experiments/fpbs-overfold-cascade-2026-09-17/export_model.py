"""Export the depth-j pullback model (C_{j+1}, iota : C_{j+1} -> C_j, seed
types) for cascade.c.

Output format (whitespace separated):
  Vc Vb T
  Vc lines: 4 neighbours of vertex c of C_{j+1} along a, a^-1, b, b^-1 (-1 = none)
  one line: iota(c) for c = 0..Vc-1
  T lines: c d lawful size level
where (c, d) is a root pair of each unordered off-diagonal component of the
pair graph C_{j+1} x_R C_{j+1}; level = largest i <= j with equal images in C_i.

Uses the pullback model of experiments/fpbs-overfold-breaker-2026-09-17/pb.py.
Usage: python3 export_model.py j > model_j.txt
"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-overfold-breaker-2026-09-17'))
from pb import model, core, iota  # noqa: E402


def main():
    j = int(sys.argv[1])
    Cs, Cb, io, types = model(j)
    nbs, words = Cs
    # images in C_i for every i <= j, to compute levels
    imgs = []
    for i in range(j + 1):
        Ci = core(i)
        imgs.append(iota(Cs, Ci))
    print(len(nbs), len(Cb[0]), len(types))
    for c in range(len(nbs)):
        print(*nbs[c])
    print(*io)
    for (c, d), law, sz in types:
        lev = max(i for i in range(j + 1) if imgs[i][c] == imgs[i][d])
        print(c, d, int(law), sz, lev)


if __name__ == '__main__':
    main()
