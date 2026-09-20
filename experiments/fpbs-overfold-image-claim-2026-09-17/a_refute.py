"""Explicit counterexamples to the image claim (A) Z = Y at k = 1.

1. B = <bab, bbAABA> (malnormal, rank 2), X = <BAB>, pair (0,1).
2. The surjective-host case found by surj_check.py seed 3:
   B = <bABaB, Abaa>, X = <bABaBAABabAbaB, bAbaBAABabAbaB, bAbbaB>, pair (1,5).
For each: malnormality of B, ranks of X, J, Y = J cap B, Z = pi_1(m Gamma_X),
the class ZX / ZY / MIX, rk B_X (image subgraph) and rk(Y:X) <= 1 verdict.
usage: a_refute.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dichotomy import classify  # noqa: E402
from surj_check import image_subgraph  # noqa: E402
from census import (graph_of, compact, is_malnormal, rank, relrank_le1,  # noqa
                    canon)

CASES = [(['bab', 'bbAABA'], ['BAB'], [(0, 1)]),
         (['bABaB', 'Abaa'], ['bABaBAABabAbaB', 'bAbaBAABabAbaB', 'bAbbaB'],
          [(1, 5)])]

for Bws, Xws, prs in CASES:
    nB, EB = compact(*graph_of(Bws))
    nx, Ex = compact(*graph_of(Xws))
    cls, rks, (ny, Ey, cy), (mz, Fz) = classify(nx, Ex, nB, EB, prs)
    nbx, Ebx = image_subgraph(nx, Ex, nB, EB)
    print('B=%s malnormal=%s X=%s prs=%s class=%s rk X,J,Y,Z=%s rkBX=%d '
          'Y==B:%s relrank_le1(Y:X)=%s'
          % (Bws, is_malnormal(nB, EB), Xws, prs, cls, rks,
             rank(*compact(nbx, Ebx)), cy == canon(nB, EB),
             relrank_le1(nx, Ex, ny, Ey, cy)))
