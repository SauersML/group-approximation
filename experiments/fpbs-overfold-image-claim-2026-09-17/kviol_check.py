"""Recheck the rank-2 non-malnormal kernel violations printed by kern.py.

X = ker(B -> S3) (index 6, normal), one pair (0,6): Y = B and rk(B:X) = 2.
Prints malnormality of B, ranks of X, J, Y and the relrank_le1 verdict.
usage: kviol_check.py
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ab_split  # noqa: E402,F401  (sets census path)
from census import (graph_of, compact, regular_action, fi_subgroup, fold,  # noqa
                    pullback, rank, canon, relrank_le1, is_malnormal)

CASES = [(['BaaB', 'BBaa'], [[0, 2, 3, 1], [0, 2, 1, 3]]),
         (['abABA', 'baaaB'], [[0, 2, 1], [2, 0, 1]])]

for ws, perms in CASES:
    nB, EB = compact(*graph_of(ws))
    reg = regular_action(perms)
    nx, Ex = fi_subgroup(ws, reg)
    m, F, _ = fold(nx, Ex, [(0, 6)])
    nj, Ej = compact(m, F)
    ny, Ey = compact(*pullback(m, F, nB, EB))
    cy = canon(ny, Ey)
    print(ws, 'malnormal=%s' % is_malnormal(nB, EB), '|G|=%d' % len(reg[0]),
          'rkX=%d rkJ=%d |V(J)|=%d rkY=%d Y==B:%s relrank_le1=%s'
          % (rank(nx, Ex), rank(nj, Ej), nj, rank(ny, Ey),
             cy == canon(nB, EB), relrank_le1(nx, Ex, ny, Ey, cy)))
