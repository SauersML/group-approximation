"""Transporters T(g) = {f in F : g f g^-1 in F} for short g in P_X, restricted to short F-words.
Run: python3 transp.py LG LF"""
import sys
from fmem import in_F, inv
from gens4 import FG, NG, ZG, words

LG = int(sys.argv[1]); LF = int(sys.argv[2])
XG = dict(NG); XG.update(ZG)
FW = words(FG, LF)
for s, g in words(XG, LG):
    T = [fs for fs, f in FW if in_F(g + f + inv(g))]
    if T and len(T) < len(FW):
        print(s, '|', len(T), ' '.join(T[:12]), flush=True)
