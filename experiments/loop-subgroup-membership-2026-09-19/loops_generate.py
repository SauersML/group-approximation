#!/usr/bin/env python3
"""Certificate that the loop subgroup L = <s,t,u> is all of G for the chain survivor (a,a,e).
(1) St_L(0) has sections u, sU, tU, s a e t, t a u at 0, so L_0 = G.
(2) d = [x, x^h] (x = sT, h = sUSSS) lies in L, fixes level 1, and is supported on {2}; its
    section at 2 has nontrivial root, so K_2 = {g : iota_2(g) in L} is a normal subgroup of G
    with a nontrivial root, whence K_2 >= G' and L >= (G')^X (proof file).
(3) run lat1.py: L maps onto G/(G')^X = Z^33 x| M_11, so L = G."""
import sys as _sys, os as _os
_HERE = _os.path.dirname(_os.path.abspath(__file__))
for _d in ('loop-graph-screen-2026-09-18', 'poly-star-obstruction-2026-09-19'):
    _sys.path.insert(0, _os.path.join(_HERE, '..', _d))
from stab import *
chk = lambda b, msg: print(("ok  " if b else "FAIL") + " " + msg) or b
def at0(w):
    w = W(w); return R.perm(w)[0] == 0, fmt(R.sec(w, 0))
for w in ["u u u u u", "s U", "t U", " ".join(["s"] * 11), " ".join(["t"] * 11)]:
    f, sec = at0(w); chk(f, "%-24s fixes 0, section at 0 = %s" % (w, sec))
x = W("s T"); h = W("s U S S S")
d = comm(x, conj(x, h))
chk(R.perm(d) == ID, "d = [sT, (sT)^(sUSSS)] has trivial root, length %d" % len(d))
chk(supp(d) == frozenset([2]), "support of d on level 1 is %s" % sorted(supp(d)))
chk(R.perm(R.sec(d, 2)) != ID, "root of d|_2 = %s" % (R.perm(R.sec(d, 2)),))
