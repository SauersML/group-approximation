"""Calibration: the Promislow (Hantzsche-Wendt) group is torsion-free and not left-orderable;
F2 x F2 is left-orderable.  The SAT search must return UNSAT for the first and SAT for the second."""
from fractions import Fraction as Fr
from lo_sat import CNFBuilder
from bmw import BMW, product_group
import itertools, sys

def amul(g, h):  # affine maps (M diag signs, t): v -> M v + t ; (g h)(v) = g(h v)
    M1, t1 = g; M2, t2 = h
    return (tuple(M1[i]*M2[i] for i in range(3)), tuple(M1[i]*t2[i] + t1[i] for i in range(3)))
def ainv(g):
    M, t = g
    return (M, tuple(-M[i]*t[i] for i in range(3)))
E = ((1,1,1),(Fr(0),)*3)
x = ((1,-1,-1),(Fr(1,2),Fr(1,2),Fr(0)))
y = ((-1,1,-1),(Fr(0),Fr(1,2),Fr(1,2)))
gens = [x, y, ainv(x), ainv(y)]
def ball(gens, mul, e, R):
    B = {e: 0}; frontier = [e]
    for k in range(1, R+1):
        nf = []
        for g in frontier:
            for s in gens:
                h = mul(g, s)
                if h not in B:
                    B[h] = k; nf.append(h)
        frontier = nf
    return B
def run(gens, mul, inv, e, R):
    B = ball(gens, mul, e, R)
    els = [g for g in B if g != e]
    cb = CNFBuilder(els, inv)
    for p in els:
        for q in els:
            r = mul(p, q)
            if r in B and r != e:
                cb.add_triple(p, q, r)
    res, model, t = cb.solve()
    return len(els), len(cb.clauses), res, t
for R in (1, 2, 3, 4):
    print("Promislow R=%d" % R, run(gens, amul, ainv, E, R)); sys.stdout.flush()
G = BMW(2, 2, product_group(2, 2))
e = ((), ())
bg = [((1,),()),((-1,),()),((2,),()),((-2,),()),((),(1,)),((),(-1,)),((),(2,)),((),(-2,))]
for R in (2, 3, 4):
    print("F2xF2 R=%d" % R, run(bg, G.mul, G.inv, e, R)); sys.stdout.flush()
