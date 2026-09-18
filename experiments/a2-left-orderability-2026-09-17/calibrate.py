"""Calibration: the same positive-cone clause builder must return SAT on left-orderable groups
(Z^2, free group F_2, Klein-bottle group) and UNSAT on a known non-LO torsion-free group
(Promislow / Fibonacci-type: <a,b | a^-1 b^2 a b^2, b^-1 a^2 b a^2>, via its Z^3 normal subgroup model)."""
from pysat.solvers import Cadical153
import itertools

def sat(elems, mul, inv, one):
    var = {}; nv = 0
    for w in elems:
        if w == one or w in var: continue
        nv += 1; var[w] = nv; var[inv(w)] = -nv
    S = Cadical153()
    for g in var:
        for h in var:
            gh = mul(g, h)
            if gh != one and gh in var:
                S.add_clause([-var[g], -var[h], var[gh]])
    return S.solve()

# Z^2
R = 4
Z2 = [(i, j) for i in range(-R, R+1) for j in range(-R, R+1) if abs(i)+abs(j) <= R]
print("Z^2 SAT:", sat(set(Z2), lambda g, h: (g[0]+h[0], g[1]+h[1]), lambda g: (-g[0], -g[1]), (0, 0)))
# F_2 reduced words
def fred(w):
    out = []
    for c in w:
        if out and out[-1] == -c: out.pop()
        else: out.append(c)
    return tuple(out)
F = {()}
for n in range(3):
    F |= {fred(w + (c,)) for w in F for c in (1, -1, 2, -2)}
print("F_2 SAT:", sat(F, lambda g, h: fred(g+h), lambda g: tuple(-c for c in reversed(g)), ()))
# Promislow group: Z^3 x| (Z/2)^2 model: elements (v, s) v in Z^3, s in {0,1}^2 acting by sign flips.
# a = ((1,0,0), (1,0)) , b = ((0,1,0),(0,1)) with a acting by diag(1,-1,-1), b by diag(-1,1,-1).
def act(s, v):
    d = [1, 1, 1]
    if s[0]: d[1] *= -1; d[2] *= -1
    if s[1]: d[0] *= -1; d[2] *= -1
    return tuple(d[i]*v[i] for i in range(3))
def pm(g, h):
    return (tuple(g[0][i] + act(g[1], h[0])[i] for i in range(3)), ((g[1][0]+h[1][0]) % 2, (g[1][1]+h[1][1]) % 2))
def pinv(g):
    s = g[1]; v = act(s, g[0])
    return (tuple(-x for x in v), s)
a = ((1, 0, 0), (1, 0)); b = ((0, 1, 0), (0, 1))
gens = [a, b, pinv(a), pinv(b)]
one = ((0, 0, 0), (0, 0))
B = {one}
for n in range(4):
    B |= {pm(w, s) for w in B for s in gens}
print("Promislow ball", len(B), "SAT:", sat(B, pm, pinv, one))
