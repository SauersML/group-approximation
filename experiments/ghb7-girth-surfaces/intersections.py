#!/usr/bin/env python3
"""Intersections of the psi-images of the GHB_2(7) vertex groups in SL_4(F_7).
Since psi is injective on each vertex group, |psi X_i ∩ psi X_j| = 7 forces X_i ∩ X_j = <g_k> in G,
and a trivial triple intersection forces X_0 ∩ X_1 ∩ X_2 = 1 in G."""
import ghb7_girth_surfaces as g

def clos(gens):
    S = {g.I4}; fr = [g.I4]
    while fr:
        nf = []
        for x in fr:
            for s in gens:
                y = g.mul(x, s)
                if y not in S: S.add(y); nf.append(y)
        fr = nf
    return S

X0, X1, X2 = clos([g.A, g.B]), clos([g.C, g.B]), clos([g.C, g.A])
Ea, Eb, Ec = clos([g.A]), clos([g.B]), clos([g.C])
print("orders", len(X0), len(X1), len(X2), "edge groups", len(Ea), len(Eb), len(Ec))
print("X0&X1 == <b>", (X0 & X1) == Eb, "X0&X2 == <a>", (X0 & X2) == Ea, "X1&X2 == <c>", (X1 & X2) == Ec)
print("triple intersection size", len(X0 & X1 & X2))

def pw(x, e):
    y = g.I4
    for _ in range(e % 7): y = g.mul(y, x)
    return y

def scaling_is_automorphism(x, y, s, t):
    """Does x -> x^s, y -> y^t extend to an automorphism of <x,y>?  Build phi along a BFS tree,
    then check phi(h*gen) = phi(h)*phi(gen) for every h and both generators, and bijectivity."""
    img = {x: pw(x, s), y: pw(y, t)}
    phi = {g.I4: g.I4}; fr = [g.I4]
    while fr:
        nf = []
        for h in fr:
            for gen in (x, y):
                k = g.mul(h, gen)
                if k not in phi: phi[k] = g.mul(phi[h], img[gen]); nf.append(k)
        fr = nf
    hom = all(phi[g.mul(h, gen)] == g.mul(phi[h], img[gen]) for h in phi for gen in (x, y))
    return hom and len(set(phi.values())) == len(phi)

for name, x, y in (("X0=<a,b>", g.A, g.B), ("X1=<c,b>", g.C, g.B), ("X2=<c,a>", g.C, g.A)):
    bad = [(s, t) for s in range(1, 7) for t in range(1, 7) if not scaling_is_automorphism(x, y, s, t)]
    print(name, "scalings that fail to be automorphisms:", bad)
