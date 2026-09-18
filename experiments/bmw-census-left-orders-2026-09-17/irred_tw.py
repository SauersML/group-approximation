# Irreducibility certificate for a BMW datum via the Thompson-Wielandt theorem.
# H = pr_V(Gamma) acts vertex-transitively on the vertical tree T_V; H_x = image of <A> (horizontal letters),
# with a acting on vertical words by a.(v1 v2 ...) = v1' (a'.(v2 ...)) where a v1 = v1' a'.
# If H were discrete and locally primitive, then H_x is finite and the edge kernel H_{xy}^{[1]}
# (elements fixing B(x,1) and B(y,1) pointwise) is a p-group (Thompson-Wielandt).  Its image Q_r in the
# permutation group P_r of the ball B(x,r) is exactly the pointwise stabilizer of B(x,1) u B(y,1) in P_r,
# so if |Q_r| has two distinct prime factors, H is non-discrete, hence Gamma is irreducible (Burger-Mozes).
# The same test is run with the roles of the letters swapped (side 'H': <B> acting on T_H).
# usage: irred_tw.py census.json r side idx...     side in {V,H}
import sys, json
from sympy.combinatorics import Permutation, PermutationGroup
from sympy import factorint
from lo_census import load

def maps(G, side):
    if side == 'V':
        return G.m, G.n, G.iB, (lambda a, x: G.SQ[(a, x)])
    SQinv = {}
    for (h, v), (v2, h2) in G.SQ.items(): SQinv[(G.iB[v2], h)] = (h2, G.iB[v])
    return G.n, G.m, G.iA, (lambda a, x: SQinv[(a, x)])

def ball_words(n, inv, r):
    W = [()]; out = []
    for _ in range(r):
        W = [w + (x,) for w in W for x in range(n) if not w or inv[w[-1]] != x]
        out += W
    return out

def act(step, a, w):
    y = []
    for x in w:
        x2, a = step(a, x); y.append(x2)
    return tuple(y)

def certify(G, r, side):
    L, n, inv, step = maps(G, side)
    pts = ball_words(n, inv, r); ix = {w: i for i, w in enumerate(pts)}
    gens = [Permutation([ix[act(step, a, w)] for w in pts]) for a in range(L)]
    P = PermutationGroup(gens)
    loc = PermutationGroup([Permutation([ix[act(step, a, (x,))] for x in range(n)]) for a in range(L)])
    y = (0,)
    fix = [ix[w] for w in pts if len(w) == 1 or (len(w) == 2 and w[0] == y[0])]
    Q = P.pointwise_stabilizer(fix)
    q = Q.order()
    return dict(local_order=int(loc.order()), local_primitive=bool(loc.is_transitive() and loc.is_primitive()),
                P_order=int(P.order()), Q_order=int(q), Q_primes=sorted(int(p) for p in factorint(q)),
                irreducible=bool(loc.is_transitive() and loc.is_primitive() and len(factorint(q)) >= 2))

if __name__ == "__main__":
    path, r, side = sys.argv[1], int(sys.argv[2]), sys.argv[3]; want = set(map(int, sys.argv[4:]))
    for i, G in load(path):
        if i in want:
            print(json.dumps(dict(census=path, idx=i, r=r, side=side, **certify(G, r, side))), flush=True)
