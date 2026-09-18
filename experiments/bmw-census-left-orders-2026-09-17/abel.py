# Abelianization of the parity kernel Gamma^+ of a BMW datum, by Reidemeister-Schreier over the four cosets
# of Gamma -> Z/2 x Z/2 (parity of horizontal and of vertical letters), followed by Smith normal form.
# usage: abel.py census.json idx...
import sys, json
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form
from lo_census import load

def abel(G):
    gens = [('h', a) for a in range(G.m)] + [('v', b) for b in range(G.n)]
    inv = {('h', a): ('h', G.iA[a]) for a in range(G.m)}; inv.update({('v', b): ('v', G.iB[b]) for b in range(G.n)})
    rels = []
    for (h, v), (v2, h2) in G.SQ.items():                         # h v h'^-1 v'^-1
        rels.append([('h', h, 1), ('v', v, 1), ('h', h2, -1), ('v', v2, -1)])
    for x in gens:                                                   # x x_inv
        rels.append([x + (1,), inv[x] + (1,)])
    cos = [(p, q) for p in range(2) for q in range(2)]
    def mv(c, x): return (c[0] ^ (x[0] == 'h'), c[1] ^ (x[0] == 'v'))
    # Schreier generators y[c, x] for each coset c and generator x (positive letter), c --x--> mv(c,x)
    Y = {}
    for c in cos:
        for x in gens: Y[(c, x)] = len(Y)
    # Schreier transversal: 1, h0, v0, h0 v0 (tree edges: (0,0)-h0->(1,0), (0,0)-v0->(0,1), (0,1)-h0->(1,1))
    tree = [((0, 0), ('h', 0)), ((0, 0), ('v', 0)), ((0, 1), ('h', 0))]
    rows = []
    for (c, x) in tree:
        r = [0] * len(Y); r[Y[(c, x)]] = 1; rows.append(r)
    for c in cos:
        for rel in rels:
            r = [0] * len(Y); cur = c
            for (t, a, e) in rel:
                x = (t, a)
                if e == 1:
                    r[Y[(cur, x)]] += 1; cur = mv(cur, x)
                else:
                    prev = mv(cur, x); r[Y[(prev, x)]] -= 1; cur = prev
            assert cur == c
            rows.append(r)
    M = Matrix(rows)
    S = smith_normal_form(M, domain=ZZ)
    d = [S[i, i] for i in range(min(S.shape)) if S[i, i] != 0]
    rank = len(d); free = len(Y) - rank
    return dict(betti1=free, torsion=[int(abs(x)) for x in d if abs(x) != 1])

if __name__ == "__main__":
    path = sys.argv[1]; want = set(map(int, sys.argv[2:]))
    for i, G in load(path):
        if i in want: print(json.dumps(dict(census=path, idx=i, **abel(G))), flush=True)
