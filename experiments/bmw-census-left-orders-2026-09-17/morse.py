# Bestvina-Brady Morse functions on the parity-kernel complex Y = X / Gamma^+ of a BMW datum.
# Y has 4 vertices (cosets c of Gamma -> Z/2 x Z/2), directed edges (c, x) for each letter x (c -> c+x),
# and one square per (c, h, v) with h v = v' h'.  A real 1-cochain f on directed edges with
# f(c+x, x^-1) = -f(c, x) and f(c,h) + f(c+h,v) = f(c,v') + f(c+v',h') for all squares is a cocycle,
# i.e. an affine Gamma^+-equivariant height on X = T_H x T_V with character phi = [f].
# The link of every vertex of X is K_{m,n} (each horizontal direction joined to each vertical one), so the
# ascending link at a vertex of type c is K_{p,q} with p (q) = number of horizontal (vertical) directions
# x with f(c,x) > 0, and the descending link is K_{m-p,n-q}.  If f never vanishes and every ascending and
# descending link is a tree (p = 1 or q = 1, and m-p = 1 or n-q = 1, all four numbers >= 1), then by
# Bestvina-Brady every level set is a tree, ker(phi) acts freely and cocompactly on it, so ker(phi) is a
# finitely generated free group and Gamma^+ = F_k x| Z (after rescaling f to a rational class) is left-orderable.
# The script enumerates sign patterns satisfying the link condition and checks strict feasibility by LP;
# a feasible pattern is then rounded to an integral cocycle which is re-verified exactly.
# usage: morse.py census.json idx...
import sys, json, itertools
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from lo_census import load

def complex_Y(G):
    cos = [(p, q) for p in range(2) for q in range(2)]
    letters = [('h', a) for a in range(G.m)] + [('v', b) for b in range(G.n)]
    inv = {('h', a): ('h', G.iA[a]) for a in range(G.m)}; inv.update({('v', b): ('v', G.iB[b]) for b in range(G.n)})
    mv = lambda c, x: (c[0] ^ (x[0] == 'h'), c[1] ^ (x[0] == 'v'))
    # geometric edges: {(c,x), (c+x, x^-1)}
    E = {}; rep = []
    for c in cos:
        for x in letters:
            if (c, x) in E: continue
            k = len(rep); rep.append((c, x)); E[(c, x)] = (k, 1); E[(mv(c, x), inv[x])] = (k, -1)
    sq = []
    for c in cos:
        for (h, v), (v2, h2) in G.SQ.items():
            row = [0] * len(rep)
            for (cc, x, s) in ((c, ('h', h), 1), (mv(c, ('h', h)), ('v', v), 1),
                               (c, ('v', v2), -1), (mv(c, ('v', v2)), ('h', h2), -1)):
                k, o = E[(cc, x)]; row[k] += s * o
            sq.append(row)
    return cos, letters, E, rep, sq, mv

def good(p, q, m, n):
    ok = lambda a, b: a >= 1 and b >= 1 and (a == 1 or b == 1)
    return ok(p, q) and ok(m - p, n - q)

def search(G):
    cos, letters, E, rep, sq, mv = complex_Y(G)
    ne = len(rep); A_eq = np.array(sq, dtype=float); found = []
    for signs in itertools.product((1, -1), repeat=ne):
        sgn = lambda c, x: signs[E[(c, x)][0]] * E[(c, x)][1]
        if not all(good(sum(sgn(c, x) > 0 for x in letters if x[0] == 'h'),
                        sum(sgn(c, x) > 0 for x in letters if x[0] == 'v'), G.m, G.n) for c in cos):
            continue
        # feasibility: A_eq f = 0, s_e f_e >= 1
        A_ub = -np.diag(signs).astype(float); b_ub = -np.ones(ne)
        r = linprog(np.zeros(ne), A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=np.zeros(len(sq)),
                    bounds=[(None, None)] * ne, method='highs')
        if r.status == 0:
            found.append((signs, r.x))
    return rep, sq, found

def integral(rep, sq, signs, x):
    # find an integral cocycle with the same signs: scale and round, else solve LP with integrality via scaling
    for scale in (1, 2, 3, 4, 6, 12, 60):
        f = [int(round(v * scale)) for v in x]
        if all(s * v > 0 for s, v in zip(signs, f)) and all(sum(a * b for a, b in zip(row, f)) == 0 for row in sq):
            return f
    return None

if __name__ == "__main__":
    path = sys.argv[1]; want = set(map(int, sys.argv[2:]))
    for i, G in load(path):
        if i not in want: continue
        rep, sq, found = search(G)
        out = dict(census=path, idx=i, n_edges=len(rep), n_patterns=len(found))
        if found:
            signs, x = found[0]
            out['edges'] = [[list(c), list(xx)] for (c, xx) in rep]
            out['cocycle'] = integral(rep, sq, signs, x)
            out['cocycle_float'] = [round(v, 4) for v in x]
        print(json.dumps(out), flush=True)
