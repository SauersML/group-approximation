"""phi transports seed types of depth j-1 bijectively onto the seed types of
depth j of level >= 1.

A seed type of depth j is a double coset L_{j+1} h L_{j+1} realised by a pair
(c, c') of vertices of C_{j+1}: h = u_c u_{c'}^{-1}.  It is realised iff the
fold X_h of (copy 1 of C_{j+1}) + (path h from base 1 to base 2) + (copy 2)
has no vertex outside the two copies; the pairs (v1, v2) glued in X_h are
then exactly the pairs of that type.
For every type (c, c') of depth j-1 this script folds X_{phi(h)} at depth j,
checks it is realised, records the type it lands in and checks:
  (a) every image is realised; (b) distinct types go to distinct types;
  (c) the image is exactly the set of level >= 1 types of depth j
      (pairs whose images in C_1 coincide), lawful going to lawful.
Usage: python3 phi_types.py jmax"""
import os
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import Fold, Graph, gamma, A, t, phi, inv, reduce  # noqa: E402


def core(i):
    return Graph(gamma([0], [0], [A, t(i)]), 1, [0], [0])


def types(C):
    """union-find on unordered off-diagonal pairs of C; returns pair -> root"""
    V = C.V
    pairs = [(c, d) for c in range(V) for d in range(c + 1, V)]
    par = {p: p for p in pairs}

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for (c, d) in pairs:
        for k in C.nb[c]:
            if k[1] == 1 and k in C.nb[d]:
                u, v = C.nb[c][k], C.nb[d][k]
                par[f((min(u, v), max(u, v)))] = f((c, d))
    return {p: f(p) for p in pairs}


def realise(C, h):
    """fold copy1 + path h + copy2; return set of glued unordered pairs, or None"""
    F = Fold()
    V = C.V
    for _ in range(2 * V):
        F.new()
    for off in (0, V):
        for v in range(V):
            for (l, e), u in C.nb[v].items():
                if e == 1:
                    F.add_edge(v + off, l, u + off)
    if h:
        F.add_path(0, h, V)
    else:
        F.union(0, V)
    roots = {F.find(x) for x in range(2 * V)}
    if roots != set(F.roots()):
        return None
    glued = set()
    for v in range(V):
        for w in range(V):
            if F.find(v) == F.find(w + V) and v != w:
                glued.add((min(v, w), max(v, w)))
    return glued


def to_c1(C_maps, v):
    for mm in C_maps:
        v = mm[v]
    return v


JMAX = int(sys.argv[1])
cores = [core(i) for i in range(JMAX + 2)]
# maps C_{i+1} -> C_i by reading BFS words
maps = {}
for i in range(JMAX + 1):
    D, C = cores[i + 1], cores[i]
    maps[i] = [C.read(0, D.word[v][1]) for v in range(D.V)]
for j in range(1, JMAX + 1):
    C0, C1 = cores[j], cores[j + 1]   # depth j-1 uses C_j; depth j uses C_{j+1}
    ty0, ty1 = types(C0), types(C1)
    reps0 = {}
    for p, r in ty0.items():
        reps0.setdefault(r, p)
    chain = [maps[i] for i in range(j, 0, -1)]   # C_{j+1} -> ... -> C_1
    lev1 = {r for p, r in ty1.items() if to_c1(chain, p[0]) == to_c1(chain, p[1])}
    law1 = {r for p, r in ty1.items() if maps[j][p[0]] == maps[j][p[1]]}
    law0 = {r for p, r in ty0.items() if maps[j - 1][p[0]] == maps[j - 1][p[1]]}
    image = {}
    ok = True
    for r, (c, d) in reps0.items():
        h = reduce(phi(C0.word[c][1] + inv(C0.word[d][1])))
        g = realise(C1, h)
        if not g:
            ok = False
            print('j', j, 'type', (c, d), 'NOT realised')
            continue
        tys = {ty1[p] for p in g}
        if len(tys) != 1:
            ok = False
            print('j', j, 'glued pairs span', len(tys), 'types')
        image[r] = tys.pop()
    inj = len(set(image.values())) == len(image)
    onto = set(image.values()) == lev1
    lawok = all((r in law0) == (image[r] in law1) for r in image)
    print('j', j, 'types depth j-1', len(reps0), 'level>=1 types depth j', len(lev1),
          'realised', ok, 'injective', inj, 'onto level>=1', onto, 'lawful<->lawful', lawok)
