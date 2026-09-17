"""Enumerate triangle presentations over PG(2,q), q = $Q (default 3), up to PGL(3,q) (CMSZ: T subset P^3, cyclically
invariant, for each x,y: exists (unique) z with (x,y,z) in T iff y in lambda(x), lambda: P -> L a bijection).
Exact cover of the arc set {(x,y): y in lambda(x)} by cyclic triangle classes, solved jointly with
lambda by SAT.  Symmetry breaking: lambda(0) in {L_flag, L_antiflag} (PGL(3,3)_0 is transitive on
lines through 0 and on lines missing 0).  After each model the whole PGL(3,3)-orbit (restricted to
images obeying the breaking) is blocked, so each solve yields a new orbit.  Usage: Q=q enumerate_pg2.py out.json (resumable)."""
import itertools, json, sys
from pysat.solvers import Cadical153
from pysat.card import CardEnc

import os
F = int(os.environ.get('Q', '3'))
vecs = []
for v in itertools.product(range(F), repeat=3):
    if v == (0, 0, 0): continue
    first = next(c for c in v if c)
    if first == 1: vecs.append(v)
n = len(vecs); idx = {v: i for i, v in enumerate(vecs)}
def norm(v):
    first = next(c for c in v if c % F)
    inv = pow(first, -1, F)
    return tuple((c * inv) % F for c in v)
lines = [frozenset(i for i, p in enumerate(vecs) if sum(a * b for a, b in zip(p, l)) % F == 0) for l in vecs]
lineidx = {L: j for j, L in enumerate(lines)}

G = set()
for m in itertools.product(range(F), repeat=9):
    M = [m[0:3], m[3:6], m[6:9]]
    det = (M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1]) - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])
           + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0])) % F
    if det == 0: continue
    perm = tuple(idx[norm(tuple(sum(M[r][c] * v[c] for c in range(3)) % F for r in range(3)))] for v in vecs)
    G.add(perm)
G = sorted(G)
assert len(G) == (F**3 - 1) * (F**3 - F) * (F**3 - F**2) // (F - 1)

def cls(t):
    rots = [t[i:] + t[:i] for i in range(3)]
    return min(rots)
classes = sorted({cls(t) for t in itertools.product(range(n), repeat=3)})
cid = {c: i for i, c in enumerate(classes)}

nv = 0
def new():
    global nv; nv += 1; return nv
lam = [[new() for _ in range(n)] for _ in range(n)]
tv = [new() for _ in classes]
arc = [[new() for _ in range(n)] for _ in range(n)]
S = Cadical153()
def addcard(lits, k=1):
    global nv
    enc = CardEnc.equals(lits=lits, bound=k, top_id=nv)
    nv = max(nv, enc.nv)
    for c in enc.clauses: S.add_clause(c)
for x in range(n):
    addcard([lam[x][L] for L in range(n)])
for L in range(n):
    addcard([lam[x][L] for x in range(n)])
for x in range(n):
    for y in range(n):
        Ls = [L for L in range(n) if y in lines[L]]
        S.add_clause([-arc[x][y]] + [lam[x][L] for L in Ls])
        for L in Ls: S.add_clause([arc[x][y], -lam[x][L]])
        tri = [tv[cid[cls((x, y, z))]] for z in range(n)]
        for t in tri: S.add_clause([arc[x][y], -t])
        S.add_clause([-arc[x][y]] + tri)
        for a, b in itertools.combinations(tri, 2): S.add_clause([-a, -b])
Lflag = next(j for j in range(n) if 0 in lines[j]); Lanti = next(j for j in range(n) if 0 not in lines[j])
S.add_clause([lam[0][Lflag], lam[0][Lanti]])

def lam0(T):
    return lineidx[frozenset(y for (x, y, z) in alltrip(T) if x == 0)]
def alltrip(T):
    out = set()
    for t in T:
        for i in range(3): out.add(t[i:] + t[:i])
    return out

OUT = sys.argv[1]
import os
reps = []
def block_orbit(T):
    seen = set(); stab = 0
    for g in G:
        img = frozenset(cls((g[a], g[b], g[c])) for (a, b, c) in T)
        if img == frozenset(T): stab += 1
        if img in seen: continue
        seen.add(img)
        if lam0(img) in (Lflag, Lanti):
            S.add_clause([-tv[cid[c]] for c in img])
    return stab
if os.path.exists(OUT):          # resume: re-block orbits already found
    for T in json.load(open(OUT)):
        T = [tuple(t) for t in T]; reps.append(T); block_orbit(T)
    print("resumed with", len(reps), "orbits", flush=True)
while S.solve():
    m = set(l for l in S.get_model() if l > 0)
    T = [classes[i] for i, v in enumerate(tv) if v in m]
    reps.append(T)
    stab = block_orbit(T)
    json.dump(reps, open(OUT + ".tmp", "w")); os.replace(OUT + ".tmp", OUT)
    torsion = sum(1 for c in T if c[0] == c[1] == c[2])
    print(f"class {len(reps)-1}: |T|={len(T)} (x,x,x)-triples={torsion} |stab|={stab}", flush=True)
print("COMPLETE: orbits under PGL(3,q):", len(reps))
