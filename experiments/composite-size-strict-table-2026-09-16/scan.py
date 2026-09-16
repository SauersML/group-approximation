import sys, itertools
from fractions import Fraction
from fastsat import partitions, solve
import numpy as np

nS, nM = int(sys.argv[1]), int(sys.argv[2])
NMAX = int(sys.argv[3])
BUDGET = int(sys.argv[4]) if len(sys.argv) > 4 else 200000

def canon(part):
    m = {}; out = []
    for c in part:
        if c not in m: m[c] = len(m)
        out.append(m[c])
    return tuple(out)

def closure_abelian(Tf):
    # labels: S labels 0..nS-1 (0 = identity), M labels 0..nM-1 (0 = identity)
    # vector for cell (s,m): e_s + e_m in Z^{(nS-1)+(nM-1)}
    d = (nS-1)+(nM-1)
    def vec(s, m):
        v = [0]*d
        if s > 0: v[s-1] += 1
        if m > 0: v[nS-1+m-1] += 1
        return v
    cells = [(s,m) for s in range(nS) for m in range(nM)]
    rels = []
    for i in range(len(cells)):
        for j in range(i+1, len(cells)):
            if Tf[i] == Tf[j]:
                a = vec(*cells[i]); b = vec(*cells[j])
                rels.append([x-y for x,y in zip(a,b)])
    # two cells equal in the abelian group iff difference lies in Z-span of rels.
    # Use rational span as approximation? torsion matters: use Smith/HNF over Z. Simple approach: integer lattice membership via sympy
    return rels, vec, cells

def hnf(rows, d):
    # integer row echelon form
    B = [list(r) for r in rows if any(r)]
    basis = []
    col = 0
    while B and col < d:
        nz = [r for r in B if r[col] != 0]
        z = [r for r in B if r[col] == 0]
        if not nz:
            col += 1; continue
        while len(nz) > 1:
            nz.sort(key=lambda r: abs(r[col]))
            p = nz[0]
            new = [p]
            for r in nz[1:]:
                q = r[col] // p[col]
                r2 = [a - q*b for a, b in zip(r, p)]
                if r2[col] != 0: new.append(r2)
                elif any(r2): z.append(r2)
            nz = new
        p = nz[0]
        if p[col] < 0: p = [-a for a in p]
        basis.append((col, p))
        B = z
        col += 1
    return basis

def in_lattice(rels, v):
    d = len(v)
    basis = hnf(rels, d)
    w = list(v)
    for col, p in basis:
        if w[col] % p[col] != 0: return False
        q = w[col] // p[col]
        w = [a - q*b for a, b in zip(w, p)]
    return not any(w)

def realized_reverse(Tf):
    rels, vec, cells = closure_abelian(Tf)
    # forward closure classes
    nc = len(cells)
    parent = list(range(nc))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    unknown = False
    for i in range(nc):
        for j in range(i+1, nc):
            a = vec(*cells[i]); b = vec(*cells[j])
            r = in_lattice(rels, [x-y for x,y in zip(a,b)])
            if r is None: unknown = True
            if r:
                parent[find(i)] = find(j)
    clos = canon([find(i) for i in range(nc)])
    # reverse cell (m,s) index m*nS+s gets class of forward (s,m)
    rev = canon([clos[s*nM+m] for m in range(nM) for s in range(nS)])
    return clos, rev, unknown

def finer_or_equal(P, Q):
    # P finer than Q: every P-class inside a Q-class
    mp = {}
    for p, q in zip(P, Q):
        if p in mp and mp[p] != q: return False
        mp[p] = q
    return True

parts = list(partitions(nS*nM))
cells_f = [(s,m) for s in range(nS) for m in range(nM)]
cells_r = [(m,s) for m in range(nM) for s in range(nS)]
# symmetry: permutations of nonidentity S labels and M labels
symS = [ (0,)+p for p in itertools.permutations(range(1,nS)) ]
symM = [ (0,)+p for p in itertools.permutations(range(1,nM)) ]
def act(Tf, Tr, ps, pm):
    Tf2 = [None]*(nS*nM); Tr2 = [None]*(nS*nM)
    for s in range(nS):
        for m in range(nM):
            Tf2[ps[s]*nM+pm[m]] = Tf[s*nM+m]
            Tr2[pm[m]*nS+ps[s]] = Tr[m*nS+s]
    return canon(Tf2), canon(Tr2)

seen = set()
stats = {}
for Tf in parts:
    clos, rev, unk = realized_reverse(Tf)
    O = Tf[0]
    for Tr in parts:
        key = (Tf, Tr)
        if key in seen: continue
        orbit = set(act(Tf, Tr, ps, pm) for ps in symS for pm in symM)
        seen |= orbit
        if finer_or_equal(rev, Tr) and not unk:
            stats['abelian'] = stats.get('abelian',0)+1
            continue
        copy = False
        for (s,m) in cells_f:
            if (s,m) != (0,0) and Tf[s*nM+m] == O and Tr[m*nS+s] != Tr[0]:
                copy = True
        if copy:
            stats['copy'] = stats.get('copy',0)+1
            continue
        res = ''
        for n in range(2, NMAX+1):
            ok, _, _ = solve(nS, nM, Tf, Tr, n, budget=BUDGET)
            res += 'Y' if ok else ('N' if ok is False else '?')
        stats[res] = stats.get(res,0)+1
        flag = 'NONMONO' if ('YN' in res) else ''
        print(Tf, Tr, res, flag, flush=True)
print(stats)
