#!/usr/bin/env python3
# Hatcher normal coordinates of spheres in M_n via cuts of dF_n (lane bh-outfn-2).
# A sphere = one-edge free splitting = F_n-orbit of a clopen cut X of dF_n. Relative to the
# maximal system Sigma dual to the blown-up rose (Y-tree at every vertex of the Cayley tree),
# a lift crosses an edge of T_Sigma iff both sides meet X and X^c; the crossed edges form a
# finite subtree K_X whose vertices of K-degree 3/2/1 are the pants/cylinder/disk pieces.
import sys, json, time, collections
T0 = time.time()
n, MAXS, TLIM, OUT = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
L = list(range(1, n + 1)) + [-i for i in range(1, n + 1)]
C = 2  # bounded-cancellation margin (elementary Nielsen moves have BCC <= 1)

def red(w):
    s = []
    for a in w:
        if s and s[-1] == -a: s.pop()
        else: s.append(a)
    return tuple(s)
def inv(w): return tuple(-a for a in reversed(w))
def app(phi, w):
    r = []
    for a in w: r.extend(phi[a] if a > 0 else inv(phi[-a]))
    return red(r)
def kids(p): return [p + (a,) for a in L if not p or a != -p[-1]]

ident = {i: (i,) for i in range(1, n + 1)}
gens = []
g = dict(ident); g[1] = (2,); g[2] = (1,); gens.append(g)                       # swap x1,x2
if n >= 3:
    g = {i: (i % n + 1,) for i in range(1, n + 1)}; gens.append(g)            # cycle
    g = {i: ((i - 2) % n + 1,) for i in range(1, n + 1)}; gens.append(g)      # cycle^-1
g = dict(ident); g[1] = (-1,); gens.append(g)                                  # invert x1
g = dict(ident); g[1] = (1, 2); gens.append(g)                                 # x1 -> x1 x2
g = dict(ident); g[1] = (1, -2); gens.append(g)                                # x1 -> x1 x2^-1

def classify(trie, P):
    lab, inn = trie
    for k in range(len(P) + 1):
        pre = P[:k]
        if pre in lab: return lab[pre]
        if pre not in inn: return None
    return None
def simplify(lab, inn):
    for p in sorted(inn, key=len, reverse=True):
        if p == (): continue
        ks = kids(p)
        if all(k in lab for k in ks):
            v = set(lab[k] for k in ks)
            if len(v) == 1:
                for k in ks: del lab[k]
                lab[p] = v.pop(); inn.discard(p)
    return (lab, inn)
def image(trie, psi, cap=150000):  # X' = phi^(X) with psi = phi^-1
    lab, inn = {}, {()}
    st = [(a,) for a in L]; c = 0
    while st:
        v = st.pop(); c += 1
        if c > cap: return None
        r = app(psi, v); r = r[:max(0, len(r) - C)]
        x = classify(trie, r)
        if x is None: inn.add(v); st.extend(kids(v))
        else: lab[v] = x
    return simplify(lab, inn)

# Y-tree on the 2n directions. Vertices: list of 3 slots, ('l',a) or ('e',k); edges k: leaf set.
if n == 2:
    YV = [[('l', 1), ('l', 2), ('e', 0)], [('l', -1), ('l', -2), ('e', 0)]]
    YE = [{1, 2}]
else:  # caterpillar
    YV = [[('l', 1), ('l', -1), ('e', 0)]]
    left = {1, -1}; YE = [set(left)]; seq = []
    for i in range(2, n + 1): seq += [i, -i]
    last = seq[-2:]; mid = seq[:-2]
    for j, a in enumerate(mid):
        YV.append([('e', j), ('l', a), ('e', j + 1)])
        left = left | {a}; YE.append(set(left))
    YV.append([('e', len(mid)), ('l', last[0]), ('l', last[1])])
NV, NE = len(YV), len(YE)
assert NV == 2 * n - 2 and NE == 2 * n - 3
SUBS = [s for s in [(0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]]
PIDX = {(y, s): y * 7 + j for y in range(NV) for j, s in enumerate(SUBS)}
NP = 7 * NV; DIM = NP + n + NE  # pieces, then w on petal edges, then w on Y edges

def coords(trie):
    lab, inn = trie
    cnt = {p: ((1, 0) if c else (0, 1)) for p, c in lab.items()}
    for p in sorted(inn, key=len, reverse=True):
        t = f = 0
        for k in kids(p): t += cnt[k][0]; f += cnt[k][1]
        cnt[p] = (t, f)
    TT, TF = cnt[()]
    def anc(p):
        for k in range(len(p) + 1):
            if p[:k] in lab: return p[:k]
        return None
    def cyl(p):
        a = anc(p)
        if a is not None: return (lab[a], not lab[a])
        t, f = cnt[p]; return (t > 0, f > 0)
    def comp(p):
        a = anc(p)
        if a is None:
            t, f = cnt[p]; return (TT - t > 0, TF - f > 0)
        t, f = cnt[a]; mt, mf = TT - t > 0, TF - f > 0
        if a != p:
            if lab[a]: mt = True
            else: mf = True
        return (mt, mf)
    bich = lambda x: x[0] and x[1]
    orr = lambda xs: (any(x[0] for x in xs), any(x[1] for x in xs))
    mono = lambda x: x[0] != x[1]
    v = [0] * DIM; crossed_any = False; w_edge = None
    for g in inn:
        H = {a: (comp(g) if g and a == -g[-1] else cyl(g + (a,))) for a in L}
        pet = {a: (bich(comp(g)) and bich(cyl(g))) if g and a == -g[-1]
               else (bich(cyl(g + (a,))) and bich(comp(g + (a,)))) for a in L}
        yx = []
        for k in range(NE):
            A = orr([H[a] for a in L if a in YE[k]]); B = orr([H[a] for a in L if a not in YE[k]])
            yx.append(bich(A) and bich(B))
            if w_edge is None and mono(A) and mono(B) and A[0] != B[0]: w_edge = n + k
        for a in L:
            if not (g and a == -g[-1]):
                p = g + (a,); x, y = cyl(p), comp(p)
                if w_edge is None and mono(x) and mono(y) and x[0] != y[0]: w_edge = abs(a) - 1
        for yi, slots in enumerate(YV):
            S = tuple(j for j, (kind, z) in enumerate(slots) if (pet[z] if kind == 'l' else yx[z]))
            if S: v[PIDX[(yi, S)]] += 1; crossed_any = True
    if not crossed_any:
        if w_edge is None: return None
        v[NP + w_edge] = 1
    return tuple(v)

# matching equations: each Sigma edge, two ends (vertex, slot)
ends = collections.defaultdict(list)
for yi, slots in enumerate(YV):
    for j, (kind, z) in enumerate(slots):
        ends[('p', abs(z)) if kind == 'l' else ('e', z)].append((yi, j))
MROWS = []
for key, ee in ends.items():
    assert len(ee) == 2
    row = [0] * DIM
    for sgn, (yi, j) in zip((1, -1), ee):
        for S in SUBS:
            if j in S: row[PIDX[(yi, S)]] += sgn
    MROWS.append(row)

def rank(rows, p=1000003):
    M = [[x % p for x in r] for r in rows]; rk = 0; ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
        if piv is None: continue
        M[rk], M[piv] = M[piv], M[rk]; iv = pow(M[rk][c], p - 2, p)
        M[rk] = [x * iv % p for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c]:
                f = M[i][c]; M[i] = [(x - f * y) % p for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk
def qrank(rows): return max(rank(rows, 1000003), rank(rows, 998244353)) if rows else 0

def std(k):  # k=0 nonseparating [x1]; k>=1 separating <x1..xk>*rest
    ins = {(1,)} if k == 0 else {(s * i,) for i in range(1, k + 1) for s in (1, -1)}
    return ({(a,): ((a,) in ins) for a in L}, {()})

# ---- density test (bh-outfn-2, pass 6): spheres vs admissible integer points in the largest classes
from fractions import Fraction
NMAX = int(sys.argv[5]); NEXP = NMAX + 6
def norm(v): return sum(len(S) * v[PIDX[(y, S)]] for y in range(NV) for S in SUBS) // 2
seen = {}; Qu = collections.deque()
for k in range(0, n // 2 + 1):
    t = std(k); v = coords(t)
    if v is not None and v not in seen: seen[v] = 1; Qu.append((t, v))
while Qu and time.time() - T0 < TLIM and len(seen) < MAXS:
    t, v = Qu.popleft()
    for psi in gens:
        t2 = image(t, psi)
        if t2 is None: continue
        v2 = coords(t2)
        if v2 is None or v2 in seen or norm(v2) > NEXP: continue
        seen[v2] = 1; Qu.append((t2, v2))
exhausted = not Qu
spheres = [v for v in seen if norm(v) <= NMAX and sum(v[:NP]) > 0]
classes = collections.defaultdict(list)
for v in spheres: classes[tuple(i for i in range(DIM) if v[i])].append(v)
EUL = [0] * DIM
for y in range(NV):
    for j in range(3): EUL[PIDX[(y, (j,))]] += 1
    EUL[PIDX[(y, (0, 1, 2))]] -= 1
NORMV = [0] * DIM
for y in range(NV):
    for S in SUBS: NORMV[PIDX[(y, S)]] = Fraction(len(S), 2)
def solve_param(cols):
    rows = [[Fraction(r[c]) for c in cols] + [Fraction(0)] for r in MROWS] + [[Fraction(EUL[c]) for c in cols] + [Fraction(2)]]
    piv = []; rk = 0
    for c in range(len(cols)):
        p = next((i for i in range(rk, len(rows)) if rows[i][c] != 0), None)
        if p is None: continue
        rows[rk], rows[p] = rows[p], rows[rk]; iv = 1 / rows[rk][c]
        rows[rk] = [x * iv for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] != 0:
                f = rows[i][c]; rows[i] = [x - f * y for x, y in zip(rows[i], rows[rk])]
        piv.append(c); rk += 1
    if any(all(x == 0 for x in r[:-1]) and r[-1] != 0 for r in rows): return None
    free = [c for c in range(len(cols)) if c not in piv]
    return piv, free, rows[:rk]
out = {'n': n, 'NMAX': NMAX, 'spheres_norm_le_NMAX': len(spheres), 'bfs_exhausted': exhausted,
       'time_bfs_s': round(time.time() - T0, 1), 'classes': []}
top = sorted(classes.items(), key=lambda kv: -len(kv[1]))[:4]
for supp, vs in top:
    cols = list(supp); sp = solve_param(cols)
    if sp is None: continue
    piv, free, rows = sp; f = len(free)
    NE_ = NMAX
    while NE_ > 4 and NE_ ** f > 500000: NE_ -= 1
    import itertools
    adm = collections.Counter()
    for fv in itertools.product(range(1, NE_ + 1), repeat=f):
        x = [None] * len(cols)
        for c, val in zip(free, fv): x[c] = Fraction(val)
        ok = True
        for r, c in zip(rows, piv):
            val = r[-1] - sum(r[fc] * x[fc] for fc in free)
            if val.denominator != 1 or val < 1: ok = False; break
            x[c] = val
        if not ok: continue
        nm = sum(NORMV[cols[i]] * x[i] for i in range(len(cols)))
        if nm.denominator != 1 or nm > NE_: continue
        adm[int(nm)] += 1
    sph = collections.Counter(norm(v) for v in vs)
    tab = []; ca = cs = 0
    for N in range(0, NE_ + 1):
        ca += adm[N]; cs += sph[N]
        if adm[N] or sph[N]: tab.append((N, cs, ca))
    out['classes'].append({'support': len(cols), 'rank': qrank(vs), 'free_dims_after_euler': f,
                           'enum_norm_bound': NE_, 'spheres_in_class': len(vs), 'table_N_spheres_admissible': tab})
out['time_total_s'] = round(time.time() - T0, 1)
json.dump(out, open(OUT, 'w'), indent=1)
print(json.dumps(out))
