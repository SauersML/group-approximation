#!/usr/bin/env python3
"""Pushout fold group P_V = N/<<K cap N>>^N for the Gamma_mal stage.

L = F(b, c) (free basis; c = b a b^-2, so a = b^-1 c b^2), K = <a, c>.
V = finite transitive right L-set given by permutations Pb, Pc on range(n)
(right action: v.b = Pb[v]).  With K transitive on V:

    N/M  =  P_V = < t_v (v in V) | t_v = t_{v c} t_{v c b} >        (*)

(one vertex, n edges, n triangles; see the research node).  We compute
  * Z_S(V) = |Hom(P_V, S)| = #{s in S^V : s_v = s_{vc} s_{vcb}}   (counting)
  * H1(P_V) = coker(I - Pc - Pc Pb) on Z^V : |H1| and max_p dim H1 (x) F_p
  * the 2-of-3 percolation number upper bound (greedy) r(V)
Relative rank e(V) = d(N | K cap N) >= d(P_V) >= log_|S| Z_S(V).
"""
import itertools, math, random, sys
from collections import deque

# ---------- finite groups S as permutation tuples ----------
def pmul(p, q):  # p then q (right action): (x)pq = ((x)p)q
    return tuple(q[p[i]] for i in range(len(p)))

def pinv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)

def closure(gens):
    idt = tuple(range(len(gens[0])))
    elems = {idt}
    frontier = [idt]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = pmul(x, g)
                if y not in elems:
                    elems.add(y)
                    nf.append(y)
        frontier = nf
    return sorted(elems)

def table(elems):
    idx = {e: i for i, e in enumerate(elems)}
    m = len(elems)
    mul = [[idx[pmul(elems[i], elems[j])] for j in range(m)] for i in range(m)]
    inv = [idx[pinv(elems[i])] for i in range(m)]
    one = idx[tuple(range(len(elems[0])))]
    return mul, inv, one

def small_groups():
    G = {}
    G['C2'] = closure([(1, 0)])
    G['C3'] = closure([(1, 2, 0)])
    G['S3'] = closure([(1, 0, 2), (1, 2, 0)])
    G['A4'] = closure([(1, 2, 0, 3), (0, 2, 3, 1)])
    G['S4'] = closure([(1, 0, 2, 3), (1, 2, 3, 0)])
    G['A5'] = closure([(1, 2, 0, 3, 4), (0, 1, 3, 4, 2), (1, 2, 3, 4, 0)])
    # SL(2,3) acting on the 8 nonzero vectors of F_3^2
    vecs = [(x, y) for x in range(3) for y in range(3) if (x, y) != (0, 0)]
    vi = {v: i for i, v in enumerate(vecs)}
    def mat(a, b, c, d):
        return tuple(vi[((a * x + c * y) % 3, (b * x + d * y) % 3)] for (x, y) in vecs)
    G['SL23'] = closure([mat(1, 1, 0, 1), mat(1, 0, 1, 1)])
    return G

# ---------- L-sets ----------
def triples(Pb, Pc):
    n = len(Pb)
    return [(v, Pc[v], Pb[Pc[v]]) for v in range(n)]  # s_v = s_{vc} s_{vcb}

def k_orbits(Pb, Pc):
    n = len(Pb)
    Pbi = pinv(Pb)
    Pa = [Pb[Pb[Pc[Pbi[v]]]] for v in range(n)]  # a = b^-1 c b^2
    seen, t = [False] * n, 0
    for s in range(n):
        if seen[s]:
            continue
        t += 1
        st = [s]; seen[s] = True
        while st:
            v = st.pop()
            for w in (Pc[v], Pa[v]):
                if not seen[w]:
                    seen[w] = True; st.append(w)
    return t

def l_transitive(Pb, Pc):
    n = len(Pb); seen = {0}; st = [0]
    Pbi, Pci = pinv(Pb), pinv(Pc)
    while st:
        v = st.pop()
        for P in (Pb, Pc, Pbi, Pci):
            if P[v] not in seen:
                seen.add(P[v]); st.append(P[v])
    return len(seen) == n

def random_lset(n, rng):
    while True:
        Pb = list(range(n)); rng.shuffle(Pb)
        Pc = list(range(n)); rng.shuffle(Pc)
        Pb, Pc = tuple(Pb), tuple(Pc)
        if l_transitive(Pb, Pc) and k_orbits(Pb, Pc) == 1:
            return Pb, Pc

def regular_lset(beta, gamma):
    """Q = <beta, gamma> as permutations; V = Q with right multiplication."""
    Q = closure([beta, gamma])
    idx = {q: i for i, q in enumerate(Q)}
    Pb = tuple(idx[pmul(q, beta)] for q in Q)
    Pc = tuple(idx[pmul(q, gamma)] for q in Q)
    return Pb, Pc, len(Q)

def psl2_gens(p):
    """Permutations of P^1(F_p) for x -> x+1 and x -> -1/x (generate PSL(2,p))."""
    pts = list(range(p)) + ['inf']
    ix = {x: i for i, x in enumerate(pts)}
    def img_t(x):
        return 'inf' if x == 'inf' else (x + 1) % p
    def img_s(x):
        if x == 'inf':
            return 0
        if x == 0:
            return 'inf'
        return (-pow(x, p - 2, p)) % p
    return (tuple(ix[img_t(x)] for x in pts), tuple(ix[img_s(x)] for x in pts))

# ---------- percolation upper bound ----------
def fold_closure(tr, n, R):
    inset = [False] * n
    for v in R:
        inset[v] = True
    inc = [[] for _ in range(n)]
    for i, t in enumerate(tr):
        for v in set(t):
            inc[v].append(i)
    q = deque(R)
    while q:
        v = q.popleft()
        for i in inc[v]:
            t = tr[i]; miss = [w for w in set(t) if not inset[w]]
            if len(miss) == 1:
                inset[miss[0]] = True; q.append(miss[0])
    return inset

def greedy_percolation(tr, n, rng, trials=20, want_set=False):
    best, bestR = n, list(range(n))
    for _ in range(trials):
        R = []; inset = [False] * n
        order = list(range(n)); rng.shuffle(order)
        for v in order:
            if not inset[v]:
                R.append(v); inset = fold_closure(tr, n, R)
        if len(R) < best:
            best, bestR = len(R), R
    return (best, bestR) if want_set else best

# ---------- counting Hom(P_V, S) ----------
def count_colorings(tr, n, mul, inv, cap=10**7, seeds=None):
    """#{s in S^V : s[v] = s[vc]*s[vcb]} by DFS + unit propagation."""
    m = len(mul)
    inc = [[] for _ in range(n)]
    for i, t in enumerate(tr):
        for v in set(t):
            inc[v].append(i)
    val = [-1] * n
    # branching order: BFS over the triple hypergraph
    order, seen = [], [False] * n
    for v in (seeds or []):
        seen[v] = True; order.append(v)
    for s0 in range(n):
        if seen[s0]:
            continue
        dq = deque([s0]); seen[s0] = True
        while dq:
            v = dq.popleft(); order.append(v)
            for i in inc[v]:
                for w in tr[i]:
                    if not seen[w]:
                        seen[w] = True; dq.append(w)
    total = 0
    sys.setrecursionlimit(100000)

    def propagate(start, trail):
        q = deque([start])
        while q:
            v = q.popleft()
            for i in inc[v]:
                x, y, z = tr[i]
                vx, vy, vz = val[x], val[y], val[z]
                unk = [w for w in {x, y, z} if val[w] < 0]
                if not unk:
                    if vx != mul[vy][vz]:
                        return False
                    continue
                if len(unk) != 1:
                    continue
                w = unk[0]
                cnt = (x == w) + (y == w) + (z == w)
                if cnt != 1:
                    continue  # repeated unknown: leave to branching
                if w == x:
                    nv = mul[vy][vz]
                elif w == y:
                    nv = mul[vx][inv[vz]]
                else:
                    nv = mul[inv[vy]][vx]
                val[w] = nv; trail.append(w); q.append(w)
        return True

    def dfs(pos):
        nonlocal total
        if total >= cap:
            return
        while pos < n and val[order[pos]] >= 0:
            pos += 1
        if pos == n:
            total += 1
            return
        v = order[pos]
        for g in range(m):
            trail = [v]; val[v] = g
            if propagate(v, trail):
                dfs(pos + 1)
            for w in trail:
                val[w] = -1

    dfs(0)
    return total

# ---------- abelianization ----------
def rank_mod_p(tr, n, p):
    import numpy as np
    A = np.zeros((n, n), dtype=np.int64)
    for i, (x, y, z) in enumerate(tr):
        A[i, x] += 1; A[i, y] -= 1; A[i, z] -= 1
    A %= p
    rk = 0
    for col in range(n):
        nz = np.nonzero(A[rk:, col])[0]
        if len(nz) == 0:
            continue
        piv = rk + nz[0]
        A[[rk, piv]] = A[[piv, rk]]
        A[rk] = (A[rk] * pow(int(A[rk, col]), p - 2, p)) % p
        f = A[:, col].copy(); f[rk] = 0
        A = (A - np.outer(f, A[rk])) % p
        rk += 1
        if rk == n:
            break
    return rk

def log_abs_det(tr, n):
    import numpy as np
    A = np.zeros((n, n))
    for i, (x, y, z) in enumerate(tr):
        A[i, x] += 1; A[i, y] -= 1; A[i, z] -= 1
    sgn, ld = np.linalg.slogdet(A)
    return (float('-inf') if sgn == 0 else ld)

PRIMES = [p for p in range(2, 400) if all(p % q for q in range(2, int(p ** .5) + 1))]

def h1_profile(tr, n):
    """(log|H1| (natural log, -inf if infinite), max_p nullity, witnessing p)."""
    ld = log_abs_det(tr, n)
    best, bp = 0, None
    for p in PRIMES:
        nul = n - rank_mod_p(tr, n, p)
        if nul > best:
            best, bp = nul, p
    return ld, best, bp

# ---------- driver ----------
def report(name, Pb, Pc, rng, groups, Snames):
    n = len(Pb); tr = triples(Pb, Pc)
    r, R = greedy_percolation(tr, n, rng, trials=10, want_set=True)
    ld, nul, p = h1_profile(tr, n)
    out = [f"{name:22s} n={n:4d} r<={r:3d} ({r/n:.3f}n)  log|H1|/n={ld/n:.3f}  maxnull={nul}@p={p}"]
    for k in Snames:
        mul, inv, one = table(groups[k])
        if len(mul) ** r > 3 * 10**6:
            continue
        Z = count_colorings(tr, n, mul, inv, cap=10**6, seeds=R)
        out.append(f"   Z_{k}={Z} (log_|S| Z={math.log(Z)/math.log(len(mul)):.2f})")
    return "".join(out)

def psl_regular_sets(p, rng, how_many):
    t, s = psl2_gens(p)
    Qfull = closure([t, s])
    res, tries = [], 0
    while len(res) < how_many and tries < 2000:
        tries += 1
        beta, gamma = rng.choice(Qfull), rng.choice(Qfull)
        alpha = pmul(pmul(pinv(beta), gamma), pmul(beta, beta))  # b^-1 c b^2
        if len(closure([gamma, alpha])) == len(Qfull):  # K surjects
            res.append(regular_lset(beta, gamma))
    return res

if __name__ == "__main__":
    rng = random.Random(20260919)
    groups = small_groups()
    Sn = ['C2', 'C3', 'S3', 'A4', 'SL23', 'S4', 'A5']
    which = sys.argv[1] if len(sys.argv) > 1 else 'random'
    if which == 'random':
        for n in [16, 24, 32, 48, 64, 96]:
            for rep in range(3):
                Pb, Pc = random_lset(n, rng)
                print(report(f"random#{rep}", Pb, Pc, rng, groups,
                             Sn), flush=True)
    else:
        for p in [5, 7, 11, 13]:
            for (Pb, Pc, q) in psl_regular_sets(p, rng, 3):
                print(report(f"PSL2({p}) regular", Pb, Pc, rng, groups,
                             Sn), flush=True)
