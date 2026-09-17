#!/usr/bin/env python3
"""Randomized checks for low-degree-view-unique-verifiers-collapse (swarm-0917-w2-ugc-decomp).

 (DZ)  Density lemma: a nonzero function F_p^m -> F_p of reduced degree <= D is
       nonzero on at least a p^(-D) fraction of points (p = 2, 3; exhaustive over
       random reduced polynomials), and at p = 2 the product of D independent
       linear forms attains 2^(-D).
 (R)   Rigidity: on composed instances over F_2 with polynomial views of degree
       <= d and arbitrary bijections sigma, every non-exact triple rejects at least
       a 2^(-D_t) fraction of H_e, D_t = degree of sigma o rho_w - rho_w' on H_e,
       and w_ex >= 1 - (1 - c) 2^(D_max).
 (P)   Partition coarsening: on exact cross triples the induced map between view
       classes is a well-defined bijection, and on 2-to-2 edges both views are
       invariant under their branch translations.
 (COL) Brute force: val(V(Phi)) >= w_ex * val(Can_part), and for a random outer
       labeling x, val_x(Can_part) >= (w_ex - eta)/w_ex.
Single-threaded. Run: nice -n 10 timeout 1200 python3 check_low_degree_collapse.py [seed]
"""
import itertools, random, sys

SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 20260917
random.seed(SEED)
fails = 0

def fail(*a):
    global fails
    fails += 1
    print("FAIL", *a)

# ---------------------------------------------------------------- (DZ)
def points(p, m):
    return list(itertools.product(range(p), repeat=m))

def monomials(p, m, D):
    return [e for e in itertools.product(range(p), repeat=m) if sum(e) <= D]

def evalpoly(coeffs, mons, x, p):
    s = 0
    for cf, e in zip(coeffs, mons):
        if cf:
            t = cf
            for xi, ei in zip(x, e):
                t = (t * pow(xi, ei, p)) % p
            s = (s + t) % p
    return s

dz = 0
for p, m in [(2, 5), (3, 3)]:
    pts = points(p, m)
    for trial in range(400):
        D = random.randrange(0, (p - 1) * m + 1)
        mons = monomials(p, m, D)
        sparsity = random.choice([0.15, 0.5, 1.0])
        coeffs = [random.randrange(p) if random.random() < sparsity else 0 for _ in mons]
        vals = [evalpoly(coeffs, mons, x, p) for x in pts]
        nz = sum(v != 0 for v in vals)
        if nz == 0:
            continue
        dz += 1
        if nz * p ** D < len(pts):
            fail("DZ", p, m, D, nz)
# tightness at p = 2: x_1 x_2 ... x_D on F_2^5
for D in range(0, 6):
    nz = sum(all(x[i] for i in range(D)) for x in points(2, 5))
    if nz * 2 ** D != 32:
        fail("DZ tight", D, nz)
print("DZ checked", dz, "polynomials; fails =", fails)

# ---------------------------------------------------------------- helpers over F_2
def bits(v, n):
    return [(v >> t) & 1 for t in range(n)]

def mat_apply(M, v):
    return sum(((bin(r & v).count("1") & 1) << t) for t, r in enumerate(M))

def rank(vs):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)

def rand_invertible(n):
    while True:
        M = [random.randrange(1 << n) for _ in range(n)]
        if rank(M) == n:
            return M

def solve(M, n, target):
    return [x for x in range(1 << n) if mat_apply(M, x) == target][0]

def rand_poly_map(l, k, d):
    """random map F_2^l -> F_2^k whose coordinates have ANF degree <= d, as a table"""
    mons = [s for s in range(1 << l) if bin(s).count("1") <= d]
    coords = []
    for _ in range(k):
        cf = [s for s in mons if random.random() < 0.5]
        coords.append([sum(1 for s in cf if (x & s) == s) & 1 for x in range(1 << l)])
    return [sum(coords[j][x] << j for j in range(k)) for x in range(1 << l)]

def anf_degree(table, m):
    """degree of f: F_2^m -> F_2 given as a list of 2^m bits (Moebius transform)"""
    a = list(table)
    for i in range(m):
        for x in range(1 << m):
            if x >> i & 1:
                a[x] ^= a[x ^ (1 << i)]
    return max((bin(x).count("1") for x in range(1 << m) if a[x]), default=-1)

def affine_param(H):
    """H: list of int points of an affine subspace (h encoded as xa | xb << l).
    Returns list param[u] = h for u in F_2^m."""
    base = H[0]
    gens = []
    for h in H:
        v = h ^ base
        r = v
        for g in gens:
            r = min(r, r ^ g)
        if r:
            gens.append(v if False else r)
    # recompute a basis spanning H - base with original vectors
    basis = []
    for h in H:
        v = h ^ base
        if rank(basis + [v]) > len(basis):
            basis.append(v)
    m = len(basis)
    param = []
    for u in range(1 << m):
        v = base
        for i in range(m):
            if u >> i & 1:
                v ^= basis[i]
        param.append(v)
    assert sorted(param) == sorted(H)
    return param, m

# ---------------------------------------------------------------- composed instances
l, k = 3, 2
MASK = (1 << l) - 1
stats = {"inst": 0, "triples": 0, "exact": 0, "exact_cross": 0, "nonexact_high": 0,
         "wex_pos": 0, "tight": 0}

def brute_value(nverts, alphs, edges):
    best = 0.0
    for lab in itertools.product(*[range(a) for a in alphs]):
        v = sum(wt for (i, j, mp, wt) in edges if mp.get(lab[i]) == lab[j])
        best = max(best, v)
    return best

for trial in range(3000):
    Z = 3
    d = random.choice([1, 2, 3])
    outer = []
    for (za, zb) in [(0, 1), (1, 2), (0, 2)]:
        T, Tp = rand_invertible(l), rand_invertible(l)
        bb = random.randrange(1 << l)
        c = random.randrange(1, 1 << l) if random.random() < 0.7 else 0  # 2-to-2 or unique
        H = [xa | (xb << l) for xa in range(1 << l) for xb in range(1 << l)
             if (mat_apply(T, xa) ^ mat_apply(Tp, xb) ^ bb) in (0, c)]
        outer.append((za, zb, H, T, Tp, bb, c))
    # output vertices: views of degree <= d, plus planted exact pairs
    W = []  # (owner, table)
    for z in range(Z):
        W.append((z, rand_poly_map(l, k, d)))
    triples = []  # (w, w', sigma, edge index)
    for ei, (za, zb, H, T, Tp, bb, c) in enumerate(outer):
        # random triples
        cand = [w for w in range(len(W)) if W[w][0] in (za, zb)]
        for _ in range(2):
            w, wp = random.choice(cand), random.choice(cand)
            sig = list(range(1 << k)); random.shuffle(sig)
            triples.append((w, wp, sig, ei))
        # planted exact cross triple: rho_b = P o M with M killing T'^-1 c
        if random.random() < 0.8:
            kill = solve(Tp, l, c) if c else 0
            while True:
                M = [random.randrange(1 << l) for _ in range(2)]
                if all(bin(r & kill).count("1") % 2 == 0 for r in M):
                    break
            P = rand_poly_map(2, k, d)
            rb = [P[mat_apply(M, x)] for x in range(1 << l)]
            sig = list(range(1 << k)); random.shuffle(sig)
            inv = [sig.index(y) for y in range(1 << k)]
            ra = [None] * (1 << l)
            for xa in range(1 << l):
                xb = solve(Tp, l, bb ^ mat_apply(T, xa))
                ra[xa] = inv[rb[xb]]
            W.append((za, ra)); W.append((zb, rb))
            triples.append((len(W) - 2, len(W) - 1, sig, ei))
            if random.random() < 0.5:  # planted intra-owner exact triple
                sig2 = list(range(1 << k)); random.shuffle(sig2)
                W.append((za, [sig2[y] for y in ra]))
                triples.append((len(W) - 3, len(W) - 1, sig2, ei))
    if len(W) > 7:
        continue
    wt = {}
    for t in triples:
        n_e = sum(1 for s in triples if s[3] == t[3])
        wt[id(t)] = 1.0 / (len(outer) * n_e)
    def coord(w, h, ei):
        za, zb = outer[ei][0], outer[ei][1]
        return (h & MASK) if W[w][0] == za else (h >> l)
    c_val, w_ex, Dmax = 0.0, 0.0, 0
    exact = []
    for t in triples:
        w, wp, sig, ei = t
        H = outer[ei][2]
        param, m = affine_param(H)
        Q = [sig[W[w][1][coord(w, h, ei)]] ^ W[wp][1][coord(wp, h, ei)] for h in param]
        dens = sum(q == 0 for q in Q) / len(Q)
        Dt = max(anf_degree([(q >> j) & 1 for q in Q], m) for j in range(k))
        stats["triples"] += 1
        c_val += wt[id(t)] * dens
        if dens == 1.0:
            w_ex += wt[id(t)]
            exact.append(t)
        else:
            Dmax = max(Dmax, Dt)
            if (1 - dens) * 2 ** Dt < 1 - 1e-12:
                fail("R reject density", dens, Dt)
            if dens > 0.5:
                stats["nonexact_high"] += 1
    if w_ex < 1 - (1 - c_val) * 2 ** Dmax - 1e-12:
        fail("R weight", w_ex, c_val, Dmax)
    stats["exact"] += len(exact)
    stats["wex_pos"] += w_ex > 0
    # partition coarsening
    part = {}
    def classes(w):
        tab = W[w][1]
        return tuple(tab)  # class of x = value tab[x]; partition = kernel of tab
    def canid(w):
        tab = W[w][1]
        vals = sorted(set(tab))
        canon = tuple(vals.index(v) for v in tab)  # partition, forgetting the injection
        # relabel canonically by first occurrence
        first = {}
        canon = tuple(first.setdefault(v, len(first)) for v in tab)
        return part.setdefault((W[w][0], canon), len(part))
    def cls(w, x):
        tab = W[w][1]
        first = {}
        canon = [first.setdefault(v, len(first)) for v in tab]
        return canon[x]
    can_edges = []
    for t in exact:
        w, wp, sig, ei = t
        za, zb, H, T, Tp, bb, c = outer[ei]
        beta = {}
        for h in H:
            s_, d_ = cls(w, coord(w, h, ei)), cls(wp, coord(wp, h, ei))
            if beta.get(s_, d_) != d_:
                fail("P beta not a function")
            beta[s_] = d_
        if len(set(beta.values())) != len(beta):
            fail("P beta not injective")
        if len(beta) != len(set(W[w][1])) or len(set(beta.values())) != len(set(W[wp][1])):
            fail("P beta not onto classes")
        if W[w][0] != W[wp][0]:
            stats["exact_cross"] += 1
            if c:
                wa = w if W[w][0] == za else wp
                wb = wp if wa == w else w
                ta, tb = solve(T, l, c), solve(Tp, l, c)
                if any(W[wa][1][x] != W[wa][1][x ^ ta] for x in range(1 << l)):
                    fail("P branch blindness a")
                if any(W[wb][1][x] != W[wb][1][x ^ tb] for x in range(1 << l)):
                    fail("P branch blindness b")
        can_edges.append((canid(w), canid(wp), beta, wt[id(t)]))
    # brute force
    gedges = [(t[0], t[1], {y: t[2][y] for y in range(1 << k)}, wt[id(t)]) for t in triples]
    vG = brute_value(len(W), [1 << k] * len(W), gedges)
    if exact:
        keys = sorted(part, key=part.get)
        alphs = [len(set(key[1])) for key in keys]
        vC = brute_value(len(keys), alphs, can_edges) / w_ex
        if vG < w_ex * vC - 1e-12:
            fail("COL", vG, w_ex, vC)
        stats["tight"] += abs(vG - w_ex * vC) < 1e-12
        # completeness transfer for a random outer labeling
        x = [random.randrange(1 << l) for _ in range(Z)]
        sat = [ (x[outer[ei][0]] | (x[outer[ei][1]] << l)) in set(outer[ei][2]) for ei in range(len(outer))]
        eta = sum(1.0 / len(outer) for ei in range(len(outer)) if not sat[ei])
        lab = {}
        for (z, canon), i in part.items():
            lab[i] = canon[x[z]]
        vx = sum(wgt for (i, j, beta, wgt) in can_edges if beta.get(lab[i]) == lab[j]) / w_ex
        if vx < (w_ex - eta) / w_ex - 1e-12:
            fail("COL completeness", vx, w_ex, eta)
    stats["inst"] += 1

print("composed instances:", stats, "total fails =", fails, "seed", SEED)
sys.exit(1 if fails else 0)
