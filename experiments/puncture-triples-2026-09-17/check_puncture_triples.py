#!/usr/bin/env python3
"""Checks for puncture-triples-defeat-partition-coarsening and
affine-view-verifiers-collapse-up-to-puncture-cost (swarm-0917-w4-pull-ugc-1).

 (CX)  Counterexample family.  Outer game: two vertices a, b, A_a = A_b = F_{p^l}
       viewed as F_p^l; r edges H_i = {x_b = lambda_i x_a} for distinct nonzero
       lambda_i.  Verifier: identity views (degree 1), cross triples
       (w_a, w_b, x -> lambda_i x) with weight 1-alpha, and same-owner puncture
       triples (w_z, w_z, pi) with pi the transposition (0 1), weight alpha/2 on each
       owner.  Brute force: val(V) = max(1-alpha, (1-alpha)/r + alpha), val(Can_part)
       = 1, val(V_0) = 1 for the verifier with pi replaced by id, oblivious
       rejection 2 alpha p^-l, pointwise rejection alpha at h = 0.
 (RIG) Rigidity for affine views and arbitrary bijections sigma: acceptance of honest
       labels above 1/p on H_e forces the image of H_e under the pair of views to
       be the graph of a bijection (compatible triple).
 (TR)  Value transfer on random small affine-view verifiers with arbitrary sigma:
       val(V) >= w_comp * val(Can_comp) - kappa, and kappa_e <= r_e * epsptw_e.
Run: nice -n 10 timeout 1800 python3 check_puncture_triples.py [seed]
"""
import itertools, random, sys
from fractions import Fraction as Fr

SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 20260917
random.seed(SEED)
fails = 0


def fail(*a):
    global fails
    fails += 1
    print("FAIL", *a)


# ---------------------------------------------------------------- field F_{p^l}
def polymulmod(u, v, mod, p):
    l = len(mod) - 1
    prod = [0] * (2 * l - 1)
    for i, ui in enumerate(u):
        if ui:
            for j, vj in enumerate(v):
                prod[i + j] = (prod[i + j] + ui * vj) % p
    for deg in range(len(prod) - 1, l - 1, -1):
        c = prod[deg]
        if c:
            for j in range(l + 1):  # mod monic: x^l = -sum mod[j] x^j
                prod[deg - l + j] = (prod[deg - l + j] - c * mod[j]) % p
    return tuple(prod[:l])


def irreducible(p, l):
    for tail in itertools.product(range(p), repeat=l):
        mod = list(tail) + [1]
        if tail[0] == 0:
            continue
        # irreducible iff no root-free factorization: test x^(p^l) = x and gcd cond.
        # small sizes: brute force that the multiplicative structure is a field
        elems = list(itertools.product(range(p), repeat=l))
        zero = tuple([0] * l)
        ok = True
        for u in elems:
            if u == zero:
                continue
            if not any(polymulmod(u, v, mod, p) == tuple([1] + [0] * (l - 1)) for v in elems):
                ok = False
                break
        if ok:
            return mod
    raise ValueError


def cx(p, l, r, alpha):
    mod = irreducible(p, l)
    elems = list(itertools.product(range(p), repeat=l))
    zero = tuple([0] * l)
    one = tuple([1] + [0] * (l - 1))
    lams = [u for u in elems if u != zero][:r]
    mul = {lam: {x: polymulmod(lam, x, mod, p) for x in elems} for lam in lams}
    P = {zero, one}

    def val(Fa, Fb, punct=True):
        cross = sum(1 for lam in lams if mul[lam][Fa] == Fb)
        v = (1 - alpha) * Fr(cross, r)
        if punct:
            v += alpha / 2 * ((Fa not in P) + (Fb not in P))
        else:
            v += alpha
        return v

    valV = max(val(Fa, Fb) for Fa in elems for Fb in elems)
    valV0 = max(val(Fa, Fb, False) for Fa in elems for Fb in elems)
    # Can_part: exact triples are the cross triples only (identity views: singleton
    # partitions, beta = lambda_i); its value is the best fraction of cross edges.
    valCan = max(Fr(sum(1 for lam in lams if mul[lam][Fa] == Fb), r)
                 for Fa in elems for Fb in elems)
    predicted = max(1 - alpha, (1 - alpha) / r + alpha)
    if valV != predicted:
        fail("CX valV", p, l, r, alpha, valV, predicted)
    if valCan != 1 or valV0 != 1:
        fail("CX can/V0", p, l, r, valCan, valV0)
    # completeness: uniform h in H_i has h_a uniform; puncture rejects iff h_a in P
    obl = alpha / 2 * Fr(2, p ** l) + alpha / 2 * Fr(2, p ** l)
    # b-side: h_b = lambda_i h_a is uniform too, same count
    ptw = max(alpha / 2 * ((x in P) + (mul[lam][x] in P)) for lam in lams for x in elems)
    if ptw != alpha:
        fail("CX pointwise", ptw)
    return valV, valCan, obl, ptw


print("(CX) p l r alpha  val(V) val(Can_part) oblivious-eps pointwise-rej")
for p, l, r in [(2, 2, 2), (2, 3, 2), (2, 3, 3), (2, 4, 2), (2, 4, 3), (2, 5, 4), (3, 2, 2), (3, 2, 3), (5, 2, 3)]:
    alpha = Fr(r - 1, 2 * r - 1)
    out = cx(p, l, r, alpha)
    print("    ", p, l, r, alpha, *out)


# ---------------------------------------------------------------- (RIG), (TR)
def vecs(p, n):
    return list(itertools.product(range(p), repeat=n))


def affmap(M, c, x, p):
    return tuple((sum(M[i][j] * x[j] for j in range(len(x))) + c[i]) % p for i in range(len(M)))


def rand_affine_subspace(p, m):
    """Random affine subspace of F_p^m x F_p^m with both projections onto."""
    while True:
        dim = random.randint(m, 2 * m)
        gens = [tuple(random.randrange(p) for _ in range(2 * m)) for _ in range(dim)]
        off = tuple(random.randrange(p) for _ in range(2 * m))
        span = set()
        for coef in itertools.product(range(p), repeat=dim):
            span.add(tuple((off[i] + sum(cf * g[i] for cf, g in zip(coef, gens))) % p
                           for i in range(2 * m)))
        H = sorted(span)
        if len({h[:m] for h in H}) == p ** m and len({h[m:] for h in H}) == p ** m:
            return H


def instance(p, m, k):
    H = rand_affine_subspace(p, m)
    views = []  # (owner, M, c)
    for owner in (0, 1):
        for _ in range(2):
            M = [[random.randrange(p) for _ in range(m)] for _ in range(k)]
            c = [random.randrange(p) for _ in range(k)]
            views.append((owner, M, c))
    return H, views


def comp_data(p, m, k, H, views, t):
    w, w2, sigma = t
    ow, Mw, cw = views[w]
    ow2, Mw2, cw2 = views[w2]
    pairs = [(affmap(Mw, cw, h[m:] if ow else h[:m], p), affmap(Mw2, cw2, h[m:] if ow2 else h[:m], p)) for h in H]
    acc = Fr(sum(1 for u, v in pairs if sigma[u] == v), len(pairs))
    U = set(pairs)
    f, g = {}, {}
    compatible = True
    for u, v in U:
        if f.setdefault(u, v) != v or g.setdefault(v, u) != u:
            compatible = False
    return pairs, acc, compatible, f


def check_instance(p, m, k):
    global rig, tr
    H, views = instance(p, m, k)
    kv = vecs(p, k)
    ntr = random.randint(2, 5)
    triples = []
    for _ in range(ntr):
        w, w2 = random.randrange(4), random.randrange(4)
        perm = kv[:]
        random.shuffle(perm)
        sigma = dict(zip(kv, perm))
        t0 = (w, w2, sigma)
        _, _, comp, f = comp_data(p, m, k, H, views, t0)
        if comp and random.random() < 0.7:
            # sigma = beta on the image, random elsewhere, then a random transposition
            rest_src = [u for u in kv if u not in f]
            rest_dst = [v for v in kv if v not in f.values()]
            random.shuffle(rest_dst)
            sigma = dict(f)
            sigma.update(zip(rest_src, rest_dst))
            if random.random() < 0.6:
                a, b = random.sample(kv, 2)
                sigma[a], sigma[b] = sigma[b], sigma[a]
        triples.append((w, w2, sigma, Fr(random.randint(1, 4))))
    tot = sum(t[3] for t in triples)
    triples = [(w, w2, s, wt / tot) for (w, w2, s, wt) in triples]
    data = []
    for (w, w2, s, wt) in triples:
        pairs, acc, comp, f = comp_data(p, m, k, H, views, (w, w2, s))
        rig += 1
        if acc > Fr(1, p) and not comp:
            fail("RIG", acc)
        data.append((w, w2, s, wt, pairs, comp, f))
    images = [sorted({affmap(M, c, x, p) for x in vecs(p, m)}) for (_, M, c) in views]
    # val(V) by brute force over F(w) in F_p^k
    best_V = 0
    for F in itertools.product(kv, repeat=4):
        v = sum(wt for (w, w2, s, wt, *_r) in data if s[F[w]] == F[w2])
        best_V = max(best_V, v)
    # Can_comp: labels for views restricted to images, constant on shared partitions
    part = []
    for (o, M, c) in views:
        cls = {}
        for x in vecs(p, m):
            cls.setdefault(affmap(M, c, x, p), []).append(x)
        part.append((o, frozenset(frozenset(v) for v in cls.values())))
    canon = {}
    for i, key in enumerate(part):
        canon.setdefault(key, []).append(i)
    groups = list(canon.values())
    wcomp = sum(d[3] for d in data if d[5])
    best_can = Fr(0)
    best_cost = None
    kappa = Fr(0)
    for F in itertools.product(*images):
        cost = sum(d[3] for d in data if d[5] and d[2][F[d[0]]] != d[6][F[d[0]]])
        kappa = max(kappa, cost)
    for choice in itertools.product(*[list(part[g[0]][1]) for g in groups]):
        # pick label of each view from the chosen class
        F = [None] * 4
        for g, cls in zip(groups, choice):
            x = next(iter(cls))
            for i in g:
                F[i] = affmap(views[i][1], views[i][2], x, p)
        v = sum(d[3] for d in data if d[5] and d[6][F[d[0]]] == F[d[1]])
        if v > best_can:
            best_can = v
    tr += 1
    stats['kappa>0'] += kappa > 0
    stats['incompatible'] += any(not d[5] for d in data)
    val_can = best_can / wcomp if wcomp else Fr(1)
    stats['V<wcomp*Can'] += best_V < wcomp * val_can
    if best_V < wcomp * val_can - kappa:
        fail("TR transfer", best_V, wcomp, val_can, kappa)
    # pointwise completeness and r
    ptw = max(sum(d[3] for d in data if d[2][d[4][j][0]] != d[4][j][1]) for j in range(len(H)))
    r = len({d[0] for d in data if d[5] and any(d[2][u] != d[6][u] for u in d[6])})
    if kappa > r * ptw:
        fail("TR kappa", kappa, r, ptw)


rig = tr = 0
stats = {'kappa>0': 0, 'incompatible': 0, 'V<wcomp*Can': 0}
for p, m, k, n in [(2, 3, 2, 250), (3, 2, 1, 250), (2, 2, 2, 250)]:
    for _ in range(n):
        check_instance(p, m, k)
print("(RIG) triples checked:", rig, " (TR) instances checked:", tr, stats)
print("seed", SEED, "failures", fails)
sys.exit(1 if fails else 0)
