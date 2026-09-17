#!/usr/bin/env python3
"""Checks for dkkms-affine-view-verifiers-any-sigma-sound-at-2c-1, part (T).

(T) Uniform-marginal transfer.  Random small linear outer games over F_p
    (3 vertices, 2-3 edges, affine H_e with onto projections), affine views,
    triples with ARBITRARY bijections sigma (mostly punctured copies of beta_t).
    Brute force:
      * oblivious rejection eps, compatible weight w_comp, E_comp (rejection
        carried by compatible triples);
      * val(V) over all output labelings;
      * Can_comp and all its labelings.
    For D_all (uniform over all Can_comp labelings, always uniform marginals)
    and D_opt (uniform over optimal labelings, marginals tested) check
        val(V) >= w_comp * nu_D - E_comp                      (Item 1a)
    and, when marginals are uniform,
        val(V) >= nu_D - p*eps/(p-1).                         (Item 1b)
    Also counts instances where D_opt has non-uniform marginals and Item 1b
    FAILS (showing the uniformity hypothesis is not vacuous).
Run: python3 check_uniform_gauge_transfer.py [seed] [instances]
"""
import itertools
import random
import sys
from fractions import Fraction as Fr

SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 20260917
NINST = int(sys.argv[2]) if len(sys.argv) > 2 else 400
rng = random.Random(SEED)


def vecs(p, d):
    return list(itertools.product(range(p), repeat=d))


def add(u, v, p):
    return tuple((a + b) % p for a, b in zip(u, v))


def matvec(M, x, p):
    return tuple(sum(a * b for a, b in zip(row, x)) % p for row in M)


def affine_view(p, d, k):
    M = [[rng.randrange(p) for _ in range(d)] for _ in range(k)]
    c = tuple(rng.randrange(p) for _ in range(k))
    return M, c


def apply_view(view, x, p):
    M, c = view
    return add(matvec(M, x, p), c, p)


def random_edge(p, d):
    """Affine subspace H of F_p^d x F_p^d with both projections onto: solution
    set of j random affine equations, rejected until onto."""
    pts = vecs(p, 2 * d)
    while True:
        j = rng.randrange(0, d + 1)
        eqs = [([rng.randrange(p) for _ in range(2 * d)], rng.randrange(p)) for _ in range(j)]
        H = [x for x in pts if all(sum(a * b for a, b in zip(r, x)) % p == b0 for r, b0 in eqs)]
        if not H:
            continue
        if len({x[:d] for x in H}) == p ** d and len({x[d:] for x in H}) == p ** d:
            return [(x[:d], x[d:]) for x in H]


def kernel_key(view, p, d):
    """Linear kernel of the view, as a frozenset."""
    M, _ = view
    z = tuple([0] * len(M))
    return frozenset(x for x in vecs(p, d) if matvec(M, x, p) == z)


def one_instance(p, d, k):
    Z = [0, 1, 2]
    edges = []
    for _ in range(rng.choice([2, 3, 4])):
        a, b = rng.choice([(0, 1), (1, 2), (0, 2), (0, 1)])
        edges.append((a, b, random_edge(p, d)))
    W = []  # (owner, view)
    for z in Z:
        for _ in range(rng.choice([1, 2])):
            W.append((z, affine_view(p, d, k)))
    if len(W) > 5:
        W = W[:5]
    labels = vecs(p, k)
    triples = []  # (edge index, w, w', sigma dict, weight)
    for ei, (a, b, H) in enumerate(edges):
        ws = [i for i, (z, _) in enumerate(W) if z in (a, b)]
        nt = rng.choice([2, 3, 4])
        wts = [rng.randrange(1, 5) for _ in range(nt)]
        tot = sum(wts)
        for t in range(nt):
            w, w2 = rng.choice(ws), rng.choice(ws)
            rel = relation(W, w, w2, a, b, H, p)
            beta = graph_bijection(rel)
            if beta is not None and rng.random() < 0.8:
                sigma = dict(beta)
                # extend beta (defined on I_w) to a bijection of F_p^k, then
                # apply 0-2 random transpositions as punctures
                rest_src = [u for u in labels if u not in sigma]
                rest_dst = [v for v in labels if v not in set(sigma.values())]
                rng.shuffle(rest_dst)
                sigma.update(zip(rest_src, rest_dst))
                for _ in range(rng.choice([0, 1, 1, 2])):
                    u, v = rng.sample(labels, 2)
                    sigma[u], sigma[v] = sigma[v], sigma[u]
            else:
                perm = labels[:]
                rng.shuffle(perm)
                sigma = dict(zip(labels, perm))
            triples.append((ei, w, w2, sigma, Fr(wts[t], tot) / len(edges)))
    return edges, W, triples


def relation(W, w, w2, a, b, H, p):
    rel = []
    for (xa, xb) in H:
        xs = {a: xa, b: xb}
        rel.append((apply_view(W[w][1], xs[W[w][0]], p), apply_view(W[w2][1], xs[W[w2][0]], p)))
    return rel


def graph_bijection(rel):
    s = set(rel)
    left = {u for u, _ in s}
    right = {v for _, v in s}
    if len(s) == len(left) == len(right):
        return dict(s)
    return None


def gf8_control(r=3, alpha=Fr(2, 5)):
    """Puncture family of puncture-triples-defeat-partition-coarsening over
    F_8 = F_2^3: vertices 0, 1; r edges x_1 = lambda_i x_0 (distinct nonzero
    lambda_i = 1, t, t^2); identity views; cross triples (weight 1 - alpha)
    with sigma = lambda_i; same-owner triples (w_z, w_z, (000 100)) of weight
    alpha/2 each.  Can_comp forces the zero label, so its optimal labelings are
    NOT uniform, and Item 1b fails: val = 3/5 < 1 - 2 eps = 4/5."""
    p, d = 2, 3

    def mul_t(x):  # F_2[t]/(t^3 + t + 1)
        return (x[2], (x[0] + x[2]) % 2, x[1])
    lams = [lambda x: x, mul_t, lambda x: mul_t(mul_t(x))][:r]
    edges = [(0, 1, [(x, lam(x)) for x in vecs(p, d)]) for lam in lams]
    ident = ([[1, 0, 0], [0, 1, 0], [0, 0, 1]], (0, 0, 0))
    W = [(0, ident), (1, ident)]
    labels = vecs(p, d)
    pi = {u: u for u in labels}
    pi[(0, 0, 0)], pi[(1, 0, 0)] = (1, 0, 0), (0, 0, 0)
    triples = []
    for ei, lam in enumerate(lams):
        triples.append((ei, 0, 1, {u: lam(u) for u in labels}, (1 - alpha) / r))
        triples.append((ei, 0, 0, dict(pi), alpha / 2 / r))
        triples.append((ei, 1, 1, dict(pi), alpha / 2 / r))
    return edges, W, triples


def analyse(p, d, k, inst=None):
    edges, W, triples = inst if inst is not None else one_instance(p, d, k)
    labels = vecs(p, k)
    eps = Fr(0)
    wcomp = Fr(0)
    Ecomp = Fr(0)
    comp = []  # (weight, w, w2, beta, S_t)
    for (ei, w, w2, sigma, wt) in triples:
        a, b, H = edges[ei]
        rel = relation(W, w, w2, a, b, H, p)
        rej = Fr(sum(1 for u, v in rel if sigma[u] != v), len(rel))
        eps += wt * rej
        beta = graph_bijection(rel)
        if beta is not None:
            wcomp += wt
            Ecomp += wt * rej
            S = {u for u in beta if sigma[u] != beta[u]}
            if rej != Fr(len(S), len(beta)):
                return "acc formula mismatch"
            comp.append((wt, w, w2, beta, S))
    # val(V)
    best = Fr(0)
    for F in itertools.product(labels, repeat=len(W)):
        acc = sum((wt for (ei, w, w2, sigma, wt) in triples if sigma[F[w]] == F[w2]), Fr(0))
        best = max(best, acc)
    # Can_comp vertices: (owner, kernel); label = coset representative
    dom = vecs(p, d)
    cverts = {}
    for i, (z, view) in enumerate(W):
        key = (z, kernel_key(view, p, d))
        if key not in cverts:
            K = key[1]
            reps = sorted({min(add(x, y, p) for y in K) for x in dom})
            cverts[key] = reps
    keys = sorted(cverts, key=lambda t: (t[0], sorted(t[1])))
    vidx = {i: keys.index((z, kernel_key(v, p, d))) for i, (z, v) in enumerate(W)}
    labs = []
    for X in itertools.product(*[cverts[kk] for kk in keys]):
        F = [apply_view(W[i][1], X[vidx[i]], p) for i in range(len(W))]
        sat = sum((wt for (wt, w, w2, beta, S) in comp if beta[F[w]] == F[w2]), Fr(0))
        labs.append((X, sat))
    if wcomp == 0:
        return None
    vals = [s / wcomp for _, s in labs]
    nu_all = sum(vals, Fr(0)) / len(vals)
    nu_max = max(vals)
    opt = [X for (X, s) in labs if s / wcomp == nu_max]
    uniform = True
    for j, kk in enumerate(keys):
        cnt = {}
        for X in opt:
            cnt[X[j]] = cnt.get(X[j], 0) + 1
        if len(cnt) != len(cverts[kk]) or len(set(cnt.values())) != 1:
            uniform = False
    bound_all_a = wcomp * nu_all - Ecomp
    bound_all_b = nu_all - Fr(p, p - 1) * eps
    bound_opt_a = wcomp * nu_max - Ecomp
    bound_opt_b = nu_max - Fr(p, p - 1) * eps
    return dict(val=best, eps=eps, uniform=uniform, nu_max=nu_max,
                ok_all=(best >= bound_all_a and best >= bound_all_b),
                ok_opt=(not uniform) or (best >= bound_opt_a and best >= bound_opt_b),
                fail_nonuniform=(not uniform) and best < bound_opt_b,
                strict=(uniform and nu_max == 1 and best < 1 and eps > 0))


def main():
    fails = 0
    stats = dict(instances=0, uniform_opt=0, uniform_value1=0, strict=0,
                 nonuniform_bound_fails=0)
    for it in range(NINST):
        p, d, k = rng.choice([(2, 2, 1), (2, 2, 2), (3, 1, 1), (3, 2, 1)])
        r = analyse(p, d, k)
        if r is None:
            continue
        if isinstance(r, str):
            print("FAIL", r)
            fails += 1
            continue
        stats["instances"] += 1
        if not r["ok_all"]:
            print("FAIL item 1 with D_all", r)
            fails += 1
        if not r["ok_opt"]:
            print("FAIL item 1 with uniform D_opt", r)
            fails += 1
        stats["uniform_opt"] += r["uniform"]
        stats["uniform_value1"] += r["uniform"] and r["nu_max"] == 1
        stats["strict"] += r["strict"]
        stats["nonuniform_bound_fails"] += r["fail_nonuniform"]
    r = analyse(2, 3, 3, gf8_control())
    print("control (GF(8) puncture family):", {x: str(y) for x, y in r.items()})
    if r["uniform"] or not r["fail_nonuniform"] or not r["ok_all"]:
        print("FAIL control: expected non-uniform optimal marginals and a failing Item 1b")
        fails += 1
    print("seed", SEED, "stats", stats)
    print("failures:", fails)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
