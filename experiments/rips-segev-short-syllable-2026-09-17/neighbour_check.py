#!/usr/bin/env python3
"""Calibration of the neighbour lemma (Lemma 2 of
rips-segev-short-syllable-two-layer-elements-are-regular-proof) in finite groups.

For beta = u(x) + w(x) y with u, w in k[<x>] linearly independent and of joint span <= d,
and any alpha != 0 with alpha beta = 0, the lemma says that V = supp(alpha u) ∪ supp(alpha w)
satisfies
  (Y) every p in V has p y or p y^{-1} in V;
  (X) every p in V has p x^n in V for some 1 <= |n| <= d,
provided x has order >= 2d+2 (so the windows [n-d, n+d] do not wrap).  The proof is local, so it
applies verbatim in finite groups, where zero divisors are plentiful.  The script computes full
left kernels of right multiplication by beta over GF(p) and checks (X), (Y) on every basis vector
and on random kernel combinations.  It also closes the alternating walk of Lemma 3 and checks that
the word it reads is trivial (a consistency check of the bookkeeping), and that its x-exponents
lie in [-d, d] minus {0} and its y-exponents are ±1.

Both roles are tested: (x, y) = (a, b) and (x, y) = (b, a).

Usage: python3 neighbour_check.py [seed]
"""
import random
import sys


def pmul(p, q):  # apply p then q (right action): (p*q)[i] = q[p[i]]
    return tuple(q[i] for i in p)


def pinv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def closure(gens):
    n = len(gens[0])
    e = tuple(range(n))
    seen = {e}
    frontier = [e]
    while frontier:
        nxt = []
        for g in frontier:
            for s in gens:
                h = pmul(g, s)
                if h not in seen:
                    seen.add(h)
                    nxt.append(h)
        frontier = nxt
    return sorted(seen)


def order(g):
    e = tuple(range(len(g)))
    k, h = 1, g
    while h != e:
        h = pmul(h, g)
        k += 1
    return k


def left_kernel(G, idx, beta, P):
    """Basis of {alpha : alpha beta = 0} over GF(P). beta: dict element -> coeff."""
    N = len(G)
    # alpha beta (g) = sum_x alpha(x) beta(s) over x s = g.  Row x of M: M[x][idx[x s]] += beta(s).
    rows = []
    for x in G:
        r = [0] * N
        for s, c in beta.items():
            j = idx[pmul(x, s)]
            r[j] = (r[j] + c) % P
        rows.append(r)
    # left kernel of M = kernel of M^T: solve sum_x alpha_x rows[x] = 0.
    # Gaussian elimination on augmented [M | I].
    A = [rows[i][:] + [1 if k == i else 0 for k in range(N)] for i in range(N)]
    piv_row = 0
    for col in range(N):
        pr = None
        for r in range(piv_row, N):
            if A[r][col] % P:
                pr = r
                break
        if pr is None:
            continue
        A[piv_row], A[pr] = A[pr], A[piv_row]
        inv = pow(A[piv_row][col], P - 2, P)
        A[piv_row] = [(v * inv) % P for v in A[piv_row]]
        for r in range(N):
            if r != piv_row and A[r][col] % P:
                f = A[r][col]
                A[r] = [(vr - f * vp) % P for vr, vp in zip(A[r], A[piv_row])]
        piv_row += 1
    return [A[r][N:] for r in range(piv_row, N)]


def rmul(G, idx, alpha, elt_coeffs, P):
    out = {}
    for i, c in enumerate(alpha):
        if c:
            for s, d in elt_coeffs.items():
                g = pmul(G[i], s)
                out[g] = (out.get(g, 0) + c * d) % P
    return {g: c for g, c in out.items() if c}


def check(G, idx, x, y, alpha, u, w, d, P):
    """u, w: lists of coefficients of x^0..x^d. Returns (ok, walk_ok)."""
    xp = [tuple(range(len(x)))]
    for _ in range(d):
        xp.append(pmul(xp[-1], x))
    ue = {}
    we = {}
    for i in range(d + 1):
        if u[i]:
            ue[xp[i]] = (ue.get(xp[i], 0) + u[i]) % P
        if w[i]:
            we[xp[i]] = (we.get(xp[i], 0) + w[i]) % P
    V = set(rmul(G, idx, alpha, ue, P)) | set(rmul(G, idx, alpha, we, P))
    yi = pinv(y)
    xi = pinv(x)
    xpow = {0: tuple(range(len(x)))}
    for n in range(1, d + 1):
        xpow[n] = pmul(xpow[n - 1], x)
        xpow[-n] = pmul(xpow[-(n - 1)], xi)
    ok = True
    ystep, xstep = {}, {}
    for p in V:
        if pmul(p, y) in V:
            ystep[p] = 1
        elif pmul(p, yi) in V:
            ystep[p] = -1
        else:
            ok = False
        for n in [k for m in range(1, d + 1) for k in (m, -m)]:
            if pmul(p, xpow[n]) in V:
                xstep[p] = n
                break
        else:
            ok = False
    if not V:
        return ok, None  # alpha u = alpha w = 0: impossible when x has infinite order
    if not ok:
        return ok, False
    # alternating walk: x-step then y-step, until a point repeats
    p = next(iter(V))
    seen = {}
    word = []
    while p not in seen:
        seen[p] = len(word)
        n = xstep[p]
        q = pmul(p, xpow[n])
        e = ystep[q]
        word.append((n, e))
        p = pmul(q, y if e == 1 else yi)
    cyc = word[seen[p]:]
    g = tuple(range(len(x)))
    for n, e in cyc:
        g = pmul(pmul(g, xpow[n]), y if e == 1 else yi)
    walk_ok = (g == tuple(range(len(x)))) and all(1 <= abs(n) <= d and abs(e) == 1 for n, e in cyc)
    return ok, walk_ok


def random_perm(n, rng):
    p = list(range(n))
    rng.shuffle(p)
    return tuple(p)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    stats = dict(groups=0, betas=0, betas_with_kernel=0, vectors=0, lemma_fail=0, walk_fail=0, empty_V=0)
    tried = 0
    while stats["groups"] < 40 and tried < 4000:
        tried += 1
        n = rng.choice([4, 5, 6])
        a, b = random_perm(n, rng), random_perm(n, rng)
        G = closure([a, b])
        if len(G) > 130 or len(G) < 8:
            continue
        idx = {g: i for i, g in enumerate(G)}
        for (x, y) in [(a, b), (b, a)]:
            ox = order(x)
            for d in (1, 2):
                if ox < 2 * d + 2:
                    continue
                stats["groups"] += 1
                for P in (2, 3, 5):
                    for _ in range(12):
                        u = [rng.randrange(P) for _ in range(d + 1)]
                        w = [rng.randrange(P) for _ in range(d + 1)]
                        # linear independence of u, w
                        indep = any((u[i] * w[j] - u[j] * w[i]) % P for i in range(d + 1) for j in range(d + 1))
                        if not indep:
                            continue
                        xp = [tuple(range(n))]
                        for _ in range(d):
                            xp.append(pmul(xp[-1], x))
                        beta = {}
                        for i in range(d + 1):
                            for g, c in ((xp[i], u[i]), (pmul(xp[i], y), w[i])):
                                if c:
                                    beta[g] = (beta.get(g, 0) + c) % P
                        beta = {g: c for g, c in beta.items() if c}
                        stats["betas"] += 1
                        K = left_kernel(G, idx, beta, P)
                        if not K:
                            continue
                        stats["betas_with_kernel"] += 1
                        vecs = list(K)
                        for _ in range(4):
                            v = [0] * len(G)
                            for kv in K:
                                c = rng.randrange(P)
                                v = [(vi + c * ki) % P for vi, ki in zip(v, kv)]
                            if any(v):
                                vecs.append(v)
                        for v in vecs:
                            stats["vectors"] += 1
                            ok, wok = check(G, idx, x, y, v, u, w, d, P)
                            if wok is None:
                                stats["empty_V"] += 1
                            elif not ok:
                                stats["lemma_fail"] += 1
                            elif not wok:
                                stats["walk_fail"] += 1
    print("seed", seed, stats)


if __name__ == "__main__":
    main()
