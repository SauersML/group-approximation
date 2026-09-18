#!/usr/bin/env python3
"""Checks for akkstv-rounding-holds-on-all-loop-free-constraint-graphs.

Degree blow-up B(U): vertex u of a loop-free weighted unique game U becomes
m_u = d_u copies (d_u = weighted degree, integer weights); copies (u,i),(v,j)
of an edge uv get weight w_uv/(d_u d_v) and the permutation pi_uv.

Part A  (spectrum)   normalized-Laplacian spectrum of B(U) equals spec(U) plus
                     eigenvalue 1 with multiplicity sum(m_u) - n, so
                     lambda_2(B(U)) = min(lambda_2(U), 1); every copy has
                     weighted degree 1.
Part B  (value)      opt(B(U)) = opt(U) by brute force on small games.
Part C  (biregular)  integer-weight version for biregular bipartite graphs:
                     A-copies d_A/g, B-copies d_B/g (g = gcd), multiplicity 1 per copy
                     pair; regular of degree d_A d_B / g; same checks.
Part D  (Grassmann)  second singular value of the bipartite containment host
                     V_(l-1) u V_l of subspaces of F_q^n (q = 2, 3), against
                     sigma_2^2 = 1 - [n]/([l][n-l+1]).
Exits 0 iff every check passes.
"""
import itertools
import random
import sys
from fractions import Fraction

import numpy as np

FAIL = []


def check(ok, msg):
    print(("PASS " if ok else "FAIL ") + msg)
    if not ok:
        FAIL.append(msg)


def laplacian_spectrum(W):
    d = W.sum(axis=1)
    Dm = np.diag(1.0 / np.sqrt(d))
    return np.sort(np.linalg.eigvalsh(np.eye(len(d)) - Dm @ W @ Dm))


def random_game(n, k, p, rng, maxw=3):
    edges = []
    for u in range(n):
        for v in range(u + 1, n):
            if rng.random() < p:
                w = rng.randint(1, maxw)
                perm = list(range(k))
                rng.shuffle(perm)
                edges.append((u, v, w, tuple(perm)))
    deg = [0] * n
    for u, v, w, _ in edges:
        deg[u] += w
        deg[v] += w
    if min(deg) == 0:
        return None
    return edges, deg


def weight_matrix(n, edges):
    W = np.zeros((n, n))
    for u, v, w, _ in edges:
        W[u, v] += float(w)
        W[v, u] += float(w)
    return W


def blowup(n, edges, m):
    """m[u] copies of u; copy-pair weight w/(m_u m_v) as a Fraction."""
    idx, off = {}, 0
    for u in range(n):
        for i in range(m[u]):
            idx[(u, i)] = off
            off += 1
    bedges = []
    for u, v, w, perm in edges:
        for i in range(m[u]):
            for j in range(m[v]):
                bedges.append((idx[(u, i)], idx[(v, j)],
                               Fraction(w, m[u] * m[v]), perm))
    return off, bedges


def opt(n, k, edges):
    tot = sum(Fraction(w) for _, _, w, _ in edges)
    best = Fraction(0)
    for lab in itertools.product(range(k), repeat=n):
        s = sum(Fraction(w) for u, v, w, p in edges if p[lab[u]] == lab[v])
        best = max(best, s)
    return best / tot


def part_a_b(rng):
    for trial in range(40):
        n, k = rng.randint(3, 5), rng.randint(2, 3)
        g = random_game(n, k, 0.7, rng)
        if g is None:
            continue
        edges, deg = g
        W = weight_matrix(n, edges)
        sG = laplacian_spectrum(W)
        N, bed = blowup(n, edges, deg)
        WB = weight_matrix(N, bed)
        dB = WB.sum(axis=1)
        check(np.allclose(dB, 1.0), f"A{trial}: every copy has degree 1 (N={N})")
        sB = laplacian_spectrum(WB)
        expect = np.sort(np.concatenate([sG, np.ones(N - n)]))
        check(np.allclose(sB, expect, atol=1e-8),
              f"A{trial}: spec(B) = spec(G) + {N - n} ones")
        check(abs(sB[1] - min(sG[1], 1.0)) < 1e-8,
              f"A{trial}: lambda_2(B)={sB[1]:.6f} = min(lambda_2(G)={sG[1]:.6f},1)")
        if N <= 11 and trial % 4 == 0:
            oG, oB = opt(n, k, edges), opt(N, k, bed)
            check(oG == oB, f"B{trial}: opt(G) = opt(B) = {oG}")


def part_c(rng):
    # biregular bipartite: A side degree dA, B side degree dB (all weights 1)
    cases = [(4, 6, 3, 2), (3, 3, 2, 2), (6, 4, 2, 3), (2, 4, 4, 2),
             (2, 3, 3, 2), (4, 2, 1, 2)]
    for t, (nA, nB, dA, dB) in enumerate(cases):
        assert nA * dA == nB * dB
        # random biregular bipartite graph by configuration with retries
        for _ in range(1000):
            stubsB = [b for b in range(nB) for _ in range(dB)]
            rng.shuffle(stubsB)
            pairs = [(a, stubsB[a * dA + r]) for a in range(nA) for r in range(dA)]
            if len(set(pairs)) == len(pairs):
                break
        k = 2
        edges = []
        for a, b in pairs:
            perm = [0, 1] if rng.random() < 0.5 else [1, 0]
            edges.append((a, nA + b, 1, tuple(perm)))
        n = nA + nB
        from math import gcd
        g = gcd(dA, dB)
        m = [dA // g] * nA + [dB // g] * nB
        # integer multiplicity 1 per copy pair: weights w * 1 (not divided)
        N, bed = blowup(n, edges, m)
        bed_int = [(u, v, Fraction(1), p) for u, v, _, p in bed]
        WB = weight_matrix(N, bed_int)
        dBv = WB.sum(axis=1)
        check(np.allclose(dBv, dA * dB // g),
              f"C{t}: integer blow-up regular of degree {dA * dB // g}, N={N}")
        sG = laplacian_spectrum(weight_matrix(n, edges))
        sB = laplacian_spectrum(WB)
        check(abs(sB[1] - min(sG[1], 1.0)) < 1e-8,
              f"C{t}: lambda_2(B)={sB[1]:.6f} = min(lambda_2(G)={sG[1]:.6f},1)")
        if N <= 12:
            check(opt(n, k, edges) == opt(N, k, bed_int), f"C{t}: opt preserved")


def subspaces(q, n, dim):
    """All dim-subspaces of F_q^n as frozensets of vectors (tuples)."""
    vecs = list(itertools.product(range(q), repeat=n))
    seen, out = set(), []
    for basis in itertools.combinations(vecs[1:], dim):
        span = set()
        for coef in itertools.product(range(q), repeat=dim):
            span.add(tuple(sum(c * b[i] for c, b in zip(coef, basis)) % q
                           for i in range(n)))
        if len(span) == q ** dim:
            f = frozenset(span)
            if f not in seen:
                seen.add(f)
                out.append(f)
    return out


def qint(m, q):
    return sum(q ** i for i in range(m))


def part_d():
    for q, n, l in [(2, 3, 1), (2, 3, 2), (2, 4, 2), (2, 4, 3), (2, 5, 2),
                    (3, 3, 2), (3, 4, 2)]:
        lo = subspaces(q, n, l - 1) if l > 1 else [frozenset([(0,) * n])]
        hi = subspaces(q, n, l)
        M = np.array([[1.0 if a <= b else 0.0 for b in hi] for a in lo])
        r, c = M.sum(axis=1), M.sum(axis=0)
        Nrm = np.diag(1 / np.sqrt(r)) @ M @ np.diag(1 / np.sqrt(c))
        sv = np.sort(np.linalg.svd(Nrm, compute_uv=False))[::-1]
        s2sq = sv[1] ** 2 if len(sv) > 1 else 0.0
        pred = 1 - qint(n, q) / (qint(l, q) * qint(n - l + 1, q))
        if l == 1:
            pred = 0.0
        check(abs(s2sq - pred) < 1e-9 and s2sq < 1 / q + 1e-12,
              f"D q={q} n={n} l={l}: sigma_2^2={s2sq:.6f} pred={pred:.6f} < 1/q;"
              f" lambda_2(host)=1-sigma_2={1 - np.sqrt(s2sq):.4f}")


if __name__ == "__main__":
    rng = random.Random(20260917)
    part_a_b(rng)
    part_c(rng)
    part_d()
    print("ALL PASS" if not FAIL else f"{len(FAIL)} FAILURES")
    sys.exit(0 if not FAIL else 1)
