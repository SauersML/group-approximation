#!/usr/bin/env python3
"""Theory-guided virtual fibring search for row 29, G = <a,t | AAttATaTAttaaTT>.

vfib.py enumerates every transitive action of degree k, which stalls near k = 13.
This driver instead feeds metabelian covers that come from the Alexander module
M = Z[s^{+-1}]/(Delta), Delta(s) = -3 + s + s^2 (level exponent sums [-3,1,1]):
  (A) affine actions on F_p or Z/p^j:  a: x -> x + 1,  t: x -> r x,  r a root of Delta
      (both r and r^-1 are tried; only actions on which w acts trivially are kept);
  (B) affine actions on F_{p^2} = F_p[theta]/(Delta) for p with Delta irreducible;
  (C) products of (A) or (B) with the cyclic action of chi mod m.
Characters and collapse certificates are searched exactly as in vfib.py, except that
vertex potentials are sampled (pot = 0, then random vectors in {-R..R}) instead of
enumerated, because 3^(k-1) is too large here.  Any CERT line is re-checked by verify.py,
so the sampling heuristic cannot produce a false certificate.
Usage: vfib_targeted.py WORD PMAX MMAX KMAX LAM NSAMP R
"""
import sys, itertools, random
from math import gcd
from vfib import LET, act, canon, cover, tree_edges, nullspace, alexander, collapses

def is_action(w, a, t):
    k = len(a)
    ai = [0] * k; ti = [0] * k
    for i in range(k):
        ai[a[i]] = i; ti[t[i]] = i
    gens = {0: (a, ai), 1: (t, ti)}
    return all(act(gens, w, i) == i for i in range(k))

def transitive(a, t):
    k, seen, st = len(a), {0}, [0]
    ai = [0] * k; ti = [0] * k
    for i in range(k):
        ai[a[i]] = i; ti[t[i]] = i
    while st:
        i = st.pop()
        for j in (a[i], ai[i], t[i], ti[i]):
            if j not in seen:
                seen.add(j); st.append(j)
    return len(seen) == k

def primes(n):
    return [p for p in range(2, n + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]

def affine_mod(n):
    """All (a, t) with a = +1 and t = multiplication by a unit r modulo n."""
    out = []
    for r in range(1, n):
        if gcd(r, n) != 1:
            continue
        a = tuple((x + 1) % n for x in range(n))
        t = tuple((r * x) % n for x in range(n))
        out.append(('Z/%d r=%d' % (n, r), a, t))
    return out

def affine_fp2(p):
    """F_p[theta]/(theta^2 + theta - 3): a = +1, t = multiplication by theta or theta^-1."""
    k = p * p
    idx = lambda u, v: (u % p) + p * (v % p)
    mul_theta = lambda u, v: (3 * v, u - v)            # theta*(u + v theta) = 3v + (u - v) theta
    a = tuple(idx(u + 1, v) for v in range(p) for u in range(p))
    t = [0] * k
    for v in range(p):
        for u in range(p):
            x, y = mul_theta(u, v)
            t[idx(u, v)] = idx(x, y)
    t = tuple(t)
    out = []
    if len(set(t)) == k:                                 # theta invertible (p != 3)
        out.append(('F_%d^2 theta' % p, a, t))
        ti = [0] * k
        for i in range(k):
            ti[t[i]] = i
        out.append(('F_%d^2 theta^-1' % p, a, tuple(ti)))
    return out

def product_cyclic(name, a, t, m):
    k = len(a)
    idx = lambda x, i: x + k * i
    A = tuple(idx(a[x], i) for i in range(m) for x in range(k))
    T = tuple(idx(t[x], (i + 1) % m) for i in range(m) for x in range(k))
    return ('%s x chi mod %d' % (name, m), A, T)

def search(s, name, a, t, LAM, NSAMP, R, rng):
    w, k = [LET[ch] for ch in s], len(a)
    ends, cells = cover(w, a, t)
    tree = tree_edges(k, ends)
    non = [e for e in range(2 * k) if e not in tree]
    M = [[sum(sg for (e, sg) in cell if e == f) for f in non] for cell in cells]
    null = nullspace(M, len(non))
    b1, nch, nmon, seen = len(null), 0, 0, set()
    for lam in itertools.product(range(-LAM, LAM + 1), repeat=b1):
        nz = [x for x in lam if x]
        if not nz or nz[0] < 0:
            continue
        cn = [sum(l * v[j] for l, v in zip(lam, null)) for j in range(len(non))]
        g = 0
        for x in cn:
            g = gcd(g, abs(x))
        c = [0] * (2 * k)
        for j, f in enumerate(non):
            c[f] = cn[j] // g
        if tuple(c) in seen:
            continue
        seen.add(tuple(c)); nch += 1
        D = alexander(cells, c, non)
        if not (D is not None and abs(D[0]) == 1 and abs(D[-1]) == 1):
            continue
        nmon += 1
        print('MONIC %s | %s k=%d b1=%d c=%s delta=%s' % (s, name, k, b1, c, D), flush=True)
        pots = [tuple([0] * k)] + [(0,) + tuple(rng.randint(-R, R) for _ in range(k - 1)) for _ in range(NSAMP)]
        for pot in pots:
            cp = [c[e] + pot[v] - pot[u] for e, (u, v) in enumerate(ends)]
            if collapses(k, ends, cells, cp, rng) and collapses(k, ends, cells, [-x for x in cp], rng):
                print('CERT %s k=%d a=%s t=%s c=%s pot=%s cp=%s delta=%s' % (s, k, list(a), list(t), c, list(pot), cp, D), flush=True)
                return True, b1, nch, nmon
    return False, b1, nch, nmon

def main():
    s, PMAX, MMAX, KMAX = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    LAM, NSAMP, R = int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
    w, rng = [LET[ch] for ch in s], random.Random(29)
    base = []
    for p in primes(PMAX):
        for n in (p, p * p, p ** 3):
            if n <= KMAX:
                base.extend(affine_mod(n))
        if p * p <= KMAX:
            base.extend(affine_fp2(p))
    cands, canon_seen = [], set()
    for name, a, t in base:
        for m in range(1, MMAX + 1):
            nm, A, T = (name, a, t) if m == 1 else product_cyclic(name, a, t, m)
            if len(A) > KMAX or not is_action(w, A, T) or not transitive(A, T):
                continue
            key = canon(A, T)
            if key in canon_seen:
                continue
            canon_seen.add(key); cands.append((nm, A, T))
    cands.sort(key=lambda x: len(x[1]))
    print('CANDIDATES %s n=%d degrees=%s' % (s, len(cands), sorted({len(x[1]) for x in cands})), flush=True)
    for nm, A, T in cands:
        ok, b1, nch, nmon = search(s, nm, A, T, LAM, NSAMP, R, rng)
        print('DONE %s | %s k=%d b1=%d chars=%d monic=%d cert=%s' % (s, nm, len(A), b1, nch, nmon, ok), flush=True)
    print('SENTINEL_DONE', flush=True)

if __name__ == '__main__':
    main()
