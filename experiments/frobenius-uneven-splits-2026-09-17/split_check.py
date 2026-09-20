#!/usr/bin/env python3
"""Uneven Frobenius splits of congruence orbits (calibration).

L = SL_n(F_p[t]) acts on unimodular vectors of A^n, A = F_p[t]/(t^N), through the
surjection L -> SL_n(A) = E_n(A).  H = alpha(L) = SL_n(F_p[t^p]) is the image of the
Frobenius endomorphism alpha(f) = f^p; its image in SL_n(A) is E_n(B) with
B = F_p-span{1, t^p, t^(2p), ...} mod t^N.

We compute:
  * the H-orbit sizes inside the single L-orbit (all unimodular vectors);
  * the largest relative suborbit size |c|/|C|;
  * fixed-point proportions of a few nontrivial elements of L (asymptotic freeness).

Elements of A are tuples of N coefficients mod p.  Only elementary generators are
used, so the orbits computed are exactly the E_n(B)-orbits = H-orbits.
"""
import itertools, sys
from collections import Counter

def run(p, n, N):
    def mul(a, b):
        c = [0]*N
        for i, x in enumerate(a):
            if x:
                for j in range(N - i):
                    c[i+j] = (c[i+j] + x*b[j]) % p
        return tuple(c)
    def add(a, b):
        return tuple((x+y) % p for x, y in zip(a, b))
    elems = list(itertools.product(range(p), repeat=N))
    zero = tuple([0]*N)
    one = tuple([1] + [0]*(N-1))
    def mono(k):
        c = [0]*N
        if k < N: c[k] = 1
        return tuple(c)
    vecs = [v for v in itertools.product(elems, repeat=n)
            if any(x[0] % p for x in v)]          # unimodular: some unit coordinate
    total = len(vecs)
    idx = {v: i for i, v in enumerate(vecs)}
    # generators of H-bar: e_ij(t^(p*k)) for p*k < N (these generate E_n(B) together
    # with F_p-multiples, which are powers of these since the additive group is p-torsion)
    Bgens = [mono(p*k) for k in range(0, (N + p - 1)//p) if p*k < N]
    def e(i, j, r):
        def act(v):
            w = list(v)
            w[i] = add(w[i], mul(r, v[j]))
            return tuple(w)
        return act
    Hgens = [e(i, j, r) for i in range(n) for j in range(n) if i != j for r in Bgens]
    seen = [False]*total
    sizes = []
    for s in range(total):
        if seen[s]: continue
        stack = [s]; seen[s] = True; cnt = 0
        while stack:
            x = stack.pop(); cnt += 1
            v = vecs[x]
            for g in Hgens:
                y = idx[g(v)]
                if not seen[y]:
                    seen[y] = True; stack.append(y)
        sizes.append(cnt)
    sizes.sort(reverse=True)
    # fixed-point proportions for some nontrivial L-elements
    tests = {"e12(1)": e(0, 1, one), "e12(t)": e(0, 1, mono(1)),
             "e12(t^(N-1))": e(0, 1, mono(N-1))}
    fp = {name: sum(1 for v in vecs if g(v) == v)/total for name, g in tests.items()}
    return total, sizes, fp

if __name__ == "__main__":
    for (p, n, N) in [(2, 3, 2), (2, 3, 3), (2, 3, 4), (2, 3, 5), (3, 3, 2), (2, 4, 2)]:
        total, sizes, fp = run(p, n, N)
        c = Counter(sizes)
        print(f"p={p} n={n} N={N}: |C|={total}, #H-orbits={len(sizes)}, "
              f"max |c|/|C| = {sizes[0]}/{total} = {sizes[0]/total:.4f}")
        print("   orbit size multiset:", sorted(c.items(), reverse=True))
        print("   fixed-point proportions:", {k: round(v, 4) for k, v in fp.items()})
        sys.stdout.flush()
