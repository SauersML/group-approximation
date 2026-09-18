#!/usr/bin/env python3
"""Consequences of the Laplacian identity d delta + delta d = c(mu) Id on C_*(L_Z)_mu (x) Z[1/3].

c(mu) = (rho,mu) - (mu,mu)/2 = deg(mu) - Q(nu), where mu = nu + m delta, nu = x alpha_1 + y alpha_2,
x = c1-c0, y = c2-c0, Q(nu) = x^2 - xy + y^2.

usage:
  linkage.py support K P1 P2 ...   for each prime p, the degrees k <= K carrying a weight mu of Lambda^2(L)
                                    with p | c(mu) (these contain D_p minus {3}), grouped by the type of nu,
                                    and the least such degree above 3 (the uniform tower-agreement bound)
  linkage.py check FILE            check an h2z.py output: every free summand sits at c(mu)=0 and every
                                    prime != 3 dividing a torsion invariant divides c(mu)
"""
import sys, re


def roots(K):
    """positive roots of affine A2 of degree <= K, as (c0,c1,c2) with multiplicity."""
    fin = [(0, 1, 0), (0, 0, 1), (0, 1, 1), (0, -1, 0), (0, 0, -1), (0, -1, -1)]
    out = []
    for a in range(0, K // 3 + 2):
        for v in fin:
            w = (v[0] + a, v[1] + a, v[2] + a)
            if min(w) >= 0 and sum(w) > 0 and sum(w) <= K:
                out.append((w, 1))
        if a >= 1 and 3 * a <= K:
            out.append(((a, a, a), 2))
    return out


def cval(w):
    x, y = w[1] - w[0], w[2] - w[0]
    return sum(w) - (x * x - x * y + y * y)


def qtype(w):
    x, y = w[1] - w[0], w[2] - w[0]
    return x * x - x * y + y * y


def lambda2_weights(K):
    R = roots(K)
    W = set()
    for i, (u, mu) in enumerate(R):
        for j, (v, mv) in enumerate(R):
            if j < i or (j == i and mu < 2):
                continue
            s = (u[0] + v[0], u[1] + v[1], u[2] + v[2])
            if sum(s) <= K:
                W.add(s)
    return W


def support(K, primes):
    W = lambda2_weights(K)
    assert {qtype(w) for w in W} <= {0, 1, 3, 4}
    for p in primes:
        bytype = {}
        for w in W:
            c = cval(w)
            if c % p == 0 and sum(w) > 3:
                bytype.setdefault(qtype(w), set()).add(sum(w))
        first = min(min(s) for s in bytype.values()) if bytype else None
        print(f"p={p}: least degree > 3 with a weight of Lambda^2 and p | c: {first}")
        for q in sorted(bytype):
            print(f"   Q(nu)={q}: degrees {sorted(bytype[q])}")


def check(fn):
    pat = re.compile(r"deg\s+(\d+) wt \((\-?\d+), (\-?\d+), (\-?\d+)\):.*H2 free (\d+) tors \[([^\]]*)\]")
    n = bad = 0
    for line in open(fn):
        m = pat.match(line)
        if not m:
            continue
        w = tuple(int(m.group(i)) for i in (2, 3, 4))
        free = int(m.group(5))
        tors = [int(t) for t in m.group(6).split(",") if t.strip()]
        c = cval(w)
        n += 1
        ok = (free == 0 or c == 0)
        for e in tors:
            q = e
            d = 2
            while q > 1:
                while q % d == 0:
                    if d != 3 and c != 0 and c % d:
                        ok = False
                    q //= d
                d += 1
        if not ok:
            bad += 1
            print("VIOLATION", line.strip())
    print(f"{n} weight lines checked, {bad} violations")


if __name__ == "__main__":
    if sys.argv[1] == "support":
        support(int(sys.argv[2]), [int(p) for p in sys.argv[3:]])
    else:
        check(sys.argv[2])
