#!/usr/bin/env python3
"""Edge-relator defect in u(heis) and its torus eigencomponents.

u(heis) over F_p: basis a^i e^k b^j (0<=i,k,j<p), [a,b]=e central,
a^p=b^p=e^p=0.  Y_x = log(1+X_x); rho: Y_a -> a, Y_b -> b is graded, so group generators map
to truncated exponentials E(a), E(b).
For an edge relator r (group word) and (lam,mu) in (F_p^*)^2 put
  D(lam,mu) = r(E(lam a), E(mu b)) - 1,
the rho-image of the torus translate of r-1.  The eigencomponent of r-1
for the character (lam,mu) -> lam^c1 mu^c2 has rho-image
  D_c = sum_{lam,mu} lam^{-c1} mu^{-c2} D(lam,mu)   ((p-1)^2 = 1 mod p).
Bidegree of a^i e^k b^j is (i+k, j+k).  We list the bidegree support of
each D_c and check: every support point is c + (p-1)*s with s in {0,1}^2
(shift set {0,p-1}^2), no letter degree is 0, the shift (0,0) never
occurs (lowest forms are rho-invisible), and we record which classes carry
a diagonal (s=(1,1)) component and which single-letter shifts occur.
Usage: heis_defect.py p
"""
import sys
import numpy as np

p = int(sys.argv[1])


def mul_a(v):
    w = np.zeros_like(v)
    w[1:, :, :] = v[:-1, :, :]
    return w


def mul_b(v):
    # b a^i e^k b^j = a^i e^k b^{j+1} - i a^{i-1} e^{k+1} b^j
    w = np.zeros_like(v)
    w[:, :, 1:] = v[:, :, :-1]
    i = np.arange(p).reshape(p, 1, 1)
    t = (i * v)[1:, :-1, :]
    w[:-1, 1:, :] -= t
    return w % p


def gpow(which, n, v):
    # left multiplication by the truncated exponential E(n x) = sum_{k<p} (n x)^k / k!
    f = mul_a if which == 'a' else mul_b
    out, cur, fact = v.copy(), v.copy(), 1
    for k in range(1, p):
        cur = f(cur)
        fact = fact * k % p
        out = (out + pow(n % p, k, p) * pow(fact, p - 2, p) * cur) % p
    return out


def apply_word(word, lam, mu, v):
    # word: list of (letter, sign); element = product left to right
    for letter, sgn in reversed(word):
        e = lam if letter == 'a' else mu
        v = gpow(letter, sgn * e, v)
    return v


def comm(x, y):
    # [x,y] = x^-1 y^-1 x y
    return [(l, -s) for l, s in reversed(x)] + \
           [(l, -s) for l, s in reversed(y)] + x + y


A, B = [('a', 1)], [('b', 1)]
RELS = {'[[a,b],a]': comm(comm(A, B), A), '[[a,b],b]': comm(comm(A, B), B)}


def support(D):
    out = {}
    for (i, k, j) in zip(*np.nonzero(D)):
        d = (int(i + k), int(j + k))
        out[d] = out.get(d, 0) + 1
    return out


one = np.zeros((p, p, p), dtype=np.int64)
one[0, 0, 0] = 1
ok = True
for name, word in RELS.items():
    Dl = {}
    for lam in range(1, p):
        for mu in range(1, p):
            Dl[(lam, mu)] = (apply_word(word, lam, mu, one.copy()) - one) % p
    print(f"== p={p} relator {name}")
    diag = []
    allsh = []
    for c1 in range(1, p):
        for c2 in range(1, p):
            Dc = np.zeros((p, p, p), dtype=np.int64)
            for (lam, mu), D in Dl.items():
                co = pow(lam, (p - 1) * p - c1, p) * pow(mu, (p - 1) * p - c2, p)
                Dc = (Dc + co * D) % p
            sp = support(Dc)
            if not sp:
                continue
            shifts = set()
            for (x, y) in sp:
                sx, sy = (x - c1), (y - c2)
                if x == 0 or y == 0 or sx % (p - 1) or sy % (p - 1) \
                        or sx not in (0, p - 1) or sy not in (0, p - 1):
                    ok = False
                    print("  VIOLATION", (c1, c2), (x, y))
                shifts.add((sx // (p - 1), sy // (p - 1)))
            allsh += list(shifts)
            if (1, 1) in shifts:
                diag.append((c1, c2))
            print(f"  class {(c1, c2)}: support {sorted(sp)} "
                  f"shifts {sorted(shifts)}")
    if any((0, 0) == sh for sh in allsh):
        ok = False
        print("  VIOLATION shift (0,0) occurs")
    print(f"  single-letter shifts occurring: {sorted(set(allsh) - {(1, 1)})}")
    print(f"  classes with diagonal (p-1,p-1) component: {diag}")
    tot = sum(Dl[(1, 1)].ravel() != 0)
    print(f"  D(1,1) nonzero PBW coords: {tot}")
print("ALL SHIFTS IN {0,p-1}^2:", ok)
