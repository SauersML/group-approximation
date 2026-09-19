#!/usr/bin/env python3
"""Hand certificate for Theorem A (one-ring push), checked mechanically for n = 5..10.

Fox 3-colorings: a homomorphism F_n -> S_3 sending every x_i to a transposition is a vector
c in F_3^n (x_i -> reflection r_{c_i} of the triangle, r_a r_b r_a = r_{2a-b}).  PSigmaAut_n acts on
the right, rho . phi = rho o phi, and on colors:
  A_ij   : c_i -> 2 c_j - c_i                       (x_i -> x_j x_i x_j^-1)
  A_ij^-1: the same (reflections are involutions)
  th_k   : c_k -> c_k + 2 c_a - 2 c_b               (x_k -> (x_a x_b) x_k (x_a x_b)^-1)
  ze_q   : c_a -> 2 c_q - c_a, c_b -> 2 c_q - c_b   (x_a, x_b -> x_q (.) x_q^-1)
(inverses of th, ze act as th with a,b swapped, and as ze).  Rings: v,w,c,a,d = 0,1,2,3,4.

Checks:
  (a) rho = (0,1,2,0,0; 1,...) and rho . (A_vc^{-+1} o A_ca) = (1,1,1,0,0; 1,...).
  (b) the full orbit of rho . p under P_(a,d) (BFS with all generators and inverses) has c_v = c_w.
  (c) the full orbit of rho under P_(v,w) has c_v != c_w.
Hence A_vc^{-+1} A_ca is not in P_b0 P_(a,d), i.e. A_ca[(a,d)] is in lk(b0) but not in lk(A_vc^{+-1} b0).
"""
import sys


def moves(rings, n):
    """Color actions of the cabling generators of P_rings and their inverses."""
    a, b = rings
    others = [i for i in range(n) if i not in rings]
    out = []
    for i in others:
        for j in others:
            if i != j:
                out.append(lambda c, i=i, j=j: c[:i] + ((2 * c[j] - c[i]) % 3,) + c[i + 1:])
    for k in others:
        for s in (1, -1):
            out.append(lambda c, k=k, s=s: c[:k] + ((c[k] + s * (2 * c[a] - 2 * c[b])) % 3,) + c[k + 1:])
        def ze(c, q=k):
            l = list(c)
            l[a] = (2 * c[q] - c[a]) % 3
            l[b] = (2 * c[q] - c[b]) % 3
            return tuple(l)
        out.append(ze)
    return out


def orbit(start, gens):
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for g in gens:
            y = g(x)
            if y not in seen:
                seen.add(y)
                stack.append(y)
    return seen


def main():
    v, w, c, a, d = 0, 1, 2, 3, 4
    ok = True
    for n in range(5, 11):
        rho = (0, 1, 2, 0, 0) + (1,) * (n - 5)
        # rho . A_vc^{-+1}: c_v -> 2 c_c - c_v ; then . A_ca: c_c -> 2 c_a - c_c
        r1 = list(rho)
        r1[v] = (2 * r1[c] - r1[v]) % 3
        r1[c] = (2 * r1[a] - r1[c]) % 3
        rp = tuple(r1)
        orbK = orbit(rp, moves((a, d), n))
        orbH = orbit(rho, moves((v, w), n))
        a_ok = rp == (1, 1, 1, 0, 0) + (1,) * (n - 5)
        b_ok = all(x[v] == x[w] for x in orbK)
        c_ok = all(x[v] != x[w] for x in orbH)
        print('n=%d  rho.p=%s  (a) %s  (b) |orbit_K|=%d c_v=c_w: %s  (c) |orbit_H|=%d c_v!=c_w: %s'
              % (n, rp, a_ok, len(orbK), b_ok, len(orbH), c_ok))
        ok = ok and a_ok and b_ok and c_ok
    print('ALL PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
