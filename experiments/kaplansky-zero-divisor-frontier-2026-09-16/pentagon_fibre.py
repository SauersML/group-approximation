#!/usr/bin/env python3
"""Pentagon relators of support-3 zero divisors as free-by-cyclic groups.

Letters are nonzero integers: i means generator i, -i its inverse.

Part A. R1 = v^-2 u^-2 v u (u = h_2 = letter 1, v = h_3 = letter 2).
  With c = v u and c_j = u^j c u^-j, check in the free group F(u, v) that
  c_2 c_1 c_0^-1 is a conjugate of R1^-1, and that the conjugation action
  theta: x1 -> x2, x2 -> x1 x2^-1 inverts the commutator [x1, x2] exactly.

Part B. R2 = v^-2 u^-1 v^-1 u^2.
  With c = u v^-3 and c_j = v^j c v^-j, check that c_0 c_3 c_1^-1 is a
  conjugate of R2^{+-1}; give psi on F(x0, x2, x3) (psi = conjugation by v)
  and its inverse; then search short cyclic words w with psi^k(w) conjugate
  to w or to w^-1.
"""
import itertools
import sys


def red(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def inv(w):
    return tuple(-x for x in reversed(w))


def mul(*ws):
    r = ()
    for w in ws:
        r = red(r + tuple(w))
    return r


def pw(w, n):
    if n < 0:
        return pw(inv(w), -n)
    r = ()
    for _ in range(n):
        r = mul(r, w)
    return r


def cyc_red(w):
    w = red(w)
    while len(w) >= 2 and w[0] == -w[-1]:
        w = w[1:-1]
    return w


def canon_cyclic(w):
    w = cyc_red(w)
    if not w:
        return ()
    return min(w[i:] + w[:i] for i in range(len(w)))


def conjugate_in_free_group(a, b):
    return canon_cyclic(a) == canon_cyclic(b)


def apply(phi, w):
    r = ()
    for x in w:
        img = phi[abs(x)]
        r = mul(r, img if x > 0 else inv(img))
    return r


def comm(a, b):
    return mul(a, b, inv(a), inv(b))


def partA():
    u, v = (1,), (2,)
    R1 = mul(pw(v, -2), pw(u, -2), v, u)
    c = mul(v, u)
    cj = [mul(pw(u, j), c, pw(u, -j)) for j in range(3)]
    lhs = mul(cj[2], cj[1], inv(cj[0]))
    ok1 = conjugate_in_free_group(lhs, inv(R1))
    # explicit conjugator: lhs == g R1^-1 g^-1 with g = u^2 v^2
    g = mul(pw(u, 2), pw(v, 2))
    ok1b = (lhs == mul(g, inv(R1), inv(g)))
    # conjugation by u on c_1, c_2:  u c_1 u^-1 = c_2,  u c_2 u^-1 = c_1 c_2^-1 mod R1
    theta = {1: (2,), 2: (1, -2)}
    x1, x2 = (1,), (2,)
    z = comm(x1, x2)
    ok2 = (apply(theta, z) == inv(z))
    # theta is an automorphism: inverse x1 -> x2^-1 x1 ... check
    theta_inv = {1: mul((2,), (1,)), 2: (1,)}
    ok3 = all(apply(theta, apply(theta_inv, (i,))) == (i,) and
              apply(theta_inv, apply(theta, (i,))) == (i,) for i in (1, 2))
    # u c_2 u^-1 == c_1 c_2^-1 holds modulo R1: difference is a conjugate of R1^+-1
    d = mul(pw(u, 1), cj[2], pw(u, -1), inv(mul(cj[1], inv(cj[2]))))
    ok4 = (d == () or conjugate_in_free_group(d, R1) or conjugate_in_free_group(d, inv(R1)))
    print("A: R1 =", R1)
    print("A: c2 c1 c0^-1 == g R1^-1 g^-1 (g = u^2 v^2):", ok1b, " conjugate check:", ok1)
    print("A: theta([x1,x2]) == [x1,x2]^-1 exactly:", ok2)
    print("A: theta is an automorphism (explicit inverse):", ok3)
    print("A: u c2 u^-1 (c1 c2^-1)^-1 =", d, "is conjugate of R1^+-1 or trivial:", ok4)
    return ok1 and ok1b and ok2 and ok3 and ok4


def partB(maxlen, maxk):
    u, v = (1,), (2,)
    R2 = mul(pw(v, -2), pw(u, -1), pw(v, -1), pw(u, 2))
    c = mul(u, pw(v, -3))
    cj = {j: mul(pw(v, j), c, pw(v, -j)) for j in range(-1, 5)}
    lhs = mul(cj[0], cj[3], inv(cj[1]))
    okB1 = conjugate_in_free_group(lhs, R2) or conjugate_in_free_group(lhs, inv(R2))
    print("B: R2 =", R2)
    print("B: c0 c3 c1^-1 =", lhs, "conjugate of R2^+-1:", okB1)
    # psi on F(x0, x2, x3) encoded as letters 1 -> x0, 2 -> x2, 3 -> x3
    psi = {1: (1, 3), 2: (3,), 3: (-3, -1, 2)}
    psi_inv = {1: (1, -2), 2: (1, 3), 3: (2,)}
    okB2 = all(apply(psi, apply(psi_inv, (i,))) == (i,) and
               apply(psi_inv, apply(psi, (i,))) == (i,) for i in (1, 2, 3))
    print("B: psi is an automorphism (explicit inverse):", okB2)
    # consistency of psi with the relation: v c_4 v^-1 ... c_4 = c_1^-1 c_2 == c_3^-1 c_0^-1 c_2
    # check that psi(x3) corresponds: c_4 * (c_3^-1 c_0^-1 c_2)^-1 is trivial mod R2 (conjugate products);
    # we verify the defining identity c_1 = c_0 c_3 shifted by one: c_2 = c_1 c_4.
    lhs2 = mul(cj[1], cj[4], inv(cj[2]))
    okB3 = conjugate_in_free_group(lhs2, R2) or conjugate_in_free_group(lhs2, inv(R2))
    print("B: c1 c4 c2^-1 conjugate of R2^+-1:", okB3)
    # search periodic conjugacy classes
    letters = [1, -1, 2, -2, 3, -3]
    seen = set()
    hits = []
    for L in range(1, maxlen + 1):
        for w in itertools.product(letters, repeat=L):
            w = tuple(w)
            if red(w) != w or cyc_red(w) != w:
                continue
            cw = canon_cyclic(w)
            if cw in seen:
                continue
            seen.add(cw)
            # skip proper powers
            proper = False
            for d in range(1, L):
                if L % d == 0 and w[:d] * (L // d) == w:
                    proper = True
                    break
            if proper:
                continue
            img = w
            for k in range(1, maxk + 1):
                img = apply(psi, img)
                if len(cyc_red(img)) > 4000:
                    break
                ci = canon_cyclic(img)
                if ci == cw:
                    hits.append((w, k, +1))
                    break
                if ci == canon_cyclic(inv(w)):
                    hits.append((w, k, -1))
                    break
    print("B: periodic conjugacy classes up to length", maxlen, "and k <=", maxk, ":", len(hits))
    for h in hits[:40]:
        print("   w =", h[0], " k =", h[1], " sign =", h[2])
    return okB1 and okB2 and okB3, hits


if __name__ == "__main__":
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    maxk = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    a = partA()
    b, hits = partB(maxlen, maxk)
    print("ALL IDENTITIES OK:", a and b)
