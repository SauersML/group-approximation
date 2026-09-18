#!/usr/bin/env python3
"""Exact sanity checks for research/f-invariant-means-on-the-free-magma-are-never-products-proof.md.

Trees of the free magma T on one generator: the leaf is the string 'o', a product a*b is the tuple (a, b).
Means are finitely supported dicts tree -> Fraction. Everything is exact rational arithmetic.
The script verifies the finite identities used in the proof (Facts 1 and 3, the right-marginal identity,
the x_2 preimage identity, the Y-identity, and the product-rule instances of Lemma M). Finitely supported
means are never F-invariant, so the contradiction itself is not (and cannot be) tested here.
"""
from fractions import Fraction
from functools import lru_cache
import random

LEAF = 'o'


def size(t):
    return 1 if t == LEAF else size(t[0]) + size(t[1])


@lru_cache(maxsize=None)
def trees(n):
    if n == 1:
        return (LEAF,)
    out = []
    for k in range(1, n):
        for a in trees(k):
            for b in trees(n - k):
                out.append((a, b))
    return tuple(out)


UNIVERSE = [t for n in range(1, 7) for t in trees(n)]


def conv(mu, nu):
    out = {}
    for s, p in mu.items():
        for t, q in nu.items():
            out[(s, t)] = out.get((s, t), 0) + p * q
    return out


def mass(mu, pred):
    return sum((p for t, p in mu.items() if pred(t)), Fraction(0))


def push(phi, mu):
    out = {}
    for t, p in mu.items():
        u = phi(t)
        out[u] = out.get(u, 0) + p
    return out


def x1(t):  # (a*b)*c -> a*(b*c)
    (a, b), c = t
    return (a, (b, c))


def in_dom_x1(t):
    return t != LEAF and t[0] != LEAF


def x2(t):  # s*w -> s*x1(w)
    s, w = t
    return (s, x1(w))


def in_dom_x2(t):
    return t != LEAF and in_dom_x1(t[1])


def r(t):
    return t[1]


def rand_mean(rng, pool, k=4):
    pts = rng.sample(pool, k)
    w = [rng.randint(1, 9) for _ in pts]
    tot = sum(w)
    return {t: Fraction(x, tot) for t, x in zip(pts, w)}


def rand_set(rng, pool):
    return frozenset(t for t in pool if rng.random() < 0.5)


# Moore's sets for w = y1*y2: s in Z iff s = a*b and b in T_{#a}; T_0 = T, T_{p+1} = (T\Z)*T_p.
@lru_cache(maxsize=None)
def in_Z(s):
    return s != LEAF and in_T(s[1], size(s[0]))


@lru_cache(maxsize=None)
def in_T(t, p):
    if p == 0:
        return True
    return t != LEAF and (not in_Z(t[0])) and in_T(t[1], p - 1)


def main():
    rng = random.Random(20260917)
    small = [t for t in UNIVERSE if size(t) <= 4]
    prod_small = [t for t in small if t != LEAF]
    names = ['fact1', 'fact3', 'right_marginal', 'x2_preimage', 'Y_identity', 'lemmaM_tails', 'lemmaM_Z']
    checks = {k: 0 for k in names}
    trials = 200
    for _ in range(trials):
        mu, beta, gam = (rand_mean(rng, small) for _ in range(3))
        A, B = rand_set(rng, small), rand_set(rng, small)
        # Fact 1: mu*beta(A*B) = mu(A) beta(B)
        lhs = mass(conv(mu, beta), lambda t: t != LEAF and t[0] in A and t[1] in B)
        assert lhs == mass(mu, lambda t: t in A) * mass(beta, lambda t: t in B)
        checks['fact1'] += 1
        # Fact 3: (x1)_*((mu*beta)*gam) = mu*(beta*gam)
        assert push(x1, conv(conv(mu, beta), gam)) == conv(mu, conv(beta, gam))
        checks['fact3'] += 1
        # right marginal: for mu on T*T, r_*((x1)_*(mu*beta)) = (r_*mu)*beta
        mup = rand_mean(rng, prod_small)
        rho = push(r, mup)
        assert push(r, push(x1, conv(mup, beta))) == conv(rho, beta)
        checks['right_marginal'] += 1
        # x2^{-1}(T*B) = T*(x1^{-1}B), checked pointwise on all trees with at most 6 leaves
        for t in UNIVERSE:
            lhs_in = in_dom_x2(t) and x2(t)[1] in B
            rhs_in = t != LEAF and in_dom_x1(t[1]) and x1(t[1]) in B
            assert lhs_in == rhs_in
        checks['x2_preimage'] += 1
        # Y-identity: (rho*gam)(x1(Y*T)) = int d rho(a) gam(Y_a * T), for Y inside T*T.
        # x1(Y*T) = {a*(b*c) : a*b in Y}.
        Y = frozenset(t for t in rand_set(rng, small) if t != LEAF)

        def in_x1YT(t):
            return t != LEAF and t[1] != LEAF and (t[0], t[1][0]) in Y

        lhs = mass(conv(rho, gam), in_x1YT)
        rhs = sum((p * mass(gam, lambda c: c != LEAF and (a, c[0]) in Y) for a, p in rho.items()),
                  Fraction(0))
        assert lhs == rhs
        # with gam = rho2*delta this is (rho*rho2)(Y), the shape used in step 3 of part (A)
        rho2, delta = rand_mean(rng, small), rand_mean(rng, small)
        assert mass(conv(rho, conv(rho2, delta)), in_x1YT) == mass(conv(rho, rho2), lambda t: t in Y)
        checks['Y_identity'] += 1
        # Lemma M product-rule instances for nu*nu
        nu = rand_mean(rng, small)
        nn = conv(nu, nu)
        notZ = mass(nu, lambda t: not in_Z(t))
        for p in range(0, 5):
            assert mass(nn, lambda t: in_T(t, p + 1)) == notZ * mass(nu, lambda t: in_T(t, p))
        checks['lemmaM_tails'] += 1
        rhsZ = sum((q * mass(nu, lambda t: in_T(t, size(a))) for a, q in nu.items()), Fraction(0))
        assert mass(nn, in_Z) == rhsZ
        checks['lemmaM_Z'] += 1
    for k in names:
        print(f"{k}: {checks[k]}/{trials} random exact trials passed")
    zc = [sum(1 for t in trees(n) if in_Z(t)) for n in range(1, 10)]
    print("Moore's Z: |Z cap S_n| for n=1..9:", zc)
    print("|S_n| for n=1..9:", [len(trees(n)) for n in range(1, 10)])
    print("ALL CHECKS PASSED")


if __name__ == '__main__':
    main()
