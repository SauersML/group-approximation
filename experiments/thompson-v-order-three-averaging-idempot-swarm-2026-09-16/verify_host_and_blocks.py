#!/usr/bin/env python3
"""Finite checks for research/artifacts/thompson-v-weakly-finite-representations-2026-09-16.md.

Single-threaded, deterministic (fixed seed), a few seconds.

Convention (artifact Section 0): a V element with prefix codes a_i -> b_i maps a_i w -> b_i w,
and the Leavitt embedding x -> sum S[b_i] T[a_i] turns right-to-left composition of maps into
the ring product.  All checks are on finite words long enough that every prefix is determined.

Checks:
  C1  h = (00,01,1)->(01,1,00) and g = (0,10,11)->(10,11,0) have order three.
  C2  k = (00,01,1)->(0,10,11) satisfies k h k^-1 = g.
  C3  D(g) commutes with g, and <g, D(g)> ~ C_3^2 translates the nine cylinders p_i p_j freely.
  C4  For a clopen U = [a] u [b] u [c] split off a complete prefix code, theta_U(y) = Phi y Phi^-1 on U
      and identity off U is a homomorphism V -> V with theta_U(h) = the 3-cycle (a b c).
  C5  Block identities in F_2[C_3^2] used in Lemma W.2: f = f_K2 + f_K3 + f_K4, f_K2 D(g) = f_K2,
      f (1 + D(g)) = (f_K3 + f_K4)(1 + D(g)), and this element is a unit of the block
      (f_K3 + f_K4) F_2[C_3^2].
"""
import itertools
import random

random.seed(20260916)


def pmap(pairs):
    """Prefix replacement a_i w -> b_i w; the domain codes must form a complete prefix code."""
    pairs = list(pairs)

    def f(w):
        for a, b in pairs:
            if w.startswith(a):
                return b + w[len(a):]
        raise ValueError("word not covered by code: %r" % w)

    return f


def inverse_pairs(pairs):
    return [(b, a) for a, b in pairs]


def compose(*fs):
    """compose(x, y, z)(w) = x(y(z(w))): right-to-left, matching the ring product."""
    def c(w):
        for f in reversed(fs):
            w = f(w)
        return w

    return c


def words(n):
    return ["".join(t) for t in itertools.product("01", repeat=n)]


def same(f, g, ws):
    return all(f(w) == g(w) for w in ws)


W12 = words(12)
ID = lambda w: w

h_pairs = [("00", "01"), ("01", "1"), ("1", "00")]
g_pairs = [("0", "10"), ("10", "11"), ("11", "0")]
k_pairs = [("00", "0"), ("01", "10"), ("1", "11")]
h, g, k = pmap(h_pairs), pmap(g_pairs), pmap(k_pairs)
kinv = pmap(inverse_pairs(k_pairs))

# C1
assert same(compose(h, h, h), ID, W12) and not same(h, ID, W12)
assert same(compose(g, g, g), ID, W12) and not same(g, ID, W12)
print("C1 ok: h and g have order three")

# C2
assert same(compose(k, h, kinv), g, W12)
print("C2 ok: k h k^-1 = g")

# C3: D(x)(p_i w) = p_i x(w) for the ternary code p = (0, 10, 11)
P = ["0", "10", "11"]


def D(x):
    def d(w):
        for p in P:
            if w.startswith(p):
                return p + x(w[len(p):])
        raise ValueError

    return d


Dg = D(g)
assert same(compose(g, Dg), compose(Dg, g), W12)
cyl9 = [p + q for p in P for q in P]
for a in range(3):
    for b in range(3):
        if (a, b) == (0, 0):
            continue
        el = compose(*([g] * a + [Dg] * b)) if a + b else ID
        for c in cyl9:
            probe = c + "0110100110"
            out = el(probe)
            assert not out.startswith(c), (a, b, c)
            assert out[len(out) - 10:] == "0110100110"
print("C3 ok: <g, D(g)> ~ C_3^2 translates the nine cylinders freely")


# C4: random elements of V as products of cylinder swaps; theta_U for two clopen splittings.
def swap(rho, sigma):
    def s(w):
        if w.startswith(rho):
            return sigma + w[len(rho):]
        if w.startswith(sigma):
            return rho + w[len(sigma):]
        return w

    return s


def random_swap():
    while True:
        r = "".join(random.choice("01") for _ in range(random.randint(1, 3)))
        s = "".join(random.choice("01") for _ in range(random.randint(1, 3)))
        if not r.startswith(s) and not s.startswith(r):
            return swap(r, s)


def random_element(n):
    return compose(*[random_swap() for _ in range(n)])


def theta(abc):
    a, b, c = abc
    phi = pmap([("00", a), ("01", b), ("1", c)])
    phiinv_pairs = [(a, "00"), (b, "01"), (c, "1")]

    def th(y):
        def t(w):
            if any(w.startswith(p) for p in abc):
                return phi(y(pmap(phiinv_pairs)(w)))
            return w

        return t

    return th


samples = ["".join(random.choice("01") for _ in range(40)) for _ in range(4000)]
for abc, rest in [(("000", "001", "01"), ["1"]), (("0", "110", "111"), ["10"])]:
    th = theta(abc)
    x = pmap([(abc[0], abc[1]), (abc[1], abc[2]), (abc[2], abc[0])] + [(r, r) for r in rest])
    assert same(th(h), x, samples)
    for _ in range(40):
        y, z = random_element(6), random_element(6)
        assert same(th(compose(y, z)), compose(th(y), th(z)), samples)
print("C4 ok: theta_U is multiplicative on 80 random pairs and theta_U(h) is the 3-cycle (a b c)")

# C5: F_2[C_3^2] as subsets of Z_3^2 (coefficients in F_2 = membership)
G9 = [(i, j) for i in range(3) for j in range(3)]


def mul(x, y):
    out = set()
    for u in x:
        for v in y:
            out ^= {((u[0] + v[0]) % 3, (u[1] + v[1]) % 3)}
    return frozenset(out)


def add(*xs):
    out = set()
    for x in xs:
        out ^= set(x)
    return frozenset(out)


ONE = frozenset({(0, 0)})
gen_g, gen_Dg = frozenset({(1, 0)}), frozenset({(0, 1)})


def eK(v):
    return frozenset({(0, 0), v, ((2 * v[0]) % 3, (2 * v[1]) % 3)})


eA9 = frozenset(G9)
K1, K2, K3, K4 = (1, 0), (0, 1), (1, 1), (1, 2)
fK = {K: add(eK(K), eA9) for K in (K1, K2, K3, K4)}
e = eK(K1)
f = add(ONE, e)
for K in fK:
    assert mul(fK[K], fK[K]) == fK[K]
for K, L in itertools.combinations(fK, 2):
    assert mul(fK[K], fK[L]) == frozenset()
assert f == add(fK[K2], fK[K3], fK[K4])
assert mul(fK[K2], gen_Dg) == fK[K2]
block = add(fK[K3], fK[K4])
lhs = mul(f, add(ONE, gen_Dg))
assert lhs == mul(block, add(ONE, gen_Dg))
elements = [frozenset(s) for r in range(10) for s in itertools.combinations(G9, r)]
inv = [y for y in elements if mul(lhs, y) == block and mul(y, block) == y]
assert inv, "no inverse in block"
print("C5 ok: block identities hold; an inverse of f(1+D(g)) in the block is", sorted(inv[0]))
print("ALL CHECKS PASSED")
