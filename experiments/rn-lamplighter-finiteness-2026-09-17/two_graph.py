"""Check the one-vertex 2-graph model of V_2(Z/2 wr Z) = PAff(O; R).

O = F_2[[pi]], pi = 1 + t, R = F_2[t, 1/t, 1/pi].  An element of Aff(R) is
x -> u x + b with u = t^i pi^j and b in R.  The monoid

    P = { a : a(O) <= O and a(rho_*) is an ancestor of rho_* in T_0 x T_inf },
    rho_* = (F_2[[t]], t^{-1} F_2[[t^{-1}]]),

has degree d(a) = (-i, i + j) in N^2.  Explicitly, a = (i, j, b) lies in P iff
m = -i >= 0, n = i + j >= 0 and b is a Laurent polynomial with
ord_0 b >= -m and deg b <= n - 1.

Checks:
  (1) e_i f_j = f_i e_{i+j} for e_c(x) = (pi/t) x + c/t, f_c(x) = pi x + c.
  (2) |P_(m,n)| = 2^(m+n), and a -> a(O) is a bijection of P_(m,n) onto the
      balls of depth m+n in O.
  (3) Every word in e, f of degree (m,n) lies in P_(m,n); the words e^m f^n
      and f^n e^m each hit every element exactly once (unique factorisation).
  (4) For a in P and p <= d(a) the unique a' in P_p with a(O) <= a'(O)
      satisfies a'^{-1} a in P (existence half of unique factorisation).
  (5) Germs: for random g in Aff(R) with poles at pi and every mu in
      P_(M,M) with g mu (O) <= O, g mu lies in P once M is large.
Laurent polynomials over F_2 are pairs (mask, v) meaning t^v * mask(t).
"""
import itertools
import random
import sys


def norm(p):
    m, v = p
    if m == 0:
        return (0, 0)
    while m & 1 == 0:
        m >>= 1
        v += 1
    return (m, v)


def add(p, q):
    (a, va), (b, vb) = p, q
    if a == 0:
        return norm(q)
    if b == 0:
        return norm(p)
    v = min(va, vb)
    return norm(((a << (va - v)) ^ (b << (vb - v)), v))


def pmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r


def mul(p, q):
    return norm((pmul(p[0], q[0]), p[1] + q[1]))


def tpow(k):
    return (1, k)


def pipow(k):
    assert k >= 0
    r = 1
    for _ in range(k):
        r ^= r << 1
    return (r, 0)


def pdivmod(a, b):
    """Polynomial division over F_2 (masks)."""
    q = 0
    db = b.bit_length()
    while a and a.bit_length() >= db:
        s = a.bit_length() - db
        q ^= 1 << s
        a ^= b << s
    return q, a


def div_pi(p, k):
    """Return p / pi^k if it is a Laurent polynomial, else None."""
    m, v = p
    if m == 0:
        return (0, 0)
    q, r = pdivmod(m, pipow(k)[0])
    if r:
        return None
    return norm((q, v))


def ordz(p):
    return p[1] if p[0] else 10 ** 9


def deg(p):
    return p[1] + p[0].bit_length() - 1 if p[0] else -10 ** 9


ZERO = (0, 0)
ONE = (1, 0)


# Affine maps with multiplier t^i pi^j (j may be negative) and b = c / pi^k.
class Aff:
    def __init__(self, i, j, c, k=0):
        self.i, self.j = i, j
        # normalise c / pi^k to lowest terms in pi
        c = norm(c)
        while k > 0 and c[0] and div_pi(c, 1) is not None:
            c, k = div_pi(c, 1), k - 1
        if c == ZERO:
            k = 0
        self.c, self.k = c, k

    def key(self):
        return (self.i, self.j, self.c, self.k)

    def __eq__(self, o):
        return self.key() == o.key()

    def __hash__(self):
        return hash(self.key())

    def u_times(self, c, k):
        """u * c / pi^k as (numerator, pole order)."""
        num = mul(tpow(self.i), c)
        jj = self.j - k
        if jj >= 0:
            return mul(num, pipow(jj)), 0
        return num, -jj

    def __mul__(self, o):
        """(self o)(x) = self(o(x))."""
        n1, k1 = self.u_times(o.c, o.k)
        n2, k2 = self.c, self.k
        k = max(k1, k2)
        c = add(mul(n1, pipow(k - k1)), mul(n2, pipow(k - k2)))
        return Aff(self.i + o.i, self.j + o.j, c, k)

    def inv(self):
        # x -> u^{-1} x - u^{-1} b
        c, k = self.c, self.k + self.j  # b / pi^j  (then times t^{-i})
        c = mul(tpow(-self.i), c)
        if k < 0:
            c, k = mul(c, pipow(-k)), 0
        return Aff(-self.i, -self.j, c, k)

    def degree(self):
        return (-self.i, self.i + self.j)

    def in_P(self):
        m, n = self.degree()
        if m < 0 or n < 0 or self.k != 0:
            return False
        b = self.c
        return b == ZERO or (ordz(b) >= -m and deg(b) <= n - 1)

    def ball(self):
        """a(O) = b + pi^j O, recorded as (j, b mod pi^j as a polynomial)."""
        assert self.k == 0 and self.j >= 0
        m, v = self.c
        if m == 0 or self.j == 0:
            return (self.j, 0)
        mod = pipow(self.j)[0]
        x = m
        if v >= 0:
            x = pmul(x, 1 << v)
        else:
            tv = pdivmod(1 << (-v), mod)[1]
            inv = next(y for y in range(mod) if pdivmod(pmul(y, tv), mod)[1] == 1)
            x = pmul(x, inv)
        return (self.j, pdivmod(x, mod)[1])


def e(c):
    return Aff(-1, 1, (c, -1))


def f(c):
    return Aff(0, 1, (c, 0))


def P_elements(m, n):
    out = []
    for bits in range(2 ** (m + n)):
        b = norm((bits, -m))
        out.append(Aff(-m, m + n, b))
    return out


def main():
    ok = True
    # (1) factorisation rule
    for i, j in itertools.product((0, 1), repeat=2):
        if e(i) * f(j) != f(i) * e((i + j) % 2):
            print("rule fails", i, j)
            ok = False
    print("(1) e_i f_j = f_i e_{i+j}:", ok)
    for x in (e(0), e(1), f(0), f(1)):
        assert x.in_P()
    # (2), (3)
    for m in range(0, 5):
        for n in range(0, 5):
            Pmn = P_elements(m, n)
            assert all(a.in_P() and a.degree() == (m, n) for a in Pmn)
            balls = {a.ball() for a in Pmn}
            if len(balls) != 2 ** (m + n):
                print("ball map not injective", m, n)
                ok = False
            S = set(Pmn)
            for order in ("ef", "fe"):
                hit = {}
                for es in itertools.product((0, 1), repeat=m):
                    for fs in itertools.product((0, 1), repeat=n):
                        w = [e(c) for c in es]
                        v = [f(c) for c in fs]
                        word = w + v if order == "ef" else v + w
                        a = Aff(0, 0, ZERO)
                        for g in word:
                            a = a * g
                        hit[a] = hit.get(a, 0) + 1
                if set(hit) != S or any(c != 1 for c in hit.values()):
                    print("unique factorisation fails", m, n, order)
                    ok = False
    print("(2),(3) counts, ball bijection, unique factorisation for m,n<=4:", ok)
    rnd = random.Random(1)
    # (4) existence of factorisations, by definition of P
    for _ in range(300):
        m, n = rnd.randrange(0, 7), rnd.randrange(0, 7)
        a = rnd.choice(P_elements(m, n))
        p = (rnd.randrange(0, m + 1), rnd.randrange(0, n + 1))
        cands = [x for x in P_elements(*p) if (x.inv() * a).in_P()]
        if len(cands) != 1:
            print("factorisation count", len(cands), m, n, p)
            ok = False
    print("(4) unique left factor of every degree <= d(a):", ok)
    # (5) germs of Aff(R) are mu' mu^{-1}: sample mu in P_(M,M), M <= 16
    worst = 0
    tested = skipped = 0
    for _ in range(40):
        i, j = rnd.randrange(-3, 4), rnd.randrange(-3, 4)
        k = rnd.randrange(0, 3)
        c = norm((rnd.randrange(1, 64), rnd.randrange(-3, 3)))
        g = Aff(i, j, c, k)
        badM = []
        goodM = set()
        for M in range(0, 17):
            for _ in range(200):
                b = norm((rnd.randrange(2 ** (2 * M)), -M))
                mu = Aff(-M, 2 * M, b)
                gm = g * mu
                if gm.k == 0 and gm.j >= 0:
                    goodM.add(M)
                    if not gm.in_P():
                        badM.append(M)
                        break
        M0 = max(badM) + 1 if badM else 0
        if not goodM:
            skipped += 1  # g(O) and O are disjoint: no germ to test
            continue
        tested += 1
        if M0 > 14 or 16 not in goodM:
            print("germ check did not stabilise", g.key(), badM)
            ok = False
        worst = max(worst, M0)
    print("(5) g mu in P for sampled admissible mu of degree (M,M), all M >=", worst, "up to 16;", tested, "maps tested,", skipped, "with g(O) disjoint from O:", ok)
    print("ALL OK" if ok else "FAILURE")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
