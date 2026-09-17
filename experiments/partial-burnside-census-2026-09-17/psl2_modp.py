#!/usr/bin/env python3
"""Irreducible two-dimensional representations of Pi_R(2,5) over finite fields.

For each prime p (p != 2), work in F_{p^2} = F_p[i]/(i^2 - nr) with nr a
non-residue.  Allowed traces: the roots of t^2 - t - 1 and t^2 + t - 1 (order 5
in PSL_2) and +-2.  For each triple (tr a, tr b, tr ab) of allowed traces with
tr[a,b] != 2, build a = [[x,1],[-1,0]], b = [[0,t],[-1/t,y]] (t + 1/t = -z) over
F_{p^4} if needed... to stay in F_{p^2} we skip triples where z^2-4 is not a
square in F_{p^2}; every element of F_{p^2} ... is a square in F_{p^4}, so
those triples are handled by the second pass over F_{p^4}? No: t + 1/t = -z
always has a solution t in F_{p^4}, but the representation is conjugate into
SL_2 of the trace field, so the law check is field-independent.  We therefore
compute in F_{p^4} = F_{p^2}[j]/(j^2 - nr2) when needed.

Each irreducible pair is tested for g^5 = +-I on every reduced word of length
<= Rmax.  The script prints, per prime, the irreducible trace triples whose law
holds to radius >= 2, and the radius reached.

Usage: python3 psl2_modp.py pmax Rmax
"""
import sys
from itertools import product


def primes(n):
    s = [True] * (n + 1)
    s[0] = s[1] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            for j in range(i * i, n + 1, i):
                s[j] = False
    return [i for i in range(n + 1) if s[i]]


class F4:
    """F_{p^4} as polynomials in u of degree < 4 modulo an irreducible quartic.

    We find an irreducible monic quartic u^4 + c u^2 + d ... by brute force:
    use a random monic quartic and test it has no roots and no quadratic
    factor.  Elements are 4-tuples mod p."""

    def __init__(self, p):
        self.p = p
        self.mod = self.find_quartic()

    def find_quartic(self):
        p = self.p
        import random
        rnd = random.Random(12345 + p)
        while True:
            c = [rnd.randrange(p) for _ in range(4)]  # u^4 = -(c0 + c1 u + c2 u^2 + c3 u^3)
            if self.irreducible(c):
                return c

    def irreducible(self, c):
        p = self.p
        # no roots
        for r in range(p):
            v = (pow(r, 4, p) + c[3] * pow(r, 3, p) + c[2] * r * r + c[1] * r + c[0]) % p
            if v == 0:
                return False
        # no monic quadratic factor u^2 + e u + f
        for e in range(p):
            for f in range(p):
                # divide quartic by quadratic, check remainder zero
                q = [c[0], c[1], c[2], c[3], 1]
                for deg in range(4, 1, -1):
                    lead = q[deg]
                    if lead:
                        q[deg] = 0
                        q[deg - 1] = (q[deg - 1] - lead * e) % p
                        q[deg - 2] = (q[deg - 2] - lead * f) % p
                if q[0] % p == 0 and q[1] % p == 0:
                    return False
        return True

    def mul(self, x, y):
        p = self.p
        r = [0] * 7
        for i in range(4):
            if x[i]:
                for j in range(4):
                    r[i + j] += x[i] * y[j]
        c = self.mod
        for deg in range(6, 3, -1):
            lead = r[deg] % p
            if lead:
                r[deg] = 0
                for k in range(4):
                    r[deg - 4 + k] -= lead * c[k]
        return tuple(v % p for v in r[:4])

    def add(self, x, y):
        return tuple((a + b) % self.p for a, b in zip(x, y))

    def neg(self, x):
        return tuple((-a) % self.p for a in x)

    def const(self, a):
        return (a % self.p, 0, 0, 0)

    def pow(self, x, e):
        r = self.const(1)
        while e:
            if e & 1:
                r = self.mul(r, x)
            x = self.mul(x, x)
            e >>= 1
        return r

    def inv(self, x):
        return self.pow(x, self.p ** 4 - 2)

    def roots_quadratic(self, b, c):
        """roots of t^2 + b t + c in F_{p^4}, b, c elements."""
        p = self.p
        # brute force over elements is p^4: too big for large p; use sqrt via
        # Tonelli-style exponentiation in F_{p^4}.
        inv2 = self.const(pow(2, p - 2, p))
        disc = self.add(self.mul(b, b), self.neg(self.mul(self.const(4), c)))
        s = self.sqrt(disc)
        if s is None:
            return []
        mb = self.neg(b)
        r1 = self.mul(self.add(mb, s), inv2)
        r2 = self.mul(self.add(mb, self.neg(s)), inv2)
        return list({r1, r2})

    def sqrt(self, a):
        p = self.p
        q = p ** 4
        zero = self.const(0)
        if a == zero:
            return zero
        # Tonelli-Shanks in F_q
        s, t = 0, q - 1
        while t % 2 == 0:
            s += 1
            t //= 2
        if self.pow(a, (q - 1) // 2) != self.const(1):
            return None
        import random
        rnd = random.Random(7)
        while True:
            zc = tuple(rnd.randrange(p) for _ in range(4))
            if zc != zero and self.pow(zc, (q - 1) // 2) != self.const(1):
                break
        M = s
        c = self.pow(zc, t)
        tt = self.pow(a, t)
        R = self.pow(a, (t + 1) // 2)
        one = self.const(1)
        while tt != one:
            i = 0
            x = tt
            while x != one:
                x = self.mul(x, x)
                i += 1
            b = self.pow(c, 2 ** (M - i - 1))
            M = i
            c = self.mul(b, b)
            tt = self.mul(tt, c)
            R = self.mul(R, b)
        return R


def run_prime(p, Rmax):
    K = F4(p)
    one, zero = K.const(1), K.const(0)
    two, mtwo = K.const(2), K.const(-2)
    theta = set(K.roots_quadratic(K.const(-1), K.const(-1)) + K.roots_quadratic(K.const(1), K.const(-1)))
    allowed = list(theta | {two, mtwo})

    def mm(A, B):
        return ((K.add(K.mul(A[0][0], B[0][0]), K.mul(A[0][1], B[1][0])),
                 K.add(K.mul(A[0][0], B[0][1]), K.mul(A[0][1], B[1][1]))),
                (K.add(K.mul(A[1][0], B[0][0]), K.mul(A[1][1], B[1][0])),
                 K.add(K.mul(A[1][0], B[0][1]), K.mul(A[1][1], B[1][1]))))

    def minv(A):
        return ((A[1][1], K.neg(A[0][1])), (K.neg(A[1][0]), A[0][0]))

    I = ((one, zero), (zero, one))
    mI = ((K.neg(one), zero), (zero, K.neg(one)))

    def ok(g):
        g5 = mm(g, mm(g, mm(g, mm(g, g))))
        return g5 == I or g5 == mI

    results = []
    for x, y, z in product(allowed, repeat=3):
        # t + 1/t = -z  <=> t^2 + z t + 1 = 0
        ts = K.roots_quadratic(z, one)
        if not ts:
            continue
        t = ts[0]
        a = ((x, one), (K.neg(one), zero))
        b = ((zero, t), (K.neg(K.inv(t)), y))
        c = mm(mm(a, b), mm(minv(a), minv(b)))
        trc = K.add(c[0][0], c[1][1])
        if trc == two:
            continue
        gens = [a, minv(a), b, minv(b)]
        invl = [1, 0, 3, 2]
        layer = [((), I)]
        reached = Rmax
        for L in range(1, Rmax + 1):
            new = []
            bad = False
            for w, g in layer:
                for s in range(4):
                    if w and invl[w[-1]] == s:
                        continue
                    h = mm(g, gens[s])
                    if not ok(h):
                        bad = True
                        break
                    new.append((w + (s,), h))
                if bad:
                    break
            if bad:
                reached = L - 1
                break
            layer = new
        if reached >= 2:
            results.append(((x[0], y[0], z[0]), reached))
    return results


def main():
    pmax, Rmax = int(sys.argv[1]), int(sys.argv[2])
    for p in primes(pmax):
        if p == 2:
            continue
        res = run_prime(p, Rmax)
        if res:
            best = max(r for _, r in res)
            print(f"p={p}: {len(res)} irreducible triples with law to radius >= 2; max radius {best}")
        else:
            print(f"p={p}: none")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
