"""Classical Garside normal form for B_n (permutation braids) and the Charney length
ell(g) = max(sup g, 0) - min(inf g, 0), which is the word length w.r.t. the simple elements
and their inverses.  Elements are pairs (p, factors) with factors a tuple of permutations
(tuples), none equal to Delta or identity, left-weighted:  g = Delta^p a_1 ... a_k.
Permutation product: (ab)(x) = a[b[x]]."""
import itertools

class Garside:
    def __init__(self, n):
        self.n = n
        self.e = tuple(range(n))
        self.w0 = tuple(range(n - 1, -1, -1))
        self.S = [p for p in itertools.permutations(range(n))]

    def mul(self, a, b):
        return tuple(a[b[x]] for x in range(self.n))

    def inv(self, a):
        r = [0] * self.n
        for i, ai in enumerate(a):
            r[ai] = i
        return tuple(r)

    def s(self, i):
        t = list(range(self.n)); t[i], t[i + 1] = t[i + 1], t[i]
        return tuple(t)

    def tau(self, a, k=1):
        if k % 2 == 0:
            return a
        return self.mul(self.w0, self.mul(a, self.w0))

    def desc_R(self, a):
        return {i for i in range(self.n - 1) if a[i] > a[i + 1]}

    def desc_L(self, b):
        bi = self.inv(b)
        return {i for i in range(self.n - 1) if bi[i] > bi[i + 1]}

    def slide(self, a, b):
        """make (a,b) left-weighted; returns (a',b') with a'b' = ab"""
        while True:
            dl = self.desc_L(b) - self.desc_R(a)
            if not dl:
                return a, b
            i = min(dl)
            si = self.s(i)
            a = self.mul(a, si)
            b = self.mul(si, b)

    def normalize(self, p, fac):
        fac = list(fac)
        changed = True
        while changed:
            changed = False
            for j in range(len(fac) - 1):
                a, b = self.slide(fac[j], fac[j + 1])
                if (a, b) != (fac[j], fac[j + 1]):
                    fac[j], fac[j + 1] = a, b
                    changed = True
        # strip leading Delta, trailing identity
        k = 0
        while k < len(fac) and fac[k] == self.w0:
            k += 1
        # leading Deltas: Delta^k a... ; they are already on the left
        p += k
        fac = fac[k:]
        while fac and fac[-1] == self.e:
            fac.pop()
        # identities can only be at the end after left-weighting; deltas only at the start
        return (p, tuple(fac))

    def times_simple(self, g, a):
        p, fac = g
        return self.normalize(p, fac + (a,))

    def times_delta_pow(self, g, q):
        p, fac = g
        return (p + q, tuple(self.tau(f, q) for f in fac))

    def times(self, g, h):
        q, hf = h
        r = self.times_delta_pow(g, q)
        p, fac = r
        return self.normalize(p, fac + hf)

    def inverse(self, g):
        # g = Delta^p a_1..a_k ; g^{-1} = a_k^{-1} .. a_1^{-1} Delta^{-p}
        # a^{-1} = Delta^{-1} (Delta a^{-1}) with Delta a^{-1} <-> w0 * inv(a)
        p, fac = g
        res = (0, ())
        for a in reversed(fac):
            res = self.times_delta_pow(res, -1)
            res = self.times_simple(res, self.mul(self.w0, self.inv(a)))
        return self.times_delta_pow(res, -p)

    def gen(self, i, sign=1):
        if sign == 1:
            return (0, (self.s(i),))
        return self.normalize(-1, (self.mul(self.w0, self.s(i)),))

    def word(self, w):
        g = (0, ())
        for x in w:
            g = self.times(g, self.gen(abs(x) - 1, 1 if x > 0 else -1))
        return g

    def inf(self, g):
        return g[0]

    def sup(self, g):
        return g[0] + len(g[1])

    def length(self, g):
        return max(self.sup(g), 0) - min(self.inf(g), 0)

    def simples(self):
        out = []
        for a in self.S:
            if a != self.e:
                out.append(self.normalize(0, (a,)))
                out.append(self.inverse(self.normalize(0, (a,))))
        return out
