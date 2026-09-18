"""Garside engine for spherical Artin groups A_Gamma (finite Coxeter type).

Elements of W are integers 0..|W|-1 (0 = identity).  A group element of A is a pair
(k, P): Delta^k * p where p is a positive element in left normal form P (tuple of
simples, none equal to e or w0).  Delta x = tau(x) Delta.

Exactness: multiplication, inversion and the membership tests below are exact
(Garside theory).  Tests of the form "g in A_Y A_X" are exact for a fixed padding
level K; positive answers are rigorous certificates.
"""
import math
from collections import deque


def _solve(B, rhs):
    n = len(B)
    M = [list(B[i]) + [rhs[i]] for i in range(n)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(M[r][c]))
        M[c], M[p] = M[p], M[c]
        for r in range(n):
            if r != c:
                f = M[r][c] / M[c][c]
                for k in range(c, n + 1):
                    M[r][k] -= f * M[c][k]
    return [M[i][n] / M[i][i] for i in range(n)]


class Coxeter:
    def __init__(self, n, mdict):
        self.n = n
        def m(i, j):
            if i == j:
                return 1
            return mdict.get((min(i, j), max(i, j)), 2)
        self.m = m
        B = [[-math.cos(math.pi / m(i, j)) if i != j else 1.0 for j in range(n)] for i in range(n)]
        rho = _solve(B, [1.0] * n)

        def refl(i, v):
            c = 2 * sum(B[i][k] * v[k] for k in range(n))
            w = list(v)
            w[i] -= c
            return w
        key = lambda v: tuple(round(x, 5) + 0.0 for x in v)
        vecs = [rho]
        index = {key(rho): 0}
        length = [0]
        word = [()]
        lmul = [[None] * n]
        q = deque([0])
        while q:
            w = q.popleft()
            for i in range(n):
                if lmul[w][i] is not None:
                    continue
                v = refl(i, vecs[w])
                kk = key(v)
                if kk not in index:
                    index[kk] = len(vecs)
                    vecs.append(v)
                    length.append(length[w] + 1)
                    word.append((i,) + word[w])
                    lmul.append([None] * n)
                    q.append(index[kk])
                u = index[kk]
                lmul[w][i] = u
                lmul[u][i] = w
        N = len(vecs)
        self.N = N
        self.length = length
        self.word = word          # reduced word, w = s_word[0] s_word[1] ...
        self.lmul = lmul          # lmul[w][i] = s_i w
        inv = [0] * N
        for w in range(N):
            x = 0
            for i in word[w]:
                x = lmul[x][i]    # builds s_{ik}...s_{i1}
            inv[w] = x
        self.inv = inv
        self.rmul = [[inv[lmul[inv[w]][i]] for i in range(n)] for w in range(N)]
        self.ld = [sum(1 << i for i in range(n) if length[lmul[w][i]] < length[w]) for w in range(N)]
        self.rd = [sum(1 << i for i in range(n) if length[self.rmul[w][i]] < length[w]) for w in range(N)]
        self.supp = [sum(1 << i for i in set(word[w])) for w in range(N)]
        self.w0 = max(range(N), key=lambda w: length[w])
        self.tau = [self.mul(self.mul(self.w0, w), self.w0) for w in range(N)]
        self._dcache = [self.mul(inv[w], self.w0) for w in range(N)]   # partial(a) = a^{-1} w0
        self._np = {}

    def mul(self, a, b):
        x = a
        for i in self.word[b]:
            x = self.rmul[x][i]
        return x

    def elt(self, letters):
        x = 0
        for i in letters:
            x = self.rmul[x][i]
        return x

    def meet(self, u, v):
        """left gcd (prefix meet) of simples"""
        res = 0
        while True:
            c = self.ld[u] & self.ld[v]
            if not c:
                return res
            i = (c & -c).bit_length() - 1
            res = self.rmul[res][i]
            u = self.lmul[u][i]
            v = self.lmul[v][i]

    def parabolic_prefix(self, w, mask):
        """maximal prefix of w lying in W_mask"""
        t = 0
        while True:
            c = self.ld[w] & mask
            if not c:
                return t
            i = (c & -c).bit_length() - 1
            t = self.rmul[t][i]
            w = self.lmul[w][i]

    def normpair(self, a, b):
        key = a * self.N + b
        r = self._np.get(key)
        if r is None:
            t = self.meet(self._dcache[a], b)
            r = (self.mul(a, t), self.mul(self.inv[t], b))
            self._np[key] = r
        return r

    def parabolic_w0(self, mask):
        t = 0
        while True:
            c = mask & ~self.rd[t]
            if not c:
                return t
            i = (c & -c).bit_length() - 1
            t = self.rmul[t][i]


class Artin:
    """group elements are (k, P) = Delta^k * P, P a left normal form tuple"""

    def __init__(self, W):
        self.W = W
        self.one = (0, ())

    def _append(self, k, L, y):
        W = self.W
        if y == 0:
            return k, L
        R = []
        cur = y
        for i in range(len(L) - 1, -1, -1):
            a2, b2 = W.normpair(L[i], cur)
            R.append(b2)
            cur = a2
        out = [cur] + R[::-1]
        j = 0
        while j < len(out) and out[j] == W.w0:
            j += 1
        k += j
        out = out[j:]
        while out and out[-1] == 0:
            out.pop()
        return k, tuple(out)

    def tau_list(self, L, m):
        if m % 2 == 0:
            return L
        t = self.W.tau
        return tuple(t[x] for x in L)

    def mul(self, g, h):
        k, P = g
        m, Q = h
        P = self.tau_list(P, m)
        k = k + m
        for y in Q:
            k, P = self._append(k, P, y)
        return (k, P)

    def mulmany(self, *gs):
        r = self.one
        for g in gs:
            r = self.mul(r, g)
        return r

    def simple(self, w):
        W = self.W
        if w == W.w0:
            return (1, ())
        if w == 0:
            return self.one
        return (0, (w,))

    def gen(self, i):
        return self.simple(self.W.lmul[0][i])

    def inv(self, g):
        W = self.W
        k, P = g
        r = self.one
        for a in reversed(P):
            r = self.mul(r, (-1, self._tp((W._dcache[a],))))
        return self.mul(r, (-k, ()))

    def _tp(self, L):
        t = self.W.tau
        return tuple(t[x] for x in L)

    def word(self, letters):
        """letters: nonzero ints, +i -> s_{i-1}, -i -> s_{i-1}^{-1}"""
        r = self.one
        for l in letters:
            g = self.gen(abs(l) - 1)
            r = self.mul(r, g if l > 0 else self.inv(g))
        return r

    def positive_list(self, g):
        k, P = g
        if k < 0:
            return None
        return (self.W.w0,) * k + P

    def normalize_list(self, L):
        k, P = 0, ()
        for y in L:
            k, P = self._append(k, P, y)
        return (k, P)

    def in_parabolic_positive(self, g, mask):
        L = self.positive_list(g)
        if L is None:
            return False
        return all((self.W.supp[x] & ~mask) == 0 for x in L)

    def strip_left_parabolic(self, g, mask):
        """g positive; return (x, r) with g = x r, x the maximal left A_mask^+ divisor"""
        W = self.W
        x = self.one
        while True:
            L = self.positive_list(g)
            if not L:
                return x, g
            t = W.parabolic_prefix(L[0], mask)
            if t == 0:
                return x, g
            x = self.mul(x, self.simple(t))
            g = self.normalize_list((W.mul(W.inv[t], L[0]),) + tuple(L[1:]))

    def in_product(self, g, maskY, maskX, K):
        """exact test: Delta_Y^{2K} g Delta_X^{2K} in A_Y^+ A_X^+ (implies g in A_Y A_X)"""
        W = self.W
        dY = self.simple(W.parabolic_w0(maskY))
        dX = self.simple(W.parabolic_w0(maskX))
        h = g
        for _ in range(2 * K):
            h = self.mul(dY, h)
            h = self.mul(h, dX)
        if h[0] < 0:
            return False
        x, r = self.strip_left_parabolic(h, maskY)
        return self.in_parabolic_positive(r, maskX)

    def in_parabolic(self, g, mask, K):
        """exact test: Delta_X^{2K} g in A_X^+ (implies g in A_X); for K>=K0 answer stabilises"""
        W = self.W
        dX = self.simple(W.parabolic_w0(mask))
        h = g
        for _ in range(2 * K):
            h = self.mul(dX, h)
        return self.in_parabolic_positive(h, mask)

    def rev(self, g):
        """anti-automorphism reversing words (fixes Delta)"""
        W = self.W
        k, P = g
        k2, Q = self.normalize_list(tuple(W.inv[a] for a in reversed(P)))
        return self._rev_fix(k, k2, Q)

    def _rev_fix(self, k, k2, Q):
        # rev(Delta^k p) = rev(p) Delta^k = Delta^k tau^k(rev p)
        return (k + k2, self.tau_list(Q, k))

    def coset_key(self, g, mask, Nb=12):
        """canonical key of the left coset g A_mask (exact if Delta^Nb g is positive)"""
        h = self.mul((Nb, ()), g)
        assert h[0] >= 0, "raise Nb"
        x, r = self.strip_left_parabolic(self.rev(h), mask)
        return self.rev(r)
