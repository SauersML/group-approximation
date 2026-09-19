#!/usr/bin/env python3
"""Tiny GF(p^k) arithmetic with element integers 0..q-1 (base-p digits =
coefficients of a polynomial mod an irreducible f), plus vectorised rank."""
import numpy as np
import itertools


def _polymulmod(a, b, f, p):
    # a, b, f coefficient lists (low degree first), f monic of degree k
    k = len(f) - 1
    res = [0] * (2 * k)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                res[i + j] = (res[i + j] + ai * bj) % p
    for dgr in range(2 * k - 1, k - 1, -1):
        c = res[dgr]
        if c:
            for j in range(k + 1):
                res[dgr - k + j] = (res[dgr - k + j] - c * f[j]) % p
    return res[:k]


class GF:
    def __init__(self, p, k):
        self.p, self.k, self.q = p, k, p ** k
        q = self.q
        # find primitive polynomial by brute force
        for tail in itertools.product(range(p), repeat=k):
            f = list(tail) + [1]
            if f[0] == 0:
                continue
            # generate powers of x
            cur = [0] * k
            cur[0] = 1
            x = [0] * k
            if k > 1:
                x[1] = 1
            else:
                x[0] = (-f[0]) % p
            seen = set()
            ok = True
            exp = np.zeros(q - 1, dtype=np.int64)
            for n in range(q - 1):
                v = sum(c * p ** i for i, c in enumerate(cur))
                if v in seen:
                    ok = False
                    break
                seen.add(v)
                exp[n] = v
                cur = _polymulmod(cur, x, f, p)
            if ok and len(seen) == q - 1:
                break
        self.f = f
        self.exp = exp
        self.log = np.full(q, -1, dtype=np.int64)
        self.log[exp] = np.arange(q - 1)
        # addition table via digits (q up to ~ 1e5 would be too big: use digit arrays)
        self.digits = np.array([[(v // p ** i) % p for i in range(k)] for v in range(q)], dtype=np.int64)
        self.pw = np.array([p ** i for i in range(k)], dtype=np.int64)

    def add(self, a, b):
        return (((self.digits[a] + self.digits[b]) % self.p) @ self.pw)

    def neg(self, a):
        return (((-self.digits[a]) % self.p) @ self.pw)

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    def mul(self, a, b):
        a = np.asarray(a)
        b = np.asarray(b)
        out = np.zeros(np.broadcast(a, b).shape, dtype=np.int64)
        m = (a != 0) & (b != 0)
        la = np.broadcast_to(self.log[a], out.shape)
        lb = np.broadcast_to(self.log[b], out.shape)
        out[m] = self.exp[(la[m] + lb[m]) % (self.q - 1)]
        return out

    def inv(self, a):
        return int(self.exp[(-self.log[a]) % (self.q - 1)])

    def from_int(self, n):
        return (n % self.p)  # prime subfield element n mod p is the integer n%p

    def rank(self, M):
        M = np.array(M, dtype=np.int64)
        rows, cols = M.shape
        r = 0
        for c in range(cols):
            if r == rows:
                break
            piv = np.nonzero(M[r:, c])[0]
            if len(piv) == 0:
                continue
            i = r + piv[0]
            if i != r:
                M[[r, i]] = M[[i, r]]
            M[r] = self.mul(M[r], self.inv(int(M[r, c])))
            col = M[:, c].copy()
            col[r] = 0
            nz = np.nonzero(col)[0]
            if len(nz):
                prod = self.mul(col[nz][:, None], M[r][None, :])
                M[nz] = self.sub(M[nz], prod)
            r += 1
        return r
