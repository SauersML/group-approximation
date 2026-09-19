"""Exact word problem for G(K; al, be) = <y, t | y_1^K = [y_0^al, y_2^be]>, y_i = t^-i y t^i, [g,h] = g^-1 h^-1 g h.

N = normal closure of y is the directed union of segments S_[0,L] = <y_0..y_L> (after shifting indices).
S_[0,1] is free on y_0, y_1 (Freiheitssatz). For L >= 2, S_[0,L] is the HNN extension of S_[0,L-1] with
stable letter x = y_L and relation R_{L-2}:  y_L^-be y_{L-2}^al y_L^be = y_{L-2}^al y_{L-1}^K,
i.e. x^-1 P x = Q with (P, Q) = (a, b) if be = 1 and (b, a) if be = -1, where a = y_{L-2}^al, b = a y_{L-1}^K.
Britton's lemma decides equality; membership in <a> and <b> is decided by exponent maps:
 - an element of <y_{L-2}> lies in S_[0,L-2], whose stable letter (or free generator) is y_{L-2};
 - the y_{L-1}-exponent map of S_[0,L-1] sends b to K.
Words are tuples of (index, +-1).
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(100000)


def free_reduce(w):
    out = []
    for g in w:
        if out and out[-1][0] == g[0] and out[-1][1] == -g[1]:
            out.pop()
        else:
            out.append(g)
    return tuple(out)


def inv(w):
    return tuple((i, -e) for (i, e) in reversed(w))


def power(w, k):
    if k >= 0:
        return w * k
    return inv(w) * (-k)


def expsum(w, i):
    return sum(e for (j, e) in w if j == i)


class Tower:
    def __init__(self, K, al, be):
        self.K, self.al, self.be = K, al, be
        self.cache = {}

    def a(self, L):
        return ((L - 2, 1),) * self.al if self.al > 0 else ((L - 2, -1),) * (-self.al)

    def b(self, L):
        return self.a(L) + (((L - 1, 1),) * self.K if self.K > 0 else ((L - 1, -1),) * (-self.K))

    # membership: return k with u = g^k in S_[0,L-1], or None
    def mem_a(self, u, L):
        # a = y_{L-2}^al ; need u in S_[0,L-2]
        r = self.reduce(u, L - 1)
        if any(i == L - 1 for (i, _) in r):
            return None
        e = expsum(r, L - 2)
        if e % self.al:
            return None
        k = e // self.al
        if self.reduce(r + power(self.a(L), -k), L - 2) == ():
            return k
        return None

    def mem_b(self, u, L):
        e = expsum(u, L - 1)
        if e % self.K:
            return None
        k = e // self.K
        if self.reduce(u + power(self.b(L), -k), L - 1) == ():
            return k
        return None

    def reduce(self, w, L):
        """Britton-reduced form of w in S_[0,L] (base pieces reduced recursively)."""
        w = free_reduce(w)
        if L <= 1:
            return w
        key = (w, L)
        if key in self.cache:
            return self.cache[key]
        if self.be == 1:
            P, Q, memP, memQ = self.a(L), self.b(L), self.mem_a, self.mem_b
        else:
            P, Q, memP, memQ = self.b(L), self.a(L), self.mem_b, self.mem_a
        # stack of blocks: segs[0], x^e1, segs[1], ..., x^en, segs[n]
        segs = [()]
        stab = []
        for g in w:
            if g[0] != L:
                segs[-1] = segs[-1] + (g,)
                continue
            e = g[1]
            if stab and stab[-1] == -e:
                u = segs[-1]
                if e == 1:  # x^-1 u x, u in <P> -> Q^k
                    k = memP(u, L)
                    rep = power(Q, k) if k is not None else None
                else:  # x u x^-1, u in <Q> -> P^k
                    k = memQ(u, L)
                    rep = power(P, k) if k is not None else None
                if rep is not None:
                    segs.pop()
                    stab.pop()
                    segs[-1] = free_reduce(segs[-1] + rep)
                    continue
            segs[-1] = self.reduce(segs[-1], L - 1)
            stab.append(e)
            segs.append(())
        out = []
        for j, s in enumerate(segs):
            out.extend(self.reduce(s, L - 1))
            if j < len(stab):
                out.append((L, stab[j]))
        res = tuple(out)
        if len(self.cache) < 2_000_000:
            self.cache[key] = res
        return res

    def trivial_N(self, w):
        """w: word in y_i (any integer indices). Decide w == 1."""
        w = free_reduce(w)
        if not w:
            return True
        m = min(i for i, _ in w)
        w = tuple((i - m, e) for i, e in w)
        L = max(i for i, _ in w)
        return self.reduce(w, max(L, 1)) == ()


def yt_to_N(word):
    """word: string over y,Y,t,T (Y=y^-1,T=t^-1) with t-exponent 0 -> tuple over y_i; None if t-exp != 0."""
    p, out = 0, []
    for ch in word:
        if ch == 't':
            p += 1
        elif ch == 'T':
            p -= 1
        elif ch == 'y':
            out.append((-p, 1))
        elif ch == 'Y':
            out.append((-p, -1))
    return tuple(out) if p == 0 else None


def relator(K, al, be, j=0):
    """R_j as a word in y_i:  y_{j+1}^-K y_j^-al y_{j+2}^-be y_j^al y_{j+2}^be."""
    def pw(i, e):
        return ((i, 1 if e > 0 else -1),) * abs(e)
    return pw(j + 1, -K) + pw(j, -al) + pw(j + 2, -be) + pw(j, al) + pw(j + 2, be)


if __name__ == '__main__':
    import random
    for (K, al, be) in [(2, 1, 1), (2, 1, -1), (2, -1, 1), (3, 1, 1)]:
        T = Tower(K, al, be)
        assert T.trivial_N(relator(K, al, be)), (K, al, be)
        assert not T.trivial_N(((0, 1),))
        # random products of conjugates of relators must be trivial
        rng = random.Random(1)
        for trial in range(200):
            w = ()
            for _ in range(rng.randint(1, 3)):
                j = rng.randint(-2, 2)
                c = tuple((rng.randint(-1, 3), rng.choice([1, -1])) for _ in range(rng.randint(0, 3)))
                r = relator(K, al, be, j)
                if rng.random() < .5:
                    r = inv(r)
                w = w + inv(c) + r + c
            assert T.trivial_N(w), (K, al, be, w)
        print('ok', (K, al, be))
