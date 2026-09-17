#!/usr/bin/env python3
"""Cyclic Andrews-Curtis search in G = Z/m * Z/n (m or n = 0 means Z, i.e. free factor).

A state is an unordered pair of conjugacy classes of G up to inversion
(AC3 conjugates each coordinate independently; AC2 inverts; swaps are AC-derivable
up to inversion).  A move replaces the class of a by the class of
(c a c^{-1}) * (d b^{+-1} d^{-1}) for representatives obtained by conjugating the
cyclically reduced word by a prefix (split inside syllables allowed).  Every move is
a composite of AC moves, so a found path is a genuine AC path.
Target: one class is x^{+-1} or y^{+-1} and the other coordinate's exponent sum in
the complementary factor is +-1 (then the pair is AC-equivalent to (x,y)).
Syllables: code (0,k) = x^k, (1,l) = y^l, word = tuple of codes.
Usage: cyc.py m n aword bword [maxstates] [maxlen]
"""
import sys, heapq

class G:
    def __init__(self, m, n):
        self.o = (m, n)
    def norm(self, t, e):
        o = self.o[t]
        return e % o if o else e
    def mul(self, u, w):
        u = list(u); i = 0
        while u and i < len(w) and u[-1][0] == w[i][0]:
            t = w[i][0]; e = self.norm(t, u[-1][1] + w[i][1]); u.pop(); i += 1
            if e:
                u.append((t, e)); break
        return tuple(u) + tuple(w[i:])
    def inv(self, u):
        return tuple((t, self.norm(t, -e)) for (t, e) in reversed(u))
    def word(self, s):
        r = ()
        for ch in s:
            r = self.mul(r, (({"x": 0, "X": 0, "y": 1, "Y": 1}[ch], 1 if ch.islower() else -1),))
            r = tuple((t, self.norm(t, e)) for t, e in r)
        return r
    def cyc(self, u):
        u = tuple(u)
        while len(u) >= 2 and u[0][0] == u[-1][0]:
            u = self.mul(u[-1:], u[:-1])
        return u
    def reps(self, u):
        """all cyclic rotations incl. syllable splits (u cyclically reduced)."""
        L = len(u); out = set()
        if L == 1:
            return {u}
        for i in range(L):
            r = u[i:] + u[:i]
            out.add(r)
            t, e = r[0]
            o = self.o[t]
            splits = range(1, o) if o else range(1, abs(e))
            for j in splits:
                if o:
                    e1, e2 = j, (e - j) % o
                else:
                    e1 = j if e > 0 else -j; e2 = e - e1
                if e2 == 0:
                    continue
                out.add(((t, e2),) + r[1:] + ((t, e1),))
        return out
    def canon(self, u):
        u = self.cyc(u)
        if not u:
            return u
        best = None
        for w in (u, self.cyc(self.inv(u))):
            L = len(w)
            for i in range(L):
                r = w[i:] + w[:i]
                if best is None or r < best:
                    best = r
        return best

def wlen(g, u):
    tot = 0
    for t, e in u:
        o = g.o[t]
        tot += min(e % o, o - e % o) if o else abs(e)
    return tot

def expsum(g, u, t):
    s = sum(e for (tt, e) in u if tt == t)
    return g.norm(t, s)

def is_unit(g, t, e):
    o = g.o[t]
    return e in ((1, o - 1) if o else (1, -1))

def target(g, a, b):
    for p, q in ((a, b), (b, a)):
        if len(p) == 1 and is_unit(g, *p[0]) and is_unit(g, 1 - p[0][0], expsum(g, q, 1 - p[0][0])):
            return True
    return False

def search(m, n, aw, bw, maxstates=500000, maxlen=12, verbose=True):
    g = G(m, n)
    a, b = g.canon(g.word(aw)), g.canon(g.word(bw))
    st = tuple(sorted((a, b)))
    seen = {st: None}
    heap = [(wlen(g, a) + wlen(g, b), 0, st)]; cnt = 0
    while heap and len(seen) < maxstates:
        _, _, s = heapq.heappop(heap)
        a, b = s
        if target(g, a, b):
            path = []
            while s is not None:
                path.append(s); s = seen[s]
            return True, len(seen), path[::-1]
        for p, q in ((a, b), (b, a)):
            rq = g.reps(q) | g.reps(g.cyc(g.inv(q)))
            for pr in g.reps(p):
                for qr in rq:
                    c = g.canon(g.mul(pr, qr))
                    if not c or wlen(g, c) > maxlen:
                        continue
                    ns = tuple(sorted((c, q)))
                    if ns not in seen:
                        seen[ns] = s; cnt += 1
                        heapq.heappush(heap, (wlen(g, c) + wlen(g, q), cnt, ns))
    return False, len(seen), None

def fmt(u):
    return ".".join("%s^%d" % ("xy"[t], e) for t, e in u) or "1"

if __name__ == "__main__":
    m, n = int(sys.argv[1]), int(sys.argv[2])
    ms = int(sys.argv[5]) if len(sys.argv) > 5 else 500000
    ml = int(sys.argv[6]) if len(sys.argv) > 6 else 12
    ok, size, path = search(m, n, sys.argv[3], sys.argv[4], ms, ml)
    print("G=Z/%d*Z/%d (%s,%s) maxlen=%d: %s, %d states" % (m, n, sys.argv[3], sys.argv[4], ml, "AC-TRIVIAL" if ok else "not found", size))
    if ok and "-v" in sys.argv:
        for s in path:
            print("   ", fmt(s[0]), "|", fmt(s[1]))
