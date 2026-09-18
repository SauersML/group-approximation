"""Word problem for triangle-presentation groups G_T = < a_0..a_6 | a_x a_y a_z (x,y,z) in T >
via a length-2 string rewriting system; letters are (x, +1) / (x, -1).
Rules (all valid identities in G_T):
  R0  s s^-1 -> empty
  R1  a_x a_y -> a_z^-1          if (x,y,z) in T (cyclically)
  R2  a_y^-1 a_x^-1 -> a_z       if (x,y,z) in T
  R3  a_y^-1 a_z -> a_z' a_y'^-1 (y != z), p = unique vertex with arcs p->y, p->z,
      z' = T(p,y), y' = T(p,z):  a_z' a_p a_y = 1, a_p a_z a_y' = 1.
Termination: (length, #neg-before-pos pairs) decreases lexicographically.
check_confluence() verifies all critical pairs (overlaps of length 3), so by Newman's
lemma irreducible words are unique normal forms of group elements."""
import itertools

class A2Group:
    def __init__(self, T):
        self.T = {}
        pts = sorted({a for t in T for a in t})
        self.n = n = len(pts)
        assert pts == list(range(n))
        for t in set(tuple(t) for t in T):
            for i in range({t[0]} == set(t) and 1 or 3):
                u = t[i:] + t[:i]
                assert (u[0], u[1]) not in self.T
                self.T[(u[0], u[1])] = u[2]
        self.N = {x: {y for (a, y) in self.T if a == x} for x in range(n)}
        k = len(self.N[0])
        assert all(len(self.N[x]) == k for x in range(n)) and n == (k - 1) ** 2 + k
        self.p = {}
        for y in range(n):
            for z in range(n):
                if y != z:
                    ps = [p for p in range(n) if y in self.N[p] and z in self.N[p]]
                    assert len(ps) == 1, (y, z, ps)
                    self.p[(y, z)] = ps[0]

    def rule(self, a, b):
        (x, e), (y, f) = a, b
        if x == y and e == -f:
            return ()
        if e == 1 and f == 1 and (x, y) in self.T:
            return ((self.T[(x, y)], -1),)
        if e == -1 and f == -1 and (y, x) in self.T:   # a_x^-1 a_y^-1 = (a_y a_x)^-1 = a_z
            return ((self.T[(y, x)], 1),)
        if e == -1 and f == 1 and x != y:
            p = self.p[(x, y)]
            return ((self.T[(p, x)], 1), (self.T[(p, y)], -1))
        return None

    def reduce(self, w):
        w = list(w)
        i = 0
        while i < len(w) - 1:
            r = self.rule(w[i], w[i+1])
            if r is None:
                i += 1
            else:
                w[i:i+2] = list(r)
                i = max(i - 1, 0)
        return tuple(w)

    def mul(self, u, v):
        return self.reduce(tuple(u) + tuple(v))

    @staticmethod
    def inv(w):
        return tuple((x, -e) for (x, e) in reversed(w))

    def letters(self):
        return [(x, e) for x in range(self.n) for e in (1, -1)]

    def check_confluence(self):
        L = self.letters()
        n = 0
        for a, b, c in itertools.product(L, repeat=3):
            r1, r2 = self.rule(a, b), self.rule(b, c)
            if r1 is None or r2 is None:
                continue
            n += 1
            if self.reduce(r1 + (c,)) != self.reduce((a,) + r2):
                return False, (a, b, c)
        return True, n

    def check_relators(self):
        for (x, y), z in self.T.items():
            assert self.reduce(((x, 1), (y, 1), (z, 1))) == ()
        return True

    def ball(self, R):
        layers = [[()]]
        seen = {()}
        for r in range(R):
            nxt = []
            for w in layers[-1]:
                for s in self.letters():
                    u = self.mul(w, (s,))
                    if u not in seen:
                        seen.add(u); nxt.append(u)
            layers.append(nxt)
        return layers
