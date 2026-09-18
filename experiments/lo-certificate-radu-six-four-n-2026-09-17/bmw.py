"""One-vertex complete VH square complexes (BMW groups) with exact normal forms.

A group is given by a-letters 1..m (inverse -i) and b-letters 1..n (inverse -j) and
m*n geometric squares, each a relator word x1 y1 x2 y2 (x a-letters, y b-letters).
Completeness of the link means: for every b-letter v and a-letter u there is exactly one
square with v u = u' v'.  Then every element is uniquely A*B with A a reduced a-word and
B a reduced b-word (Bridson-Wise normal form lemma), and multiplication is computed by
pushing letters through the squares.
"""


def parse_word(s):
    """'a1 b2 a3^-1 b4^-1' -> list of ('a',1),('b',2),('a',-3),('b',-4)."""
    out = []
    for tok in s.split():
        e = 1
        if '^-1' in tok:
            e = -1
            tok = tok.replace('^-1', '')
        out.append((tok[0], e * int(tok[1:])))
    return out


def inv_word(w):
    return [(t, -x) for (t, x) in reversed(w)]


class BMW:
    def __init__(self, m, n, relators):
        self.m, self.n = m, n
        self.swap = {}  # (v, u) -> (u', v') with v u = u' v'
        for r in relators:
            w = parse_word(r) if isinstance(r, str) else r
            assert len(w) == 4
            for ww in (w, inv_word(w)):
                for k in range(4):
                    c = ww[k:] + ww[:k]
                    # c = z1 z2 z3 z4 = 1.  If z1 is a b-letter: v u = z4^-1 z3^-1
                    if c[0][0] == 'b':
                        v, u = c[0][1], c[1][1]
                        assert c[1][0] == 'a' and c[2][0] == 'b' and c[3][0] == 'a'
                        res = (-c[3][1], -c[2][1])  # u' = z4^-1 (a), v' = z3^-1 (b)
                        if (v, u) in self.swap:
                            assert self.swap[(v, u)] == res, ("inconsistent square", r)
                        self.swap[(v, u)] = res
        need = 2 * m * 2 * n
        assert len(self.swap) == need, ("link not complete bipartite", len(self.swap), need)

    @staticmethod
    def reduce(w):
        out = []
        for x in w:
            if out and out[-1] == -x:
                out.pop()
            else:
                out.append(x)
        return tuple(out)

    def push(self, B, A):
        """B*A (B b-word, A a-word) -> (A', B') with B*A = A'*B'."""
        B = list(B)
        Aout = []
        sw = self.swap
        for u in A:
            for i in range(len(B) - 1, -1, -1):
                u, B[i] = sw[(B[i], u)]
            Aout.append(u)
        return tuple(Aout), tuple(B)

    def mul(self, g, h):
        A1, B1 = g
        A2, B2 = h
        A2p, B1p = self.push(B1, A2)
        return (self.reduce(A1 + A2p), self.reduce(B1p + B2))

    def inv(self, g):
        A, B = g
        Bi = tuple(-x for x in reversed(B))
        Ai = tuple(-x for x in reversed(A))
        return self.push(Bi, Ai)

    def gen_a(self, i):
        return ((i,), ())

    def gen_b(self, j):
        return ((), (j,))

    def reduced_words(self, k, length):
        """All reduced words of given length over letters +-1..k."""
        letters = [x for i in range(1, k + 1) for x in (i, -i)]
        words = [()]
        for _ in range(length):
            words = [w + (x,) for w in words for x in letters if not (w and w[-1] == -x)]
        return words


RATTAGGI_INCOHERENT = [
    "a1 b1 a2^-1 b2^-1", "a1 b2 a1^-1 b1^-1", "a1 b3 a2^-1 b3^-1", "a1 b4 a1^-1 b4^-1", "a1 b5 a2^-1 b5",
    "a1 b5^-1 a4 b5^-1", "a1 b3^-1 a2^-1 b2", "a1 b1^-1 a2^-1 b3", "a2 b2 a2^-1 b1^-1", "a2 b4 a2^-1 b4^-1",
    "a2 b5 a5^-1 b5", "a3 b1 a4^-1 b2^-1", "a3 b2 a3^-1 b1^-1", "a3 b3 a4^-1 b3^-1", "a3 b4 a4 b4",
    "a3 b5 a4 b4^-1", "a3 b5^-1 a6^-1 b5^-1", "a3 b4^-1 a4 b5", "a3 b3^-1 a4^-1 b2", "a3 b1^-1 a4^-1 b3",
    "a4 b2 a4^-1 b1^-1", "a5 b1 a5^-1 b1^-1", "a5 b2 a5 b3^-1", "a5 b3 a6^-1 b5", "a5 b4 a5^-1 b4^-1",
    "a5 b5 a6^-1 b2^-1", "a5 b2^-1 a6 b3", "a6 b1 a6^-1 b3", "a6 b2 a6^-1 b4^-1", "a6 b4 a6^-1 b1",
]


def product_group(m, n):
    return [[('a', i), ('b', j), ('a', -i), ('b', -j)] for i in range(1, m + 1) for j in range(1, n + 1)]


# Rattaggi, "A finitely presented torsion-free simple group", arXiv:math/0411546, Example R_Delta (Wise's D)
WISE_D = [
    "a1 b1 a2^-1 b2^-1", "a1 b2 a1^-1 b1^-1", "a1 b3 a2^-1 b3^-1", "a1 b3^-1 a2^-1 b2",
    "a1 b1^-1 a2^-1 b3", "a2 b2 a2^-1 b1^-1", "a3 b1 a4^-1 b2^-1", "a3 b2 a3^-1 b1^-1",
    "a3 b3 a4^-1 b3^-1", "a3 b3^-1 a4^-1 b2", "a3 b1^-1 a4^-1 b3", "a4 b2 a4^-1 b1^-1",
]
# Sigma, a (12,8)-group; Sigma_0 = ker(Sigma -> Z/2 x Z/2) is simple (loc. cit., Theorem ThSimple)
RATTAGGI_SIGMA = WISE_D + [
    "a1 b4 a3 b4", "a1 b4^-1 a2 b4^-1", "a2 b4 a5 b4", "a3 b4^-1 a4^-1 b4^-1",
    "a4 b4^-1 a5 b4^-1", "a5 b1 a6^-1 b2", "a5 b2 a6^-1 b2^-1", "a5 b3 a5^-1 b3^-1",
    "a5 b2^-1 a6^-1 b1^-1", "a5 b1^-1 a6^-1 b1", "a6 b3 a6^-1 b4^-1", "a6 b4 a6^-1 b3",
]
# (6,6)-group acting locally like A_6 (loc. cit.); NST holds, Lambda_0 conjectured simple
RATTAGGI_A6 = [
    "a1 b1 a1^-1 b1^-1", "a1 b2 a1^-1 b3^-1", "a1 b3 a2 b2^-1",
    "a1 b3^-1 a3^-1 b2", "a2 b1 a3^-1 b2^-1", "a2 b2 a3^-1 b3^-1",
    "a2 b3 a3^-1 b1", "a2 b3^-1 a3 b2", "a2 b1^-1 a3^-1 b1^-1",
]
# Radu, arXiv:1712.01091, Section 6.1, Figure: the non-residually-finite torsion-free (4,4)-group Gamma_{4,4}
RADU_44 = ["a1 b1 a2^-1 b1", "a1 b2 a2 b2^-1", "a1 b2^-1 a2^-1 b1^-1", "a1 b1^-1 a2^-1 b2"]
# Radu, loc. cit., Corollary C(i): a (6,6)-group with a simple subgroup of index 4 (contains Gamma_{4,4})
RADU_66 = RADU_44 + ["a1 b3 a1 b3^-1", "a2 b3 a2 b3", "a2 b3^-1 a3 b3^-1", "a3 b1 a3^-1 b1^-1",
                     "a3 b2 a3 b3", "a3 b2^-1 a3 b2^-1"]
GROUPS = {
    "radu44": (2, 2, RADU_44),
    "radu66": (3, 3, RADU_66),
    "incoherent": (6, 5, RATTAGGI_INCOHERENT),
    "sigma": (6, 4, RATTAGGI_SIGMA),
    "a6": (3, 3, RATTAGGI_A6),
    "wiseD": (4, 3, WISE_D),
    "f2xf2": (2, 2, None),
}


def make_group(name):
    m, n, rel = GROUPS[name]
    return BMW(m, n, rel if rel is not None else product_group(m, n))
