"""Exact word problems for the target groups used in target_search.py.

Every target is an HNN extension Q = <B, b | b^-1 u b = v> of a base group B with an exact
multiplication, along infinite cyclic subgroups <u>, <v>.  Britton's lemma decides the word
problem: a word is reduced by removing pinches b^-1 g b (g in <u>) and b g b^-1 (g in <v>);
a reduced word is trivial iff it has no b-letter and its base element is 1.

Words are strings over a, A, b, B (capital = inverse); a is the base generator, b the stable
letter.

  BG(k)   base BS(1,k) = <a, c | c^-1 a c = a^k>, u = a, v = c   (k = 2: the Baumslag-Gersten
          group <a, b | (a^b)^-1 a (a^b) = a^2>)
  BS(p,q) base Z = <a>, u = a^p, v = a^q
"""
from fractions import Fraction


class BG:
    """Base BS(1,k) as matrices [[1, beta], [0, k^n]], stored (beta, n)."""

    def __init__(self, k):
        self.k = k
        self.name = "BG(%d)" % k
        self.one = (Fraction(0), 0)
        self.gen = (Fraction(1), 0)

    def mul(self, g, h):
        (b1, n1), (b2, n2) = g, h
        return (b2 + b1 * Fraction(self.k) ** n2, n1 + n2)

    def inv(self, g):
        b, n = g
        return (-b * Fraction(self.k) ** (-n), -n)

    def pinch_down(self, g):
        """b^-1 g b: g in <a> -> c^m."""
        b, n = g
        if n == 0 and b.denominator == 1:
            return (Fraction(0), int(b))
        return None

    def pinch_up(self, g):
        """b g b^-1: g in <c> -> a^m."""
        b, n = g
        if b == 0:
            return (Fraction(n), 0)
        return None


class BS:
    """Base Z, u = a^p, v = a^q."""

    def __init__(self, p, q):
        self.p, self.q = p, q
        self.name = "BS(%d,%d)" % (p, q)
        self.one = 0
        self.gen = 1

    def mul(self, g, h):
        return g + h

    def inv(self, g):
        return -g

    def pinch_down(self, g):
        return g // self.p * self.q if g % self.p == 0 else None

    def pinch_up(self, g):
        return g // self.q * self.p if g % self.q == 0 else None


def reduce_word(G, w):
    """Britton-reduce the word w (string over aAbB); returns the stack [g0, e1, g1, ...]."""
    st = [G.one]
    for ch in w:
        if ch in "aA":
            x = G.gen if ch == "a" else G.inv(G.gen)
            st[-1] = G.mul(st[-1], x)
            continue
        e = 1 if ch == "b" else -1
        if len(st) >= 3 and st[-2] == -e:
            g = st[-1]
            h = G.pinch_down(g) if e == 1 else G.pinch_up(g)
            if h is not None:
                st.pop()
                st.pop()
                st[-1] = G.mul(st[-1], h)
                continue
        st.append(e)
        st.append(G.one)
    return st


def is_trivial(G, w):
    st = reduce_word(G, w)
    return len(st) == 1 and st[0] == G.one


def inv_word(w):
    return w[::-1].swapcase()
