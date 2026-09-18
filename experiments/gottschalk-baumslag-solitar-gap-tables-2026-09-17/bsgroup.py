"""Baumslag-Solitar group BS(p,q) = < a, t | t a^p t^-1 = a^q >, gcd(p,q) = 1, 1 < p < q.

Words are lists of nonzero ints: 1 = a, -1 = a^-1, 2 = t, -2 = t^-1.

* nf(word): the right normal form a^k t^e1 a^r1 ... t^ej a^rj (Britton reduced, remainders
  0 <= r < p after t, 0 <= r < q after t^-1). Two words are equal in G iff their normal forms agree.
* rfq(word): the image in H = Z[1/pq] x| Z (t acts by multiplication by q/p), the largest residually
  finite quotient of G. A word is trivial in every finite quotient of G iff its image in H is trivial.
"""
from fractions import Fraction


class BS:
    def __init__(self, p, q):
        self.p, self.q = p, q

    # ---------- word problem ----------
    def syllables(self, w):
        out = []  # tokens ('a', k) and ('t', e)
        for x in w:
            if abs(x) == 1:
                if out and out[-1][0] == 'a':
                    k = out[-1][1] + x
                    out.pop()
                    if k:
                        out.append(('a', k))
                else:
                    out.append(('a', x))
            else:
                e = 1 if x > 0 else -1
                self._push_t(out, e)
        return out

    def _push_t(self, out, e):
        p, q = self.p, self.q
        # try pinch: out ends with t^-e a^k  (or t^-e directly)
        if out and out[-1] == ('t', -e):
            out.pop()
            return
        if len(out) >= 2 and out[-1][0] == 'a' and out[-2] == ('t', -e):
            k = out[-1][1]
            # t a^(p j) t^-1 = a^(q j) ; t^-1 a^(q j) t = a^(p j)
            if -e == 1 and k % p == 0:
                val = q * (k // p)
            elif -e == -1 and k % q == 0:
                val = p * (k // q)
            else:
                out.append(('t', e))
                return
            out.pop(); out.pop()
            if out and out[-1][0] == 'a':
                k2 = out[-1][1] + val
                out.pop()
                if k2:
                    out.append(('a', k2))
            elif val:
                out.append(('a', val))
            return
        out.append(('t', e))

    def nf(self, w):
        syl = self.syllables(w)
        p, q = self.p, self.q
        # push a-powers leftwards: t a^r = a^(q j) t a^rho with r = p j + rho; t^-1 a^r = a^(p j) t^-1 a^rho, r = q j + rho
        res = []
        carry = 0
        for tok in reversed(syl):
            if tok[0] == 'a':
                carry += tok[1]
            else:
                e = tok[1]
                if e == 1:
                    j, rho = divmod(carry, p)
                    res.append(rho); res.append(1)
                    carry = q * j
                else:
                    j, rho = divmod(carry, q)
                    res.append(rho); res.append(-1)
                    carry = p * j
        res.append(carry)
        return tuple(reversed(res))

    def is_trivial(self, w):
        return self.nf(w) == (0,)

    # ---------- residually finite quotient ----------
    def rfq(self, w):
        lam = Fraction(self.q, self.p)
        x, i = Fraction(0), 0
        for c in w:
            if abs(c) == 1:
                x += c * lam ** i
            else:
                i += 1 if c > 0 else -1
        return (x, i)


def inv(w):
    return [-x for x in reversed(w)]


def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out


def ball(G, radius):
    """Distinct elements of the ball of given radius, as (normal form, shortest word)."""
    seen = {G.nf([]): []}
    frontier = [[]]
    for _ in range(radius):
        nxt = []
        for w in frontier:
            for x in (1, -1, 2, -2):
                if w and w[-1] == -x:
                    continue
                v = w + [x]
                k = G.nf(v)
                if k not in seen:
                    seen[k] = v
                    nxt.append(v)
        frontier = nxt
    return seen


def wstr(w):
    s = {1: 'a', -1: 'A', 2: 't', -2: 'T'}
    return ''.join(s[x] for x in w) or '1'


if __name__ == '__main__':
    G = BS(2, 3)
    r = [2, 1, 1, -2, -1, -1, -1]
    assert G.is_trivial(r)
    assert G.rfq(r) == (0, 0)
    c = [1, 2, 1, -2, -1, 2, -1, -2]  # [a, t a t^-1]
    assert not G.is_trivial(c) and G.rfq(c) == (0, 0)
    import random
    random.seed(1)
    # consistency: nf is a function of the element (random conjugates of relator are trivial)
    for _ in range(2000):
        u = [random.choice((1, -1, 2, -2)) for _ in range(random.randint(0, 8))]
        v = u + (r if random.random() < 0.5 else inv(r)) + inv(u)
        assert G.is_trivial(v), wstr(v)
        z = [random.choice((1, -1, 2, -2)) for _ in range(random.randint(0, 10))]
        y = z[:random.randint(0, len(z))]
        y2 = y + v + z[len(y):]
        assert G.nf(y2) == G.nf(z)
        assert G.rfq(y2) == G.rfq(z)
    print('ball sizes', [len(ball(G, k)) for k in range(5)])
    print('selftest ok')
