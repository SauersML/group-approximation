#!/usr/bin/env python3
"""Sanity checks for the Basilica group conventions used in
research/artifacts/basilica-group-torsion-free-2026-09-16.md.

Convention (Bartholdi-Virag, arXiv:math/0305262v1, Section 1): right actions
v -> v^g, products gh = first g then h, (g,h) acts as g on 0T and h on 1T,
eps swaps the two subtrees, and

    a = (1, b),    b = (1, a) eps.

Letters: 1 = a, -1 = a^-1, 2 = b, -2 = b^-1.  A word is trivial in B iff its
eps-part is trivial and both section words are trivial; the recursion
terminates because B is contracting.  Everything here is exact (no floating
point); the only bounded part is the torsion scan in check 7, which is
evidence, not proof.
"""
import itertools
import random
import sys
from functools import lru_cache

sys.setrecursionlimit(100000)

A, AI, Bb, BI = 1, -1, 2, -2
INV = {A: AI, AI: A, Bb: BI, BI: Bb}
# (index m of the nontrivial section, the section letter, eps-part)
LETTER = {
    A: (1, Bb, 0),   # a   = (1, b)
    AI: (1, BI, 0),  # a^-1 = (1, b^-1)
    Bb: (1, A, 1),   # b   = (1, a) eps
    BI: (0, AI, 1),  # b^-1 = (a^-1, 1) eps
}


def reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def inv(w):
    return tuple(INV[x] for x in reversed(w))


def mul(*ws):
    return reduce(sum((tuple(w) for w in ws), ()))


def power(w, k):
    if k < 0:
        return power(inv(w), -k)
    return reduce(tuple(w) * k)


def comm(x, y):  # [x,y] = x^-1 y^-1 x y
    return mul(inv(x), inv(y), x, y)


def conj(x, y):  # x^y = y^-1 x y
    return mul(inv(y), x, y)


def sections(w):
    """Return (w0, w1, parity) with w = (w0, w1) eps^parity as words."""
    s = [[], []]
    c = 0
    for x in w:
        m, letter, e = LETTER[x]
        s[(m + c) % 2].append(letter)
        c ^= e
    return reduce(s[0]), reduce(s[1]), c


@lru_cache(maxsize=None)
def trivial(w):
    w = reduce(w)
    if not w:
        return True
    w0, w1, c = sections(w)
    if c:
        return False
    return trivial(w0) and trivial(w1)


def equal(u, v):
    return trivial(mul(u, inv(v)))


a, b = (A,), (Bb,)


def sigma(w):  # substitution b -> a, a -> b^2
    img = {A: (Bb, Bb), AI: (BI, BI), Bb: (A,), BI: (AI,)}
    return reduce(sum((img[x] for x in w), ()))


def exp_a(w):
    return sum(1 if x == A else -1 if x == AI else 0 for x in w)


def check(name, ok):
    print(("PASS " if ok else "FAIL ") + name)
    if not ok:
        check.failed = True


check.failed = False

# 1. L-presentation relators sigma^n([a, a^b]) hold (Bartholdi-Virag Lemma 11).
r = comm(a, conj(a, b))
for n in range(6):
    check(f"sigma^{n}([a,a^b]) = 1  (word length {len(r)})", trivial(r))
    r = sigma(r)

# 2. Reading of the printed relator [[[a,t^-1],a],a] with b = t a t^-1:
#    under [x,y] = x^-1 y^-1 x y it is [[b,a],a]; under x y x^-1 y^-1 it would
#    be equivalent to a commuting with a^(b^2).
check("[[b,a],a] = 1", trivial(comm(comm(b, a), a)))
check("[a, a^(b^2)] != 1 (other commutator convention fails)",
      not trivial(comm(a, conj(a, power(b, 2)))))

# 3. b^2 = (a, a), a^b = (b^a, 1), [a, b^2] = (1, [b,a]), (x,1)^b = (1,x).
w0, w1, c = sections(power(b, 2))
check("b^2 = (a,a)", c == 0 and equal(w0, a) and equal(w1, a))
w0, w1, c = sections(conj(a, b))
check("a^b = (b^a, 1)", c == 0 and equal(w0, conj(b, a)) and trivial(w1))
w0, w1, c = sections(comm(a, power(b, 2)))
check("[a,b^2] = (1,[b,a])", c == 0 and trivial(w0) and equal(w1, comm(b, a)))
check("[b,a] != 1", not trivial(comm(b, a)))

# 4. sigma(g) = (a^{eps_a(g)}, g) on random words; images of generators.
check("sigma(a) = b^2 and sigma(b) = a",
      sigma(a) == (Bb, Bb) and sigma(b) == (A,))
random.seed(20260916)
ok = True
for _ in range(300):
    g = reduce(tuple(random.choice([A, AI, Bb, BI]) for _ in range(random.randint(0, 14))))
    w0, w1, c = sections(sigma(g))
    ok &= c == 0 and equal(w0, power(a, exp_a(g))) and equal(w1, g)
check("sigma(g) = (a^eps_a(g), g) on 300 random words", ok)

# 5. (x,1)^b = (1,x) for random x, realised through x = [b,a]^h with h in St(1).
ok = True
for _ in range(100):
    h = reduce(tuple(random.choice([A, AI, Bb, BI]) for _ in range(random.randint(0, 10))))
    y = conj(comm(b, a), h)
    # (1, y) is realised by [a,b^2]^{sigma(h)}, since sigma(h) = (a^e, h)
    one_y = conj(comm(a, power(b, 2)), sigma(h))
    w0, w1, c = sections(one_y)
    ok &= c == 0 and trivial(w0) and equal(w1, y)
    w0, w1, c = sections(conj(one_y, inv(b)))
    ok &= c == 0 and equal(w0, y) and trivial(w1)
check("1 x B' and B' x 1 realised in B (100 random conjugates of [b,a])", ok)

# 6. Words with all sections in one coordinate are a^k, a^k b, b^-1 a^k, b^-1 a^k b.
ok = True
for n in range(1, 9):
    for w in itertools.product([A, AI, Bb, BI], repeat=n):
        if reduce(w) != w:
            continue
        s = [[], []]
        cc = 0
        for x in w:
            m, letter, e = LETTER[x]
            s[(m + cc) % 2].append(letter)
            cc ^= e
        if s[0] and s[1]:
            continue
        core = list(w)
        if core and core[0] == BI:
            core = core[1:]
        if core and core[-1] == Bb:
            core = core[:-1]
        ok &= all(x in (A, AI) for x in core) and len(set(core)) <= 1
check("one-coordinate reduced words have the form b^-1? a^k b? (lengths 1..8)", ok)

# 7. Bounded torsion scan: g^k != 1 for 1 <= k <= 6, nontrivial reduced words g of length <= 7.
ok = True
count = 0
for n in range(1, 8):
    for w in itertools.product([A, AI, Bb, BI], repeat=n):
        if reduce(w) != w or trivial(w):
            continue
        count += 1
        ok &= all(not trivial(power(w, k)) for k in range(2, 7))
check(f"no g^k = 1 (2 <= k <= 6) among {count} nontrivial words of length <= 7", ok)

sys.exit(1 if check.failed else 0)
