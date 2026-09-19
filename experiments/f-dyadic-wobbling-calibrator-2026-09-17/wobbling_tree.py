#!/usr/bin/env python3
"""Wobbling calibrator for Thompson's F on the dyadic rationals (runtime: a few seconds).

Checks, exactly (Fractions), the finite facts behind
research/f-dyadic-orbit-geometry-cannot-force-extensive-amenability.md :

1. The block code {A,B,C} = {01, 011, 0111} is a suffix code, and phi(u) = .u1 (binary) is injective on
   block words u (checked on all words of <= 7 blocks).
2. The six prefix replacements c' -> c c' (c != c'), and the three root moves 1/2 -> .c1, are realised
   by explicit elements g of F: g is the PL map built from matching dyadic subdivisions. We verify that
   g is in F (dyadic breakpoints, slopes powers of 2, fixes 0 and 1), that g(.c'xi) = .cc'xi for random tails xi,
   and we bound its word length by an exact bidirectional BFS in the Schreier graph of F on D.
3. The resulting Lipschitz constant L of the tree embedding (max Schreier distance over tree edges) is
   reported, and random long tree edges are re-checked by BFS.
4. A Folner segment {2^-k/8 : 0 <= k < N} of the x0-ray is disjoint from Y and has 2 boundary edges.
"""
from fractions import Fraction as Q
import random, itertools

random.seed(20260917)
BLOCKS = {'A': '01', 'B': '011', 'C': '0111'}

def x0(t):
    if t <= Q(1, 2):
        return 2 * t if t <= Q(1, 4) else t + Q(1, 4)
    return t / 2 + Q(1, 2)

def x0i(t):
    if t <= Q(1, 2):
        return t / 2
    return t - Q(1, 4) if t <= Q(3, 4) else 2 * t - 1

def x1(t):
    if t <= Q(1, 2):
        return t
    return Q(1, 2) + x0(2 * t - 1) / 2

def x1i(t):
    if t <= Q(1, 2):
        return t
    return Q(1, 2) + x0i(2 * t - 1) / 2

GENS = [x0, x0i, x1, x1i]

def word_to_dyadic(w):
    """binary word w (ending in 1) -> dyadic .w"""
    return sum((Q(1, 2 ** (i + 1)) for i, ch in enumerate(w) if ch == '1'), Q(0))

def phi(u):
    return word_to_dyadic(''.join(BLOCKS[c] for c in u) + '1')

def ball(start, r):
    dist = {start: 0}
    frontier = [start]
    for d in range(1, r + 1):
        nxt = []
        for t in frontier:
            for g in GENS:
                s = g(t)
                if s not in dist:
                    dist[s] = d
                    nxt.append(s)
        frontier = nxt
    return dist

def schreier_distance(a, b, r=6):
    """exact distance if <= 2r, else None (bidirectional BFS)"""
    da, db = ball(a, r), ball(b, r)
    best = None
    for t, d in da.items():
        if t in db:
            v = d + db[t]
            best = v if best is None or v < best else best
    return best

# 1. suffix code and injectivity
codes = list(BLOCKS.values())
assert all(not a.endswith(b) for a in codes for b in codes if a != b), "not a suffix code"
seen = {}
for n in range(0, 8):
    for u in itertools.product('ABC', repeat=n):
        v = phi(u)
        assert v not in seen, (u, seen.get(v))
        seen[v] = u
print(f"[1] phi injective on {len(seen)} block words of <= 7 blocks; suffix code ok")

# 2. explicit elements for prefix replacements a -> b (a, b interior words)
def interval(w):
    lo = word_to_dyadic(w) if w else Q(0)
    return lo, lo + Q(1, 2 ** len(w))

def subdivision_around(w):
    """standard dyadic subdivision of [0,1] containing I_w: sibling intervals along the path"""
    left, right = [], []
    for i, ch in enumerate(w):
        sib = w[:i] + ('1' if ch == '0' else '0')
        (left if ch == '1' else right).append(interval(sib))
    return sorted(left), sorted(right)

def refine(ints, k):
    ints = list(ints)
    while len(ints) < k:           # halve the largest interval
        j = max(range(len(ints)), key=lambda i: ints[i][1] - ints[i][0])
        a, b = ints[j]
        m = (a + b) / 2
        ints[j:j + 1] = [(a, m), (m, b)]
    return ints

def element(a, b):
    La, Ra = subdivision_around(a)
    Lb, Rb = subdivision_around(b)
    assert La and Ra and Lb and Rb, "words must be interior"
    nl, nr = max(len(La), len(Lb)), max(len(Ra), len(Rb))
    P = refine(La, nl) + [interval(a)] + refine(Ra, nr)
    R = refine(Lb, nl) + [interval(b)] + refine(Rb, nr)
    pieces = list(zip(P, R))
    for (p0, p1), (q0, q1) in pieces:
        s = (q1 - q0) / (p1 - p0)
        assert s.numerator & (s.numerator - 1) == 0 and s.denominator & (s.denominator - 1) == 0
    def g(t):
        for (p0, p1), (q0, q1) in pieces:
            if p0 <= t <= p1:
                return q0 + (t - p0) * (q1 - q0) / (p1 - p0)
        raise ValueError
    return g, len(pieces)

L = 0
for c2, c in itertools.product('ABC', repeat=2):
    if c == c2:
        continue
    a, b = BLOCKS[c2], BLOCKS[c] + BLOCKS[c2]
    g, npieces = element(a, b)
    worst = 0
    for _ in range(40):
        xi = ''.join(random.choice('01') for _ in range(random.randint(0, 12))) + '1'
        assert g(word_to_dyadic(a + xi)) == word_to_dyadic(b + xi)
        d = schreier_distance(word_to_dyadic(a + xi), word_to_dyadic(b + xi))
        assert d is not None
        worst = max(worst, d)
    L = max(L, worst)
    print(f"[2] {c2}->{c}{c2}: g in F with {npieces} pieces maps .{a}xi to .{b}xi; max BFS distance {worst}")
for c in 'ABC':
    d = schreier_distance(Q(1, 2), phi(c))
    L = max(L, d)
    print(f"[2] root 1/2 -> phi({c}) = {phi(c)}: distance {d}")

# 3. random long tree edges (reduced words in Z/2*Z/2*Z/2, newest letter prepended)
for _ in range(60):
    u = []
    for _ in range(random.randint(1, 9)):
        u.insert(0, random.choice([c for c in 'ABC' if not u or c != u[0]]))
    c = random.choice([c for c in 'ABC' if c != u[0]])
    d = schreier_distance(phi(u), phi([c] + u))
    assert d is not None and d <= L, (u, c, d)
print(f"[3] Lipschitz constant of the tree embedding: L = {L} (random long edges all <= L)")

# 4. Folner segment of the x0-ray, disjoint from Y (Y lies in [1/4, 1/2])
N = 200
seg = [Q(1, 8) / 2 ** k for k in range(N)]
S = set(seg)
assert all(not (Q(1, 4) <= t <= Q(1, 2)) for t in seg)
boundary = sum(1 for t in seg for g in GENS if g(t) not in S)
print(f"[4] x0-ray segment of {N} points misses Y; boundary edges (x0, x1 and their inverses) = {boundary}")
