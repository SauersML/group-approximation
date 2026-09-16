"""Exact checks for the Guba-Sapir normal-form fellow-travel obstruction.

Run:  timeout 600 python3 check_witnesses.py [LMAX] [RADIUS]

Letters: x = x0, X = x0^-1, y = x1, Y = x1^-1.  A word s1...sk is the map
s1 o s2 o ... o sk (convention 'left' of plf.py), which satisfies the CFP
relators and the Guba-Sapir rules (checked in part 0).

Parts
 0  convention: relators and Guba-Sapir rules hold as map identities.
 1  witnesses: u_L = y x^L and v_L = x^L y x^-(L+1) y x^(L+1) lie in N and
    satisfy  u_L . y = v_L  in F.
 2  depth claims of the artifact (segment A, B, C) and the resulting lower
    bound  dist(y x^a, path(v_L)) >= (a-1)/2,  a = floor(L/2).
 3  Lemma A (|h| >= D(h) - 2) and the alpha/beta bounds, exhaustively on the
    ball of radius RADIUS (BFS word lengths are exact inside the ball).
 4  exact distances from y x^a to path(v_L) for small L, from the BFS ball.
 5  TSNF x1-example: x_n^-1 . x1 = x1 x_(n+1)^-1 and the synchronous distance
    lower bound n - 3 at time n - 1.
 6  uniqueness sanity check: N-words of length <= NLEN represent distinct
    elements (evidence only; uniqueness is Guba-Sapir's theorem).
"""
import re
import sys
from collections import deque

from plf import (GEN, ID, X0, X1, Ddom, Dran, alpha, beta, breakpoints,
                 comp, depth, inv, word_map, xp)

LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 40
RADIUS = int(sys.argv[2]) if len(sys.argv) > 2 else 9
NLEN = int(sys.argv[3]) if len(sys.argv) > 3 else 10

FAIL = []


def ok(cond, msg):
    if not cond:
        FAIL.append(msg)
        print('FAIL', msg)


INVL = {'x': 'X', 'X': 'x', 'y': 'Y', 'Y': 'y'}


def winv(w):
    return ''.join(INVL[c] for c in reversed(w))


BAD = re.compile(r'xX|Xx|yY|Yy|[yY]x+y|[yY]xx+Y')


def in_N(w):
    """Guba-Sapir normal forms: freely reduced, no y^e x^i y (i>=1) and no
    y^e x^(i+1) y^-1 (i>=1) as a subword (CGHJS, arXiv:1811.11691, Sec. 1)."""
    return BAD.search(w) is None


def lower_bound(h):
    return max(abs(alpha(h)), abs(beta(h)), Ddom(h) - 2, Dran(h) - 2, 0)


def xn(n):
    """x_n = x0^-(n-1) x1 x0^(n-1) as a word, n >= 1."""
    return xp(-(n - 1)) + 'y' + xp(n - 1)


def zm(m):
    """z_m = x0^m x1 x0^-m."""
    return xp(m) + 'y' + xp(-m)


# ---------------------------------------------------------------- part 0
print('== part 0: convention')
rel1 = 'x' + 'Y' + 'X' + 'y' + 'x' + 'X' + 'y' + 'x' + 'Y' + 'X' + 'y' + 'x'
# [x0 x1^-1, x0^-1 x1 x0] with [a,b] = a^-1 b^-1 a b
a = 'xY'
b = 'Xyx'
c = 'XXyxx'
ok(word_map(winv(a) + winv(b) + a + b) == ID, 'CFP relator 1')
ok(word_map(winv(a) + winv(c) + a + c) == ID, 'CFP relator 2')
for i in range(1, 7):
    for e in 'yY':
        ok(word_map(e + xp(i) + 'y') ==
           word_map(xp(i) + 'y' + xp(-i - 1) + e + xp(i + 1)),
           'y-rule size %d eps %s' % (i, e))
        ok(word_map(e + xp(i + 1) + 'Y') ==
           word_map(xp(i + 1) + 'Y' + xp(-i) + e + xp(i)),
           'y^-1-rule size %d eps %s' % (i, e))
# supports used in the artifact
for n in range(1, 8):
    f = word_map(xn(n))
    ok(breakpoints(f)[0] == 1 - __import__('fractions').Fraction(1, 2 ** n),
       'left end of supp x_%d' % n)
for m in range(1, 8):
    f = word_map(zm(m))
    ok(breakpoints(f)[0] == __import__('fractions').Fraction(1, 2 ** (m + 1)),
       'left end of supp z_%d' % m)
print('part 0 done')

# ---------------------------------------------------------------- part 1
print('== part 1: witnesses')
for L in range(1, LMAX + 1):
    u = 'y' + xp(L)
    v = xp(L) + 'y' + xp(-L - 1) + 'y' + xp(L + 1)
    ok(in_N(u) and in_N(v), 'membership L=%d' % L)
    ok(comp(word_map(u), X1) == word_map(v), 'u_L y = v_L, L=%d' % L)
print('part 1 done for L = 1..%d' % LMAX)

# ---------------------------------------------------------------- part 2
print('== part 2: depth claims and distance bound')
worst = []
for L in range(4, LMAX + 1):
    aa = L // 2
    m = L - aa
    p = word_map('y' + xp(aa))
    pinv = inv(p)
    v = xp(L) + 'y' + xp(-L - 1) + 'y' + xp(L + 1)
    best = None
    q = ID
    for t in range(len(v) + 1):
        if t > 0:
            q = comp(q, GEN[v[t - 1]])
        h = comp(pinv, q)
        lb = lower_bound(h)
        # segment bookkeeping and the specific depth claims
        if t <= L:
            j = t
            ok(alpha(h) == aa - j, 'alpha A L=%d j=%d' % (L, j))
            if j >= 1:
                ok(Ddom(h) >= j + 1, 'depth A L=%d j=%d' % (L, j))
        elif t <= 2 * L + 2:
            j = t - L - 1
            ok(alpha(h) == aa - L + j, 'alpha B L=%d j=%d' % (L, j))
            if j >= 1:
                ok(Ddom(h) >= j + 1, 'depth B L=%d j=%d' % (L, j))
        else:
            j = t - 2 * L - 3
            ok(alpha(h) == aa + 1 - j, 'alpha C L=%d j=%d' % (L, j))
            if j <= L:
                ok(Ddom(h) >= L + 2 - j, 'depth C L=%d j=%d' % (L, j))
        best = lb if best is None else min(best, lb)
    ok(best >= (aa - 1) / 2, 'distance bound L=%d' % L)
    worst.append((L, best, (aa - 1) / 2))
print('  L, min_q LB(p^-1 q), proven (a-1)/2:')
print('  ' + ' '.join('%d:%d/%.1f' % w for w in worst))
# synchronous difference at time L: |x_L^-1 x0| >= L - 1
for L in range(3, LMAX + 1):
    h = word_map(winv(xn(L)) + 'x')
    ok(Ddom(h) >= L + 1, 'sync depth L=%d' % L)
    u = 'y' + xp(L)
    v = xp(L) + 'y' + xp(-L - 1) + 'y' + xp(L + 1)
    ok(comp(inv(word_map(u[:L])), word_map(v[:L])) == h, 'sync element L=%d' % L)
print('part 2 done')

# ---------------------------------------------------------------- part 3
print('== part 3: Lemma A on the ball of radius %d' % RADIUS)
dist = {ID: 0}
frontier = deque([ID])
while frontier:
    g = frontier.popleft()
    d = dist[g]
    if d == RADIUS:
        continue
    for s in 'xXyY':
        h = comp(g, GEN[s])
        if h not in dist:
            dist[h] = d + 1
            frontier.append(h)
sizes = [0] * (RADIUS + 1)
tight = 0
for g, d in dist.items():
    sizes[d] += 1
    ok(d >= lower_bound(g), 'Lemma A / alpha-beta at element of length %d' % d)
    if d == max(Ddom(g), Dran(g)) - 2:
        tight += 1
print('  sphere sizes', sizes, ' elements with |h| = D(h)-2:', tight)
print('part 3 done')

# ---------------------------------------------------------------- part 4
print('== part 4: exact distances inside the ball')
for L in range(4, 17):
    aa = L // 2
    p = word_map('y' + xp(aa))
    pinv = inv(p)
    v = xp(L) + 'y' + xp(-L - 1) + 'y' + xp(L + 1)
    exact = []
    q = ID
    for t in range(len(v) + 1):
        if t > 0:
            q = comp(q, GEN[v[t - 1]])
        exact.append(dist.get(comp(pinv, q)))
    known = [e for e in exact if e is not None]
    mn = min(known) if known else None
    print('  L=%2d a=%d  min exact distance among q within radius: %s ;'
          ' number of q outside the ball: %d' % (L, aa, mn,
                                                  exact.count(None)))
print('part 4 done')

# ---------------------------------------------------------------- part 5
print('== part 5: TSNF x1-example')
for n in range(3, LMAX + 1):
    u = xp(-(n - 1)) + 'Y' + xp(n - 1)          # x_n^-1
    v = 'y' + xp(-n) + 'Y' + xp(n)               # x_1 x_(n+1)^-1
    ok(word_map(u) == inv(word_map(xn(n))), 'TSNF u n=%d' % n)
    ok(word_map(v) == comp(X1, inv(word_map(xn(n + 1)))), 'TSNF v n=%d' % n)
    ok(comp(word_map(u), X1) == word_map(v), 'TSNF u x1 = v n=%d' % n)
    h = comp(inv(word_map(u[:n - 1])), word_map(v[:n - 1]))
    ok(h == word_map(zm(n - 1) + 'x'), 'TSNF difference element n=%d' % n)
    ok(Ddom(h) >= n - 1, 'TSNF depth n=%d' % n)
print('part 5 done')

# ---------------------------------------------------------------- part 6
print('== part 6: N-words of length <= %d represent distinct elements' % NLEN)
seen = {}
count = 0
stack = [('', ID)]
dup = 0
while stack:
    w, g = stack.pop()
    count += 1
    if g in seen:
        dup += 1
        FAIL.append('duplicate %s %s' % (w, seen[g]))
    else:
        seen[g] = w
    if len(w) == NLEN:
        continue
    for s in 'xXyY':
        w2 = w + s
        if in_N(w2):
            stack.append((w2, comp(g, GEN[s])))
print('  N-words checked:', count, ' duplicates:', dup)
print('part 6 done')

print('TOTAL FAILURES:', len(FAIL))
sys.exit(1 if FAIL else 0)
