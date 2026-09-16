"""Exact checks for the TSNF remark (artifact section 7).

Run:  timeout 600 python3 -B check_tsnf.py [NMAX] [NALL]

u = x^-(n-1) y^-1 x^(n-1)  (TSNF of x_n^-1),  v = y x^-n y^-1 x^n  (TSNF of
x_1 x_(n+1)^-1).  For 3 <= n <= NMAX checks  u y = v  as maps and, for
p = x^-k with k = n-1 (and every 1 <= k <= n-1 when n <= NALL), the depth
claims of the proof of Proposition 7.1 at every vertex q of P(v):
  (i)  q = y x^-j,             j >= 1        : Ddom(p^-1 q) >= j + 1,
  (ii) q = y x^-n y^-1 x^j,    j <= n - 1    : Ddom(p^-1 q) >= n - j + 1,
the alpha values, and min_q LB(p^-1 q) >= (k - 1)/2, where LB is the
max(|alpha|, |beta|, Ddom - 2, Dran - 2) lower bound of the artifact.
"""
import sys

from plf import GEN, ID, Ddom, Dran, alpha, beta, comp, inv, word_map, xp

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 30
NALL = int(sys.argv[2]) if len(sys.argv) > 2 else 12
FAIL = []


def ok(cond, msg):
    if not cond:
        FAIL.append(msg)
        print('FAIL', msg)


def lb(h):
    return max(abs(alpha(h)), abs(beta(h)), Ddom(h) - 2, Dran(h) - 2, 0)


def verts(w):
    out = [ID]
    q = ID
    for c in w:
        q = comp(q, GEN[c])
        out.append(q)
    return out


rows = []
for n in range(3, NMAX + 1):
    u = xp(-(n - 1)) + 'Y' + xp(n - 1)
    v = 'y' + xp(-n) + 'Y' + xp(n)
    ok(comp(word_map(u), GEN['y']) == word_map(v), 'u y = v, n=%d' % n)
    Pv = verts(v)
    ks = range(1, n) if n <= NALL else [n - 1]
    for k in ks:
        pinv = word_map(xp(k))          # (x^-k)^-1 = x^k
        best = None
        for t, q in enumerate(Pv):
            h = comp(pinv, q)
            if 1 <= t <= n + 1:          # q = y x^-j, j = t - 1
                j = t - 1
                ok(alpha(h) == j - k, 'alpha (i) n=%d k=%d j=%d' % (n, k, j))
                if j >= 1:
                    ok(Ddom(h) >= j + 1, 'depth (i) n=%d k=%d j=%d' % (n, k, j))
            elif t >= n + 2:             # q = y x^-n y^-1 x^j, j = t - n - 2
                j = t - n - 2
                ok(alpha(h) == n - k - j,
                   'alpha (ii) n=%d k=%d j=%d' % (n, k, j))
                if j <= n - 1:
                    ok(Ddom(h) >= n - j + 1,
                       'depth (ii) n=%d k=%d j=%d' % (n, k, j))
            b = lb(h)
            best = b if best is None else min(best, b)
        ok(best >= (k - 1) / 2, 'distance bound n=%d k=%d' % (n, k))
        if k == n - 1:
            rows.append((n, best, (n - 2) / 2))
print('n: min_q LB(x^(n-1) q) over q in P(v) / proven (n-2)/2')
print(' '.join('%d:%d/%.1f' % r for r in rows))
print('TOTAL FAILURES:', len(FAIL))
sys.exit(1 if FAIL else 0)
