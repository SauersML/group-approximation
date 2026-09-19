#!/usr/bin/env python3
"""Bounded search for hidden relations in K_2 = <GL_2(Z), diag(2,1), sigma_2>.

Generators of N = <<GL_2(Z)>>: conjugates sigma_2^j M sigma_2^-j, M in {X, X^-1, Y, Y^-1}
(elementary matrices), |j| <= J, plus the signed permutations W, D (which commute with sigma_2).
All of them are degree-0 elements of N, so every word lies in N.

Elements are compared through their images of a fixed probe set of integer points.
A left-linear normal key detects words W1, W2 with W1 = L W2 on the probes; then
L = W1 W2^-1 is in N, and |det L| != 1 would be a hidden relation (Pi_2 -> K_2 not injective).
A second table is keyed by r o W' (r the three-line fixer of Attempt 3); a match W = L r W'
gives |det L|/2 in I_2, which is new unless |det L| = 2.
Probe agreement is a FILTER, not a proof: every hit must be re-verified on random points
and then certified symbolically.
"""
import sys, time, bisect, random
from fractions import Fraction as Fr

T0 = time.time()
BUDGET = float(sys.argv[1]) if len(sys.argv) > 1 else 540.0
MAXLEN = int(sys.argv[2]) if len(sys.argv) > 2 else 4
J = int(sys.argv[3]) if len(sys.argv) > 3 else 1
RLEN = int(sys.argv[4]) if len(sys.argv) > 4 else 3
WIDE = len(sys.argv) > 5 and sys.argv[5] == 'wide'
CALIB = len(sys.argv) > 5 and sys.argv[5] == 'calib'  # adds e = diag(2,1): hits MUST appear
TAB = len(sys.argv) > 5 and sys.argv[5] == 'tab'  # tabulate near misses on extra lines

LIMIT = 5_000_000
sieve = bytearray([1]) * (LIMIT + 1)
sieve[0] = sieve[1] = 0
for i in range(2, int(LIMIT ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i::i] = bytearray(len(range(i * i, LIMIT + 1, i)))
PR = [i for i in range(LIMIT + 1) if sieve[i]]
del sieve


class Overflow(Exception):
    pass


def idx_to_k(n):  # n = 1-based prime index; p_k is the 2k-th prime (k>0), (1-2k)-th (k<=0)
    return n // 2 if n % 2 == 0 else (1 - n) // 2


def k_to_idx(k):
    return 2 * k if k > 0 else 1 - 2 * k


FCACHE = {}


def factor(m):
    """m >= 1 -> tuple of (prime, exponent)."""
    if m in FCACHE:
        return FCACHE[m]
    orig, out = m, []
    for p in PR:
        if p * p > m:
            break
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            out.append((p, e))
    if m > 1:
        if m > LIMIT:
            raise Overflow()
        out.append((m, 1))
    res = tuple(out)
    if len(FCACHE) < 3_000_000:
        FCACHE[orig] = res
    return res


def sig_int(m, j):
    if m == 0 or j == 0:
        return m
    s, a = (1, m) if m > 0 else (-1, -m)
    r = 1
    for p, e in factor(a):
        n = bisect.bisect_left(PR, p) + 1
        n2 = k_to_idx(idx_to_k(n) + j)
        if n2 > len(PR):
            raise Overflow()
        r *= PR[n2 - 1] ** e
        if r > 10 ** 15:
            raise Overflow()
    return s * r


def sig(q, j):
    if isinstance(q, int):
        return sig_int(q, j)
    return Fr(sig_int(q.numerator, j), sig_int(q.denominator, j))


def mat_apply(M, v):
    return (M[0][0] * v[0] + M[0][1] * v[1], M[1][0] * v[0] + M[1][1] * v[1])


def gen_apply(g, v):
    j, M = g
    if j == 0:
        return mat_apply(M, v)
    w = (sig(v[0], -j), sig(v[1], -j))
    w = mat_apply(M, w)
    return (sig(w[0], j), sig(w[1], j))


X = ((1, 1), (0, 1)); Xi = ((1, -1), (0, 1))
Y = ((1, 0), (1, 1)); Yi = ((1, 0), (-1, 1))
Wm = ((0, 1), (1, 0)); Dm = ((-1, 0), (0, 1))
X2 = ((1, 2), (0, 1)); X2i = ((1, -2), (0, 1)); Y2 = ((1, 0), (2, 1)); Y2i = ((1, 0), (-2, 1))
PAIRS = [(X, Xi), (Xi, X), (Y, Yi), (Yi, Y)]
if WIDE:
    PAIRS += [(X2, X2i), (X2i, X2), (Y2, Y2i), (Y2i, Y2)]
INVM = {a: b for a, b in PAIRS}
GENS, INV = [], []
for j in range(-J, J + 1):
    for M, Mi in PAIRS:
        GENS.append((j, M))
for M in (Wm, Dm):
    GENS.append((0, M))
Em = ((2, 0), (0, 1))
if CALIB:
    GENS.append((0, Em))
for g in GENS:
    j, M = g
    if M in (Wm, Dm, Em):
        INV.append(-1 if M == Em else GENS.index(g))
    else:
        Mi = INVM[M]
        INV.append(GENS.index((j, Mi)))
NG = len(GENS)

PROBES = [(1, 0), (0, 1), (1, 1), (1, -1), (2, 1), (1, 2), (3, 5), (5, -3), (7, 2), (2, 9)]


def normkey(imgs):
    (a, c), (b, d) = imgs[0], imgs[1]
    det = a * d - b * c
    if det == 0:
        return None, None
    det = Fr(det)
    key = []
    for (x, y) in imgs[2:]:
        # L^-1 = (1/det) [[d, -b], [-c, a]]
        key.append(((d * x - b * y) / det, (-c * x + a * y) / det))
    return tuple(key), abs(det)


def word_str(w):
    return ' '.join('s%d%s' % (GENS[i][0], {X: 'X', Xi: 'x', Y: 'Y', Yi: 'y', X2: 'P', X2i: 'p', Y2: 'Q', Y2i: 'q', Wm: 'W', Dm: 'D', Em: 'E'}[GENS[i][1]]) for i in w)


# ---- the elements g, k, r of Attempts 2 and 3 ----
G2 = ((2, 1), (1, 1)); SG2inv = ((Fr(1, 2), Fr(-1, 2)), (Fr(-1, 2), Fr(3, 2)))  # sigma(g) = [[3,1],[1,1]]
assert sig(2, 1) == 3 and sig(3, 1) == 7 and sig(5, 1) == 2 and sig(11, 1) == 5


def k_apply(v):
    w = (sig(v[0], -1), sig(v[1], -1))
    w = mat_apply(G2, w)
    w = (sig(w[0], 1), sig(w[1], 1))
    return mat_apply(SG2inv, w)


Mm = ((1, 0), (-1, -1))


def MkM(v):
    return mat_apply(Mm, k_apply(mat_apply(Mm, v)))


def wMkMw(v):
    return mat_apply(Wm, MkM(mat_apply(Wm, v)))


def r_apply(v):
    v = (2 * v[0], 2 * v[1])
    return k_apply(MkM(wMkMw(v)))


def as_fr(v):
    return (Fr(v[0]), Fr(v[1]))


# sanity: k fixes the axes pointwise and halves (1,-1); r fixes three lines pointwise
assert as_fr(k_apply((1, 0))) == (1, 0) and as_fr(k_apply((0, 1))) == (0, 1)
assert as_fr(k_apply((1, -1))) == (Fr(1, 2), Fr(-1, 2))
for v in ((1, 0), (0, 1), (1, -1), (5, 0), (0, -7), (3, -3)):
    assert as_fr(r_apply(v)) == as_fr(v), v
if CALIB:  # calibration: look up k in place of r; the word s1Y s1X must be found with |det L| = 2
    r_apply = k_apply
R_IMG = [as_fr(r_apply(p)) for p in PROBES]
print('k(1,1) =', k_apply((1, 1)), ' r on probes:', [(str(a), str(b)) for a, b in R_IMG])
print('generators:', NG, ' wide =', WIDE, ' J =', J, ' MAXLEN =', MAXLEN, ' RLEN =', RLEN, flush=True)

# ---- BFS ball with dedup by exact probe images ----
ident = tuple(PROBES)
seen = {ident: ()}
frontier = [(ident, ())]
table = {}  # normkey -> dict |det| -> word
k0, d0 = normkey(ident)
table[k0] = {d0: ()}
hits, near, overflow = [], [], 0
levels = []
stopped = False
for L in range(1, MAXLEN + 1):
    nxt = []
    for imgs, w in frontier:
        if time.time() - T0 > BUDGET:
            stopped = True
            break
        last = w[-1] if w else None
        for gi in range(NG):
            if last is not None and gi == INV[last]:
                continue
            try:
                new = tuple(gen_apply(GENS[gi], v) for v in imgs)
            except Overflow:
                overflow += 1
                continue
            if new in seen:
                continue
            nw = w + (gi,)
            seen[new] = nw
            nxt.append((new, nw))
            key, dt = normkey(new)
            if key is None:
                continue
            ent = table.setdefault(key, {})
            for d2, w2 in ent.items():
                if d2 != dt:
                    hits.append(('linear', nw, w2, dt / d2))
            ent.setdefault(dt, nw)
            if new[0] == (1, 0) and new[1] == (0, 1) and new[3] == (1, -1):
                agree = sum(1 for a, b in zip(new, R_IMG) if as_fr(a) == b)
                near.append((agree, nw))
    levels.append((L, len(nxt), round(time.time() - T0, 1)))
    print('level', L, 'new elements', len(nxt), 'time', round(time.time() - T0, 1), 'overflow', overflow, flush=True)
    frontier = nxt
    if stopped:
        break

# ---- r-translated lookup over short words ----
rhits, rchecked, roverflow = [], 0, 0
for imgs, w in list(seen.items()):
    if len(w) > RLEN or time.time() - T0 > BUDGET + 40:
        continue
    try:
        rim = [r_apply(v) for v in imgs]
    except Overflow:
        roverflow += 1
        continue
    rchecked += 1
    key, dt = normkey(rim)
    if key in table:
        for d2, w2 in table[key].items():
            # W2 = L r W with |det L| = d2 / dt
            ratio = d2 / dt
            rhits.append((ratio, w2, w))

print('ball size', len(seen), 'overflow', overflow, 'stopped_early', stopped)
print('linear-collision hits (|det L| != 1):', len(hits))
for h in hits[:20]:
    print('  HIT', h[3], '|', word_str(h[1]), '| vs |', word_str(h[2]))
print('near misses (fix both axes and (1,-1)):', len(near))
near.sort(key=lambda t: -t[0])
for a, w in near[:10]:
    print('  near', a, '/', len(PROBES), 'probes agree with r |', word_str(w))
print('r-translated words checked', rchecked, 'overflow', roverflow, 'matches', len(rhits))
for ratio, w2, w in rhits[:20]:
    tag = 'uninformative' if ratio == 2 else ('E-IN-N' if ratio == 1 else 'NEW')
    print('  RHIT |det L| =', ratio, tag, '|', word_str(w2), '| = L r |', word_str(w))
if TAB:
    from math import gcd
    EXTRA = [(1, 1), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3), (1, -2)]

    def content(v):
        a, b = Fr(v[0]), Fr(v[1])
        n = gcd(a.numerator, b.numerator)
        d = (a.denominator * b.denominator) // gcd(a.denominator, b.denominator)
        return Fr(n, d)

    def replay(w, v):
        for gi in w:
            v = gen_apply(GENS[gi], v)
        return v

    def describe(img, v):
        a, b = Fr(img[0]), Fr(img[1])
        same = a * v[1] == b * v[0]
        lam = (a / v[0] if v[0] else b / v[1]) if same else None
        return same, lam, content(img) / content(v)

    stats = {v: {'line_kept': 0, 'content_ratio_1': 0, 'n': 0, 'scalars': {}} for v in EXTRA}
    for _, w in near:
        for v in EXTRA:
            try:
                img = replay(w, v)
            except Overflow:
                continue
            same, lam, cr = describe(img, v)
            s = stats[v]
            s['n'] += 1
            s['line_kept'] += same
            s['content_ratio_1'] += (cr == 1)
            if same:
                s['scalars'][str(lam)] = s['scalars'].get(str(lam), 0) + 1
    print('TABULATION over', len(near), 'near misses (words in N_0 fixing both axes and (1,-1))')
    for v in EXTRA:
        s = stats[v]
        print('  line', v, ': evaluated', s['n'], 'kept', s['line_kept'], 'content ratio 1:', s['content_ratio_1'], 'scalars when kept:', dict(sorted(s['scalars'].items(), key=lambda t: -t[1])[:6]))
    for v in EXTRA:
        img = r_apply(v)
        same, lam, cr = describe(img, v)
        print('  r on', v, '->', (str(Fr(img[0])), str(Fr(img[1]))), 'line kept', same, 'scalar', lam, 'content ratio', cr)
print('total time', round(time.time() - T0, 1))
