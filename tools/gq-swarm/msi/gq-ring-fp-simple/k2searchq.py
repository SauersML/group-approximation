#!/usr/bin/env python3
"""Informative search for a hidden relation in K_2, with RATIONAL shears.

N = <sigma_2^j SL_2(Q) sigma_2^-j, D> (Attempt 5). Generators here:
sigma_2^j x_12(q) sigma_2^-j and sigma_2^j x_21(q) sigma_2^-j, |j| <= J, q in QSET, plus W and D.
Same two tests as k2search.py (left-linear key; r-translated key). Planted calibration:
the target r is replaced by an element PLANTED of the searched subgroup, which must be found
with |det L| = 1; and linear collisions with |det L| = 1 and L != +-I are counted.
Usage: k2searchq.py BUDGET MAXLEN J QSET RLEN MAXELTS [planted]
  QSET: 'two' = {+-1, +-2, +-1/2}, 'twothree' = {+-1, +-2, +-1/2, +-3, +-1/3}
"""
import sys, time, bisect
from fractions import Fraction as Fr

T0 = time.time()
BUDGET = float(sys.argv[1]); MAXLEN = int(sys.argv[2]); J = int(sys.argv[3])
QSET = sys.argv[4]; RLEN = int(sys.argv[5]); MAXELTS = int(sys.argv[6])
PLANT = len(sys.argv) > 7 and sys.argv[7] == 'planted'

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


def idx_to_k(n):
    return n // 2 if n % 2 == 0 else (1 - n) // 2


def k_to_idx(k):
    return 2 * k if k > 0 else 1 - 2 * k


FCACHE = {}


def factor(m):
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
    if len(FCACHE) < 2_000_000:
        FCACHE[orig] = res
    return res


def sig_int(m, j):
    if m == 0 or j == 0:
        return m
    s, a = (1, m) if m > 0 else (-1, -m)
    r = 1
    for p, e in factor(a):
        n2 = k_to_idx(idx_to_k(bisect.bisect_left(PR, p) + 1) + j)
        if n2 > len(PR):
            raise Overflow()
        r *= PR[n2 - 1] ** e
        if r > 10 ** 15:
            raise Overflow()
    return s * r


def sig(q, j):
    if j == 0:
        return q
    q = Fr(q)
    return Fr(sig_int(q.numerator, j), sig_int(q.denominator, j))


def mat_apply(M, v):
    return (M[0][0] * v[0] + M[0][1] * v[1], M[1][0] * v[0] + M[1][1] * v[1])


def gen_apply(g, v):
    j, M = g
    if j == 0:
        return mat_apply(M, v)
    w = mat_apply(M, (sig(v[0], -j), sig(v[1], -j)))
    return (sig(w[0], j), sig(w[1], j))


QS = [Fr(1), Fr(-1), Fr(2), Fr(-2), Fr(1, 2), Fr(-1, 2)]
if QSET == 'twothree':
    QS += [Fr(3), Fr(-3), Fr(1, 3), Fr(-1, 3)]
GENS, NAMES = [], []
for j in range(-J, J + 1):
    for q in QS:
        GENS.append((j, ((Fr(1), q), (Fr(0), Fr(1))))); NAMES.append('s%dX(%s)' % (j, q))
        GENS.append((j, ((Fr(1), Fr(0)), (q, Fr(1))))); NAMES.append('s%dY(%s)' % (j, q))
Wm = ((0, 1), (1, 0)); Dm = ((-1, 0), (0, 1))
GENS += [(0, Wm), (0, Dm)]; NAMES += ['W', 'D']
INV = []
for g in GENS:
    j, M = g
    if M in (Wm, Dm):
        INV.append(GENS.index(g))
    else:
        Mi = ((M[0][0], -M[0][1]), (-M[1][0], M[1][1]))
        INV.append(GENS.index((j, Mi)))
NG = len(GENS)
PROBES = [(1, 0), (0, 1), (1, 1), (1, -1), (2, 1), (1, 2), (3, 5), (5, -3), (7, 2), (2, 9)]
PROBES = [(Fr(a), Fr(b)) for a, b in PROBES]


def normkey(imgs):
    (a, c), (b, d) = imgs[0], imgs[1]
    det = a * d - b * c
    if det == 0:
        return None, None, None
    key = tuple(((d * x - b * y) / det, (-c * x + a * y) / det) for (x, y) in imgs[2:])
    return key, abs(det), (a, b, c, d)


def wstr(w):
    return ' '.join(NAMES[i] for i in w)


# ---- target r (Attempt 3) ----
G2 = ((2, 1), (1, 1)); SG2inv = ((Fr(1, 2), Fr(-1, 2)), (Fr(-1, 2), Fr(3, 2)))
Mm = ((1, 0), (-1, -1))
assert sig(2, 1) == 3 and sig(5, 1) == 2


def k_apply(v):
    w = mat_apply(G2, (sig(v[0], -1), sig(v[1], -1)))
    return mat_apply(SG2inv, (sig(w[0], 1), sig(w[1], 1)))


def r_apply(v):
    v = (2 * v[0], 2 * v[1])
    v = mat_apply(Wm, mat_apply(Mm, k_apply(mat_apply(Mm, mat_apply(Wm, v)))))
    v = mat_apply(Mm, k_apply(mat_apply(Mm, v)))
    return k_apply(v)


for v in ((1, 0), (0, 1), (1, -1), (3, -3)):
    assert r_apply((Fr(v[0]), Fr(v[1]))) == (v[0], v[1])

TARGET, TNAME = r_apply, 'r'
if PLANT:
    # planted target inside the searched subgroup: the near miss X(-1) o (sigma_2^-1 X(1) sigma_2)
    PW = [NAMES.index('s-1X(1)'), NAMES.index('s0X(-1)')]

    def planted(v):
        for gi in PW:
            v = gen_apply(GENS[gi], v)
        return v
    TARGET, TNAME = planted, 'planted ' + wstr(PW)
print('generators', NG, 'J', J, 'QSET', QSET, 'MAXLEN', MAXLEN, 'RLEN', RLEN, 'target', TNAME, flush=True)

ident = tuple(PROBES)
seen = {ident: ()}
frontier = [(ident, ())]
k0, d0, _ = normkey(ident)
table = {k0: {d0: ()}}
hits, det1_nontriv, near, overflow = [], 0, 0, 0
stopped = False
for L in range(1, MAXLEN + 1):
    nxt = []
    for imgs, w in frontier:
        if time.time() - T0 > BUDGET or len(seen) > MAXELTS:
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
            key, dt, ab = normkey(new)
            if key is None:
                continue
            ent = table.setdefault(key, {})
            for d2, w2 in ent.items():
                if d2 != dt:
                    hits.append((nw, w2, dt / d2))
            if key == k0 and dt == 1 and ab not in ((1, 0, 0, 1), (-1, 0, 0, -1)):
                det1_nontriv += 1
            ent.setdefault(dt, nw)
            if new[0] == (1, 0) and new[1] == (0, 1) and new[3] == (1, -1):
                near += 1
    print('level', L, 'new', len(nxt), 'time', round(time.time() - T0, 1), 'overflow', overflow, flush=True)
    frontier = nxt
    if stopped:
        break

rhits, rchecked, rover = [], 0, 0
for imgs, w in list(seen.items()):
    if len(w) > RLEN or time.time() - T0 > BUDGET + 60:
        continue
    try:
        rim = [TARGET(v) for v in imgs]
    except Overflow:
        rover += 1
        continue
    rchecked += 1
    key, dt, _ = normkey(rim)
    if key in table:
        for d2, w2 in table[key].items():
            rhits.append((d2 / dt, w2, w))

print('ball', len(seen), 'overflow', overflow, 'stopped_early', stopped)
print('linear hits |det L| != 1:', len(hits))
for a, b, ratio in hits[:20]:
    print('  HIT |det L| =', ratio, '|', wstr(a), '| = L |', wstr(b))
print('calibration B: words equal to a linear map of |det| 1 other than +-I:', det1_nontriv)
print('near misses (fix both axes and (1,-1)):', near)
print('target-translated words checked', rchecked, 'overflow', rover, 'matches', len(rhits))
informative = [h for h in rhits if h[0] != 2] if not PLANT else rhits
for ratio, w2, w in rhits[:20]:
    tag = ('uninformative' if ratio == 2 else ('E-IN-N' if ratio == 1 else 'NEW')) if not PLANT else 'planted'
    print('  THIT |det L| =', ratio, tag, '|', wstr(w2), '| = L target |', wstr(w))
print('total time', round(time.time() - T0, 1))
