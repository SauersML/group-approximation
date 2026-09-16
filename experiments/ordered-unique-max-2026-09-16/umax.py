#!/usr/bin/env python3
"""Ordered-quotient unique-maximum checks for two-generator one-relator relators.

Date: 2026-09-16.  Single-threaded, exact rational arithmetic.

Letters: 'a','A'(=a^-1),'t','T'(=t^-1).  Conventions: x^g = g^-1 x g,
[x,y] = x^-1 y^-1 x y.

Target group BS(1,N) = <a,t | t^-1 a t = a^N>, realized by affine maps
(k,c): x -> N^k x + c, with a -> (0,1) (x -> x+1), t -> (-1,0) (x -> x/N),
and product g*h = g o h.

Left orders checked on the finite vertex set of the relator path:
  * xi-orders g < h iff g(xi) < h(xi), xi generic, and their reverses;
  * the four lexicographic (Conradian) orders, which are the limits xi -> +-oo.
All of them are read off the upper and lower envelopes of the lines
xi -> N^k xi + c.  An envelope segment whose element is visited at exactly
one cyclic position certifies the unique-maximum hypothesis.

Also computed: Magnus rewriting with respect to a zero-exponent generator,
syllables of the extreme letters, peelability, Brown's Sigma^1 test for the
Magnus character (extreme letter occurs exactly once), the 1-chain of the
relator path in the Cayley graph of BS(1,N) (to certify w in r[N,N] at the
chain level), and a Nielsen-ball search for peelable extremes.
"""
from fractions import Fraction
import json
import sys

INV = {'a': 'A', 'A': 'a', 't': 'T', 'T': 't'}


def red(w):
    out = []
    for c in w:
        if out and out[-1] == INV[c]:
            out.pop()
        else:
            out.append(c)
    return ''.join(out)


def cyc(w):
    w = red(w)
    while len(w) > 1 and w[0] == INV[w[-1]]:
        w = w[1:-1]
    return w


def inv(w):
    return ''.join(INV[c] for c in reversed(w))


def pw(x, n):
    return x * n if n >= 0 else inv(x) * (-n)


def conj(x, g):
    return red(inv(g) + x + g)


def comm(x, y):
    return red(inv(x) + inv(y) + x + y)


def expsum(w, gen):
    return w.count(gen) - w.count(INV[gen])


# ---------------------------------------------------------------- BS(1,N)

def make_bs(N):
    NF = Fraction(N)

    def mul(g, h):
        k1, c1 = g
        k2, c2 = h
        return (k1 + k2, NF ** k1 * c2 + c1)

    def ginv(g):
        k, c = g
        return (-k, -(NF ** (-k)) * c)

    gens = {'a': (0, Fraction(1)), 't': (-1, Fraction(0))}
    gens['A'] = ginv(gens['a'])
    gens['T'] = ginv(gens['t'])
    return mul, ginv, gens


def path_vertices(w, N):
    """Vertices p_0 = 1, ..., p_{L-1}; also returns p_L."""
    mul, _, gens = make_bs(N)
    p = (0, Fraction(0))
    verts = []
    for c in w:
        verts.append(p)
        p = mul(p, gens[c])
    return verts, p


def envelope(lines, upper=True):
    """Upper (or lower) envelope of lines y = s x + c, s > 0 distinct or not.

    lines: dict element -> (s, c).  Returns list of (element, x_left, x_right)
    with x_left/x_right Fractions or None for -oo/+oo, in increasing x order.
    """
    items = []
    for e, (s, c) in lines.items():
        if upper:
            items.append((s, c, e))
        else:
            items.append((-s, -c, e))  # lower envelope of f = upper of -f
    # for equal slopes keep the largest intercept
    best = {}
    for s, c, e in items:
        if s not in best or c > best[s][0]:
            best[s] = (c, e)
    hull = []  # (s, c, e)
    for s in sorted(best):
        c, e = best[s]
        while len(hull) >= 2:
            s1, c1, _ = hull[-2]
            s2, c2, _ = hull[-1]
            # line2 useless if intersection(l1,l3) <= intersection(l1,l2)
            x13 = (c1 - c) / (s - s1)
            x12 = (c1 - c2) / (s2 - s1)
            if x13 <= x12:
                hull.pop()
            else:
                break
        hull.append((s, c, e))
    segs = []
    for i, (s, c, e) in enumerate(hull):
        left = None if i == 0 else (hull[i - 1][1] - c) / (s - hull[i - 1][0])
        right = None if i == len(hull) - 1 else (c - hull[i + 1][1]) / (hull[i + 1][0] - s)
        segs.append((e, left, right))
    return segs


def unique_extrema(w, N):
    """Return envelope segments (kind, element, left, right, visits)."""
    verts, end = path_vertices(w, N)
    assert end == (0, Fraction(0)), "relator does not die in BS(1,N)"
    count = {}
    for v in verts:
        count[v] = count.get(v, 0) + 1
    lines = {v: (Fraction(N) ** v[0], v[1]) for v in count}
    out = []
    for kind, up in (('max', True), ('min', False)):
        for e, l, r in envelope(lines, upper=up):
            out.append((kind, e, l, r, count[e]))
    return out, verts, count


def certified_orders(w, N):
    segs, verts, count = unique_extrema(w, N)
    good = [s for s in segs if s[4] == 1]
    return good, segs, len(verts), len(count)


# ---------------------------------------------------------------- Magnus

def magnus(w, t='t'):
    """Magnus rewriting of cyclic word w w.r.t. zero-exponent generator t.

    Returns list of (index, sign) for the a-letters, a_i = t^-i a t^i.
    """
    a = 'a' if t in 't T'.split() else 't'
    T = INV[t]
    s = 0
    out = []
    for c in w:
        if c == t:
            s += 1
        elif c == T:
            s -= 1
        else:
            out.append((-s, 1 if c == a else -1))
    assert s == 0
    return out


def syllables(seq, idx):
    """Syllable exponents of letter a_idx in the cyclic sequence seq."""
    n = len(seq)
    pos = [i for i in range(n) if seq[i][0] == idx]
    if len(pos) == n:
        return [sum(sg for _, sg in seq)]
    # rotate to start right after a non-idx letter
    start = next(i for i in range(n) if seq[i][0] != idx)
    rot = seq[start + 1:] + seq[:start + 1]
    syl = []
    cur = 0
    for j, sg in rot:
        if j == idx:
            cur += sg
        else:
            if cur:
                syl.append(cur)
            cur = 0
    if cur:
        syl.append(cur)
    return syl


def peelable(syl):
    return len(syl) == 1 or (len(syl) == 2 and abs(syl[0]) == abs(syl[1]))


def extremes(w, t='t'):
    seq = magnus(w, t)
    idxs = [j for j, _ in seq]
    m, n = min(idxs), max(idxs)
    top = syllables(seq, n)
    bot = syllables(seq, m)
    top_occ = sum(abs(x) for x in top)
    bot_occ = sum(abs(x) for x in bot)
    return {
        'm': m, 'n': n, 'top_syllables': top, 'bottom_syllables': bot,
        'top_peelable': peelable(top), 'bottom_peelable': peelable(bot),
        'brown_sigma1_plus_or_minus': top_occ == 1 or bot_occ == 1,
    }


# ---------------------------------------------------------------- chains

def chain(w, N, base=(0, Fraction(0))):
    mul, _, gens = make_bs(N)
    z = {}
    p = base
    for c in w:
        q = mul(p, gens[c])
        if c in 'at':
            key = (p, c)
            z[key] = z.get(key, 0) + 1
        else:
            key = (q, INV[c])
            z[key] = z.get(key, 0) - 1
        p = q
    return {k: v for k, v in z.items() if v}


# ---------------------------------------------------------------- Nielsen

SUBS = [
    {'a': 'at', 't': 't'}, {'a': 'aT', 't': 't'}, {'a': 'ta', 't': 't'},
    {'a': 'Ta', 't': 't'}, {'a': 'a', 't': 'ta'}, {'a': 'a', 't': 'tA'},
    {'a': 'a', 't': 'at'}, {'a': 'a', 't': 'At'}, {'a': 't', 't': 'a'},
    {'a': 'A', 't': 't'}, {'a': 'a', 't': 'T'},
]


def apply_sub(w, sub):
    full = dict(sub)
    full['A'] = inv(sub['a'])
    full['T'] = inv(sub['t'])
    return cyc(''.join(full[c] for c in w))


def canon(w):
    cands = []
    for ww in (w, inv(w)):
        for i in range(len(ww)):
            cands.append(ww[i:] + ww[:i])
    return min(cands)


def nielsen_ball(w, depth, maxlen=400):
    seen = {canon(w): w}
    frontier = [w]
    for _ in range(depth):
        nxt = []
        for u in frontier:
            for sub in SUBS:
                v = apply_sub(u, sub)
                if len(v) > maxlen:
                    continue
                cv = canon(v)
                if cv not in seen:
                    seen[cv] = v
                    nxt.append(v)
        frontier = nxt
    return list(seen.values())


def peel_scan(words):
    peel = []
    checked = 0
    for u in words:
        for t in ('t', 'a'):
            if expsum(u, t) == 0:
                seq = magnus(u, t)
                idxs = {j for j, _ in seq}
                if len(idxs) < 2:
                    peel.append((u, t, 'single-level'))
                    continue
                ex = extremes(u, t)
                checked += 1
                if ex['top_peelable'] or ex['bottom_peelable']:
                    peel.append((u, t, ex['top_syllables'], ex['bottom_syllables']))
    return checked, peel


# ---------------------------------------------------------------- family

R0 = 'TatAA'   # r = t^-1 a t a^-2, H = BS(1,2)


def family(M, j, Mp, jp):
    """w = r [r^g, r^h] with g^-1 = a^-M t^-j, h^-1 = a^-Mp t^-jp."""
    ginv = pw('a', -M) + pw('t', -j)
    hinv = pw('a', -Mp) + pw('t', -jp)
    g = inv(ginv)
    h = inv(hinv)
    return cyc(R0 + comm(conj(R0, g), conj(R0, h)))


def fmt(x):
    return 'inf' if x is None else str(x)


def report(w, N=2, depth=3):
    good, segs, L, E = certified_orders(w, N)
    ex = extremes(w, 't')
    z_w = chain(w, N)
    z_r = chain(R0, N)
    res = {
        'word': w, 'length': len(w), 'exp_a': expsum(w, 'a'), 'exp_t': expsum(w, 't'),
        'distinct_vertices': E,
        'certified_segments': [
            {'kind': k, 'element': [e[0], str(e[1])], 'xi_left': fmt(l), 'xi_right': fmt(r)}
            for (k, e, l, r, c) in good],
        'envelope_visit_counts': [(k, [e[0], str(e[1])], fmt(l), fmt(r), c)
                                  for (k, e, l, r, c) in segs],
        'magnus': ex,
        'chain_equals_r_chain': z_w == z_r,
        'not_conjugate_to_r': len(cyc(w)) != len(R0),
    }
    if depth > 0:
        ball = nielsen_ball(w, depth)
        checked, peel = peel_scan(ball)
        res['nielsen_ball_size'] = len(ball)
        res['nielsen_zero_exponent_rewritings_checked'] = checked
        res['nielsen_peelable_found'] = len(peel)
        res['nielsen_peelable_examples'] = [list(map(str, p)) for p in peel[:3]]
    return res


def search(prange, qvals):
    """Shortest family members with a certified order and unpeelable extremes."""
    best = []
    opts = [(p, q) for p in prange for q in qvals]
    for i, (M, j) in enumerate(opts):
        for (Mp, jp) in opts[i + 1:]:
            w = family(M, j, Mp, jp)
            if len(w) == len(R0):
                continue
            if expsum(w, 't') != 0:
                continue
            ex = extremes(w, 't')
            if ex['top_peelable'] or ex['bottom_peelable']:
                continue
            good, _, _, _ = certified_orders(w, 2)
            if good:
                best.append((len(w), (M, j, Mp, jp), w))
    best.sort()
    return best


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'report'
    if mode == 'report':
        M, j, Mp, jp = map(int, sys.argv[2:6])
        depth = int(sys.argv[6]) if len(sys.argv) > 6 else 3
        w = family(M, j, Mp, jp)
        print(json.dumps(report(w, 2, depth), indent=1))
    elif mode == 'word':
        w = cyc(sys.argv[2])
        depth = int(sys.argv[3]) if len(sys.argv) > 3 else 0
        print(json.dumps(report(w, 2, depth), indent=1))
    elif mode == 'search':
        lo, hi, qs = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
        qvals = [int(x) for x in qs.split(',')]
        best = search(range(lo, hi + 1), qvals)
        print('found', len(best))
        for L, par, w in best[:15]:
            print(L, par, w)
