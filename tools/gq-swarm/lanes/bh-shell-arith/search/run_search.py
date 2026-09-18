#!/usr/bin/env python3
"""Driver: validation, calibration, negative control, targeted + random search.
usage: run_search.py PHASE [seconds]
  PHASE = validate | control | main | random-control | random-main
"""
import sys, random, time
from fractions import Fraction
sys.setrecursionlimit(10000)
from rnu_tables import *

T0 = time.time()
BUDGET = float(sys.argv[2]) if len(sys.argv) > 2 else 500.0
def left():
    return BUDGET - (time.time() - T0)

# ---------------- independent free-product model ----------------
def encode(word, G0, G1):
    """word = (eps, [elements]) or None for identity -> table point (root, y)."""
    if word is None:
        return (1, 0)
    eps, els = word
    Gs = (G0, G1)
    q = 0; mult = 1
    for j, x in enumerate(els):
        Gj = Gs[(eps + j) % 2]
        q += Gj[2][x] * mult
        mult *= Gj[3]
    return (eps, q)

def fp_left(x, side, word, G0, G1):
    Gs = (G0, G1)
    ident = Gs[side][0]
    if word is None:
        return (side, [x])
    eps, els = word
    if eps != side:
        return (side, [x] + els)
    y = perm_mul(x, els[0])
    if y == ident:
        rest = els[1:]
        return None if not rest else (1 - side, rest)
    return (side, [y] + els[1:])

def random_word(G0, G1, maxlen):
    l = random.randint(0, maxlen)
    if l == 0:
        return None
    eps = random.randint(0, 1)
    Gs = (G0, G1)
    els = []
    for j in range(l):
        Gj = Gs[(eps + j) % 2]
        els.append(Gj[1][random.randint(1, Gj[3])])
    return (eps, els)

def decode_n(n, G0, G1):
    """n -> word, inverse of nu (n = 2q-1+eps, identity 0)."""
    if n == 0:
        return None
    eps = 1 if n % 2 == 0 else 0
    q = (n + 1 - eps) // 2
    Gs = (G0, G1)
    els = []; j = 0
    while q > 0:
        Gj = Gs[(eps + j) % 2]
        h = Gj[3]
        d = q % h
        if d == 0: d = h
        els.append(Gj[1][d])
        q = (q - d) // h
        j += 1
    return (eps, els)

def point_to_n(pt):
    e, y = pt
    return 2 * y - 1 + e if e == 0 else 2 * y

# ---------------- setup ----------------
def setup(kind):
    A5 = alt_group(5); A6 = alt_group(6)
    def find(group, order_min, avoid=()):
        ident = tuple(range(len(group[0])))
        for x in group:
            if x == ident or x in avoid: continue
            p = x; o = 1
            while p != ident:
                p = perm_mul(x, p); o += 1
            if o >= order_min:
                inv = [y for y in group if perm_mul(x, y) == ident][0]
                if inv != x:
                    return x
        return None
    if kind == 'main':      # A_5 * A_6, h0 = 59, h1 = 359, fixed point -1/2 digits 29 / 179
        x = find(A5, 3); z = find(A6, 3)
        G0 = labeling(A5, {x: 29}); G1 = labeling(A6, {z: 179})
        radices = [59, 359]
    elif kind == 'control':  # equal radix A_5 * A_5, both digits 29 (fixed point -1/2)
        x = find(A5, 3); z = find(A5, 3)
        G0 = labeling(A5, {x: 29}); G1 = labeling(A5, {z: 29})
        radices = [59]
    else:
        raise SystemExit("kind")
    return G0, G1, x, z, radices

def gens(G0, G1, radices, k=3):
    """lambda of a few elements of each factor (incl. a generating pair), s, s^-1."""
    out = []
    for side, G in ((0, G0), (1, G1)):
        els = G[1][1:1 + k]
        for x in els:
            out.append(('l%d_%d' % (side, G[2][x]), lam(x, G, side)))
    out.append(('s', S_SHIFT))
    out.append(('S', inverse(S_SHIFT)))
    return out

def mulr(radices):
    return lambda *gs: mul(*gs, radices=radices)

def is_identity(g):
    return all(is_identity_leaf(L) for L in g)

def report(name, g):
    non, roots, nonunit = support_report(g)
    ms = sorted(set((L[2], L[5]) for L in nonunit))[:6]
    print("  %-28s leaves=%6d moved=%6d roots=%s nonunit=%d slopes(M->M')=%s HIT=%s" %
          (name, len(g), len(non), roots, len(nonunit), ms, detector(g)), flush=True)

def validate():
    random.seed(1)
    for kind in ('main', 'control'):
        G0, G1, x, z, radices = setup(kind)
        m = mulr(radices)
        print("== validate", kind, "h =", G0[3], G1[3], flush=True)
        # 1. tables vs independent free-product model on random points
        bad = 0; tests = 0; badpts = set()
        for side, G in ((0, G0), (1, G1)):
            for d in (1, 2, G[3] // 2, G[3]):
                xx = G[1][d]
                L = lam(xx, G, side)
                for _ in range(300):
                    w = random_word(G0, G1, 5)
                    pt = encode(w, G0, G1)
                    got = evaluate(L, *pt)
                    exp = encode(fp_left(xx, side, w, G0, G1), G0, G1)
                    tests += 1
                    if got != exp:
                        bad += 1; badpts.add(pt)
        for n in range(0, 2000):
            pt = encode(decode_n(n, G0, G1), G0, G1)
            got = evaluate(S_SHIFT, *pt)
            exp = encode(decode_n(n + 1, G0, G1), G0, G1)
            tests += 1
            if got != exp:
                bad += 1
                if bad < 10: print("   MISMATCH s", n, got, exp)
            if point_to_n(pt) != n:
                bad += 1
        print("  point tests:", tests, "bad:", bad, "distinct bad input points:", sorted(badpts), flush=True)
        bad = 0
        # 2. group sanity
        gl = gens(G0, G1, radices)
        for nm, g in gl:
            ok = is_identity(m(g, inverse(g))) and is_identity(m(inverse(g), g))
            if not ok: print("   inverse FAIL", nm)
        l0 = lam(x, G0, 0); o = 1; p = l0
        while not is_identity(p):
            p = m(l0, p); o += 1
            if o > 20: break
        print("  order of lambda_x:", o, flush=True)
        # composition vs pointwise
        for _ in range(20):
            w = [random.choice(gl) for _ in range(4)]
            g = m(*[t[1] for t in w])
            for _ in range(50):
                e = random.randint(0, 1); y = random.randint(-50, 5000)
                pt = (e, y)
                for t in reversed(w):
                    pt = evaluate(t[1], *pt)
                if evaluate(g, e, y) != pt:
                    bad += 1
        print("  composition-vs-pointwise bad:", bad, flush=True)
        # 3. detector calibration (planted)
        h0 = radices[0]
        planted = [(0, 0, 1, 0, 0, 1, 0),
                   (1, 0, h0, 1, 1, h0 * h0, 0),
                   (1, 1, h0 * h0, 1, 0, h0, 0)]
        for k in range(1, h0):
            planted.append((1, 1 + h0 * k, h0 * h0, 1, 1 + h0 * k, h0 * h0, 0))
        for r in range(2, h0):
            planted.append((1, r, h0, 1, r, h0, 0))
        print("  planted positive valid:", is_identity(m(planted, inverse(planted))), flush=True)
        report("planted positive", planted)
        pn = [(0, 0, 1, 0, 0, 1, 0), (1, 0, h0, 1, 0, h0, 1), (1, 1, h0, 1, 1, h0, -1)]
        pn += [(1, r, h0, 1, r, h0, 0) for r in range(2, h0)]
        report("planted negative (odometer pair)", pn)
        report("lambda_x (full support)", l0)

def targeted(kind):
    G0, G1, x, z, radices = setup(kind)
    m = mulr(radices)
    lx = lam(x, G0, 0); lz = lam(z, G1, 1)
    s = S_SHIFT; S = inverse(s)
    A = m(lx, s); B = m(S, lz)
    print("== targeted", kind, "A leaves", len(A), "B leaves", len(B), flush=True)
    Ai, Bi = inverse(A), inverse(B)
    rho = m(A, B); rhoi = inverse(rho)
    words = {'A': A, 'B': B, 'Ai': Ai, 'Bi': Bi}
    pairs = [('A', 'B'), ('A', 'BB'), ('AA', 'B'), ('A', 'BAB'), ('AB', 'BA'), ('A', 'BBB'),
             ('AAA', 'B'), ('AB', 'B'), ('AAB', 'ABB')]
    def word(wd):
        return m(*[{'A': A, 'B': B}[c] for c in wd]) if len(wd) > 1 else {'A': A, 'B': B}[wd]
    hits = 0
    for p1, p2 in pairs:
        if left() < 60: print("  budget stop"); break
        P = word(p1); Q = word(p2)
        k = m(P, Q, inverse(P), inverse(Q))
        report("[%s,%s]" % (p1, p2), k)
        kc = k
        for n in range(1, 4):
            kc = m(rhoi, kc, rho)
            non, roots, nonunit = support_report(kc)
            if roots == [1]:
                report("  rho^-%d [%s,%s] rho^%d" % (n, p1, p2, n), kc)
                if detector(kc):
                    hits += 1
                    print("  HIT", kind, p1, p2, n, "leaves:", len(kc), flush=True)
                    fn = "hit_%s_%s_%s_%d.txt" % (kind, p1, p2, n)
                    with open(fn, "w") as fh:
                        for L in sorted(kc):
                            fh.write("%s\n" % (L,))
                break
            if left() < 60: break
    print("== targeted", kind, "hits:", hits, "time", round(time.time() - T0), flush=True)

def random_search(kind, maxlen):
    random.seed(7)
    G0, G1, x, z, radices = setup(kind)
    m = mulr(radices)
    gl = gens(G0, G1, radices)
    tried = 0; hits = 0; proper = 0
    while left() > 30:
        w1 = [random.choice(gl) for _ in range(random.randint(1, maxlen))]
        w2 = [random.choice(gl) for _ in range(random.randint(1, maxlen))]
        g1 = m(*[t[1] for t in w1]); g2 = m(*[t[1] for t in w2])
        k = m(g1, g2, inverse(g1), inverse(g2))
        tried += 1
        non, roots, nonunit = support_report(k)
        if len(non) and len(roots) == 1:
            proper += 1
            if nonunit:
                hits += 1
                print("  HIT", kind, [t[0] for t in w1], [t[0] for t in w2], "leaves", len(k), flush=True)
    print("== random", kind, "tried", tried, "proper-support", proper, "hits", hits, flush=True)

if __name__ == '__main__':
    ph = sys.argv[1]
    if ph == 'validate': validate()
    elif ph == 'control': targeted('control')
    elif ph == 'main': targeted('main')
    elif ph == 'random-control': random_search('control', 3)
    elif ph == 'random-main': random_search('main', 3)
    print("elapsed", round(time.time() - T0), "s")

# ---------------- independent symbolic cone trace (no compose/merge) ----------------
def trace(word, e0, a0, M0):
    """Push the cone (e0, a0 + M0 t) through the tables in `word` (applied left to right).
    Returns ('ok', e, alpha, beta) meaning the cone maps to (e, alpha + beta t), or
    ('split', None) if some step does not contain the current cone in a single leaf."""
    e, al, be = e0, a0, M0
    for tab in word:
        hit = None
        for (e1, a1, M1, f, b, N, G) in tab:
            if e1 == e and be % M1 == 0 and (al - a1) % M1 == 0:
                hit = (a1, M1, f, b, N, G); break
        if hit is None:
            return ('split', None)
        a1, M1, f, b, N, G = hit
        u0 = (al - a1) // M1
        e, al, be = f, b + N * (u0 + G), N * (be // M1)
    return ('ok', e, al, be)

def trace_partition(word, e0, a0, M0, radices, depth=0, maxdepth=6, out=None):
    out = [] if out is None else out
    r = trace(word, e0, a0, M0)
    if r[0] == 'ok':
        out.append((e0, a0, M0) + r[1:])
        return out
    if depth >= maxdepth:
        raise RuntimeError("trace too deep")
    h = radices[depth % len(radices)]
    for k in range(h):
        trace_partition(word, e0, a0 + M0 * k, M0 * h, radices, depth + 1, maxdepth, out)
    return out

def verify(kind):
    G0, G1, x, z, radices = setup(kind)
    inv0 = [y for y in G0[1][1:] if perm_mul(x, y) == G0[0]][0]
    inv1 = [y for y in G1[1][1:] if perm_mul(z, y) == G1[0]][0]
    lx, lz = lam(x, G0, 0), lam(z, G1, 1)
    lxi, lzi = lam(inv0, G0, 0), lam(inv1, G1, 1)
    s = S_SHIFT; S = inverse(s)
    # k1 = s^-1 lam(x^-1) lam(z^-1) s lam(x) lam(z): apply lam(z) first
    word = [lz, lx, s, lzi, lxi, S]
    print("== verify", kind, "digits x,z =", G0[2][x], G1[2][z], "x^-1,z^-1 =", G0[2][inv0], G1[2][inv1], flush=True)
    r0 = trace(word, 0, 0, 1)
    print("  root 0 traced as one cone:", r0, " identity:", r0 == ('ok', 0, 0, 1), flush=True)
    part = trace_partition(word, 1, 0, 1, radices[::-1] if kind == 'main' else radices)
    slopes = {}
    for (e0, a0, M0, e, al, be) in part:
        key = Fraction(be, M0)
        slopes[key] = slopes.get(key, 0) + 1
    print("  root 1 partition pieces:", len(part), " slope histogram:", sorted(slopes.items()), flush=True)
    ex = [p for p in part if p[5] != p[2]][:3]
    for p in ex:
        print("   e.g. cone (1, %d mod %d) -> (%d, %d + %d t), slope %s" % (p[1], p[2], p[3], p[4], p[5], Fraction(p[5], p[2])), flush=True)
    # cross-check against the composed table
    m = mulr(radices)
    k1 = m(S, lxi, lzi, s, lx, lz)
    report("k1 (composed table)", k1)
    bad = 0
    for (e0, a0, M0, e, al, be) in part[:2000]:
        for t in (0, 1, 7, -3):
            y = a0 + M0 * t
            if evaluate(k1, 1, y) != (e, al + be * t):
                bad += 1
    print("  trace-vs-table disagreements:", bad, flush=True)

if __name__ == '__main__' and sys.argv[1] == 'verify':
    verify('main'); verify('control')
    print("elapsed", round(time.time() - T0), "s")
