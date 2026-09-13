#!/usr/bin/env python3
"""Census of unpeelable Magnus extremes for G = <a,t | w>, t-exponent sum 0.

Letters: 1 = a, -1 = a^-1, 2 = t, -2 = t^-1.  A cyclic word with t-exponent 0
is stored as its cyclic list of a-syllables (h, e): a^e at t-height h.
Certificates use only established theorems of the graph:
  PP    partially positive relator (residually solvable)
  PEEL  a peelable Magnus extreme in some zero-exponent basis
  R1    overlap rank one after the level-gcd reduction: G is an HNN extension
        (over Z) of B_0 = <a_m, a_n | W_0>, recursively certified
  CYC   an extreme letter whose coefficients lie in one cyclic subgroup <c>:
        B_0 = F_-+ *_<c> Q with Q = <y,z | P>, an amenable envelope, recursively
        certified
  PRIMITIVE / Z  the group is infinite cyclic
Usage: enum.py LMIN LMAX [MAXPRINT]
"""
import sys, math, time

def free_reduce(w):
    out = []
    for x in w:
        if out and out[-1] == -x:
            out.pop()
        else:
            out.append(x)
    return out

def cyc_reduce(w):
    w = free_reduce(w)
    i, j = 0, len(w) - 1
    while i < j and w[i] == -w[j]:
        i += 1; j -= 1
    return w[i:j + 1]

def inv(w):
    return [-x for x in reversed(w)]

def min_period(w):
    n = len(w)
    for p in range(1, n + 1):
        if n % p == 0 and w[:n - p] == w[p:]:
            return p
    return n

def expsums(w):
    p = sum(1 if x == 1 else -1 for x in w if abs(x) == 1)
    q = sum(1 if x == 2 else -1 for x in w if abs(x) == 2)
    return p, q

def power(letter, k):
    return [letter] * k if k > 0 else [-letter] * (-k)

def subst(w, img):
    out = []
    for x in w:
        out.extend(img[x] if x > 0 else inv(img[-x]))
    return cyc_reduce(out)

def adapt(w, x, y):
    """phi(a)=x, phi(t)=y, gcd 1, phi(w)=0.  Rewrite w in a basis (a',t') with
    phi(a')=0, phi(t')=1, by Euclidean Nielsen moves."""
    while True:
        if x == 0:
            if y == -1:
                w = subst(w, {1: [1], 2: [-2]}); y = 1
            assert y == 1, (x, y)
            return w
        if y == 0:
            w = subst(w, {1: [2], 2: [1]}); x, y = 0, x
            continue
        if abs(x) >= abs(y):
            k = (abs(x) // abs(y)) * (1 if x * y > 0 else -1)
            w = subst(w, {1: [1] + power(2, k), 2: [2]}); x -= k * y
        else:
            k = (abs(y) // abs(x)) * (1 if x * y > 0 else -1)
            w = subst(w, {1: [1], 2: [2] + power(1, k)}); y -= k * x

def magnus(w):
    n = len(w)
    start = None
    for i in range(n):
        if abs(w[i]) == 1 and abs(w[i - 1]) == 2:
            start = i; break
    if start is None:
        return None
    w = w[start:] + w[:start]
    seq, h, i = [], 0, 0
    while i < n:
        if abs(w[i]) == 1:
            e = 0
            while i < n and abs(w[i]) == 1:
                e += w[i]; i += 1
            seq.append((h, e))
        else:
            h += 1 if w[i] == 2 else -1
            i += 1
    m = min(s[0] for s in seq)
    return [(hh - m, e) for hh, e in seq]

def seq_to_word(seq):
    w, k = [], len(seq)
    for i, (h, e) in enumerate(seq):
        w.extend(power(1, e))
        w.extend(power(2, seq[(i + 1) % k][0] - h))
    return w

def extremes(seq):
    hs = [h for h, _ in seq]
    m, n = min(hs), max(hs)
    g = 0
    for h in hs:
        g = math.gcd(g, h - m)
    return m, n, g, [e for h, e in seq if h == n], [e for h, e in seq if h == m]

def peelable(ex):
    return len(ex) == 1 or (len(ex) == 2 and abs(ex[0]) == abs(ex[1]))

def pp(w):
    s = set(w)
    return ((1 in s) != (-1 in s)) or ((2 in s) != (-2 in s))

WH = []
for (X, Y) in ((1, 2), (2, 1)):
    for s in (1, -1):
        WH.append({X: [X, s * Y], Y: [Y]})
        WH.append({X: [s * Y, X], Y: [Y]})
        WH.append({X: [-s * Y, X, s * Y], Y: [Y]})

def wh_min(w):
    w = cyc_reduce(w)
    improved = True
    while improved:
        improved = False
        for img in WH:
            v = subst(w, img)
            if len(v) < len(w):
                w, improved = v, True
                break
    return w

def root(u):
    i, j = 0, len(u) - 1
    while i < j and u[i] == -u[j]:
        i += 1; j -= 1
    g, c = u[:i], u[i:j + 1]
    p = min_period(c)
    return tuple(g + c[:p] + inv(g)), len(c) // p

def coefficients(seq, lvl):
    k = len(seq)
    idx = [i for i, (h, _) in enumerate(seq) if h == lvl]
    out = []
    for j in range(len(idx)):
        i0, i1 = idx[j], idx[(j + 1) % len(idx)]
        u, i = [], (i0 + 1) % k
        while i != i1:
            h, e = seq[i]
            u.extend(power(h + 1, e))
            i = (i + 1) % k
        out.append((seq[i0][1], u))
    return out

def cyclic_Q(seq, lvl):
    base, P = None, []
    for e, u in coefficients(seq, lvl):
        rt, kk = root(u)
        if base is None or rt == base:
            base = rt
        elif rt == tuple(inv(list(base))):
            kk = -kk
        else:
            return None
        P.extend(power(1, e)); P.extend(power(2, kk))
    return P

def small_phis(B=3):
    out = [(0, 1)]
    for x in range(1, B + 1):
        for y in range(-B, B + 1):
            if math.gcd(x, y) == 1:
                out.append((x, y))
    return out

MAXD, BUDGET = 8, [0]
SUCCESS, INPROG = {}, set()

def cert_word(w, depth):
    w = cyc_reduce(w)
    key = tuple(w)
    if key in SUCCESS:
        return True, SUCCESS[key]
    if key in INPROG:
        return False, 'LOOP'
    BUDGET[0] -= 1
    if BUDGET[0] < 0:
        return False, 'BUDGET'
    INPROG.add(key)
    ok, why = _cert_word(w, depth)
    INPROG.discard(key)
    if ok:
        SUCCESS[key] = why
    return ok, why

def _cert_word(w, depth):
    if len(w) <= 1:
        return True, 'Z'
    if min_period(w) < len(w):
        return False, 'POWER'
    wm = wh_min(w)
    if len(wm) == 1:
        return True, 'PRIMITIVE'
    if pp(w) or pp(wm):
        return True, 'PP'
    if depth >= MAXD:
        return False, 'DEPTH'
    p, q = expsums(w)
    if (p, q) != (0, 0):
        g = math.gcd(p, q)
        phis = [(q // g, -p // g)]
    else:
        phis = small_phis()
    fails = []
    for (x, y) in phis:
        seq = magnus(adapt(w, x, y))
        if seq is None:
            return True, 'Z'
        ok, why = cert_seq(seq, depth)
        if ok:
            return True, ('phi=%d,%d:' % (x, y) if len(phis) > 1 else '') + why
        fails.append(why)
    return False, 'FAIL'

def cert_seq(seq, depth):
    m, n, g, top, bot = extremes(seq)
    if peelable(top) or peelable(bot):
        return True, 'PEEL'
    if pp(seq_to_word(seq)):
        return True, 'PP'
    if (n - m) // g <= 1:
        P = []
        for h, e in seq:
            P.extend(power(1 if h == m else 2, e))
        ok, why = cert_word(P, depth + 1)
        if ok:
            return True, 'R1(g=%d)[%s]' % (g, why)
    for side, lvl in (('top', n), ('bot', m)):
        P = cyclic_Q(seq, lvl)
        if P is not None:
            ok, why = cert_word(P, depth + 1)
            if ok:
                return True, 'CYC-%s[%s]' % (side, why)
    return False, 'R%d' % ((n - m) // g)

def word_str(w):
    return ''.join({1: 'a', -1: 'A', 2: 't', -2: 'T'}[x] for x in w)

def mag_str(u):
    return ''.join(('a%d' % (x - 1)) if x > 0 else ('A%d' % (-x - 1)) for x in u)

def canon(seq):
    n = max(h for h, _ in seq)
    best = None
    for s in (seq, [(n - h, e) for h, e in seq]):
        for s1 in (s, [(h, -e) for h, e in s]):
            for s2 in (s1, [(h, -e) for h, e in reversed(s1)]):
                for r in range(len(s2)):
                    t = tuple(s2[r:] + s2[:r])
                    if best is None or t < best:
                        best = t
    return best

def gen(L):
    seq = []
    def rec(used, h):
        if h != 0 and used + h == L and len(seq) >= 2:
            yield list(seq)
        for da in range(1, L - used):
            for d in (da, -da):
                h2 = h + d
                if h2 < 0:
                    continue
                need = h2 if h2 > 0 else 3
                for ea in range(1, L - used - da - need + 1):
                    for e in (ea, -ea):
                        seq.append((h2, e))
                        yield from rec(used + da + ea, h2)
                        seq.pop()
    for ea in range(1, L):
        for e in (ea, -ea):
            seq.append((0, e))
            yield from rec(ea, 0)
            seq.pop()

def main():
    lmin, lmax = int(sys.argv[1]), int(sys.argv[2])
    maxprint = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    for L in range(lmin, lmax + 1):
        t0 = time.time()
        seen, cats, surv = set(), {}, []
        for seq in gen(L):
            m, n, g, top, bot = extremes(seq)
            if peelable(top) or peelable(bot):
                continue
            c = canon(seq)
            if c in seen:
                continue
            seen.add(c)
            cs = list(c)
            w = seq_to_word(cs)
            if min_period(w) < len(w):
                cats['POWER'] = cats.get('POWER', 0) + 1
                continue
            BUDGET[0] = 3000
            ok, why = cert_word(w, 0)
            key = why.split('[')[0] if ok else 'SURVIVOR'
            cats[key] = cats.get(key, 0) + 1
            if not ok:
                surv.append((cs, w, why))
        print('L=%d classes=%d time=%.1fs cats=%s' % (L, len(seen), time.time() - t0, sorted(cats.items())), flush=True)
        for cs, w, why in surv[:maxprint]:
            m, n, g, top, bot = extremes(cs)
            sig = {}
            for h, e in cs:
                sig[h] = sig.get(h, 0) + e
            ones = sorted(h for h in sig if sum(abs(e) for hh, e in cs if hh == h) == 1)
            print(' SURV %s  seq=%s R=%d g=%d top=%s bot=%s sa=%d delta=%s once=%s why=%s'
                  % (word_str(w), cs, n - m, g, top, bot, sum(e for _, e in cs),
                     [sig.get(h, 0) for h in range(n + 1)], ones, why))
            for side, lvl in (('top', n), ('bot', m)):
                print('   %s coeffs: %s' % (side, ' | '.join('%d:%s' % (e, mag_str(u)) for e, u in coefficients(cs, lvl))))
        print('DONE_L=%d' % L, flush=True)
    print('SENTINEL_DONE', flush=True)

if __name__ == '__main__':
    main()
