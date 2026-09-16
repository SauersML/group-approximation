#!/usr/bin/env python3
"""Exact and numerical checks for radu-mark-is-bounded-by-every-vertical-elliptic-element.

Radu's BMW lattice
    Gamma_R = <a,b,c,x,y,z | involutions, axax, ayay, azbz, bxbx, bycy, cxcz>,
C = <a,b,c>, V = <x,y,z>, delta = xz, u = y delta^2 y, T_v = Gamma_R / C.
Elements are stored in the normal form (v, h) = v*h with v a reduced V-word and
h a reduced C-word; the square table pushes C-letters through V-letters.

Part A (exact, symbolic):
  A1  the six relators, (E1), (E2), (E4), u^2 = y delta^4 y, delta b delta^-1 = a,
      delta^4 != 1;
  A2  the local action of C at o is chi(h) = (-1)^(number of c in h), which swaps
      xC and zC and fixes yC;
  A3  for every reduced gamma in C of length 1..LMAX: the fixing radius r(gamma)
      (largest r with B(o,r) fixed pointwise) is finite, via the section automaton;
      the boundary vertex v (depth r) ends in y or is o; pushing gamma through v z
      takes L(r+1) square moves and gives v x k with k in C; the normal-form
      identity gamma = v x k z v^-1 holds; k' = k or kb has even b-parity and
      commutes with u; r(gamma) <= 3 N_+(L) + 1, and r <= 2 for odd L; r = 0 iff #c is odd,
      r = 1 iff #c is even and #b odd, r = 2 for odd L with #b, #c even; for L <= LCROSS the radius is
      cross-checked by brute force on all vertices of depth <= r+1.
Part B (numerical sanity check of the finite inequality and its three steps):
  exact involution almost actions obtained by sparse involutive surgery on the
  regular action of the abelianization; every intermediate inequality of the
  proof is evaluated with normalized Hamming distance.

Single-threaded, deterministic (seeded).  Usage: elliptic_support_check.py [LMAX]
"""
import random
import sys
from collections import deque

TABLE = {('a', 'x'): ('x', 'a'), ('a', 'y'): ('y', 'a'), ('a', 'z'): ('z', 'b'),
         ('b', 'x'): ('x', 'b'), ('b', 'y'): ('y', 'c'), ('b', 'z'): ('z', 'a'),
         ('c', 'x'): ('z', 'c'), ('c', 'y'): ('y', 'b'), ('c', 'z'): ('x', 'c')}


def red(w):
    st = []
    for l in w:
        if st and st[-1] == l:
            st.pop()
        else:
            st.append(l)
    return tuple(st)


def push(h, v):
    """h a C-word, v a V-word; return (v', h') with h v = v' h' (letterwise, L*|v| moves)."""
    h = list(h)
    out = []
    for s in v:
        cur = s
        newh = []
        for l in reversed(h):
            s2, l2 = TABLE[(l, cur)]
            newh.append(l2)
            cur = s2
        h = list(reversed(newh))
        out.append(cur)
    return tuple(out), tuple(h)


def mul(g1, g2):
    v1, h1 = g1
    v2, h2 = g2
    v2p, h1p = push(h1, v2)
    return (red(v1 + v2p), red(h1p + h2))


def prod(*gs):
    g = ((), ())
    for x in gs:
        g = mul(g, x)
    return g


def inv(g):
    v, h = g
    return mul(((), tuple(reversed(h))), (tuple(reversed(v)), ()))


def el(word):
    """Element of Gamma_R from a string of letters."""
    g = ((), ())
    for l in word:
        g = mul(g, ((l,), ()) if l in 'xyz' else ((), (l,)))
    return g


ONE = ((), ())
FAIL = []


def check(name, cond):
    if not cond:
        FAIL.append(name)
        print('FAIL', name)


def chi(h):
    return -1 if h.count('c') % 2 else 1


def parity_b(h):
    return h.count('b') % 2


def reduced_c_words(L):
    if L == 0:
        yield ()
        return
    def rec(prefix):
        if len(prefix) == L:
            yield tuple(prefix)
            return
        for l in 'abc':
            if not prefix or prefix[-1] != l:
                prefix.append(l)
                yield from rec(prefix)
                prefix.pop()
    yield from rec([])


def part_a1():
    a, b, c, x, y, z = (el(s) for s in 'abcxyz')
    for rel in ['axax', 'ayay', 'azbz', 'bxbx', 'bycy', 'cxcz']:
        check('relator ' + rel, el(rel) == ONE)
    d = el('xz')
    d2 = mul(d, d)
    dm2 = inv(d2)
    u = prod(y, d2, y)
    check('E1 da=bd', mul(d, a) == mul(b, d))
    check('E1 db=ad', mul(d, b) == mul(a, d))
    check('E2 a d^2 = d^2 a', mul(a, d2) == mul(d2, a))
    check('E2 b d^2 = d^2 b', mul(b, d2) == mul(d2, b))
    check('E2 c d^2 c = d^-2', prod(c, d2, c) == dm2)
    check('E4 aua=u', prod(a, u, a) == u)
    check('E4 cuc=u', prod(c, u, c) == u)
    check('E4 bub=u^-1', prod(b, u, b) == inv(u))
    check('u^2 = y d^4 y', mul(u, u) == prod(y, d2, d2, y))
    check('d b d^-1 = a', prod(d, b, inv(d)) == a)
    db = mul(d, b)
    check('(db) b (db)^-1 = a', prod(db, b, inv(db)) == a)
    check('delta^4 != 1', prod(d2, d2) != ONE)
    # calibration (K1): w = [delta^2, u] is a reduced V-word of length 20
    w = prod(d2, u, dm2, inv(u))
    check('K1 w in V, reduced, length 20', w[1] == () and red(w[0]) == w[0] and len(w[0]) == 20)
    check('K1 w spelled xzxz yxzxzy zxzx yzxzxy', w[0] == tuple('xzxzyxzxzyzxzxyzxzxy'))
    # lambda-derivations used in the proof: letter counts of each rewriting
    check('a y = y a', mul(a, y) == mul(y, a))
    check('c y = y b', mul(c, y) == mul(y, b))
    check('b y = y c', mul(b, y) == mul(y, c))
    print('A1 relators and identities checked')
    return u


def part_a2():
    ok = True
    for L in range(0, 7):
        for h in reduced_c_words(L):
            for s, t in (('x', 'z'), ('y', 'y'), ('z', 'x')):
                vp, _ = push(h, (s,))
                want = (s,) if chi(h) == 1 else (t,)
                ok = ok and vp == want
    check('A2 local action at o is chi', ok)
    print('A2 local action at o: chi(h) = (-1)^{#c}, swaps x,z, fixes y (all h, |h| <= 6)')


def fixing_radius(gamma):
    """BFS on (section, last letter).  Returns (r, v) or (None, None) if gamma fixes T_v."""
    g = red(gamma)
    if chi(g) == -1:
        return 0, ()
    start = (g, None)
    seen = {start}
    q = deque([(g, (), None)])
    while q:
        h, v, last = q.popleft()
        for s in 'xyz':
            if s == last:
                continue
            s2, h2 = push(h, (s,))
            assert s2 == (s,)  # chi(h) = +1 fixes every neighbour
            h2 = red(h2)
            if chi(h2) == -1:
                return len(v) + 1, v + (s,)
            key = (h2, s)
            if key not in seen:
                seen.add(key)
                q.append((h2, v + (s,), s))
    return None, None


def brute_radius(gamma, rmax):
    """Largest r <= rmax with B(o,r) fixed, by acting on all reduced V-words."""
    frontier = [()]
    for depth in range(1, rmax + 2):
        new = []
        for v in frontier:
            for s in 'xyz':
                if v and v[-1] == s:
                    continue
                w = v + (s,)
                if push(gamma, w)[0] != w:
                    return depth - 1
                new.append(w)
        frontier = new
    return None


def part_a3(u, LMAX, LCROSS):
    print('A3 section automaton, reduced gamma in C with 1 <= |gamma| <= %d' % LMAX)
    print('   L   #gamma  max r  #(r=0) #(r=1) #(r=2) #(r>=3)  N_+(L)  max 4L(r+4)+48')
    worst = {}
    obs_violations = []
    for L in range(1, LMAX + 1):
        nplus = sum(1 for m in range(0, L + 1) for h in reduced_c_words(m) if chi(h) == 1)
        count = 0
        maxr = -1
        hist = [0, 0, 0, 0]
        maxconst = 0
        for gamma in reduced_c_words(L):
            count += 1
            r, v = fixing_radius(gamma)
            if r is None:
                check('A3 nontrivial gamma acts nontrivially %s' % ''.join(gamma), False)
                continue
            check('A3 r <= 3 N_+(L) + 1 %s' % ''.join(gamma), r <= 3 * nplus + 1)
            if L % 2 == 1:
                check('A3 odd length gives r <= 2 %s' % ''.join(gamma), r <= 2)
            nc, nb = gamma.count('c') % 2, gamma.count('b') % 2
            check('A3 r = 0 iff #c odd %s' % ''.join(gamma), (r == 0) == (nc == 1))
            check('A3 r = 1 iff #c even, #b odd %s' % ''.join(gamma),
                  (r == 1) == (nc == 0 and nb == 1))
            if L % 2 == 1 and nc == 0 and nb == 0:
                check('A3 odd L, #b and #c even gives r = 2 %s' % ''.join(gamma), r == 2)
            if r > max(2, L - 1):
                obs_violations.append((''.join(gamma), r))
            check('A3 boundary vertex ends in y or is o %s' % ''.join(gamma),
                  len(v) == 0 or v[-1] == 'y')
            vout, k = push(gamma, v + ('z',))
            check('A3 gamma v z = v x k %s' % ''.join(gamma), vout == v + ('x',))
            check('A3 |k| = L %s' % ''.join(gamma), len(k) == L)
            vrev = tuple(reversed(v))
            ident = prod((v, ()), (('x',), ()), ((), red(k)), (('z',), ()), (vrev, ()))
            check('A3 gamma = v x k z v^-1 %s' % ''.join(gamma), ident == ((), gamma))
            kp = red(k + ('b',)) if parity_b(k) else red(k)
            check('A3 k\' even b-parity %s' % ''.join(gamma), parity_b(kp) == 0)
            check('A3 k\' commutes with u %s' % ''.join(gamma),
                  mul(u, ((), kp)) == mul(((), kp), u))
            if L <= LCROSS:
                br = brute_radius(gamma, r + 1)
                check('A3 brute radius %s' % ''.join(gamma), br == r)
            maxr = max(maxr, r)
            hist[min(r, 3)] += 1
            const = 4 * L * (r + 4) + 48
            maxconst = max(maxconst, const)
            if r == maxr:
                worst[L] = (''.join(gamma), r, ''.join(v))
        print('  %2d  %6d  %5d  %6d %6d %6d %7d  %6d  %d' %
              (L, count, maxr, hist[0], hist[1], hist[2], hist[3], nplus, maxconst))
    print('   proven bounds checked: r <= 3 N_+(L) + 1 for all gamma, r <= 2 for odd L,')
    print('   r = 0 iff #c odd, r = 1 iff #c even and #b odd, r = 2 for odd L with #b, #c even')
    print('   observed bound r <= max(2, L-1): %d exceptions' % len(obs_violations))
    print('   a word attaining max r, with its boundary vertex v:')
    for L in sorted(worst):
        g, r, v = worst[L]
        print('   L=%d gamma=%s r=%d v=%s' % (L, g, r, v if v else '(o)'))


# ---------------------------------------------------------------- Part B

def perm_mul(p, q):
    """(p q)(i) = p(q(i)): apply q first."""
    return [p[i] for i in q]


def word_perm(word, gens, n):
    """Permutation of the word w = l_1 ... l_m acting on the left: w(i) = l_1(...l_m(i))."""
    res = list(range(n))
    for l in word:
        res = perm_mul(res, gens[l])
    return res


def dist(p, q):
    n = len(p)
    return sum(1 for i in range(n) if p[i] != q[i]) / n


def surgery(sigma, t, rng):
    """t involutive surgeries on an involution: pick p,q with {p,sp},{q,sq} disjoint,
    redefine p<->q, sp<->sq.  The result is again an involution."""
    s = list(sigma)
    n = len(s)
    for _ in range(t):
        while True:
            p = rng.randrange(n)
            q = rng.randrange(n)
            sp, sq = s[p], s[q]
            if len({p, q, sp, sq}) == 4:
                break
        s[p], s[q], s[sp], s[sq] = q, p, sq, sp
    return s


def part_b(u_word_unused, trials, seed):
    rng = random.Random(seed)
    words = ['ab', 'ac', 'bc', 'abab', 'acac', 'abc' * 2, 'abcb', 'acbcab', 'a', 'c']
    info = {}
    for w in words:
        r, v = fixing_radius(tuple(w))
        vout, k = push(tuple(w), v + ('z',))
        kb = parity_b(k)
        kp = ''.join(k) + ('b' if kb else '')
        info[w] = (r, ''.join(v), ''.join(k), kp, kb)
    min_slack = {'final': 1e9, 'step1': 1e9, 'step3': 1e9, 'lambda': 1e9, 'kappa': 1e9}
    min_ratio = 1e9  # (final right side - mark) / eps over instances with eps > 0
    max_mark = 0.0
    nonvacuous = 0
    positive_eps = 0
    for trial in range(trials):
        m = rng.choice([50, 200, 800])
        n = 8 * m
        # regular action of the abelianization Z/2^3 on 8m points: a=b=c flip bit0, x=z bit1, y bit2
        def flip(bit):
            return [i ^ (1 << bit) for i in range(n)]
        base = {'a': flip(0), 'b': flip(0), 'c': flip(0), 'x': flip(1), 'z': flip(1), 'y': flip(2)}
        t = rng.choice([0, 1, 2, 5, 10, 20])
        gens = {l: surgery(base[l], rng.randrange(0, t + 1), rng) for l in 'abcxyz'}
        for l in 'abcxyz':
            assert perm_mul(gens[l], gens[l]) == list(range(n))
        idp = list(range(n))
        e = [dist(word_perm(r, gens, n), idp) for r in ['axax', 'ayay', 'azbz', 'bxbx', 'bycy', 'cxcz']]
        eps = max(e)
        mark = dist(word_perm('xzxzxzxz', gens, n), idp)
        uw = 'y' + 'xzxz' + 'y'
        lam = {'a': e[0] + 2 * e[1] + 2 * e[2] + e[3],
               'c': e[0] + 2 * e[2] + e[3] + 2 * e[4],
               'b': 2 * e[4] + 4 * e[5]}
        up = word_perm(uw, gens, n)
        uinv = word_perm(uw[::-1], gens, n)
        for l in 'abc':
            conj = word_perm(l + uw + l, gens, n)
            target = uinv if l == 'b' else up
            min_slack['lambda'] = min(min_slack['lambda'], lam[l] - dist(conj, target))
        mu = max(lam.values())
        for w, (r, v, k, kp, kb) in info.items():
            L = len(w)
            g = word_perm(w, gens, n)
            dg = dist(g, idp)
            # step 1: d(gamma, v x k z v^-1) <= L (r+1) eps, hence |d(gamma,1) - d(k,delta)| <= that
            rhs1 = word_perm(v + 'x' + k + 'z' + v[::-1], gens, n)
            min_slack['step1'] = min(min_slack['step1'], L * (r + 1) * eps - dist(g, rhs1))
            dkd = dist(word_perm(k, gens, n), word_perm('xz', gens, n))
            # step 3: d(u k', k' u) <= sum of lambda over letters of k'
            s3 = dist(word_perm(uw + kp, gens, n), word_perm(kp + uw, gens, n))
            min_slack['step3'] = min(min_slack['step3'], sum(lam[l] for l in kp) - s3)
            dp = 'xz' + ('b' if kb else '')
            kappa = dist(word_perm(uw + dp, gens, n), word_perm(dp + uw, gens, n))
            min_slack['kappa'] = min(min_slack['kappa'], 2 * dkd + len(kp) * mu - kappa)
            final_rhs = 4 * dg + (4 * L * (r + 4) + 48) * eps
            min_slack['final'] = min(min_slack['final'], final_rhs - mark)
            if eps > 0:
                positive_eps += 1
                min_ratio = min(min_ratio, (final_rhs - mark) / eps)
                max_mark = max(max_mark, mark)
                if final_rhs < 1:
                    nonvacuous += 1
    for key, val in min_slack.items():
        check('B slack %s >= 0' % key, val >= -1e-12)
    print('B %d perturbed almost actions (n = 400..6400, t <= 20 surgeries per generator), words %s'
          % (trials, ','.join(words)))
    print('  boundary data: ' + '; '.join('%s: r=%d v=%s k=%s k\'=%s' % (w, i[0], i[1] or 'o', i[2], i[3])
                                         for w, i in info.items()))
    print('  minimal slacks: ' + ', '.join('%s=%.5f' % kv for kv in min_slack.items()))
    print('  instances (action, word) with eps > 0: %d; among them right side < 1: %d' % (positive_eps, nonvacuous))
    print('  over eps > 0: min (right side - d(delta^4,1))/eps = %.3f, max d(delta^4,1) = %.5f' % (min_ratio, max_mark))


def main():
    LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    LCROSS = min(LMAX, 7)
    u = part_a1()
    part_a2()
    part_a3(u, LMAX, LCROSS)
    part_b(None, trials=120, seed=20260916)
    print('ALL_OK' if not FAIL else 'FAILURES: %d' % len(FAIL))


if __name__ == '__main__':
    main()
