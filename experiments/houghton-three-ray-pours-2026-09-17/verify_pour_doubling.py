#!/usr/bin/env python3
"""Check the doubling recursion for three-ray pours in H_3.

Conventions as in research/artifacts/zp-houghton-pours-2026-09-17.md, Section 0:
points (x, p), p >= 1, words act on the right and are read left to right.
  lam(x,y): (x,p)->(x,p-1) for p>=2, (x,1)->(y,1), (y,p)->(y,p+1).
  tau(x):   swaps (x,1),(x,2).
Rays are 'a', 'b', 'c'.  The route ray c is the SPECIAL ray of the doubling
  beta(c,p,e) = (c, 2p-1+e),   beta(x,p,e) = (x, 2p-e) for x in {a,b},
  Delta(g) sends beta(y,e) to beta(y.g, e).

Checks (all on every point of depth <= R of every ray, R >= word length + 3,
which is enough: a point deeper than the length of both words is moved by a
pure translation, and depth R pins that translation down):
 (1) Delta(lam_ac) = lam_ac^2, Delta(lam_cb) = lam_cb^2, Delta(lam_ca) = lam_ca^2,
     Delta(lam_bc) = lam_bc^2, computed from the beta formula.
 (2) For each two-ray letter l in {lam_ab, lam_ba, tau_a, tau_b}, a shortest
     two-ray word DH[l] representing Delta(l) (found by BFS), and a shortest
     two-ray word PSI[l] representing lam_ac . l . lam_ca.
 (3) lam_ac lam_cb = lam_ab.
 (4) The recursion N_1 = lam_ab, N_2m = DH(N_m), N_2m+1 = PSI(N_2m) lam_ab
     gives two-ray words with N_m = E^c_(a,b)(m) = lam_ac^m lam_cb^m, checked
     directly for 1 <= m <= MDIRECT; lengths |N_m| are reported up to 2^12.
 (5) Delta is a homomorphism on random words (spot check of Lemma B.1).
 (6) In H_4 (rays a,b,c,d), the same words DH[l], PSI[l] represent the doubling
     with d special and conjugation by lam_da, and the same N_m equals both
     lam_ac^m lam_cb^m and lam_ad^m lam_db^m (m <= MDIRECT).
 (7) The triangle word X_k = lam_ba^k lam_ac^k lam_cb^k is the reversal r_k
     of (b,1..k), for 1 <= k < 25 (used in the R_3 remark, Section 5).
Runtime is roughly 10-15 minutes (dominated by (4) and (6)); the output of
one run is saved in verify_pour_doubling.out.
Used by research/artifacts/zp-houghton-pour-doubling-2026-09-18.md.
"""
import random
import sys

RAYS = ('a', 'b', 'c')
SPECIAL = 'c'


def lam_f(x, y):
    def f(pt):
        r, p = pt
        if r == x:
            return (x, p - 1) if p >= 2 else (y, 1)
        if r == y:
            return (y, p + 1)
        return pt
    return f


def tau_f(x):
    def f(pt):
        r, p = pt
        if r == x and p in (1, 2):
            return (x, 3 - p)
        return pt
    return f


LETTERS = {}
for x in RAYS:
    LETTERS['t' + x] = tau_f(x)
    for y in RAYS:
        if x != y:
            LETTERS['l' + x + y] = lam_f(x, y)

TWO_RAY = ['lab', 'lba', 'ta', 'tb']
INV = {'lab': 'lba', 'lba': 'lab', 'ta': 'ta', 'tb': 'tb'}


def apply(word, pt):
    for s in word:
        pt = LETTERS[s](pt)
    return pt


def beta(x, p, e):
    if x == SPECIAL:
        return (x, 2 * p - 1 + e)
    return (x, 2 * p - e)


def beta_inv(pt):
    x, q = pt
    if x == SPECIAL:
        return (x, (q + 1) // 2, (q + 1) % 2)
    return (x, (q + 1) // 2, q % 2)


def delta_apply(word, pt):
    x, p, e = beta_inv(pt)
    y = apply(word, (x, p))
    return beta(y[0], y[1], e)


def points(R):
    return [(x, p) for x in RAYS for p in range(1, R + 1)]


def same(f, g, R):
    return all(f(pt) == g(pt) for pt in points(R))


def key(word, R):
    return tuple(apply(word, pt) for pt in points(R))


def bfs_word(target, R, maxlen=12):
    """Shortest word in TWO_RAY letters whose action agrees with target
    on all points of depth <= R (target: function on points)."""
    tkey = tuple(target(pt) for pt in points(R))
    frontier = [[]]
    seen = {key([], R)}
    if key([], R) == tkey:
        return []
    for _ in range(maxlen):
        nxt = []
        for w in frontier:
            for s in TWO_RAY:
                if w and INV[w[-1]] == s:
                    continue
                w2 = w + [s]
                k = key(w2, R)
                if k in seen:
                    continue
                seen.add(k)
                if k == tkey:
                    return w2
                nxt.append(w2)
        frontier = nxt
    return None


def main():
    ok = True
    R0 = 12
    # (1) route letters double exactly
    for s in ('lac', 'lcb', 'lca', 'lbc'):
        if not same(lambda pt: delta_apply([s], pt), lambda pt: apply([s, s], pt), R0):
            print('FAIL (1)', s)
            ok = False
    print('(1) Delta(l) = l^2 for l in lac, lcb, lca, lbc:', ok)
    # (2) letter images
    DH, PSI = {}, {}
    for s in TWO_RAY:
        DH[s] = bfs_word(lambda pt: delta_apply([s], pt), R0)
        PSI[s] = bfs_word(lambda pt: apply(['lac', s, 'lca'], pt), R0)
        if DH[s] is None or PSI[s] is None:
            print('FAIL (2)', s)
            ok = False
            continue
        # recheck at larger depth
        R = 3 * (len(DH[s]) + len(PSI[s])) + 10
        assert same(lambda pt: delta_apply([s], pt), lambda pt: apply(DH[s], pt), R)
        assert same(lambda pt: apply(['lac', s, 'lca'], pt), lambda pt: apply(PSI[s], pt), R)
        print('(2)', s, ' DH =', ' '.join(DH[s]), '   PSI =', ' '.join(PSI[s]))
    # (3)
    r3 = same(lambda pt: apply(['lac', 'lcb'], pt), lambda pt: apply(['lab'], pt), R0)
    print('(3) lac lcb = lab:', r3)
    ok = ok and r3
    return ok, DH, PSI


def build_N(M, DH, PSI):
    N = {1: ['lab']}
    for m in range(2, M + 1):
        if m % 2 == 0:
            N[m] = [t for s in N[m // 2] for t in DH[s]]
        else:
            N[m] = [t for s in N[m - 1] for t in PSI[s]] + ['lab']
    return N


def lengths(M, DH, PSI):
    """Exact letter counts of N_m without building the words."""
    cnt = {1: {'lab': 1, 'lba': 0, 'ta': 0, 'tb': 0}}
    for m in range(2, M + 1):
        src = cnt[m // 2] if m % 2 == 0 else cnt[m - 1]
        img = DH if m % 2 == 0 else PSI
        new = {s: 0 for s in TWO_RAY}
        for s, k in src.items():
            for t in img[s]:
                new[t] += k
        if m % 2 == 1:
            new['lab'] += 1
        cnt[m] = new
    return {m: sum(c.values()) for m, c in cnt.items()}


def run(MDIRECT=40, MLEN=4096):
    ok, DH, PSI = main()
    N = build_N(MDIRECT, DH, PSI)
    for m in range(1, MDIRECT + 1):
        E = ['lac'] * m + ['lcb'] * m
        R = max(len(N[m]), 2 * m) + 3
        good = same(lambda pt: apply(E, pt), lambda pt: apply(N[m], pt), R)
        two_ray = all(s in TWO_RAY for s in N[m])
        if not (good and two_ray):
            print('FAIL (4) m =', m)
            ok = False
    print('(4) N_m = E^c_(a,b)(m) as elements, N_m two-ray, for 1 <= m <=', MDIRECT, ':', ok)
    L = lengths(MLEN, DH, PSI)
    for m in (2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096):
        print('    |N_%d| = %d' % (m, L[m]))
    worst = max(L[m] for m in range(1, MLEN + 1) if m >= 2 ** 11)
    print('    max |N_m| over 2^11 <= m <= 2^12:', worst)
    # (5) homomorphism spot check
    rnd = random.Random(1)
    allL = sorted(LETTERS)
    for _ in range(200):
        u = [rnd.choice(allL) for _ in range(rnd.randint(1, 8))]
        v = [rnd.choice(allL) for _ in range(rnd.randint(1, 8))]
        R = 2 * (len(u) + len(v)) + 6
        lhs = lambda pt: delta_apply(u + v, pt)
        rhs = lambda pt: delta_apply(v, delta_apply(u, pt))
        if not same(lhs, rhs, R):
            print('FAIL (5)', u, v)
            ok = False
    print('(5) Delta(uv) = Delta(u)Delta(v) on 200 random pairs:', ok)
    # (7) the triangle word X_k = lam_ba^k lam_ac^k lam_cb^k reverses (b,1..k)
    ok7 = True
    for k in range(1, 25):
        X = ['lba'] * k + ['lac'] * k + ['lcb'] * k

        def rev(pt, k=k):
            r, p = pt
            return (r, k + 1 - p) if (r == 'b' and p <= k) else pt
        if not same(lambda pt: apply(X, pt), rev, 3 * k + 3):
            print('FAIL (7) k =', k)
            ok7 = False
    print('(7) lam_ba^k lam_ac^k lam_cb^k = reversal of (b,1..k), k < 25:', ok7)
    ok = ok and ok7
    ok = four_ray_check(DH, PSI, N, MDIRECT) and ok
    print('ALL OK' if ok else 'SOME CHECK FAILED')
    return ok


def four_ray_check(DH, PSI, N, MDIRECT):
    """(6) In H_4 with rays a,b,c,d: the SAME words DH[l], PSI[l] represent
    Delta_d(l) (doubling with d special, a,b,c ordinary) and lam_ad l lam_da,
    and the same N_m equals the d-routed pour lam_ad^m lam_db^m and also
    lam_ac^m lam_cb^m.  So the skew square splits through N_m."""
    global RAYS, SPECIAL
    RAYS, SPECIAL = ('a', 'b', 'c', 'd'), 'd'
    for x in RAYS:
        LETTERS['t' + x] = tau_f(x)
        for y in RAYS:
            if x != y:
                LETTERS['l' + x + y] = lam_f(x, y)
    ok = True
    for s in TWO_RAY:
        R = 30
        if not same(lambda pt: delta_apply([s], pt), lambda pt: apply(DH[s], pt), R):
            print('FAIL (6) Delta_d', s)
            ok = False
        if not same(lambda pt: apply(['lad', s, 'lda'], pt), lambda pt: apply(PSI[s], pt), R):
            print('FAIL (6) psi_d', s)
            ok = False
    for m in range(1, MDIRECT + 1):
        R = max(len(N[m]), 2 * m) + 3
        Ed = ['lad'] * m + ['ldb'] * m
        Ec = ['lac'] * m + ['lcb'] * m
        if not (same(lambda pt: apply(Ed, pt), lambda pt: apply(N[m], pt), R)
                and same(lambda pt: apply(Ec, pt), lambda pt: apply(N[m], pt), R)):
            print('FAIL (6) m =', m)
            ok = False
    print('(6) in H_4: same DH, PSI words work with d special; N_m = E^c(m) = E^d(m)'
          ' for 1 <= m <=', MDIRECT, ':', ok)
    RAYS, SPECIAL = ('a', 'b', 'c'), 'c'
    return ok


if __name__ == '__main__':
    sys.exit(0 if run() else 1)
