#!/usr/bin/env python3
"""Local-certificate search for bh-shell-germ's twisted C_2*C_3 enumeration.
X = {0,1}^N (one root, radix 2, lowest digit first: cone [w] = residue sum w_i 2^(i-1) mod 2^|w|).
R = <tau, w, b>, b = x1^-1 a x1 (or x1 a x1^-1), a = odometer.  B = <V, a>.
Goal: elements of R supported in the cone [0]; pulled back to X they form the local group L.
If L contains x0, x1, tau, pi_{00,01}, pi_{00,10} then L >= V (T = <F,tau>, V = <all cone
transpositions>), hence R >= Rist_V([0]), hence R >= V by extreme proximality of <tau,w>, hence R = B.
usage: c2c3_local.py MODE SECONDS   MODE = twist | twistinv | untwisted (control) | planted
"""
import sys, random, time
from rnu_tables import compose, inverse, is_identity_leaf, merge
T0 = time.time()
BUDGET = float(sys.argv[2]) if len(sys.argv) > 2 else 500.0
R2 = [2]
def left(): return BUDGET - (time.time() - T0)
def m(*gs):
    r = gs[-1]
    for g in reversed(gs[:-1]):
        r = merge(compose(g, r), R2)
    return r
def L(a, M, b, N, G=0): return (0, a, M, 0, b, N, G)
ID = [L(0, 1, 0, 1)]
TAU = [L(0, 2, 1, 2), L(1, 2, 0, 2)]
W3 = [L(1, 2, 2, 4), L(2, 4, 0, 4), L(0, 4, 1, 2)]
X0 = [L(0, 2, 0, 4), L(1, 4, 2, 4), L(3, 4, 1, 2)]           # [0]->[00],[10]->[01],[11]->[1]
X1 = [L(0, 2, 0, 2), L(1, 4, 1, 8), L(3, 8, 5, 8), L(7, 8, 3, 4)]
A = [L(0, 1, 0, 1, 1)]
PI_00_01 = [L(0, 4, 2, 4), L(2, 4, 0, 4), L(1, 2, 1, 2)]
PI_00_10 = [L(0, 4, 1, 4), L(1, 4, 0, 4), L(2, 4, 2, 4), L(3, 4, 3, 4)]
def canon(g): return tuple(sorted(merge(g, R2)))
TARGETS = {canon(X0): 'x0', canon(inverse(X0)): 'x0^-1', canon(X1): 'x1', canon(inverse(X1)): 'x1^-1',
           canon(TAU): 'tau', canon(PI_00_01): 'pi_00_01', canon(PI_00_10): 'pi_00_10'}
def nontriv(g): return [x for x in g if not is_identity_leaf(x)]
def carry_free(g): return all(x[6] == 0 for x in g)
def support_cone(g):
    """smallest cone (r mod 2^j) containing all moved leaves' domains, or None if trivial."""
    non = nontriv(g)
    if not non: return None
    j = 0
    while True:
        J = 2 ** (j + 1)
        if all(x[2] % J == 0 for x in non) and len(set(x[1] % J for x in non)) == 1:
            j += 1
        else:
            break
    return (non[0][1] % (2 ** j), 2 ** j)
def pull_back_from0(g):
    """g supported in [0] (residue 0 mod 2): conjugate by psi(y)=2y and return element on X."""
    out = []
    for (e, a, M, f, b, N, G) in g:
        if a % 2 == 0 and M % 2 == 0:
            assert b % 2 == 0 and N % 2 == 0
            out.append((0, a // 2, M // 2, 0, b // 2, N // 2, G))
    return merge(out, R2)
def push_to0(g):
    """if the support lies in a proper cone, conjugate into [0] (by tau if needed) and pull back."""
    c = support_cone(g)
    if c is None or c[1] == 1: return None
    if c[0] % 2 == 1:
        g = m(TAU, g, TAU)
    return pull_back_from0(g)

def main(mode):
    random.seed(5)
    x1i = inverse(X1)
    if mode == 'twist': b = m(x1i, A, X1)
    elif mode == 'twistinv': b = m(X1, A, x1i)
    else: b = A
    gens = [('t', TAU), ('w', W3), ('W', inverse(W3)), ('b', b), ('B', inverse(b))]
    print("== mode", mode, "b leaves", len(b), flush=True)
    pool = {}
    def consider(name, h):
        if h is None: return
        c = canon(h)
        if len(c) == 1 and is_identity_leaf(c[0]): return
        if c in TARGETS: print("  TARGET FOUND", TARGETS[c], "=", name, flush=True)
        if len(c) <= 24 and c not in pool: pool[c] = name
    if mode == 'planted':  # calibration: plant a local copy of x0 in [0]
        planted = m(TAU, TAU)  # identity
        loc = [(0, 2 * a, 2 * M, 0, 2 * bb, 2 * N, G) for (e, a, M, f, bb, N, G) in X0] + [L(1, 2, 1, 2)]
        consider('planted', push_to0(loc))
    # phase 1: random commutators, localized
    tried = 0
    while left() > BUDGET * 0.45:
        w1 = [random.choice(gens) for _ in range(random.randint(1, 5))]
        w2 = [random.choice(gens) for _ in range(random.randint(1, 5))]
        g1 = m(*[t[1] for t in w1]); g2 = m(*[t[1] for t in w2])
        k = m(g1, g2, inverse(g1), inverse(g2))
        tried += 1
        nm = '[%s,%s]' % (''.join(t[0] for t in w1), ''.join(t[0] for t in w2))
        consider(nm, push_to0(k))
    print("  phase1 tried %d, local pool %d (<=24 leaves)" % (tried, len(pool)), flush=True)
    # phase 2: bootstrap inside L (products and commutators of pool elements, keep small)
    items = sorted(pool.items(), key=lambda kv: len(kv[0]))
    items = items[:300]
    cf_small = {}
    it = 0
    while left() > 15 and items:
        (c1, n1) = random.choice(items); (c2, n2) = random.choice(items)
        g1, g2 = list(c1), list(c2)
        for (nm, h) in (('(%s)(%s)' % (n1, n2), m(g1, g2)), ('[%s,%s]' % (n1, n2), m(g1, g2, inverse(g1), inverse(g2)))):
            it += 1
            c = canon(h)
            if len(c) == 1 and is_identity_leaf(c[0]): continue
            if c in TARGETS: print("  TARGET FOUND", TARGETS[c], "=", nm[:300], flush=True)
            if carry_free(c) and len(c) <= 6 and c not in cf_small:
                cf_small[c] = nm
            if len(c) <= 12 and c not in pool and len(items) < 3000:
                pool[c] = nm; items.append((c, nm))
    print("  phase2 products %d, pool %d, small carry-free elements %d" % (it, len(pool), len(cf_small)), flush=True)
    for c, nm in sorted(cf_small.items(), key=lambda kv: len(kv[0]))[:25]:
        print("   cf", len(c), [x[1:6] for x in c], "  via", nm[:120], flush=True)

if __name__ == '__main__':
    main(sys.argv[1])
    print("elapsed", round(time.time() - T0), "s")
