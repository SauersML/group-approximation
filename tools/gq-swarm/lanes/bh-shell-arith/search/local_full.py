#!/usr/bin/env python3
"""Local-fullness exploration for Gamma_U = R_nu ∩ Rist(root 1), small unequal-radix instance.
usage: local_full.py KIND SECONDS      KIND = small (Z/4*Z/5, h=3,4) | smallctl (Z/4*Z/4, h=3)
Collect elements of R_nu that are the identity on root 0, then search products for
(a) slope-changing cone transpositions (involution swapping two cones of different moduli),
(b) localized odometers, (c) the smallest non-slope-1 elements.  Evidence only.
"""
import sys, random, time
from rnu_tables import *

T0 = time.time()
BUDGET = float(sys.argv[2]) if len(sys.argv) > 2 else 400.0
def left():
    return BUDGET - (time.time() - T0)

def setup(kind):
    Z4 = cyclic_group(4); Z5 = cyclic_group(5)
    x = Z4[1]            # order 4 (x != x^-1)
    if kind == 'small':
        z = Z5[1]
        G0 = labeling(Z4, {x: 2}); G1 = labeling(Z5, {z: 3}); radices = [3, 4]
    else:
        z = Z4[1]
        G0 = labeling(Z4, {x: 2}); G1 = labeling(Z4, {z: 2}); radices = [3]
    return G0, G1, x, z, radices

def inv_el(G, x):
    return [y for y in G[1][1:] if perm_mul(x, y) == G[0]][0]

def canon(g, radices):
    return tuple(sorted(merge(g, radices)))

def on_root0_identity(g):
    return all(is_identity_leaf(L) for L in g if L[0] == 0)

def classify(g):
    non = [L for L in g if not is_identity_leaf(L)]
    nonunit = [L for L in non if L[5] != L[2]]
    return len(non), len(nonunit)

def is_cone_transposition(g):
    non = [L for L in g if not is_identity_leaf(L)]
    if len(non) != 2: return False
    L1, L2 = non
    # L1: c -> c', L2: c' -> c, carry-free inverse pair
    return (L1[3], L1[4], L1[5]) == (L2[0], L2[1], L2[2]) and (L2[3], L2[4], L2[5]) == (L1[0], L1[1], L1[2]) \
        and L1[6] == 0 and L2[6] == 0

def main(kind):
    random.seed(11)
    G0, G1, x, z, R = setup(kind)
    m = lambda *gs: mul(*gs, radices=R)
    lx, lz = lam(x, G0, 0), lam(z, G1, 1)
    lxi, lzi = lam(inv_el(G0, x), G0, 0), lam(inv_el(G1, z), G1, 1)
    s = S_SHIFT; S = inverse(s)
    k = m(S, lxi, lzi, s, lx, lz)
    print("== %s radices %s: k leaves=%d root0-identity=%s moved/nonunit=%s" % (kind, R, len(k), on_root0_identity(k), classify(k)), flush=True)
    gens = [('x', lx), ('X', lxi), ('z', lz), ('Z', lzi), ('s', s), ('S', S)]
    # 1. conjugates w k^{±1} w^-1 supported in root 1
    pool = {}
    def add(name, g):
        c = canon(g, R)
        if c not in pool and len(c) > 0 and not all(is_identity_leaf(L) for L in c):
            pool[c] = name
    add('k', k); add('K', inverse(k))
    frontier = [('', [(0, 0, 1, 0, 0, 1, 0), (1, 0, 1, 1, 0, 1, 0)])]
    seen = {canon(frontier[0][1], R)}
    for depth in range(5):
        nf = []
        for (wn, w) in frontier:
            for (gn, g) in gens:
                w2 = m(g, w); c = canon(w2, R)
                if c in seen: continue
                seen.add(c); nf.append((gn + wn, w2))
                if left() < BUDGET * 0.6: break
        frontier = nf
        for (wn, w) in frontier:
            wi = inverse(w)
            for (kn, kk) in (('k', k), ('K', inverse(k))):
                c = m(w, kk, wi)
                if on_root0_identity(c):
                    add(wn + '.' + kn, c)
        print("  depth %d: words %d, U-supported pool %d, t=%ds" % (depth + 1, len(frontier), len(pool), time.time() - T0), flush=True)
        if left() < BUDGET * 0.6: break
    # 2. products / commutators of pool elements, look for small elements
    items = sorted(pool.items(), key=lambda kv: len(kv[0]))[:200]
    best = []; ctr = 0; odom = 0
    tried = 0
    while left() > 20 and items:
        (c1, n1) = random.choice(items); (c2, n2) = random.choice(items)
        g1, g2 = list(c1), list(c2)
        for (nm, h) in (('[%s,%s]' % (n1, n2), m(g1, g2, inverse(g1), inverse(g2))), ('%s*%s' % (n1, n2), m(g1, g2))):
            tried += 1
            if all(is_identity_leaf(L) for L in h): continue
            nmv, nnu = classify(h)
            if is_cone_transposition(h):
                ctr += 1
                non = [L for L in h if not is_identity_leaf(L)]
                if non[0][2] != non[0][5]:
                    print("  SLOPE-CHANGING CONE TRANSPOSITION:", nm, non, flush=True)
            best.append((nmv, nnu, nm))
            if nmv <= 12 and len(items) < 400:
                items.append((canon(h, R), nm))
    best.sort()
    print("  tried %d products; cone transpositions %d" % (tried, ctr), flush=True)
    for b in best[:15]:
        print("   moved=%d nonunit=%d  %s" % b, flush=True)
    nonunit_small = [b for b in best if b[1] > 0][:10]
    print("  smallest with non-unit slope:", nonunit_small[:5], flush=True)

if __name__ == '__main__':
    main(sys.argv[1])
    print("elapsed", round(time.time() - T0), "s")
