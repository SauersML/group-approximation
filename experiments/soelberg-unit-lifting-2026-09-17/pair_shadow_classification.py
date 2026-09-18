#!/usr/bin/env python3
"""Rational units on Gardam's Soelberg support pair (A, B), using the definite shadows.

Input facts (soelberg-gardam-unit-has-no-integral-lift):
  rho1: x -> t, y -> u   and   rho2: x -> u, y -> t   are ring homomorphisms Z[S] -> D(Z), and every
  unit of Z[S] maps to a signed monomial +-t^m u^e under each.  By rational-units-rescale-to-integral-units
  (S is torsion-free elementary amenable) a unit U of Q[S] is c U0 with U0 in Z[S]^x, so
  rho_i(U) = lambda_i * (monomial), lambda_i in Q^x.

System for a nontrivial unit U = sum u_k A_k, V = U^{-1} = sum v_l B_l of Q[S]:
  * rescale U so that lambda_1 = 1 (V absorbs 1/lambda_1);
  * choose the monomials m1 = rho1(U) (among the monomials of rho1(A)), m2 with rho2(U) = lam * m2;
  * linear equations: rho1(U) = m1, rho2(U) = lam m2, rho1(V) = m1^{-1}, rho2(V) = mu m2^{-1}, lam mu = 1;
  * bilinear equations U V = 1;
  * localization (i, j): u_k = 0 for k < j, k != i, and w u_i u_j = 1 (first two nonzero coefficients),
    restricted to the 11 pairs (i, j) surviving the no-unique-product SAT pruning of build_system.py.
Every nontrivial unit of Q[S] supported in A with inverse supported in B satisfies one of these systems.
All systems are written for msolve over Q (characteristic 0); output [-1] means no solution over Q-bar.

usage: python3 pair_shadow_classification.py outdir [char]   (char: 0 (default) or a prime < 2^31)
"""
import sys, os
from soelberg_engine import A, B, A_WORDS, B_WORDS, I3, product_table
from soelberg_definite_shadows import image_word, mono

N = len(A)
TAB = product_table(A, B)
VIABLE = [(1, 2), (1, 3), (1, 4), (1, 5), (1, 7), (2, 3), (2, 4), (2, 5), (2, 9), (3, 4), (5, 6)]  # 1-based

RHO = {1: (mono(1, 1, 0), mono(1, 0, 1)), 2: (mono(1, 0, 1), mono(1, 1, 0))}

def signed(w, r):
    gx, gy = RHO[r]
    im = image_word(w, gx, gy)
    assert len(im) == 1
    (key, c), = im.items()
    return key, c

def inverse_mono(key):
    m, e = key
    return ((-m, 0), 1) if e == 0 else ((m, 1), -1)

SA = {r: [signed(w, r) for w in A_WORDS] for r in (1, 2)}
SB = {r: [signed(w, r) for w in B_WORDS] for r in (1, 2)}

def classes(S):
    out = {}
    for k, (key, c) in enumerate(S):
        out.setdefault(key, []).append((k, c))
    return out

def lin(terms, rhs):
    s = '+'.join('%d*%s' % (c, v) for c, v in terms).replace('+-', '-')
    if rhs:
        s += rhs if rhs[0] in '+-' else '+' + rhs
    return s

def system(m1, m2, i, j):
    zero = set(k for k in range(j) if k != i)
    uv = lambda k: 'u%d' % (k + 1)
    vv = lambda l: 'v%d' % (l + 1)
    polys = []
    # rho1(U) = m1
    for key, mem in classes(SA[1]).items():
        terms = [(c, uv(k)) for k, c in mem if k not in zero]
        s = lin(terms, '-1' if key == m1 else '')
        polys.append(s if terms else ('-1' if key == m1 else None))
    # rho2(U) = lam m2
    for key, mem in classes(SA[2]).items():
        terms = [(c, uv(k)) for k, c in mem if k not in zero]
        if key == m2:
            terms.append((-1, 'lam'))
        if terms:
            polys.append(lin(terms, ''))
    # rho1(V) = m1^{-1}
    k1, c1 = inverse_mono(m1)
    cl = classes(SB[1])
    if k1 not in cl:
        return None
    for key, mem in cl.items():
        terms = [(c, vv(l)) for l, c in mem]
        polys.append(lin(terms, ('-%d' % c1 if c1 > 0 else '+%d' % -c1) if key == k1 else ''))
    # rho2(V) = mu m2^{-1}
    k2, c2 = inverse_mono(m2)
    cl = classes(SB[2])
    if k2 not in cl:
        return None
    for key, mem in cl.items():
        terms = [(c, vv(l)) for l, c in mem]
        if key == k2:
            terms.append((-c2, 'mu'))
        polys.append(lin(terms, ''))
    polys.append('lam*mu-1')
    # U V = 1
    for g, pairs in TAB.items():
        terms = ['%s*%s' % (uv(k), vv(l)) for (k, l) in pairs if k not in zero]
        s = '+'.join(terms)
        if g == I3:
            s = (s + '-1') if s else '-1'
        if s:
            polys.append(s)
    polys.append('w*%s*%s-1' % (uv(i), uv(j)))
    if any(p is None for p in polys):
        polys = [p for p in polys if p is not None]
    vars_ = [uv(k) for k in range(N) if k not in zero] + [vv(l) for l in range(N)] + ['lam', 'mu', 'w']
    return vars_, polys

if __name__ == '__main__':
    outdir = sys.argv[1]
    char = sys.argv[2] if len(sys.argv) > 2 else '0'
    os.makedirs(outdir, exist_ok=True)
    M1 = sorted(classes(SA[1]))
    M2 = sorted(classes(SA[2]))
    print('rho1 monomial classes of A:', len(M1), ' rho2 monomial classes of A:', len(M2))
    count = skipped = 0
    for (i1, j1) in VIABLE:
        i, j = i1 - 1, j1 - 1
        for m1 in M1:
            for m2 in M2:
                res = system(m1, m2, i, j)
                if res is None:
                    skipped += 1
                    continue
                vs, ps = res
                fn = 'ps_%02d_%02d_%d%d%d_%d%d%d.ms' % (i1, j1, m1[0] + 4, m1[1], 0, m2[0] + 4, m2[1], 0)
                with open(os.path.join(outdir, fn), 'w') as f:
                    f.write(','.join(vs) + '\n' + char + '\n' + ',\n'.join(ps) + '\n')
                count += 1
    print('systems written:', count, ' cases with inverse monomial outside rho(B) (no unit, skipped):', skipped)
