#!/usr/bin/env python3
"""Odd-prime addendum (lane hl-promislow-case-a): for Murray's Theorem 3 units of F_d[P], d = 3, 5, 7,
test at the shadow level whether quotients w1 * w2^-1 among the 64 elements sigma_h(u_i)
(h in the 8 diagonal signs including identity, i in the 8 parameter pairs), and commutators
u g u^-1 g^-1 for g in {a, b, ab, x, y, z}, are nontrivial units with all three definite
shadows signed monomials. Shadows of products are computed in D(F_d); triviality is tested exactly.
"""
import sys, io, itertools, contextlib, importlib.util
here = sys.path[0]
sys.argv = ['tw']
spec = importlib.util.spec_from_file_location('tw', here + '/promislow-shadow-twisted-units.py')
T = importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(T)
R, G = T.R, T.G
lp_add, lp_mul, mono, ONE, zp = R.lp_add, R.lp_mul, R.mono, R.ONE, R.zp
X_, Xi, Y_, Yi = mono(1, 0, 0), mono(-1, 0, 0), mono(0, 1, 0), mono(0, -1, 0)

def murray(d, t_, w_):
    h_ = ONE
    for _ in range(d - 2):
        h_ = lp_mul(h_, lp_add(ONE, zp(1 - 2 * t_, -1)))
    f1 = lp_mul(lp_add(zp(t_), zp(1 - t_)), h_); f2 = lp_mul(zp(w_), h_)
    f3 = lp_mul(zp(w_), lp_add(ONE, zp(2 * t_ - 1)), h_); f4 = lp_mul(zp(w_ + t_), h_)
    f5 = lp_mul(zp(w_), lp_add(zp(t_), zp(1 - t_)), h_); f6 = h_; f7 = zp(2 * t_ - 1)
    p_ = lp_mul(lp_add(ONE, X_), lp_add(ONE, Y_), f1)
    q_ = lp_add(lp_mul(lp_add(ONE, X_), lp_add(Xi, Yi), f2), lp_mul(lp_add(ONE, Yi), f3))
    r_ = lp_add(lp_mul(lp_add(ONE, Yi), lp_add(X_, Y_), f4), lp_mul(lp_add(ONE, X_), f5))
    s_ = lp_add(lp_mul(lp_add(X_, mono(0, 0, 0, 4), Xi, Y_, Yi), f6), f7)
    return T.pqrs_to_gr([p_, q_, r_, s_], d)

def shadows(U, p):
    return {line: R.shadow(R.group_ring_to_pqrs(U, lambda c: c), line, p) for line in 'CAB'}

HS = [(1, 1, 1)] + T.VALID
GENS = {'a': G.a, 'b': G.b, 'ab': G.w(G.a, G.b), 'x': G.w(G.a, G.a), 'y': G.w(G.b, G.b), 'z': G.w(G.a, G.b, G.a, G.b)}
total_hits = 0
for d in (3, 5, 7):
    elems = []
    for t_, w_ in itertools.product((-1, 0, 1, 2), (0, 1)):
        U = murray(d, t_, w_)
        for h in HS:
            SU = T.gr_red(T.gr_apply(U, T.sigma(h)), d)
            elems.append(((t_, w_, h), SU, shadows(SU, d)))
    pairs = hits = 0
    for (k1, U1, S1), (k2, U2, S2) in itertools.permutations(elems, 2):
        pairs += 1
        if all(R.monomial_shadow(R.dmul(S1[l], T.dinv(S2[l], d), d), d) for l in 'CAB'):
            if not T.is_trivial_quotient(U1, U2, d):
                hits += 1
                print('  HIT quotient d=%d %s * %s^-1' % (d, k1, k2))
    comm = chits = 0
    for t_, w_ in itertools.product((-1, 0, 1, 2), (0, 1)):
        U = murray(d, t_, w_)
        SU = shadows(U, d)
        for gname, g in GENS.items():
            comm += 1
            Sg = shadows({g: 1}, d)
            ok = all(R.monomial_shadow(R.dmul(R.dmul(SU[l], Sg[l], d), T.dinv(R.dmul(Sg[l], SU[l], d), d), d), d) for l in 'CAB')
            if ok:
                Ug = T.gr_red({G.mul(k, g): c for k, c in U.items()}, d)
                gU = T.gr_red({G.mul(g, k): c for k, c in U.items()}, d)
                if not T.is_trivial_quotient(Ug, gU, d):
                    chits += 1
                    print('  HIT commutator d=%d (t,w)=%s g=%s' % (d, (t_, w_), gname))
    print('d=%d: %d ordered quotient pairs, %d hits; %d commutators, %d hits' % (d, pairs, hits, comm, chits))
    total_hits += hits + chits
print('TOTAL HITS', total_hits)
print('DONE')
