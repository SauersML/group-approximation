#!/usr/bin/env python3
"""Signed-monomial units on Gardam's Soelberg support pair, by SAT.

Ansatz (the shape of Gardam's complex unit of the Promislow group, coefficients +-s^i t^j):
    u = sum_k eps_k alpha^{ex(A_k)} beta^{ey(A_k)} A_k,   v = sum_l del_l alpha^{ex(B_l)} beta^{ey(B_l)} B_l,
with eps_k, del_l in {-1, 0, 1}, ex / ey the x / y exponent sums of the fixed words, and alpha^4 = a,
beta^4 = b for a class (a, b) in {+-1}^2.  S^ab = Z/4 + Z/4 with x, y independent, so for every pair
(k, l) with A_k B_l = g the exponent sums of the concatenated word agree with those of g mod 4, and
    coefficient of g in u v = alpha^{ex_g} beta^{ey_g} * sum_{(k,l)} eps_k del_l a^{m_x(k,l)} b^{m_y(k,l)}
where m_x = (ex(A_k) + ex(B_l) - ex_g) / 4 etc., relative to the reference pair of g (identity: 0).
So u v = 1 is the exact integer sign problem
    sum_{(k,l) in pairs(g)} eps_k del_l a^{m_x} b^{m_y} = [g == 1]   for every g in A B.
Class (1, 1) with alpha = beta = 1 is a +-1-coefficient unit of Z[S] (a counterexample to Higman's
conjecture on S); the other classes give units over Z[zeta_8].  Nontriviality: |supp u| >= 2.

usage: python3 signed_monomial_sat.py [--full]   (--full: require supp u = A, supp v = B)
"""
import sys, itertools
from soelberg_engine import A, B, A_WORDS, B_WORDS, I3, product_table
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153

def expsum(w):
    ex = ey = 0
    for tok in w.split('*'):
        l, n = (tok.split('^') + ['1'])[:2]
        n = int(n)
        ex += n if l == 'x' else -n if l == 'X' else 0
        ey += n if l == 'y' else -n if l == 'Y' else 0
    return ex, ey

N = len(A)
EA = [expsum(w) for w in A_WORDS]
EB = [expsum(w) for w in B_WORDS]
TAB = product_table(A, B)

def build(a, b, full, TAB=TAB, EA=EA, EB=EB, NA=N, NB=N, ONE=I3):
    pool = IDPool()
    z = lambda side, k: pool.id(('z', side, k))   # nonzero
    s = lambda side, k: pool.id(('s', side, k))   # sign is -1
    cl = []
    for g, pairs in TAB.items():
        if g == ONE:
            ref = (0, 0)
        else:
            k0, l0 = pairs[0]
            ref = (EA[k0][0] + EB[l0][0], EA[k0][1] + EB[l0][1])
        pos, neg = [], []
        for (k, l) in pairs:
            dx = EA[k][0] + EB[l][0] - ref[0]
            dy = EA[k][1] + EB[l][1] - ref[1]
            assert dx % 4 == 0 and dy % 4 == 0
            flip = ((dx // 4) % 2 if a == -1 else 0) ^ ((dy // 4) % 2 if b == -1 else 0)
            p = pool.id(('p', k, l)); q = pool.id(('q', k, l))
            za, zb, sa, sb = z('A', k), z('B', l), s('A', k), s('B', l)
            # p <-> za & zb & (sa xor sb xor flip == 0);  q <-> za & zb & (sa xor sb xor flip == 1)
            for (va, vb) in itertools.product((0, 1), repeat=2):
                par = va ^ vb ^ flip
                lits = [-za, -zb, sa if va == 0 else -sa, sb if vb == 0 else -sb]
                # under (sa=va, sb=vb, za, zb): term sign negative iff par == 1
                cl.append(lits + ([q] if par else [p]))
                cl.append(lits + ([-p] if par else [-q]))
            cl += [[-p, za], [-p, zb], [-q, za], [-q, zb]]
            pos.append(p); neg.append(q)
        target = 1 if g == ONE else 0
        lits = pos + [-x for x in neg]
        enc = CardEnc.equals(lits=lits, bound=target + len(neg), vpool=pool, encoding=EncType.totalizer)
        cl += enc.clauses
    zA = [z('A', k) for k in range(NA)]
    if full:
        cl += [[x] for x in zA] + [[z('B', l)] for l in range(NB)]
    else:
        cl += CardEnc.atleast(lits=zA, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses
    # normalization: first nonzero coefficient of u is +1 (scaling by -1)
    for k in range(NA):
        cl.append([-z('A', k), -s('A', k)] + [z('A', m) for m in range(k)])
    return pool, cl, z, s

def solve(a, b, full, limit=50, **data):
    pool, cl, z, s = build(a, b, full, **data)
    NA = data.get('NA', N); NB = data.get('NB', N)
    sols = []
    with Cadical153(bootstrap_with=cl) as S:
        while len(sols) < limit and S.solve():
            m = set(x for x in S.get_model() if x > 0)
            u = [0 if z('A', k) not in m else (-1 if s('A', k) in m else 1) for k in range(NA)]
            v = [0 if z('B', l) not in m else (-1 if s('B', l) in m else 1) for l in range(NB)]
            sols.append((u, v))
            block = []
            for k in range(NA):
                block += [-z('A', k) if u[k] else z('A', k)]
                if u[k]:
                    block += [-s('A', k) if u[k] < 0 else s('A', k)]
            for l in range(NB):
                block += [-z('B', l) if v[l] else z('B', l)]
                if v[l]:
                    block += [-s('B', l) if v[l] < 0 else s('B', l)]
            S.add_clause(block)
    return sols

if __name__ == '__main__':
    full = '--full' in sys.argv
    for a, b in [(1, 1), (1, -1), (-1, 1), (-1, -1)]:
        sols = solve(a, b, full)
        print('class alpha^4=%2d beta^4=%2d  full=%s  solutions found: %d' % (a, b, full, len(sols)))
        for u, v in sols[:4]:
            print('   u =', u)
            print('   v =', v)
