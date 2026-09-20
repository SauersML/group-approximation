"""Toeplitz relative-commutant scout in L = L_{F_2}(1,2).

For a unit u put S = u s_0, S' = t_0 u^{-1} (so S'S = 1) and P = 1 - S S'.
Compute C(S,S') = {T : TS = ST, TS' = S'T} inside the box V_{N,L} of commutant.py,
then the compression kappa(T) = P T P and, for each basis element and for random
combinations, the rank of {P, kappa, kappa^2, ..., kappa^d}.  A rank < d+1 exhibits
a polynomial relation (kappa algebraic); the claim
toeplitz-commutant-compression-detects-polynomial-pairs says a transcendental kappa
would refute leavitt-algebras-contain-no-two-variable-polynomial-ring at k = F_2.
"""
import random, sys
from l2 import El, words, ONE, ZERO, s0, s1, t0, t1
from commutant import box_basis, nullspace, combo, rank

def tagged(e, D, index, tag):
    e = e.extend(D)
    v = 0
    for m, S in e.T.items():
        for w in S:
            key = (tag, m, w)
            if key not in index:
                index[key] = len(index)
            v ^= 1 << index[key]
    return v

def rel_commutant(S, Sp, N, L):
    basis = box_basis(N, L)
    D = max(S.N, Sp.N) + N
    index = {}
    vecs = [tagged(S * b + b * S, D, index, 0) ^ tagged(Sp * b + b * Sp, D, index, 1)
            for b in basis]
    return [combo(basis, c) for c in nullspace(vecs)]

def span_rank(els):
    D = max(e.N for e in els)
    index = {}
    return rank([tagged(e, D, index, 0) for e in els])

def power_rank(k, P, d):
    pw = [P]
    cur = P
    for _ in range(d):
        cur = cur * k
        pw.append(cur)
    return span_rank(pw)

s = El.s; t = El.t
UNITS = {
    '1+s00t1': (ONE + s('00') * t('1'), ONE + s('00') * t('1')),
    '1+s0t1': (ONE + s('0') * t('1'), ONE + s('0') * t('1')),
    '1+s1t00': (ONE + s('1') * t('00'), ONE + s('1') * t('00')),
    '1+s0t10': (ONE + s('0') * t('10'), ONE + s('0') * t('10')),
}
a, b = UNITS['1+s00t1'][0], UNITS['1+s1t00'][0]
UNITS['(1+s00t1)(1+s1t00)'] = (a * b, b * a)
sw = s('00') * t('01') + s('01') * t('00') + s('1') * t('1')
UNITS['swap00_01'] = (sw, sw)
UNITS['swap*(1+s00t1)'] = (sw * a, a * sw)
c = UNITS['1+s0t10'][0]
UNITS['(1+s0t10)(1+s1t00)(1+s00t1)'] = (c * b * a, a * b * c)

flip = s('00') * t('00') + s('10') * t('01') + s('01') * t('10') + s('11') * t('11')
UNITS['flip (control: C contains M_2)'] = (flip, flip)

def main(N=2, L=3, d=6, trials=8, seed=0, only=None):
    rng = random.Random(seed)
    # control: the detector sees transcendence of s_0 in L (rank d+1)
    print('control power_rank(s_0) =', power_rank(s0, ONE, d), '(expect %d)' % (d + 1))
    for name, (u, ui) in UNITS.items():
        if only is not None and only not in name:
            continue
        assert u * ui == ONE and ui * u == ONE, name
        S, Sp = u * s0, t0 * ui
        assert Sp * S == ONE
        P = ONE + S * Sp
        C = rel_commutant(S, Sp, N, L)
        kap = [P * T * P for T in C]
        dk = span_rank(kap) if kap else 0
        alg = [power_rank(k, P, d) for k in kap]
        rnd = []
        for _ in range(trials if C else 0):
            T = ZERO
            for e in C:
                if rng.random() < 0.5:
                    T = T + e
            rnd.append(power_rank(P * T * P, P, d))
        print('%-32s dimC=%d dim kappa(C)=%d  basis power-ranks=%s  random=%s  (max %d)'
              % (name, len(C), dk, alg, rnd, d + 1))
        sys.stdout.flush()

if __name__ == '__main__':
    args = [int(x) for x in sys.argv[1:]]
    main(*args)
