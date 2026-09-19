# Image of H_1(N) in H_1(J), J = L cap F_4, L = Stab(b) in a permutation action of G with H <= L.
# N = <phi^k(a0,b0,c0,e0)>, so im H_1(N) is the phi-stable lattice spanned by a0..e0.
# Prints Smith invariants of H_1(J)/im H_1(N) and the vector of c_H.
import sys
from common import *
from lattice import hnf, member, invariant_span, smith

def analyse(act, b, verbose=True):
    for h in ['XyxYx', 'Xyyyx', 'XYxyx', 'y', 'xyX']:
        assert act.imgxy(h, b) == b, 'H does not fix b'
    assert all(act.imgxy(W, i) == i for i in range(1, act.n + 1)), 'relator'
    sg = Schreier(act, b); n = sg.rank
    Pm = [sg.ab(apply(PHI, sg.word(g))) for g in sg.gens]    # rows: phi(gen_i)
    Pi = [sg.ab(apply(PHII, sg.word(g))) for g in sg.gens]
    mul = lambda M: (lambda v: [sum(v[i] * M[i][j] for i in range(n)) for j in range(n)])
    vecs = [sg.ab(w) for w in N0.values()]
    Lam = invariant_span(vecs, [mul(Pm), mul(Pi)], n)
    cH = sg.ab(U)
    assert member(Lam, cH, n)
    inv_ = smith(Lam, n)
    if verbose:
        print('index', act.n, 'rank H_1(J) =', n, ' rank im H_1(N) =', len(Lam),
              ' coker invariants (non-1):', [d for d in inv_ if d != 1])
        from math import gcd
        g = 0
        for x in cH: g = gcd(g, x)
        print('c_H in H_1(J): gcd of coordinates =', g, ' nonzero:', {sg.gens[i]: x for i, x in enumerate(cH) if x})
    return sg, Lam, cH, inv_, (Pm, Pi)

if __name__ == '__main__':
    analyse(S9(), 4)
