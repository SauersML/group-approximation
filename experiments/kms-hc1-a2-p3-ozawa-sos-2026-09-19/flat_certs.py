"""Exact certificates for the explicit flat of Gamma_3 (tube.certify_word; sound for any quotient Q).
u = bcba, v = babc.  Proves in Gamma_3:  [u,v] = 1,  (ba) u (ba)^-1 = AcAB (a second element of C(u)),
and baCa commutes with u; infinite order of u, v, v u^-1 is checked by x^3 != 1 in Q (every finite
subgroup of Gamma_3 lies in a vertex-group conjugate, exponent 3).  Rank 2 of <u,v> is flat_rank.g.
Usage: python3 flat_certs.py QFILE"""
import sys
from qball import Q
from tube import certify_word, W, inv_word, commutator
from qsearch import QBall, wstr

q = Q(sys.argv[1]); QB = QBall(q, 3)
u, v = W('bcba'), W('babc')
checks = [('[u,v]', commutator(u, v)),
          ('[u, baCa]', commutator(u, W('baCa'))),
          ('(ba)^-1 u (ba) = AcAB', inv_word(W('ba')) + u + W('ba') + inv_word(W('AcAB'))),
          ('u^-1 = Acbc', u + W('Acbc')),
          ('v u = bcAc', v + u + inv_word(W('bcAc'))),
          ('v u^-1 = ABCabc', v + inv_word(u) + inv_word(W('ABCabc')))]
for name, w in checks:
    ok = False
    for rho in (1, 2, 3, 4):
        ok, info = certify_word(q, w, rho)
        if ok: break
    print(f"{name:28s} trivial in Gamma_3: {ok}  (tube rho={rho}, {info})")
for name, w in (('u', u), ('v', v), ('v u^-1', v + inv_word(u)), ('baCa', W('baCa'))):
    print(f"{name:8s} infinite order: {QB.infinite(w)}")
