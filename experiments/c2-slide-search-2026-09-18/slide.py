# General relator-slide deletion for configuration (C2).
# Given a certificate d (sum_z c_z d_z = 1 in ZG) and a coordinate z0 with d_{z0} = eps*u a unit,
# slide r_z (z != z0) by prod_i (w_i u^-1) r_{z0}^{-eps n_i} (w_i u^-1)^-1 for d_z = sum n_i w_i.
# Then the r_{z0}-coefficient of sigma is c_{z0} - sum_{z!=z0} c_z (-eps d_z u^-1) = eps u^-1, a unit.
# Delete r_{z0}, eliminate z != z0 by their slid relators, put z0 = t phi(z0): Gamma'' = <t,x,y|R0,R1>.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_unimodular import BAS, U0, U1, G_, inv, fred, ring, fox, rmul, W
def cyc(u):
    while len(u) > 1 and u[0] == u[-1].swapcase(): u = u[1:-1]
    return u
def check_cert(D):
    total = {}
    for z in 'abcde':
        cz = ring([(s, G_ + u) for s, u in fox(U0, z)] + [(-s, u) for s, u in fox(U1, z)])
        for k, v in rmul(cz, ring(D[z])).items(): total[k] = total.get(k, 0) + v
    return {k: v for k, v in total.items() if v} == {('', 0): 1}
def build(D, z0, conj=None):
    """conj: optional dict (z, i) -> extra word W_i inserted as w_i u^-1 W t^n W^-1 u w_i^-1 (W in <<w>>)."""
    assert len(ring(D[z0])) == 1
    eps, u = D[z0][0]
    ui = inv(u)
    SUB = {}
    for z in 'abcde':
        if z == z0: continue
        P = ''
        for i, (n, wd) in enumerate(D[z]):
            Wx = (conj or {}).get((z, i), '')
            m = -eps * n
            pre = wd + ui + Wx
            P += pre + ('t' if m > 0 else 'T') * abs(m) + inv(pre)
        SUB[z] = fred(inv(P) + BAS[z])
    SUB[z0] = 't' + BAS[z0]
    def subst(v): return fred(''.join(SUB[ch] if ch.islower() else inv(SUB[ch.lower()]) for ch in v))
    return cyc(subst(U0)), cyc(subst(U1))
def gapword(R):
    return '*'.join(c if c.islower() else c.lower() + '^-1' for c in R) or 'One(F)'
if __name__ == '__main__':
    from verify_unimodular import D
    print('cert ok', check_cert(D))
    for z0 in 'bc':
        R0, R1 = build(D, z0)
        print(z0, len(R0), len(R1), 'texp', R0.count('t') - R0.count('T'), R1.count('t') - R1.count('T'))
        print(' t=1:', cyc(fred(R0.replace('t','').replace('T',''))), cyc(fred(R1.replace('t','').replace('T',''))))
