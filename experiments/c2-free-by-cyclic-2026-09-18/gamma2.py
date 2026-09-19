# Build Gamma'' = <t, x, y | R_0, R_1>: slide r_x (x != c) by conjugates of r_c = c phi(c)^-1 with
# coefficients d_x, delete r_c, eliminate a,b,d,e, and put c = t phi(c).
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from verify_unimodular import D, BAS, U0, U1, inv, fred, W
PHI = dict(BAS)
def Pi(x):
    # product of w_i rho^{n_i} w_i^-1, rho = t (after c = t phi(c))
    return ''.join(u + ('t' if n > 0 else 'T') * abs(n) + inv(u) for n, u in D[x])
SUB = {}
for x in 'abde': SUB[x] = fred(inv(Pi(x)) + PHI[x])
SUB['c'] = 't' + PHI['c']
def subst(u): return fred(''.join(SUB[ch] if ch.islower() else inv(SUB[ch.lower()]) for ch in u))
R0, R1 = subst(U0), subst(U1)
def cyc(u):
    while len(u) > 1 and u[0] == u[-1].swapcase(): u = u[1:-1]
    return u
R0, R1 = cyc(R0), cyc(R1)
if __name__ == '__main__':
    for R in (R0, R1):
        print(len(R), 't-exp', R.count('t') - R.count('T'), R)
    print('check t=1:', cyc(fred(R0.replace('t', '').replace('T', ''))), cyc(fred(R1.replace('t','').replace('T',''))), W)
