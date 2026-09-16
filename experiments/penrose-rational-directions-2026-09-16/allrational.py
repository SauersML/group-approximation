# Is there a 2-dim Q-subspace W of Q(zeta) meeting all five lines E_j = zeta^j u Q(sqrt5) nontrivially?
import sympy as sp
z = sp.symbols('z'); p,q,r,s = sp.symbols('p q r s')
cyc = sp.Poly(z**4+z**3+z**2+z+1, z)
def vec(expr):
    P = sp.Poly(sp.expand(expr), z).rem(cyc)
    c = P.all_coeffs()[::-1]; c = c + [0]*(4-len(c))
    return [sp.expand(x) for x in c]
u = z - z**4; r5 = 1 + 2*(z+z**4)
a = u*(p + q*r5); b = z*u*(r + s*r5)
eqs = []
for j in (2,3,4):
    M = sp.Matrix([vec(a), vec(b), vec(z**j*u), vec(z**j*u*r5)]).T
    eqs.append(sp.factor(M.det()))
for e in eqs: print(e)
print(sp.solve(eqs, [p,q,r,s], dict=True))
