# Exact check of the Moebius model of K(#281), O = F_3[[s]], sigma: s -> -s (ring automorphism).
# Phi(x w) = t_x(Phi(w)), t_0 = s*sigma(z), t_1 = C(s*sigma(z)), t_2 = -C(s*z), C(y) = (1-y)/(1+y).
# A_0 = sigma, A_1 = -sigma, A_2 = -z, A_3 = T = (u - z)/(1 - s*u*z), u = 1/(1-s).
# Claim: A_a o t_x = t_{out_a(x)} o A_{sec_a(x)} for all 12 pairs (a, x), as maps O -> O.
# Maps are represented as (flag, R) meaning z -> R(sigma^flag z) with R in F_3(s)(z).
# Composition: (f1,R1) o (f2,R2) = (f1+f2 mod 2, z -> R1^{sigma^f1}(R2(z)) ), where R^sigma applies
# s -> -s to the coefficients of R.  Equality of maps on O (infinite, Zariski dense) = equality of pairs.
import sympy as sp
from aut import AUT
s, z = sp.symbols('s z')
u = 1/(1-s)
C = lambda y: (1-y)/(1+y)
def sig(R): return R.subs(s, -s)
def comp(F, G):
    (f1, R1), (f2, R2) = F, G
    # (F o G)(z) = R1(sigma^f1 (R2(sigma^f2 z))); sigma^f1(R2(w)) = R2^{sigma^f1}(sigma^f1 w)
    R2s = sig(R2) if f1 else R2
    # so F o G = (f1+f2, z -> R1(R2^{sigma^f1}(z)))
    return ((f1 + f2) % 2, R1.subs(z, R2s))
def eq(F, G):
    if F[0] != G[0]: return False
    num = sp.numer(sp.together(F[1] - G[1]))
    return sp.Poly(sp.expand(num), s, z, modulus=3).is_zero
t = {0: (1, s*z), 1: (1, C(s*z)), 2: (0, -C(s*z))}
A = {0: (1, z), 1: (1, -z), 2: (0, -z), 3: (0, (u - z)/(1 - s*u*z))}
out, sec = AUT['281']
ok = True
for a in range(4):
    for x in range(3):
        r = eq(comp(A[a], t[x]), comp(t[out[a][x]], A[sec[a][x]]))
        print('relation', a, x, r); ok &= r
r = eq(comp(A[3], A[3]), (0, z)); print('T^2 = 1', r); ok &= r
print('ALL', ok)
# negative controls: the checker must reject these
print('control T t0 = t0 T (expect False)', eq(comp(A[3], t[0]), comp(t[0], A[3])))
print('control A1 t1 = t1 A1 (expect False)', eq(comp(A[1], t[1]), comp(t[1], A[1])))
# orders of tau*a2 on levels 1..9 (infinite order predicted: T*N = I + E, E^2 = s*u^2)
from aut import perms
for n in range(1, 10):
    P = perms('281', n); g = [P[3][P[2][i]] for i in range(3**n)]
    seen = [False]*len(g); o = 1
    from math import gcd
    for i in range(len(g)):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]: seen[j] = True; j = g[j]; l += 1
            o = o*l//gcd(o, l)
    print('order of tau a2 on level', n, o, flush=True)
