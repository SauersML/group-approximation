# Replay of the proof that the (C2) two-cell complex C is a core (pi_1 C -> G injective).
# Steps (numbers as in the proof file):
#  1. Reidemeister-Schreier: K_C = ker(pi_1 C -> Z) = < a_j, b_j, c_j, e_j | R0^(k), R1^(k) >, rewritten here from u_0, u_1.
#  2. The map Phi: K_C -> F_4 kills R0, R1.
#  3. psi = theta phi theta^-1 is a train track on the rose; its gates.
#  4. Sanity: V_{M+1} = < phi V_M, A, phi^-1 B > as subgroups of F_4 for M = 4..7 (the proof derives it abstractly).
#  5. Base case M0 = 8 and the fixed-point step on the radius-R ball datum.
import sys
from fbc import tofib, apply, PHI, PHII, red, inv
from fold2 import SG
from cert import TH, PSI, D, illegal, Vgens, NEW, datum, step, dist, canon_ok, pw, A, B
# 1. Reidemeister-Schreier with transversal {d^l}; level shifts: a,c: 0; b: +3; d: +1; e: +1.
SH = {'a': 0, 'b': 3, 'c': 0, 'd': 1, 'e': 1}
def rs(u):
    l = 0; out = []
    for ch in u:
        g = ch.lower(); s = 1 if ch.islower() else -1
        if s == -1: l -= SH[g]
        if g != 'd': out.append((g, l, s))
        if s == 1: l += SH[g]
    assert l == 0
    return out
u0 = 'd' + 'E' + 'bcBA' + 'DD' + 'e' + 'd'
u1 = 'bcBAAbDcBd'
R0, R1 = rs(u0), rs(u1)
print('1. R0 =', R0); print('   R1 =', R1)
# 2. Phi(g_j) = phi^j(image of g d^{-SH[g]}): a -> XyxYx, b d^-3 -> Xyyyx YYY, c -> XYxyx, e d^-1 -> xyX Y
IMG = {'a': tofib('XyxYx'), 'b': tofib('XyyyxYYY'), 'c': tofib('XYxyx'), 'e': tofib('xyXY')}
def Phi(z, j): return pw(IMG[z], j)
for k in (-3, 0, 5):
    for R in (R0, R1):
        wd = red(''.join(Phi(g, l + k) if s == 1 else inv(Phi(g, l + k)) for g, l, s in R)); assert wd == ''
print('2. Phi kills R0^(k), R1^(k) (checked k = -3, 0, 5; the general case is phi^k of k = 0)')
# 3. train track (asserted inside cert.py) and gates
gates = []
for x in D:
    for gt in gates:
        if illegal(x, gt[0]): gt.append(x); break
    else: gates.append([x])
print('3. theta =', TH, ' psi =', PSI, ' gates =', gates, ' (train-track check passed)')
# 4. subgroup identity sanity
def graph(ws):
    G = SG()
    for u in ws: G.add_loop(u)
    return G
for M in range(4, 8):
    big = graph(Vgens(M + 1)); small = graph([apply(PHI, u) for u in Vgens(M)] + [A, pw(B, -1)])
    ok = all(big.member(apply(PHI, u)) for u in Vgens(M)) and big.member(A) and big.member(pw(B, -1)) and all(small.member(u) for u in Vgens(M + 1))
    assert ok, M
print('4. V_{M+1} = <phi V_M, A, phi^-1 B> for M = 4..7')
# 5. base case and the step
R = int(sys.argv[1]) if len(sys.argv) > 1 else 12; M0 = 8
G = SG()
for u in Vgens(M0): G.add_loop(apply(TH, u))
V, Ed, rk = G.stats(); b = G.f(0)
assert rk == 2 * M0 + 6 and canon_ok(G, b, R)
dt = datum(G, b, R)
ok, msg, nd, drop = step(dt, R)
assert ok and drop == 0 and nd == dt
print('5. M0 = %d: rank %d = 2*M0+6, all vertices beyond radius %d legal, ball datum has %d vertices;' % (M0, rk, R, len(dt)))
print('   step on the datum:', msg, '; rank(Z) - rank(Z\') = 0 ; output datum = input datum (fixed point)')
for M in range(M0):
    G = graph(Vgens(M)); assert G.stats()[2] == 2 * M + 6
print('   direct: rank V_M = 2M+6 for M < M0.  CONCLUSION: rank V_M = 2M+6 for all M >= 0.')
