# Self-check of the canonical 2-cycle z_H of the H-cover of the rose mapping torus M_f.
#   (1) z = sum c_i chain(l_i) (loops l_i in N) is phi-invariant as a 1-cycle of Gamma_N, using only
#       exact (positive) window memberships to identify cosets;  its letter sums are v = -p + r + s.
#   (2) the p-part of z is -2 [p~(N)] + 1 [p~(N Sr)] and Sr is not in N (S_9 certificate), so z uses
#       two lifts of the P-cell.
# Usage: python3 verify_cycle.py <w11 experiment dir> [M]
import sys, itertools
sys.path.insert(0, sys.argv[1])
from fbc import red, inv, apply, PHI, PHII
from fold2 import SG
from cert import Vgens
M = int(sys.argv[2]) if len(sys.argv) > 2 else 8
X2 = 'rrSqPRs'
LOOPS = [(-1, 'Q' + X2), (1, inv(X2) + 's' + X2), (-2, 'pQ'), (-2, 'qR')]
def pw(u, j):
    for _ in range(abs(j)): u = apply(PHI if j > 0 else PHII, u)
    return u
g = SG()
for v in Vgens(M): g.add_loop(v)
def member(u):
    v = g.f(0)
    for c in u:
        if c not in g.out[v]: return False
        v = g.f(g.out[v][c])
    return v == g.f(0)
def inN(u): return any(member(pw(u, k)) for k in range(-3, 4))   # phi^k(u) in T_M  =>  u in N
def chain(u, coef, acc):
    pre = ''
    for ch in u:
        if ch.islower(): acc.append((ch, pre, coef)); pre = red(pre + ch)
        else: pre = red(pre + ch); acc.append((ch.lower(), pre, -coef))
    return pre
for _, l in LOOPS: assert inN(l), l
z, fz = [], []
for c, l in LOOPS: chain(l, c, z); chain(apply(PHI, l), c, fz)
# union-find on coset representatives, merged only by exact memberships
reps = sorted({pre for _, pre, _ in z + fz}, key=len)
par = {r: r for r in reps}
def fd(r):
    while par[r] != r: r = par[r]
    return r
for a, b in itertools.combinations(reps, 2):
    if fd(a) != fd(b) and inN(red(a + inv(b))): par[fd(b)] = fd(a)
def reduce(ch):
    out = {}
    for e, pre, c in ch: out[(e, fd(pre))] = out.get((e, fd(pre)), 0) + c
    return {k: v for k, v in out.items() if v}
Z, FZ = reduce(z), reduce(fz)
print('coset classes used:', len({fd(r) for r in reps}), ' of', len(reps), 'representatives')
print('z =', Z)
print('phi-invariant (f_N# z = z):', Z == FZ)
print('letter sums:', {e: sum(v for (e2, _), v in Z.items() if e2 == e) for e in 'pqrs'})
print('lifts of the P-cell in supp z:', [(k, v) for k, v in Z.items() if k[0] == 'p'])
print('Sr in some window (would merge the two P-lifts):', inN('Sr'))
# S_9 certificate that Sr = y x^-1 y^-1 x is not in H (points 1..9, perms act on the right as in GAP)
def perm(cycles, n=9):
    p = list(range(n + 1))
    for cyc in cycles:
        for i, a in enumerate(cyc): p[a] = cyc[(i + 1) % len(cyc)]
    return p
PX, PY = perm([(3, 4, 6, 5), (7, 8, 9)]), perm([(1, 2, 3), (5, 7, 8)])
def img(word, pt):
    for ch in word:
        P = PX if ch.lower() == 'x' else PY
        if ch.islower(): pt = P[pt]
        else: pt = P.index(pt)
    return pt
W = 'yxYXXyyxYXYxYYxyXy'
assert all(img(W, i) == i for i in range(1, 10)), 'relator'
HS = ['XyxYx', 'Xyyyx', 'XYxyx', 'y', 'xyX']
fixed = [i for i in range(1, 10) if all(img(h, i) == i for h in HS)]
print('points fixed by pi(H):', fixed, '  image of that point under pi(y x^-1 y^-1 x):',
      [img('yXYx', i) for i in fixed])
# Push z forward to the finite cover X_L, L = pi^-1(Stab(4)) >= H: the vertex N a goes to point 4^pi(a).
XY = {'p': 'YYxyy', 'q': 'Yxy', 'r': 'x', 's': 'yxY'}
def toxy(u): return ''.join(XY[c] if c.islower() else inv_xy(XY[c.lower()]) for c in u)
def inv_xy(u): return ''.join(c.swapcase() for c in reversed(u))
b = fixed[0]; push = {}
for (e, rep), c in Z.items():
    k = (e, img(toxy(rep), b)); push[k] = push.get(k, 0) + c
print('z pushed to X_L:', {k: v for k, v in push.items() if v})
print('P-cell coefficients in X_L:', {k: v for k, v in push.items() if k[0] == 'p' and v})
