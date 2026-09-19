# H_1-level orbit invariant of F-discs in the l_X-fibration (w18-042).
# Collision planes of the base: y_r = y_r' iff n = r/r_1 - r'/r'_1 vanishes; group pairs by the line of n.
# A generic meridian of a collision plane Q acts on H_1(PB_45) by the sum of e_{ij} over pairs colliding on Q.
# iota(D) for D = sigma.Delta_F lies in Z^{1035}/H_1(Stab Delta_F); modulo point-pushing of m this is
# (+)_{j outside} Z^3/diag  (coordinates e_{F_a j}).  Lambda = image of the 121 meridians there.
import sys, os, numpy as np, itertools
# mono.py is the w17 engine: experiments/h4-monodromy-2026-09-19/mono.py in the repo
_here = os.path.dirname(os.path.abspath(__file__)) if '__file__' in globals() else sys.path[0]
sys.path.insert(0, os.path.join(_here, '..', 'h4-monodromy-2026-09-19'))
from mono import Arr
from sympy import Matrix
from sympy.matrices.normalforms import smith_normal_form

name = sys.argv[1] if len(sys.argv) > 1 else 'H4'
A = Arr(name); R = A.nonX; B = A.B; n = len(R)
Fw = [(1, 0, 0, 0), (1, 1, 0, 0), (1, 1, 1, 0)]
Fi = [min(range(n), key=lambda k: np.abs(R[k] - np.array(f)).sum()) for f in Fw]
assert all(np.abs(R[Fi[a]] - np.array(Fw[a])).sum() < 1e-9 for a in range(3))
def key(v):
    v = v / v[np.argmax(np.abs(v) > 1e-9)]
    return tuple(np.round(v, 6))
planes = {}
for i, j in itertools.combinations(range(n), 2):
    nv = R[i] / R[i][0] - R[j] / R[j][0]
    planes.setdefault(key(nv), []).append((i, j))
Xkeys = {key(r) for r in A.X}
def clusters(pairs):
    par = {}
    def f(x):
        while par.setdefault(x, x) != x: x = par[x]
        return x
    for i, j in pairs: par[f(i)] = f(j)
    cl = {}
    for x in list(par): cl.setdefault(f(x), set()).add(x)
    return list(cl.values())
nX = sum(k in Xkeys for k in planes); print(name, 'punctures', n, 'planes', len(planes), 'X-planes', nX,
                                              'D-planes', len(planes) - nX)
out = [j for j in range(n) if j not in Fi]; col = {j: t for t, j in enumerate(out)}
rows = []; info = []
for k, pairs in planes.items():
    cl = clusters(pairs)
    for C in cl:   # a clique check: every pair of a cluster collides
        assert all((min(i, j), max(i, j)) in set(pairs) for i, j in itertools.combinations(sorted(C), 2))
    v = [0] * (2 * len(out))
    for C in cl:
        for a in range(3):
            if Fi[a] in C:
                for j in C:
                    if j in col:
                        e = [0, 0, 0]; e[a] = 1
                        v[2 * col[j]] += e[0] - e[2]; v[2 * col[j] + 1] += e[1] - e[2]
    rows.append(v)
    info.append((('X' if k in Xkeys else 'D'), sorted(len(C) for C in cl),
                 [sorted(C) for C in cl if set(C) & set(Fi)]))
M = Matrix(rows)
print('rank of Lambda in Z^%d:' % (2 * len(out)), M.rank())
snf = smith_normal_form(M.T)
d = [snf[i, i] for i in range(min(snf.shape)) if snf[i, i] != 0]
print('invariant factors != 1:', [x for x in d if abs(x) != 1])
touch = [t for t in info if t[2]]
print('planes with a cluster through an F-puncture:', len(touch))
for t in touch: print(' ', t[0], 'cluster sizes', t[1], 'F-clusters', t[2])

# ---- gluing closure: iota whose three F-pair projections each lie in the projection of Lambda ----
J = len(out)
Px = Matrix([[1 if c == 2 * t else 0 for c in range(2 * J)] for t in range(J)])          # e_0 - e_2
Py = Matrix([[1 if c == 2 * t + 1 else 0 for c in range(2 * J)] for t in range(J)])      # e_1 - e_2
Pxy = Px - Py                                                                             # e_0 - e_1
def span_rank(*Ms): return Matrix.vstack(*Ms).rank()
L = M  # rows generate Lambda
cons = []   # Lambda^glue_Q = {z : P z in span(P L^T) for P in (Px,Py,Pxy)}
for Pm in (Px, Py, Pxy):
    img = (Pm * L.T)                      # columns span the projection
    # annihilator of the column space, composed with Pm, gives linear constraints on z
    ann = img.T.nullspace()
    cons += [a.T * Pm for a in ann]
C = Matrix.vstack(*cons) if cons else Matrix.zeros(0, 2 * J)
glue_rank = 2 * J - C.rank()
print('rank of projections (x, y, x-y):', (Px * L.T).rank(), (Py * L.T).rank(), (Pxy * L.T).rank())
print('rank of gluing closure over Q:', glue_rank, ' vs rank Lambda', L.rank())
# the extra direction: a vector of the gluing closure outside span(Lambda)
Gb = C.nullspace()
annL = L.nullspace()            # vectors orthogonal to all rows of L: the functionals killing Lambda
extra = None
for g in Gb:
    if any((a.T * g)[0] != 0 for a in annL): extra = g; break
from sympy import lcm, gcd
den = lcm([x.q for x in extra]); extra = extra * den
gg = gcd([int(x) for x in extra]); extra = extra / gg
lab = lambda j: 'r%d%s' % (j, tuple(np.round(R[j], 3)))
print('extra direction (outside j: (e_F0-e_F2, e_F1-e_F2)):')
for t, j in enumerate(out):
    if extra[2 * t] or extra[2 * t + 1]: print('  ', lab(j), extra[2 * t], extra[2 * t + 1])
print('F:', [lab(j) for j in Fi])
# ---- integral checks with python-flint HNF ----
import flint
def hnf_rows(Mx):
    H = flint.fmpz_mat([[int(x) for x in Mx.row(i)] for i in range(Mx.rows)]).hnf()
    return [tuple(int(H[i, j]) for j in range(H.ncols())) for i in range(H.nrows()) if any(H[i, j] != 0 for j in range(H.ncols()))]
def member(Lrows, b): return hnf_rows(Lrows) == hnf_rows(Matrix.vstack(Lrows, b.T if b.cols == 1 else b))
t29 = col[29]; zeta = Matrix([[1 if c == 2 * t29 + 1 else 0 for c in range(2 * J)]])
print('zeta in Lambda (Z)?', member(M, zeta))
for nm, Pm in (('F0-F2', Px), ('F1-F2', Py), ('F0-F1', Pxy)):
    print('  proj', nm, 'of zeta in proj(Lambda) (Z)?', member((Pm * M.T).T, (Pm * zeta.T).T))
