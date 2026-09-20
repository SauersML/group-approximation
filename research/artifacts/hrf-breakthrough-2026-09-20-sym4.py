"""Exact Sage/Singular probe; run only on MSI under a 60-second CPU/wall cap.

One specified twist, (a,b,c)=(1,0,0), in the three-conjugate Sym^4 family.
No field equations: a unit ideal excludes this family over algebraic closure.
An unfinished or nonunit computation proves no nonexistence assertion.
"""
from sage.all import GF, PolynomialRing, matrix, diagonal_matrix, identity_matrix, binomial, prod
from pathlib import Path
import json
import os
import time

started = time.monotonic()
os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
out = Path('/projects/standard/hsiehph/sauer354/hrf-breakthrough-2026-09-20-sym4')
base = GF(19)
base_poly = PolynomialRing(base, 't')
t = base_poly.gen()
k = GF(19**2, name='z', modulus=t*t - 4*t + 1)
z = k.gen()
assert z**5 == 1 and z != 1


def sym4(g):
    a, b, c, d = g.list()
    return matrix(k, 5, 5, lambda j, i: sum(
        binomial(4-i, r) * binomial(i, j-r)
        * a**(4-i-r) * c**r * b**(i-j+r) * d**(j-r)
        for r in range(max(0, j-i), min(j, 4-i)+1)))


edges = [matrix(k, [[2, 11], [16, 3]]),
         matrix(k, [[5, 11], [4, 9]]),
         matrix(k, [[6, 15], [12, 8]])]
A, B, C = [sym4(g) for g in edges]
for g, X in zip(edges, [A, B, C]):
    assert g.det() == 1
    assert X.det() == 1 and X**5 == identity_matrix(k, 5)
    assert sym4(-g) == X
for g in edges:
    for h in edges:
        assert sym4(g*h) == sym4(g)*sym4(h)


def eigenbasis(X):
    columns = []
    for j in range(5):
        kernel = (X-z**j*identity_matrix(k, 5)).right_kernel()
        assert kernel.dimension() == 1
        columns.append(kernel.basis()[0])
    P = matrix(k, columns).transpose()
    assert P.det() != 0
    assert P.inverse()*X*P == diagonal_matrix(k, [z**j for j in range(5)])
    return P


def encode(X):
    return [[list(map(int, X[i, j].polynomial().list())) for j in range(X.ncols())]
            for i in range(X.nrows())]


PA, PB, PC = [eigenbasis(X) for X in [A, B, C]]
record = {'characteristic': 19, 'field_order': 361,
          'modulus': 'z^2-4*z+1', 'twist_exponents': [1, 0, 0],
          'A': encode(A), 'B': encode(B), 'C': encode(C),
          'PB': encode(PB), 'PC': encode(PC),
          'domain': 'algebraic closure; no finite-field equations',
          'normalization': 'first diagonal coefficient of each of V,W is 1'}
(out/'input.json').write_text(json.dumps(record, indent=2)+'\n')

R = PolynomialRing(k, names=('v1','v2','v3','v4','w1','w2','w3','w4','inv'),
                   order='degrevlex')
variables = R.gens()
v = [R(1)] + list(variables[:4])
w = [R(1)] + list(variables[4:8])
V = PB.change_ring(R)*diagonal_matrix(R, v)*PB.inverse().change_ring(R)
W = PC.change_ring(R)*diagonal_matrix(R, w)*PC.inverse().change_ring(R)
U = V*W
equations = (U*A.change_ring(R) - z*A.change_ring(R)*U).list()
equations.append(variables[8]*prod(v+w)-1)
I = R.ideal(equations)
(out/'equations.txt').write_text('\n'.join(map(str, equations))+'\n')
print('INPUT_READY', json.dumps({'equations': len(equations),
      'variables': R.ngens(), 'elapsed_seconds': time.monotonic()-started}), flush=True)
print('GROEBNER_BEGIN', flush=True)
G = I.groebner_basis(algorithm='libsingular:std')
is_unit = len(G) == 1 and G[0] == 1
(out/'groebner.txt').write_text('\n'.join(map(str, G))+'\n')
result = {'unit_ideal': bool(is_unit), 'basis_length': len(G),
          'elapsed_seconds': time.monotonic()-started,
          'conclusion': ('No invertible solution in this Sym^4 conjugacy family '
                         'for twist (1,0,0), over the algebraic closure of F19.'
                         if is_unit else 'No nonexistence conclusion.')}
(out/'result.json').write_text(json.dumps(result, indent=2)+'\n')
print('RESULT', json.dumps(result), flush=True)
