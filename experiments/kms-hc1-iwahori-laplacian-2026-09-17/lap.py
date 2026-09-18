#!/usr/bin/env python3
"""usage: lap.py MAXDEG   (output: "checked N bad 0" = identity holds at all N (weight, j) blocks, j=1,2)

Test the Garland--Lepowsky/Kostant Laplacian identity on the integral CE complex of L_Z.
d = CE boundary on Lambda(L), delta = its adjoint for the contravariant form B
(B(t^aE_ij,t^aE_ij)=1, B(t^a h_s, t^a h_r)=[[2,-1],[-1,2]]), extended to Lambda^j by Gram determinants.
Check d delta + delta d = c(mu) Id on Lambda^j_mu, c(mu) = deg(mu) - (x^2-xy+y^2), x=c1-c0, y=c2-c0."""
import sys, itertools
sys.argv = [sys.argv[0], sys.argv[1] if len(sys.argv) > 1 else '15']
import os
H2Z = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'kms-hc1-iwahori-integral-h2-2026-09-17', 'h2z.py')
exec(open(H2Z).read().split("if __name__ == '__main__':")[0])
from flint import fmpq_mat, fmpq

def B1(x, y):
    bx, by = basis[x], basis[y]
    if bx[3] != by[3] or bx[0] != by[0]:
        return 0
    if bx[0] == 'e':
        return 1 if bx[1:3] == by[1:3] else 0
    return 2 if bx[1] == by[1] else -1

def gram(tuples):
    n = len(tuples)
    M = [[0]*n for _ in range(n)]
    for i, u in enumerate(tuples):
        for j, v in enumerate(tuples):
            A = [[B1(a, b) for b in v] for a in u]
            M[i][j] = int(fmpq_mat(A).det()) if A else 1
    return fmpq_mat(M) if n else None

def dmat(src, tgt, j):
    """matrix (cols = src, rows = tgt) of CE boundary Lambda^j -> Lambda^{j-1}."""
    tidx = {t: i for i, t in enumerate(tgt)}
    M = [[0]*len(src) for _ in tgt]
    for c, tup in enumerate(src):
        for i in range(j):
            for k in range(i+1, j):
                br = bracket(tup[i], tup[k])
                rest = [tup[m] for m in range(j) if m != i and m != k]
                for z, co in br.items():
                    if z in rest:
                        continue
                    lst = [z] + rest
                    # sign of sorting
                    perm = sorted(range(len(lst)), key=lambda q: lst[q])
                    inv = sum(1 for a in range(len(perm)) for b in range(a+1, len(perm)) if perm[a] > perm[b])
                    s = (-1) ** (i + k + 1) * (-1) ** inv  # d(x1..xj) = sum (-1)^{i+k+1}... convention
                    M[tidx[tuple(sorted(lst))]][c] += s * co
    return fmpq_mat(M)

def tuples_at(w, j):
    if j == 1:
        return [(n,) for n in byw.get(w, [])]
    if j == 2:
        return list(PAIRS.get(w, []))
    if j == 3:
        return list(TRIPLES.get(w, []))

def cval(w):
    x, y = w[1]-w[0], w[2]-w[0]
    return sum(w) - (x*x - x*y + y*y)

bad = 0; checked = 0
for w in sorted(set(PAIRS) | set(byw), key=lambda w: (sum(w), w)):
    T1, T2, T3 = tuples_at(w, 1), tuples_at(w, 2), tuples_at(w, 3)
    c = cval(w)
    for (Tj, Tlo, Thi, j) in ((T1, None, T2, 1), (T2, T1, T3, 2)):
        if not Tj:
            continue
        n = len(Tj)
        L = fmpq_mat(n, n)
        Gj = gram(Tj)
        if Thi:
            D = dmat(Thi, Tj, j+1)            # Lambda^{j+1} -> Lambda^j
            Ghi = gram(Thi)
            delta = Ghi.inv() * D.transpose() * Gj   # adjoint: Lambda^j -> Lambda^{j+1}
            L += D * delta
        if Tlo:
            D2 = dmat(Tj, Tlo, j)
            Glo = gram(Tlo)
            delta2 = Gj.inv() * D2.transpose() * Glo
            L += delta2 * D2
        ok = all(L[a, b] == (c if a == b else 0) for a in range(n) for b in range(n))
        checked += 1
        if not ok:
            bad += 1
            if bad <= 5:
                print("FAIL", w, j, c, [L[a, a] for a in range(n)][:6], flush=True)
print("checked", checked, "bad", bad)
