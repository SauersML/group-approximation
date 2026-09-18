"""Exact (big-integer) verification of Venkataramana-pair certificates for rho_k(F).

A certificate is (k, t, g) with t, g words in x, X, y, Y (capital = inverse).
We check with exact integer arithmetic:
  (1) T = rho_k(t) is a rank-one unipotent: N1 = T - I has rank 1 and N1^2 = 0;
  (2) T2 = G T G^-1 with G = rho_k(g); N2 = T2 - I;
  (3) N1 N2 = N2 N1 = 0 (so T, T2 commute and T^a T2^b = I + a N1 + b N2);
  (4) N1, N2 are linearly independent (so <T, T2> is free abelian of rank 2).
Then [Venkataramana 87, Thm 3.7] (quoted as Long-Reid Thm 3.2) together with
Long-Reid Thm 2.6 (rho_k(F) Zariski dense for every integer k) gives
[SL(3,Z) : rho_k(F)] < infinity.

usage: python3 verify.py k t g   or   python3 verify.py --file certs.txt  (lines "k t g")
"""
import sys
from fractions import Fraction


def mat(rows): return [list(r) for r in rows]


def X(k): return mat([[1, -2, 3], [0, k, -1 - 2 * k], [0, 1, -2]])
def Y(k): return mat([[-2 - k, -1, 1], [-2 - k, -2, 3], [-1, -1, 2]])


def mul(A, B): return [[sum(A[i][l] * B[l][j] for l in range(3)) for j in range(3)] for i in range(3)]


def adj(A):
    a = A
    return [[a[1][1] * a[2][2] - a[1][2] * a[2][1], a[0][2] * a[2][1] - a[0][1] * a[2][2], a[0][1] * a[1][2] - a[0][2] * a[1][1]],
            [a[1][2] * a[2][0] - a[1][0] * a[2][2], a[0][0] * a[2][2] - a[0][2] * a[2][0], a[0][2] * a[1][0] - a[0][0] * a[1][2]],
            [a[1][0] * a[2][1] - a[1][1] * a[2][0], a[0][1] * a[2][0] - a[0][0] * a[2][1], a[0][0] * a[1][1] - a[0][1] * a[1][0]]]


I3 = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]


def word(k, w):
    gens = {'x': X(k), 'y': Y(k)}
    invs = {'x': adj(X(k)), 'y': adj(Y(k))}  # det = 1
    M = I3
    for c in w:
        M = mul(M, gens[c] if c.islower() else invs[c.lower()])
    return M


def sub(A, B): return [[A[i][j] - B[i][j] for j in range(3)] for i in range(3)]


def is_zero(A): return all(v == 0 for r in A for v in r)


def rank(vecs):
    rows = [[Fraction(v) for v in r] for r in vecs]
    rk, col, n = 0, 0, len(rows[0]) if rows else 0
    for col in range(n):
        piv = next((i for i in range(rk, len(rows)) if rows[i][col] != 0), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(len(rows)):
            if i != rk and rows[i][col] != 0:
                f = rows[i][col] / rows[rk][col]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def check(k, t, g, verbose=True):
    T = word(k, t)
    G = word(k, g)
    Gi = adj(G)
    assert mul(G, Gi) == I3
    N1 = sub(T, I3)
    ok1 = (not is_zero(N1)) and rank(N1) == 1 and is_zero(mul(N1, N1))
    T2 = mul(mul(G, T), Gi)
    N2 = sub(T2, I3)
    ok3 = is_zero(mul(N1, N2)) and is_zero(mul(N2, N1))
    ok4 = rank([sum(N1, []), sum(N2, [])]) == 2
    res = ok1 and ok3 and ok4
    if verbose:
        print('k=%d t=%s (len %d) g=%s (len %d): rank-one unipotent %s, N1N2=N2N1=0 %s, independent %s => %s'
              % (k, t, len(t), g, len(g), ok1, ok3, ok4, 'CERTIFIED finite index' if res else 'FAIL'))
        if res:
            print('   T =', T)
    return res


if __name__ == '__main__':
    if sys.argv[1] == '--file':
        allok = True
        for line in open(sys.argv[2]):
            line = line.split('#')[0].split()
            if len(line) == 3:
                allok &= check(int(line[0]), line[1], line[2])
        print('ALL CERTIFIED' if allok else 'SOME FAILED')
    else:
        check(int(sys.argv[1]), sys.argv[2], sys.argv[3])
