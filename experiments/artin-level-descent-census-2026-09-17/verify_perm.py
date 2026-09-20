"""Exact check (sympy, over Q(s)) that an S_6 permutation representation of the census2 CANDIDATE
group is a twisted witness: Artin relations hold and the stacked twisted matrix
[S_k(pq) (s P(p) - 1)] has rank < 6 over Q(s), so [chi] is not in Sigma^1.
Also reports c0 (rank of the stacked sigma over Q) for the same rep, and an explicit kernel vector."""
from sympy import Matrix, eye, symbols, simplify, zeros

s = symbols('s')
V = ['a', 'b', 'c', 'd', 'e']
E = {('a', 'b'): 6, ('a', 'c'): 4, ('a', 'd'): 4, ('a', 'e'): 10, ('b', 'c'): 3, ('b', 'd'): 4,
     ('b', 'e'): 2, ('c', 'e'): 2}
CROSS = [('a', 'b', 3), ('a', 'c', 2), ('a', 'e', 5), ('d', 'b', 2)]
REP = {'a': (0, 2, 1, 4, 5, 3), 'b': (1, 3, 5, 0, 4, 2), 'c': (0, 4, 5, 1, 3, 2),
       'd': (4, 2, 1, 5, 3, 0), 'e': (0, 1, 5, 3, 4, 2)}


def pmat(p):
    M = zeros(len(p), len(p))
    for i, j in enumerate(p):
        M[j, i] = 1
    return M


def alt(X, Y, m):
    P = eye(X.rows)
    for t in range(m):
        P = P * (X if t % 2 == 0 else Y)
    return P


M = {v: pmat(p) for v, p in REP.items()}
n = 6
for (x, y), m in E.items():
    assert alt(M[x], M[y], m) == alt(M[y], M[x], m), (x, y, m)
print("Artin relations hold for all 8 edges (cd, de free)")
Ss = []
for p, q, k in CROSS:
    X = M[p] * M[q]
    S, Pw = eye(n), eye(n)
    for _ in range(k - 1):
        Pw = Pw * X
        S = S + Pw
    Ss.append(S)
st = Matrix.vstack(*Ss)
print("rank of stacked sigma over Q:", st.rank(), " => c0 =", n - st.rank())
Mt = Matrix.vstack(*[S * (s * M[p] - eye(n)) for S, (p, q, k) in zip(Ss, CROSS)])
r = Mt.rank(simplify=True)
print("rank of twisted stack over Q(s):", r, " => ct =", n - r)
ns = Mt.nullspace(simplify=True)
if ns:
    v = ns[0].applyfunc(simplify)
    print("kernel vector:", list(v.T))
    assert all(simplify(x) == 0 for x in (Mt * v))
    print("verified: twisted stack kills it identically in s")
