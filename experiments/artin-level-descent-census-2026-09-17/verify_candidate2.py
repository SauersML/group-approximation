"""Exact sympy check over F_5 of a 2-dim level-0 witness of the census2 CANDIDATE group
(labels ab 6, ac 4, ad 4, ae 10, bc 3, bd 4, be 2, ce 2; cd, de free; chi = (1,-1,-1,1,-1);
cross edges ab 3, ac 2, ae 5, db 2): c0 = 1 but the gcd of the 2x2 minors of the twisted
stack is nonzero, so ct = 0 (the witness does not descend)."""
from sympy import GF, Matrix, eye, symbols, Poly, gcd
from sympy.polys.matrices import DomainMatrix

l = 5
t = symbols('t')
R = {'a': [[0, 1], [1, 1]], 'b': [[0, 4], [4, 1]], 'c': [[0, 1], [1, 1]], 'd': [[3, 4], [1, 0]],
     'e': [[2, 0], [0, 2]]}
E = {('a', 'b'): 6, ('a', 'c'): 4, ('a', 'd'): 4, ('a', 'e'): 10, ('b', 'c'): 3, ('b', 'd'): 4,
     ('b', 'e'): 2, ('c', 'e'): 2}
CROSS = [('a', 'b', 3), ('a', 'c', 2), ('a', 'e', 5), ('d', 'b', 2)]


def modl(X):
    return X.applyfunc(lambda z: Poly(z, t, modulus=l).as_expr())


def alt(M, x, y, m):
    P = eye(2)
    for i in range(m):
        P = P * (M[x] if i % 2 == 0 else M[y])
    return modl(P)


def S(X, k):
    Rr, P = eye(2), eye(2)
    for _ in range(k - 1):
        P = P * X
        Rr = Rr + P
    return modl(Rr)


M = {k: Matrix(v) for k, v in R.items()}
for (x, y), m in E.items():
    assert alt(M, x, y, m) == alt(M, y, x, m), (x, y, m)
Ss = [S(M[p] * M[q], k) for p, q, k in CROSS]
D0 = DomainMatrix.from_Matrix(Matrix.vstack(*Ss)).convert_to(GF(l))
Mt = Matrix.vstack(*[modl(s_ * (t * M[p] - eye(2))) for s_, (p, q, k) in zip(Ss, CROSS)])
minors = []
for i in range(Mt.rows):
    for j in range(i + 1, Mt.rows):
        d = Poly(Mt[[i, j], :].det(), t, modulus=l)
        if not d.is_zero:
            minors.append(d)
g = minors[0]
for d in minors[1:]:
    g = gcd(g, d)
print(f"Artin relations hold over F_{l}; sigma's = {[x.tolist() for x in Ss]}")
print(f"rank of stacked sigma = {D0.rank()} => c0 = {2 - D0.rank()}")
print(f"nonzero 2x2 minors of twisted stack: {len(minors)}; gcd = {g.as_expr()} => ct = 0")
