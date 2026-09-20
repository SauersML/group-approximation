"""Independent sympy check of 2-dim reps over F_5 of the opposite-twos 2x2 dead joins with
c0 = 1 (L_0 not onto over Z[H]) and ct = 0 (the same rep has zero twisted Alexander rank).
Halves (ac, bc, be, ae); chi = (1, 1, -1, -1); labels are twice the halves; [a,b] = [c,e] = 1."""
from sympy import GF, Matrix, eye, symbols, Poly, gcd
from sympy.polys.matrices import DomainMatrix

l = 5
t = symbols('t')
EXAMPLES = {
    (2, 3, 2, 4): {'a': [[0, 1], [2, 0]], 'b': [[2, 4], [3, 2]], 'c': [[0, 2], [1, 2]], 'e': [[4, 2], [1, 1]]},
    (2, 3, 2, 5): {'a': [[0, 1], [1, 1]], 'b': [[3, 1], [1, 4]], 'c': [[1, 4], [4, 2]], 'e': [[1, 1], [1, 0]]},
}


def modl(X):
    return X.applyfunc(lambda z: Poly(z, t, modulus=l).as_expr())


def alt(M, x, y, m):
    P = eye(2)
    for i in range(m):
        P = P * (M[x] if i % 2 == 0 else M[y])
    return modl(P)


def S(X, k):
    R, P = eye(2), eye(2)
    for _ in range(k - 1):
        P = P * X
        R = R + P
    return modl(R)


for h, R in EXAMPLES.items():
    M = {k: Matrix(v) for k, v in R.items()}
    E = {('a', 'b'): 2, ('c', 'e'): 2, ('a', 'c'): 2 * h[0], ('b', 'c'): 2 * h[1],
         ('b', 'e'): 2 * h[2], ('a', 'e'): 2 * h[3]}
    for (x, y), m in E.items():
        assert alt(M, x, y, m) == alt(M, y, x, m), (h, x, y, m)
    cross = [('a', 'c', h[0]), ('b', 'c', h[1]), ('b', 'e', h[2]), ('a', 'e', h[3])]
    Ss = [S(M[p] * M[q], k) for p, q, k in cross]
    D0 = DomainMatrix.from_Matrix(Matrix.vstack(*Ss)).convert_to(GF(l))
    Mt = Matrix.vstack(*[modl(s * (t * M[p] - eye(2))) for s, (p, q, k) in zip(Ss, cross)])
    # gcd of all 2x2 minors of the twisted stack: nonzero <=> ct = 0
    minors = []
    for i in range(Mt.rows):
        for j in range(i + 1, Mt.rows):
            d = Poly(Mt[[i, j], :].det(), t, modulus=l)
            if not d.is_zero:
                minors.append(d)
    g = minors[0]
    for d in minors[1:]:
        g = gcd(g, d)
    print(f"halves {h}: Artin relations hold over F_{l}; sigma's = {[s.tolist() for s in Ss]}")
    print(f"   rank of stacked sigma = {D0.rank()}  => c0 = {2 - D0.rank()}; common kernel "
          f"{D0.nullspace().to_Matrix().tolist()}")
    print(f"   nonzero 2x2 minors of twisted stack: {len(minors)}; gcd = {g.as_expr()}  => ct = 0")
