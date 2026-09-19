# Exact verification of the rank-three contraction trap in EL_3(J), J = F_2<S,T | TS=1>.
# A J element is a frozenset of monomials (a,b) meaning S^a T^b, coefficients in F_2.
# Matrices are 3x3 tuples of tuples of J elements; indices 0,1,2 stand for matrix indices 1,2,3.
# Exit code 0 iff every check passes.
import sys


def mono_mul(m, n):
    a, b = m
    c, d = n
    if b >= c:
        return (a, b - c + d)
    return (a + c - b, d)


def jmul(x, y):
    r = set()
    for m in x:
        for n in y:
            r ^= {mono_mul(m, n)}
    return frozenset(r)


def jadd(*xs):
    r = set()
    for x in xs:
        r ^= set(x)
    return frozenset(r)


Z = frozenset()
O = frozenset({(0, 0)})
S = frozenset({(1, 0)})
T = frozenset({(0, 1)})


def mono(a, b):
    return frozenset({(a, b)})


Q = jadd(O, jmul(S, T))          # Q = 1 - ST = 1 + ST over F_2
SQ = jmul(S, Q)
QT = jmul(Q, T)
N = 3


def mat(entries):
    return tuple(tuple(row) for row in entries)


def ident():
    return mat([[O if i == j else Z for j in range(N)] for i in range(N)])


def mmul(A, B):
    return mat([[jadd(*[jmul(A[i][k], B[k][j]) for k in range(N)]) for j in range(N)] for i in range(N)])


def elem(i, j, r):
    M = [list(row) for row in ident()]
    M[i - 1][j - 1] = r
    return mat(M)


def diag(d1, d2, d3):
    return mat([[d1, Z, Z], [Z, d2, Z], [Z, Z, d3]])


def prod(*Ms):
    R = ident()
    for M in Ms:
        R = mmul(R, M)
    return R


def check_inverse(A, B):
    return mmul(A, B) == ident() and mmul(B, A) == ident()


# Inverses: every elementary matrix over F_2 is an involution; for the other generators
# we give explicit two-sided inverses and check them.
def inv_word(word):
    return [w for w in reversed(word)]


fails = 0


def check(name, cond):
    global fails
    print(('PASS ' if cond else 'FAIL ') + name)
    if not cond:
        fails += 1


I3 = ident()

# Generators of A_2 (supported on indices 1,3).
a1 = elem(1, 3, O)          # x_13(1)
a2 = elem(1, 3, S)          # x_13(S)
a3 = elem(3, 1, O)          # x_31(1)
a4 = elem(3, 1, T)          # x_31(T)
a5 = diag(jadd(O, SQ), O, O)  # c  = diag(1+SQ,1,1)
a6 = diag(jadd(O, QT), O, O)  # c' = diag(1+QT,1,1)
gens = [a1, a2, a3, a4, a5, a6]
for k, a in enumerate(gens, 1):
    check('a%d is an involution' % k, mmul(a, a) == I3)

# c and c' and e as elementary words.
check('c = [x_12(S), x_21(Q)]', prod(elem(1, 2, S), elem(2, 1, Q), elem(1, 2, S), elem(2, 1, Q)) == a5)
check("c' = [x_12(Q), x_21(T)]", prod(elem(1, 2, Q), elem(2, 1, T), elem(1, 2, Q), elem(2, 1, T)) == a6)

# U = u^(13) = w(S) w(1), the compressor in the (1,3) block.
U = prod(a2, a4, a2, a1, a3, a1)
U_expected = mat([[S, Z, Q], [Z, O, Z], [Z, Z, T]])
Uinv_expected = mat([[T, Z, Z], [Z, O, Z], [Q, Z, S]])
check('U = x13(S)x31(T)x13(S)x13(1)x31(1)x13(1) = [[S,Q],[0,T]] on (1,3)', U == U_expected)
check('U^{-1} = [[T,0],[Q,S]] on (1,3)', check_inverse(U, Uinv_expected))
Uinv = prod(a1, a3, a1, a2, a4, a2)
check('U^{-1} = reversed word', Uinv == Uinv_expected)

# g = diag(u,1) on indices (1,2), as the p22 elementary word over F_2.
g = prod(elem(1, 2, S), elem(2, 1, T), elem(1, 2, S), elem(2, 1, O), elem(1, 2, O), elem(2, 1, O))
g_expected = mat([[S, Q, Z], [Z, T, Z], [Z, Z, O]])
ginv = mat([[T, Z, Z], [Q, S, Z], [Z, Z, O]])
check('g = x12(S)x21(T)x12(S)x21(1)x12(1)x21(1) = diag([[S,Q],[0,T]],1)', g == g_expected)
check('g^{-1} = diag([[T,0],[Q,S]],1)', check_inverse(g, ginv))

# e = diag(1, 1+SQ, 1) = [x_21(S), x_12(Q)].
e = diag(O, jadd(O, SQ), O)
check('e = [x_21(S), x_12(Q)]', prod(elem(2, 1, S), elem(1, 2, Q), elem(2, 1, S), elem(1, 2, Q)) == e)
check('e is an involution', mmul(e, e) == I3)


def conj(x, y, xinv):
    return prod(x, y, xinv)


# Contraction relations (C1)-(C6).
check('(C1) g a1 g^-1 = a2', conj(g, a1, ginv) == a2)
check('(C2) g a2 g^-1 = a5 U a1 U^-1', conj(g, a2, ginv) == prod(a5, U, a1, Uinv))
check('(C2 value) g a2 g^-1 = x_13(S^2)', conj(g, a2, ginv) == elem(1, 3, mono(2, 0)))
check('(C3) g a3 g^-1 = a4', conj(g, a3, ginv) == a4)
check('(C4) g a4 g^-1 = U a3 U^-1 a6', conj(g, a4, ginv) == prod(U, a3, Uinv, a6))
check('(C4 value) g a4 g^-1 = x_31(T^2)', conj(g, a4, ginv) == elem(3, 1, mono(0, 2)))
check('(C5) g a5 g^-1 = U a5 U^-1', conj(g, a5, ginv) == prod(U, a5, Uinv))
check('(C6) g a6 g^-1 = U a6 U^-1', conj(g, a6, ginv) == prod(U, a6, Uinv))

# Centralizing relations (Z1)-(Z6).
for k, a in enumerate(gens, 1):
    check('(Z%d) [e, a%d] = 1' % (k, k), mmul(e, a) == mmul(a, e))

# Witness.
y = conj(ginv, a1, g)
check('g^-1 a1 g = x_13(T) x_23(Q)', y == mmul(elem(1, 3, T), elem(2, 3, Q)))
w = prod(e, y, e, conj(ginv, a1, g))  # [e, y] with e, y involutions
check('y is an involution', mmul(y, y) == I3)
check('[e, g^-1 a1 g] = x_23(SQ)', w == elem(2, 3, SQ))
check('x_23(SQ) != 1', w != I3)
check('SQ != 0', SQ != Z)

print('failures:', fails)
sys.exit(1 if fails else 0)
