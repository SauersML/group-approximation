# Signed verification of the rank-three contraction trap over J_Z = Z<S,T | TS=1>.
# Every identity checked here is an identity in the universal ring with ts = 1, so it holds in
# EL_3(R) for every unital ring R and elements t s = 1 (via the ring map S -> s, T -> t).
# A J_Z element is a dict {(a,b): coefficient} meaning sum c * S^a T^b.
# Exit code 0 iff every check passes.
import sys


def mono_mul(m, n):
    a, b = m
    c, d = n
    if b >= c:
        return (a, b - c + d)
    return (a + c - b, d)


def norm(d):
    return tuple(sorted((k, v) for k, v in d.items() if v != 0))


def jmul(x, y):
    r = {}
    for m, cm in x:
        for n, cn in y:
            p = mono_mul(m, n)
            r[p] = r.get(p, 0) + cm * cn
    return norm(r)


def jadd(*xs):
    r = {}
    for x in xs:
        for m, c in x:
            r[m] = r.get(m, 0) + c
    return norm(r)


def jneg(x):
    return tuple((m, -c) for m, c in x)


Z = ()
O = (((0, 0), 1),)
S = (((1, 0), 1),)
T = (((0, 1), 1),)
Q = jadd(O, jneg(jmul(S, T)))    # q = 1 - st
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


I3 = ident()
fails = 0


def check(name, cond):
    global fails
    print(('PASS ' if cond else 'FAIL ') + name)
    if not cond:
        fails += 1


def x(i, j, r):
    return elem(i, j, r)


def xi(i, j, r):
    return elem(i, j, jneg(r))


sq = jmul(S, Q)
qt = jmul(Q, T)
check('qs = 0', jmul(Q, S) == Z)
check('tq = 0', jmul(T, Q) == Z)
check('sq != 0', sq != Z)

a1, a1i = x(1, 3, O), xi(1, 3, O)
a2, a2i = x(1, 3, S), xi(1, 3, S)
a3, a3i = x(3, 1, O), xi(3, 1, O)
a4, a4i = x(3, 1, T), xi(3, 1, T)

# c = diag(1+sq,1,1), c^-1 = diag(1-sq,1,1); d = diag(1-qt,1,1), d^-1 = diag(1+qt,1,1).
c, ci = diag(jadd(O, sq), O, O), diag(jadd(O, jneg(sq)), O, O)
d, di = diag(jadd(O, jneg(qt)), O, O), diag(jadd(O, qt), O, O)
check('c c^-1 = 1', mmul(c, ci) == I3 and mmul(ci, c) == I3)
check('d d^-1 = 1', mmul(d, di) == I3 and mmul(di, d) == I3)
# Elementary words for c and d (Whitehead type, using qs = 0 and tq = 0).
cw = prod(x(1, 2, S), x(2, 1, Q), xi(1, 2, S), xi(2, 1, Q))
dw = prod(x(1, 2, Q), x(2, 1, T), xi(1, 2, Q), xi(2, 1, T))
check('c = [x_12(s), x_21(q)]', cw == c)
check('d^-1 = [x_12(q), x_21(t)]', dw == di)

# U = compressor on (1,3): w(s) w(1)^-1 with w(a) = x13(a) x31(-t or -1) x13(a).
U = prod(x(1, 3, S), xi(3, 1, T), x(1, 3, S), xi(1, 3, O), x(3, 1, O), xi(1, 3, O))
Uexp = mat([[S, Z, jneg(Q)], [Z, O, Z], [Z, Z, T]])
Uinv = mat([[T, Z, Z], [Z, O, Z], [jneg(Q), Z, S]])
check('U = [[s,-q],[0,t]] on (1,3)', U == Uexp)
check('U^-1 = [[t,0],[-q,s]] on (1,3)', mmul(U, Uinv) == I3 and mmul(Uinv, U) == I3)

# g = diag([[s,-q],[0,t]], 1): the p22 word x12(s) x21(-t) x12(s) x21(1) x12(-1) x21(1).
g = prod(x(1, 2, S), xi(2, 1, T), x(1, 2, S), x(2, 1, O), xi(1, 2, O), x(2, 1, O))
gexp = mat([[S, jneg(Q), Z], [Z, T, Z], [Z, Z, O]])
ginv = mat([[T, Z, Z], [jneg(Q), S, Z], [Z, Z, O]])
check('g = diag([[s,-q],[0,t]],1)', g == gexp)
check('g^-1 = diag([[t,0],[-q,s]],1)', mmul(g, ginv) == I3 and mmul(ginv, g) == I3)

# e = diag(1, 1+sq, 1), e^-1 = diag(1, 1-sq, 1).
e, ei = diag(O, jadd(O, sq), O), diag(O, jadd(O, jneg(sq)), O)
check('e = [x_21(s), x_12(q)]', prod(x(2, 1, S), x(1, 2, Q), xi(2, 1, S), xi(1, 2, Q)) == e)
check('e e^-1 = 1', mmul(e, ei) == I3)


def conj(y, h, hinv):
    return prod(h, y, hinv)


check('(C1) g a1 g^-1 = a2', conj(a1, g, ginv) == a2)
check('(C2) g a2 g^-1 = c U a1 U^-1', conj(a2, g, ginv) == prod(c, U, a1, Uinv))
check('(C2 value) = x_13(s^2)', conj(a2, g, ginv) == x(1, 3, jmul(S, S)))
check('(C3) g a3 g^-1 = a4', conj(a3, g, ginv) == a4)
check('(C4) g a4 g^-1 = U a3 U^-1 d^-1', conj(a4, g, ginv) == prod(U, a3, Uinv, di))
check('(C4 value) = x_31(t^2)', conj(a4, g, ginv) == x(3, 1, jmul(T, T)))
check('(C5) g c g^-1 = U c U^-1', conj(c, g, ginv) == prod(U, c, Uinv))
check('(C6) g d g^-1 = U d U^-1', conj(d, g, ginv) == prod(U, d, Uinv))
for nm, a in [('a1', a1), ('a2', a2), ('a3', a3), ('a4', a4), ('c', c), ('d', d)]:
    check('(Z) [e, %s] = 1' % nm, mmul(e, a) == mmul(a, e))

y = conj(a1, ginv, g)
yi = conj(a1i, ginv, g)
check('g^-1 a1 g = x_13(t) x_23(-q)', y == mmul(x(1, 3, T), x(2, 3, jneg(Q))))
w = prod(e, y, ei, yi)
check('[e, g^-1 a1 g] = x_23(-sq)', w == x(2, 3, jneg(sq)))
check('witness != 1', w != I3)
print('failures:', fails)
sys.exit(1 if fails else 0)
