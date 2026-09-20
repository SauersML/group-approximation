# Exact verification that Houghton's group H_3 sits inside EL_3(J), J = F_2<S,T | TS=1>,
# as basis permutations of the Fock module V = F_2^(Omega), Omega = {1,2,3} x N.
# J elements: frozensets of monomials (a,b) = S^a T^b (normal form, since TS = 1), F_2 coefficients.
# Exit code 0 iff every check passes.
import sys
from itertools import product


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
Q = jadd(O, jmul(S, T))  # 1 - ST


def mat(rows):
    return tuple(tuple(r) for r in rows)


def mmul(A, B):
    return mat([[jadd(*[jmul(A[i][k], B[k][j]) for k in range(3)]) for j in range(3)] for i in range(3)])


I3 = mat([[O if i == j else Z for j in range(3)] for i in range(3)])


def x(i, j, r):
    return mat([[O if a == b else (r if (a, b) == (i - 1, j - 1) else Z) for b in range(3)] for a in range(3)])


def word(*ms):
    R = I3
    for M in ms:
        R = mmul(R, M)
    return R


# Fock action of a J monomial S^a T^b on delta_n: T^b lowers (kills if n < b), S^a raises.
def jact(r, n):
    out = set()
    for (a, b) in r:
        if n >= b:
            out ^= {n - b + a}
    return out


def mact(M, vec):
    # vec: set of (ray, index), ray in 0..2; column-vector convention.
    out = set()
    for (k, n) in vec:
        for i in range(3):
            for m in jact(M[i][k], n):
                out ^= {(i, m)}
    return frozenset(out)


fails = 0


def check(name, cond):
    global fails
    print(("ok   " if cond else "FAIL ") + name)
    if not cond:
        fails += 1


# 1. The Levi compressor word of jacobson-el3-is-not-lef (signs vanish in characteristic 2).
d12 = word(x(1, 2, S), x(2, 1, T), x(1, 2, S), x(2, 1, O), x(1, 2, O), x(2, 1, O))
check("d12 word = [[S,Q,0],[0,T,0],[0,0,1]]", d12 == mat([[S, Q, Z], [Z, T, Z], [Z, Z, O]]))
d12inv = mat([[T, Z, Z], [Q, S, Z], [Z, Z, O]])
check("d12 * [[T,0,0],[Q,S,0],[0,0,1]] = 1", mmul(d12, d12inv) == I3)
check("[[T,0,0],[Q,S,0],[0,0,1]] * d12 = 1", mmul(d12inv, d12) == I3)
check("d12 = a_12 of binary-jacobson-active-cycle-generates-rank-three", d12 == mat([[S, Q, Z], [Z, T, Z], [Z, Z, O]]))

# 2. Constant permutation matrix P23 = x23(1) x32(1) x23(1), and d13 = P23 d12 P23.
P23 = word(x(2, 3, O), x(3, 2, O), x(2, 3, O))
check("P23 swaps coordinates 2,3", P23 == mat([[O, Z, Z], [Z, Z, O], [Z, O, Z]]))
d13 = word(P23, d12, P23)
check("d13 = [[S,0,Q],[0,1,0],[0,0,T]]", d13 == mat([[S, Z, Q], [Z, O, Z], [Z, Z, T]]))

N = 40  # indices tested; all maps below move an index by at most 1


def houghton_translation(M, j, name):
    # expected: ray1 n -> n+1; ray j: n -> n-1 for n >= 1, (j,0) -> (1,0); other ray fixed.
    ok = True
    for k, n in product(range(3), range(N)):
        img = mact(M, {(k, n)})
        if k == 0:
            exp = {(0, n + 1)}
        elif k == j:
            exp = {(k, n - 1)} if n >= 1 else {(0, 0)}
        else:
            exp = {(k, n)}
        ok = ok and img == frozenset(exp)
    check(name + " acts as the Houghton translation g_1%d on Omega (indices < %d)" % (j + 1, N), ok)


houghton_translation(d12, 1, "d12")
houghton_translation(d13, 2, "d13")

# 3. The commutator [d12, d13] = d12^-1 d13^-1 d12 d13 is a finitary permutation (a transposition
# in Houghton's H_3).  Compute it exactly in M_3(J) and on the Fock basis.
d13inv = word(P23, d12inv, P23)
c = word(d12inv, d13inv, d12, d13)
moved = []
perm_ok = True
for k, n in product(range(3), range(N)):
    img = mact(c, {(k, n)})
    perm_ok = perm_ok and len(img) == 1
    if img != frozenset({(k, n)}):
        moved.append(((k + 1, n), tuple(sorted((a + 1, b) for (a, b) in img))))
check("[d12,d13] maps basis vectors to basis vectors", perm_ok)
print("     [d12,d13] moves:", moved)
check("[d12,d13] is a transposition of two basis vectors", len(moved) == 2)
diff = [[jadd(c[i][j], I3[i][j]) for j in range(3)] for i in range(3)]
# an element of J is finitary iff it is killed by S^m (x) T^m-conjugation for large m, i.e. T^m e S^m = 0
m = 5
fin = all(jmul(jmul(frozenset({(0, m)}), e), frozenset({(m, 0)})) == Z for row in diff for e in row)
check("[d12,d13] - 1 has finitary entries (T^5 e S^5 = 0)", fin)

# 4. The head x13(Q) is the transvection delta_0^(3) -> delta_0^(3) + delta_0^(1).
h = x(1, 3, Q)
hk = all(mact(h, {(k, n)}) == (frozenset({(2, 0), (0, 0)}) if (k, n) == (2, 0) else frozenset({(k, n)}))
         for k, n in product(range(3), range(N)))
check("head x13(Q) is the elementary transvection at (3,0)->(1,0)", hk)

# 5. Rank two: d12 already lies in EL_2(J) (upper-left block), so H_2 <= EL_2(J).
check("d12 is supported in the upper-left 2x2 block", all(d12[i][2] == (O if i == 2 else Z) and d12[2][i] == (O if i == 2 else Z) for i in range(3)))

print("FAILURES:", fails)
sys.exit(1 if fails else 0)
