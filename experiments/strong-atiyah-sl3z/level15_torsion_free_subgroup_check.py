"""Check the level-15 torsion-free subgroup of SL_3(Z) used in
sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts.

S = {(t^chi(M), M) : M in P5} inside SL_3(F_3) x SL_3(F_5), where
  P5  = <diag(2,1,3), diag(1,2,3), [[0,1,0],[1,0,0],[0,0,4]]>  (a Sylow 2-subgroup of SL_3(F_5)),
  chi = 1 iff det of the top-left 2x2 block is a non-square mod 5,
  t   = diag(-1,-1,1) mod 3.
H = {g in SL_3(Z) : (g mod 3, g mod 5) in S}.
"""
import itertools

I3 = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def mul(A, B, m):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(3)) % m for j in range(3)) for i in range(3))


def mulz(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)) for i in range(3))


def det(A):
    return (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
            - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
            + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))


def red(A, m):
    return tuple(tuple(x % m for x in row) for row in A)


def closure(gens, m):
    seen = {I3}
    frontier = [I3]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mul(x, g, m)
                if y not in seen:
                    seen.add(y)
                    new.append(y)
        frontier = new
    return seen


def order(x, m):
    y, k = x, 1
    while y != I3:
        y = mul(y, x, m)
        k += 1
    return k


P5 = closure([((2, 0, 0), (0, 1, 0), (0, 0, 3)),
              ((1, 0, 0), (0, 2, 0), (0, 0, 3)),
              ((0, 1, 0), (1, 0, 0), (0, 0, 4))], 5)
print("|P5| =", len(P5))
assert len(P5) == 32
assert all(det(M) % 5 == 1 for M in P5)


def chi(M):
    d = (M[0][0] * M[1][1] - M[0][1] * M[1][0]) % 5
    return 0 if d in (1, 4) else 1


t = ((2, 0, 0), (0, 2, 0), (0, 0, 1))
S = {((t if chi(M) else I3), M) for M in P5}
print("|S| =", len(S))
assert len(S) == 32
for (a, b), (c, d) in itertools.product(S, S):
    assert (mul(a, c, 3), mul(b, d, 5)) in S
print("S is closed under multiplication")
assert {x for x, _ in S} == {I3, t}
print("projection of S to SL_3(F_3) is {1, t}")

inv_pairs = [(x, y) for x, y in S if x != I3 and y != I3 and order(x, 3) == 2 and order(y, 5) == 2]
print("pairs in S with both coordinates involutions:", len(inv_pairs))
assert not inv_pairs
print("orders of y over the coset x = t:", sorted({order(y, 5) for x, y in S if x == t}))

count = 0
bad = 0
rng = range(-2, 3)
for entries in itertools.product(rng, repeat=9):
    g = (entries[0:3], entries[3:6], entries[6:9])
    if det(g) != 1:
        continue
    y, k = g, 1
    while y != I3 and k < 12:
        y = mulz(y, g)
        k += 1
    if y != I3 or g == I3:
        continue
    count += 1
    if (red(g, 3), red(g, 5)) in S:
        bad += 1
print("nontrivial torsion elements with entries in [-2,2]:", count, " lying in H:", bad)
assert bad == 0
print("index [SL_3(Z):H] =", 5616 * 372000 // 32)
print("DONE")
