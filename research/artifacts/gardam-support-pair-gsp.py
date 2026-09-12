#!/usr/bin/env python3
"""Gardam support pair (arXiv:2312.05240, Theorem A) over Z, Q and Q_2.

Part 1: exact check in R[P], R = Z[s,t]/(s^4+1, t^4+1), that alpha*beta = 1,
        and that supp(alpha), supp(beta) are the 21-element sets S, T of
        Gardam's unit_problem.py (zenodo 14008425).
Part 2: build the bilinear system uv = 1 on (S, T) with augmentation
        normalisation, write the F_2 product table for the C enumerator.
Part 3 (after enumeration): Jacobian ranks mod 2 at every F_2-point and
        2-adic lifting of every nontrivial residue.
"""
import sys, json, itertools
from collections import defaultdict, Counter

def mul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(4)) for j in range(4)) for i in range(4))

def inv(A):
    # affine isometry [[R, t], [0, 1]] with R a signed permutation matrix
    R = [[A[j][i] for j in range(3)] for i in range(3)]  # R^T = R^-1
    t = [A[i][3] for i in range(3)]
    nt = [-sum(R[i][k] * t[k] for k in range(3)) for i in range(3)]
    return tuple(tuple(R[i]) + (nt[i],) for i in range(3)) + ((0, 0, 0, 1),)

E = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
a = ((1, 0, 0, 1), (0, -1, 0, 1), (0, 0, -1, 0), (0, 0, 0, 1))
b = ((-1, 0, 0, 0), (0, 1, 0, 1), (0, 0, -1, 1), (0, 0, 0, 1))

def w(*gs):
    r = E
    for g in gs:
        r = mul(r, g)
    return r

A, B = inv(a), inv(b)
assert mul(a, A) == E and mul(b, B) == E
assert w(A, b, b, a, b, b) == E and w(B, a, a, b, a, a) == E
x, y, z = w(a, a), w(b, b), w(a, b, a, b)
X, Y, Z = inv(x), inv(y), inv(z)

# ---- supports from unit_problem.py, verbatim ordering ----
p = [E, w(x, Z), w(X, Z), w(y, Z), w(Y, Z)]
q = [X, E, w(X, Y, z), w(y, z)]
r = [w(X, Y, z), w(x, z), w(Y, z, z), w(z, z)]
s_ = [w(X, Z), w(y, Z), Z, w(X, y, Z), w(X, Z, Z), w(y, Z, Z), w(Z, Z), w(X, y, Z, Z)]
pd = [E, w(X, z), w(x, z), w(y, z), w(Y, z)]
qd = [E, X, w(y, z), w(X, Y, z)]
rd = [w(X, Y, z), w(x, z), w(Y, z, z), w(z, z)]
sd = [w(X, y), E, y, X, w(X, y, z), z, w(y, z), w(X, z)]
assert pd == [w(B, g, b) for g in p]
assert qd == [w(X, B, A, g, a, b) for g in q]
assert rd == r
assert sd == [w(y, Z, A, g, a) for g in s_]
S = p + [w(g, a) for g in q] + [w(g, b) for g in r] + [w(g, a, b) for g in s_]
T = pd + [w(g, a) for g in qd] + [w(g, b) for g in rd] + [w(g, a, b) for g in sd]
assert len(set(S)) == 21 and len(set(T)) == 21

# ---- Part 1: R = Z[s,t]/(s^4+1,t^4+1), elements as dict (i,j) -> int, 0<=i,j<4 ----
def rmono(sign, i, j):
    sg = sign
    if i >= 4: i -= 4; sg = -sg
    if j >= 4: j -= 4; sg = -sg
    return {(i, j): sg}

def rmul(c, d):
    out = defaultdict(int)
    for (i, j), m in c.items():
        for (k, l), n in d.items():
            ii, jj, sg = i + k, j + l, 1
            if ii >= 4: ii -= 4; sg = -sg
            if jj >= 4: jj -= 4; sg = -sg
            out[(ii, jj)] += sg * m * n
    return {kk: vv for kk, vv in out.items() if vv}

def gr(terms):
    """terms: list of (sign, s_exp, t_exp, [group letters])"""
    out = defaultdict(dict)
    for sign, i, j, word in terms:
        g = w(*word) if word else E
        c = out[g]
        for kk, vv in rmono(sign, i, j).items():
            c[kk] = c.get(kk, 0) + vv
    return {g: {kk: vv for kk, vv in c.items() if vv} for g, c in out.items() if any(c.values())}

def gmul(U, V):
    out = defaultdict(lambda: defaultdict(int))
    for g, c in U.items():
        for h, d in V.items():
            k = mul(g, h)
            for kk, vv in rmul(c, d).items():
                out[k][kk] += vv
    return {g: {kk: vv for kk, vv in c.items() if vv} for g, c in out.items() if any(v for v in c.values())}

def gscale_right(U, g):
    return {mul(h, g): c for h, c in U.items()}

def gscale_coef(U, sign, i, j):
    return {g: rmul(c, rmono(sign, i, j)) for g, c in U.items()}

def gadd(*Us):
    out = defaultdict(lambda: defaultdict(int))
    for U in Us:
        for g, c in U.items():
            for kk, vv in c.items():
                out[g][kk] += vv
    return {g: {kk: vv for kk, vv in c.items() if vv} for g, c in out.items() if any(v for v in c.values())}

al1 = gr([(1, 0, 0, []), (1, 0, 2, [x, Z]), (-1, 0, 2, [X, Z]), (-1, 2, 0, [y, Z]), (1, 2, 0, [Y, Z])])
ala = gr([(-1, 2, 0, [X]), (1, 0, 0, []), (-1, 0, 0, [X, Y, z]), (1, 2, 0, [y, z])])
alb = gr([(1, 0, 0, [X, Y, z]), (-1, 0, 2, [x, z]), (1, 0, 2, [Y, z, z]), (-1, 0, 0, [z, z])])
alc = gr([(-1, 0, 2, [X, Z]), (-1, 2, 0, [y, Z]), (1, 2, 2, [Z]), (1, 0, 0, [X, y, Z]),
          (1, 2, 0, [X, Z, Z]), (1, 0, 2, [y, Z, Z]), (-1, 0, 0, [Z, Z]), (-1, 2, 2, [X, y, Z, Z])])
be1 = gr([(1, 0, 0, []), (1, 0, 2, [X, z]), (-1, 0, 2, [x, z]), (1, 2, 0, [y, z]), (-1, 2, 0, [Y, z])])
bea = gr([(-1, 0, 0, []), (1, 2, 0, [X]), (-1, 2, 0, [y, z]), (1, 0, 0, [X, Y, z])])
beb = gr([(-1, 0, 0, [X, Y, z]), (1, 0, 2, [x, z]), (-1, 0, 2, [Y, z, z]), (1, 0, 0, [z, z])])
bec = gr([(1, 2, 2, [X, y]), (1, 0, 0, []), (-1, 0, 2, [y]), (-1, 2, 0, [X]), (-1, 0, 0, [X, y, z]),
          (-1, 2, 2, [z]), (1, 2, 0, [y, z]), (1, 0, 2, [X, z])])

def assemble(c1, ca, cb, cc):
    return gadd(c1, gscale_coef(gscale_right(ca, a), 1, 1, 0), gscale_coef(gscale_right(cb, b), 1, 0, 1),
                gscale_coef(gscale_right(cc, w(a, b)), 1, 1, 1))

alpha = assemble(al1, ala, alb, alc)
beta = assemble(be1, bea, beb, bec)
ab = gmul(alpha, beta)
ba = gmul(beta, alpha)
one = {E: {(0, 0): 1}}
print("part1 |supp alpha| =", len(alpha), "|supp beta| =", len(beta))
print("part1 alpha*beta == 1:", ab == one, " beta*alpha == 1:", ba == one)
print("part1 supp(alpha) == S:", set(alpha) == set(S), " supp(beta) == T:", set(beta) == set(T))
# every coefficient is a signed monomial s^i t^j (Remark 2 grading)
print("part1 coefficients are signed monomials:", all(len(c) == 1 and abs(list(c.values())[0]) == 1
                                                     for U in (alpha, beta) for c in U.values()))

# ---- Part 2: product table ----
prod = {}
index = {}
for i, g in enumerate(S):
    for j, h in enumerate(T):
        k = mul(g, h)
        if k not in index:
            index[k] = len(index)
        prod[(i, j)] = index[k]
K = len(index)
eid = index.get(E, -1)
assert eid >= 0
cnt = Counter(prod.values())
odd = [k for k, c in cnt.items() if c % 2 == 1]
print("part2 products K =", K, "identity index", eid, "reps at identity", cnt[eid], "odd-count products", odd)
if len(sys.argv) > 1 and sys.argv[1] == "table":
    with open("table.txt", "w") as f:
        f.write(f"21 {K} {eid}\n")
        for i in range(21):
            f.write(" ".join(str(prod[(i, j)]) for j in range(21)) + "\n")
    print("wrote table.txt")
json.dump({"K": K, "eid": eid, "prod": [[prod[(i, j)] for j in range(21)] for i in range(21)],
           "trivial_pairs": [[i, j] for i in range(21) for j in range(21) if mul(S[i], T[j]) == E]},
          open("system.json", "w"))
print("part2 trivial pairs (g_i h_j = 1):", sum(1 for i in range(21) for j in range(21) if mul(S[i], T[j]) == E))
