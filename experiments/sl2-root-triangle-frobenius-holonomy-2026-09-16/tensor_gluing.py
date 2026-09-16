# tensor_gluing.py -- linear-algebra checks for sl2-root-triangle-tensor-vertex-reps-force-2hol-zero (2026-09-16).
# Pure python3 + sympy, single-threaded, runs in seconds.  Usage: python3 tensor_gluing.py
# Slot operators on (K^2)^{tensor f}: x_c = E_21 in slot c, y_c = E_12 in slot c (the root coefficients
# X^v_c, X^u_c of the twisted tensor module L(Z/f) of SL_2(2^f)).
# (1) Centralizer: dim C({x_c3, y_c3 : c3 != c1,c2} U {x_c1, y_c2}) = 4, spanned by 1, x_c1, y_c2, x_c1 y_c2.
#     (Rank over F_2 equals rank over every extension field, so this is the dimension over K.)
# (2) Commutator of P = b x_c1 + g y_{c1-h} + d x_c1 y_{c1-h} and Q = b' x_{c1+h} + g' y_c1 + d' x_{c1+h} y_c1:
#     the set of distinct nonzero entries mod 2, which must generate the ideal (b,d)(g',d').
# (3) The case 2h = 0 (f = 4, h = 2): exhibit commuting P, Q with (b,d) != 0, (g',d') != 0.
import itertools
import sympy as sp

def kron(A, B):
    n, m = len(A), len(B)
    return [[A[i // m][j // m] * B[i % m][j % m] for j in range(n * m)] for i in range(n * m)]
def slot(op, c, f):
    I2 = [[1, 0], [0, 1]]
    M = [[1]]
    for t in range(f):
        M = kron(M, op if t == c else I2)
    return M
def mm(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
def add(*Ms):
    n = len(Ms[0])
    return [[sum(M[i][j] for M in Ms) for j in range(n)] for i in range(n)]
def scal(a, M): return [[a * e for e in row] for row in M]
def comm(A, B):
    AB, BA = mm(A, B), mm(B, A)
    return [[AB[i][j] - BA[i][j] for j in range(len(A))] for i in range(len(A))]
E12 = [[0, 1], [0, 0]]; E21 = [[0, 0], [1, 0]]

def rank_mod2(rows):
    rows = [int("".join(str(e % 2) for e in r), 2) for r in rows]
    basis = []
    for r in rows:
        for b in basis:
            r = min(r, r ^ b)
        if r: basis.append(r)
    return len(basis)

# (1) centralizer dimension, f = 3 and f = 4
for f in (3, 4):
    for h in range(1, f):
        if (2 * h) % f == 0: continue
        c1 = 0; c2 = (c1 - h) % f
        ops = [slot(E21, c1, f), slot(E12, c2, f)]
        for c3 in range(f):
            if c3 not in (c1, c2): ops += [slot(E21, c3, f), slot(E12, c3, f)]
        n = 2 ** f
        eqs = []   # linear equations in the n^2 entries of Z: Z A - A Z = 0
        for A in ops:
            for i in range(n):
                for j in range(n):
                    row = [0] * (n * n)
                    for k in range(n):
                        row[i * n + k] += A[k][j]      # (Z A)_{ij} = sum_k Z_ik A_kj
                        row[k * n + j] -= A[i][k]      # (A Z)_{ij} = sum_k A_ik Z_kj
                    eqs.append(row)
        dim = n * n - rank_mod2(eqs)
        span = [slot([[1, 0], [0, 1]], 0, f), ops[0], ops[1], mm(ops[0], ops[1])]
        ok = all(all(comm(S, A)[i][j] % 2 == 0 for i in range(n) for j in range(n)) for S in span for A in ops)
        print(f"(1) f={f} h={h}: centralizer dimension {dim}; 1, x_c1, y_c2, x_c1*y_c2 lie in it: {ok}; "
              f"independent: {rank_mod2([sum(S, []) for S in span]) == 4}")

# (2) symbolic commutator
b, g, d, b2, g2, d2 = sp.symbols("b g d b2 g2 d2")
for f in (3, 4, 5):
    for h in range(1, f):
        if (2 * h) % f == 0: continue
        c1 = 0
        x = lambda c: slot(E21, c % f, f); y = lambda c: slot(E12, c % f, f)
        P = add(scal(b, x(c1)), scal(g, y(c1 - h)), scal(d, mm(x(c1), y(c1 - h))))
        Q = add(scal(b2, x(c1 + h)), scal(g2, y(c1)), scal(d2, mm(x(c1 + h), y(c1))))
        C = comm(P, Q)
        entries = set()
        for row in C:
            for e in row:
                p = sp.Poly(sp.expand(e), b, g, d, b2, g2, d2, modulus=2)
                if not p.is_zero: entries.add(p.as_expr())
        target = {b * g2, b * d2, d * g2, d * d2}
        print(f"(2) f={f} h={h}: distinct nonzero entries of [P,Q] mod 2: {sorted(map(str, entries))}; "
              f"equal to {{b g', b d', d g', d d'}}: {entries == target}")

# (3) f = 4, h = 2: a commuting pair
f, h, c1 = 4, 2, 0
x = lambda c: slot(E21, c % f, f); y = lambda c: slot(E12, c % f, f)
P = add(x(c1), y(c1 - h)); Q = add(x(c1 + h), y(c1))
C = comm(P, Q)
print(f"(3) f=4 h=2: P = x_0 + y_2, Q = x_2 + y_0 commute mod 2: {all(e % 2 == 0 for row in C for e in row)}; "
      f"P y_0 != y_0 P: {any(e % 2 for row in comm(P, y(0)) for e in row)}; "
      f"P x_2 != x_2 P: {any(e % 2 for row in comm(P, x(2)) for e in row)}")
