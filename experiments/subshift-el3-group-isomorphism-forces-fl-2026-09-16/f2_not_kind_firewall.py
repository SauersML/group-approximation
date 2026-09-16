#!/usr/bin/env python3
"""F_2 is not a 'kind' coefficient ring: exact checks behind the firewall in
notes/subshift-el3-group-isomorphism-forces-fl-swarm-2026-09-16.md.

Part 1 (exhaustive, exact): symmetric idempotents and orthogonal matrices
(A A^T = I) in M_3(F_2) and M_4(F_2); count the non-diagonal / non-monomial ones.

Part 2 (sanity check of an identity that is proved algebraically in the notes):
the Fibonacci Sturmian subshift X, a clopen cylinder U with U, TU, T^2U, T^3U
pairwise disjoint, matrix units e_ij = u^i 1_U u^-j (0 <= i,j <= 3), and
w = sum_{i != j} e_ij + (1 - 1_W), W = U u TU u T^2U u T^3U.
We act on the orbit module V_x = F_2^(Z) of one point x, with
f . delta_n = f(T^n x) delta_n and u . delta_n = delta_{n+1}; this representation
is faithful because R_X is simple. We check w^2 = 1 on a window and that
w 1_U w maps some delta_n off the line F_2 delta_n, so w 1_U w is not in D_X.
"""
import itertools
from math import isqrt

# ---------- Part 1 ----------
def matmul(A, B, n):
    return tuple(tuple(sum(A[i][k] & B[k][j] for k in range(n)) % 2 for j in range(n)) for i in range(n))

def transpose(A, n):
    return tuple(tuple(A[j][i] for j in range(n)) for i in range(n))

def all_mats(n):
    for bits in itertools.product((0, 1), repeat=n * n):
        yield tuple(tuple(bits[i * n + j] for j in range(n)) for i in range(n))

def is_monomial(A, n):
    return all(sum(r) == 1 for r in A) and all(sum(A[i][j] for i in range(n)) == 1 for j in range(n))

def ident(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))

for n in (2, 3, 4):
    I = ident(n)
    sym_idem = nondiag_sym_idem = orth = nonmono_orth = 0
    for A in all_mats(n):
        sym = (A == transpose(A, n))
        if sym and matmul(A, A, n) == A:
            sym_idem += 1
            if any(A[i][j] for i in range(n) for j in range(n) if i != j):
                nondiag_sym_idem += 1
        if matmul(A, transpose(A, n), n) == I:
            orth += 1
            if not is_monomial(A, n):
                nonmono_orth += 1
    print(f"M_{n}(F_2): symmetric idempotents {sym_idem}, non-diagonal {nondiag_sym_idem}; "
          f"orthogonal {orth}, non-monomial {nonmono_orth}")

J3 = tuple(tuple(1 for _ in range(3)) for _ in range(3))
assert matmul(J3, J3, 3) == J3 and J3 == transpose(J3, 3)
W4 = tuple(tuple(int(i != j) for j in range(4)) for i in range(4))  # J_4 - I over F_2
assert W4 == transpose(W4, 4) and matmul(W4, W4, 4) == ident(4) and not is_monomial(W4, 4)
print("J_3 is a symmetric non-diagonal idempotent; J_4 - I is a symmetric non-monomial involution over F_2")

# ---------- Part 2 ----------
def floor_m_alpha(m):
    # alpha = (3 - sqrt 5)/2; floor(m*alpha) exactly
    # m*alpha = (3m - sqrt(5 m^2))/2 for m >= 0; handle sign separately
    if m == 0:
        return 0
    if m > 0:
        s = isqrt(5 * m * m)  # floor(m sqrt 5); m sqrt 5 is irrational
        # m*alpha lies strictly between (3m - s - 1)/2 and (3m - s)/2
        return (3 * m - s - 1) // 2
    return -floor_m_alpha(-m) - 1  # m alpha irrational for m != 0

def x_letter(n):
    # mechanical Sturmian word s_n = floor((n+2) alpha) - floor((n+1) alpha)
    return floor_m_alpha(n + 2) - floor_m_alpha(n + 1)

N = 4000
x = {n: x_letter(n) for n in range(-N - 60, N + 60)}
assert set(x.values()) <= {0, 1}

def word_at(n, L):
    return tuple(x[n + k] for k in range(L))

# choose a word of length L whose occurrences in the window are >= 4 apart
chosen = None
for L in range(1, 30):
    occ = {}
    for n in range(-N, N):
        occ.setdefault(word_at(n, L), []).append(n)
    for wd, ps in occ.items():
        gaps = [b - a for a, b in zip(ps, ps[1:])]
        if len(ps) > 50 and min(gaps) >= 4:
            chosen = (L, wd, min(gaps), max(gaps))
            break
    if chosen:
        break
L, wd, gmin, gmax = chosen
print(f"cylinder U = [{''.join(map(str, wd))}] at coordinates 0..{L-1}; return times in window {gmin}..{gmax}")

def in_U(m):
    return word_at(m, L) == wd

def e(i, j, vec):
    out = {}
    for n, c in vec.items():
        if c and in_U(n - j):
            out[n - j + i] = out.get(n - j + i, 0) ^ 1
    return {k: v for k, v in out.items() if v}

def add(a, b):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) ^ v
    return {k: v for k, v in out.items() if v}

def in_W(m):
    return any(in_U(m - i) for i in range(4))

def w_op(vec):
    out = {}
    for i in range(4):
        for j in range(4):
            if i != j:
                out = add(out, e(i, j, vec))
    rest = {n: c for n, c in vec.items() if c and not in_W(n)}
    return add(out, rest)

def oneU(vec):
    return {n: c for n, c in vec.items() if c and in_U(n)}

bad = 0
offdiag_witness = None
for n in range(-N + 20, N - 20):
    d = {n: 1}
    if w_op(w_op(d)) != d:
        bad += 1
    img = w_op(oneU(w_op(d)))
    if offdiag_witness is None and any(k != n for k in img):
        offdiag_witness = (n, sorted(img))
print(f"w^2 = 1 fails on {bad} basis vectors of the window")
print(f"w 1_U w is off-diagonal: delta_{offdiag_witness[0]} -> support {offdiag_witness[1]}")
assert bad == 0 and offdiag_witness is not None
print("OK")
