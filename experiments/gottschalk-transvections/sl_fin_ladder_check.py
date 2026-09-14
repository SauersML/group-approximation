#!/usr/bin/env python3
"""Exact F_3 check of the elementary-transvection ladder in the half-line group Gamma_V.

Positions p = 2n + sigma. N_A e_{2n+1} = e_{2n}, N_B e_{2n} = e_{2n+1}, N_C e_{2n} = e_{2n-1} (n >= 1),
N_D e_{2n+1} = e_{2n+2}, X = I + E_{31}. Operators are truncated to a window of size L; every identity
checked involves products of at most 8 factors of propagation <= 2 near small indices, so the
top-left R x R block is exact for R + 16 < L.
"""
L, R, P = 48, 24, 3


def zero():
    return [[0] * L for _ in range(L)]


def eye():
    m = zero()
    for i in range(L):
        m[i][i] = 1
    return m


def mul(a, b):
    c = zero()
    for i in range(L):
        ai = a[i]
        ci = c[i]
        for k in range(L):
            if ai[k]:
                bk = b[k]
                x = ai[k]
                for j in range(L):
                    if bk[j]:
                        ci[j] = (ci[j] + x * bk[j]) % P
    return c


def add(a, b, s=1):
    return [[(a[i][j] + s * b[i][j]) % P for j in range(L)] for i in range(L)]


def E(q, p, lam=1):
    m = zero()
    m[q][p] = lam % P
    return m


def unip(pairs):
    """I + sum of E_{q,p} for (q, p) in pairs, and its inverse I - N (N^2 = 0 is asserted)."""
    n = zero()
    for q, p in pairs:
        if q < L and p < L:
            n[q][p] = 1
    assert mul(n, n) == zero(), "N^2 != 0"
    return add(eye(), n), add(eye(), n, -1)


A, Ai = unip([(2 * k, 2 * k + 1) for k in range(L)])
B, Bi = unip([(2 * k + 1, 2 * k) for k in range(L)])
C, Ci = unip([(2 * k - 1, 2 * k) for k in range(1, L)])
D, Di = unip([(2 * k + 2, 2 * k + 1) for k in range(L)])
X, Xi = unip([(3, 1)])


def inv_unip(m):
    n = add(m, eye(), -1)
    assert mul(n, n) == zero()
    return add(eye(), n, -1)


def comm(g, gi, h, hi):
    return mul(mul(mul(g, h), gi), hi)


def conj(g, gi, h):
    return mul(mul(g, h), gi)


def block(m):
    return [row[:R] for row in m[:R]]


def T(q, p, lam=1):
    return add(eye(), E(q, p, lam))


fails = 0


def check(name, got, want):
    global fails
    ok = block(got) == block(want)
    print(("OK   " if ok else "FAIL ") + name)
    if not ok:
        fails += 1


# Step 1: commutators of X with the four generators.
check("[X,A] = I - E21", comm(X, Xi, A, Ai), T(2, 1, -1))
check("[X,B] = I + E30", comm(X, Xi, B, Bi), T(3, 0))
check("[X,C] = I + E32", comm(X, Xi, C, Ci), T(3, 2))
check("[X,D] = I - E41", comm(X, Xi, D, Di), T(4, 1, -1))


def vphi(v, phi):
    m = eye()
    for i, a in v.items():
        for j, b in phi.items():
            m[i][j] = (m[i][j] + a * b) % P
    return m


# Step 2: conjugations and commutators in the window {0,...,4}.
check("C E21 C^-1 = I + (e2+e1)(e1*-e2*)", conj(C, Ci, T(2, 1)), vphi({2: 1, 1: 1}, {1: 1, 2: -1}))
check("A E32 A^-1 = I + (e3+e2)(e2*-e3*)", conj(A, Ai, T(3, 2)), vphi({3: 1, 2: 1}, {2: 1, 3: -1}))
check("[E23,E30] = E20", comm(T(2, 3), T(2, 3, -1), T(3, 0), T(3, 0, -1)), T(2, 0))
check("C E20 C^-1 = (I+E20)(I+E10)", conj(C, Ci, T(2, 0)), mul(T(2, 0), T(1, 0)))
check("A E10 A^-1 = I + (e1+e0)(e0*-e1*)", conj(A, Ai, T(1, 0)), vphi({1: 1, 0: 1}, {0: 1, 1: -1}))
check("C E03 C^-1 = (I+E03)(I-E04)", conj(C, Ci, T(0, 3)), mul(T(0, 3), T(0, 4, -1)))

# SL_2(F_3) generation: two transvections with distinct centres generate SL_2(F_3) and contain the
# opposite elementary transvection.
def m2mul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2)) % P for j in range(2)) for i in range(2))


def closure(gens):
    seen = {((1, 0), (0, 1))}
    frontier = list(seen)
    while frontier:
        nxt = []
        for g in frontier:
            for h in gens:
                x = m2mul(g, h)
                if x not in seen:
                    seen.add(x)
                    nxt.append(x)
        frontier = nxt
    return seen


# on (e_a, e_b) with E_ba the given elementary transvection (centre e_b) and v = e_a + e_b,
# phi = e_a* - e_b* in the order (a, b):
low = ((1, 0), (1, 1))            # I + E_{ba}: e_a -> e_a + e_b
tv = ((1 + 1, -1 % P), (1, (1 - 1) % P))  # I + v phi^T, v = (1,1), phi = (1,-1)
tv = ((2 % P, 2 % P), (1, 0))
grp = closure([low, tv])
up = ((1, 1), (0, 1))             # I + E_{ab}
print(("OK   " if len(grp) == 24 and up in grp else "FAIL ") + f"SL_2(F_3) generated: order {len(grp)}, contains opposite transvection {up in grp}")
if not (len(grp) == 24 and up in grp):
    fails += 1

# Step 3: induction conjugations for K = 4..9.
for K in range(4, 10):
    g, gi = (A, Ai) if K % 2 == 0 else (C, Ci)
    check(f"K={K}: conj E0K = (I+E0K)(I-E0,K+1)", conj(g, gi, T(0, K)), mul(T(0, K), T(0, K + 1, -1)))
    g, gi = (B, Bi) if K % 2 == 0 else (D, Di)
    check(f"K={K}: conj EK0 = (I+EK0)(I+EK+1,0)", conj(g, gi, T(K, 0)), mul(T(K, 0), T(K + 1, 0)))

# F3 sample: [E_ab, E_bc] = E_ac.
for a, b, c in [(0, 1, 2), (4, 0, 3), (1, 3, 0), (5, 2, 7)]:
    check(f"[E{a}{b},E{b}{c}] = E{a}{c}", comm(T(a, b), T(a, b, -1), T(b, c), T(b, c, -1)), T(a, c))

print("TOTAL_FAILS", fails)
