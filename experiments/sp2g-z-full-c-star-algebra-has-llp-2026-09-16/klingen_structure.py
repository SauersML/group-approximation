"""Sanity check of the Klingen subgroup E_K = H_3(Z) x| SL_2(Z) inside Sp_4(Z).

Basis (e1, e2, f1, f2), omega(x, y) = x^T J y, J = [[0, I], [-I, 0]].
X_v(x) = omega(v, x) e1 + omega(e1, x) v  for v in <e2, f2>;
Z(x)   = omega(e1, x) e1;   N(a, b, c) = (I + X_v)(I + c Z), v = a e2 + b f2.
L(g) = SL_2 acting on (e2, f2), identity on (e1, f1).
Checks: integrality, symplecticity, commutator [N(1,0,0), N(0,1,0)] = N(0,0,+-1),
L(g) fixes the centre, L(g) N(v) L(g)^-1 = N(g v) * centre, and the reduction of the
centre generator modulo k has order exactly k.
"""
import itertools
import numpy as np

J = np.block([[np.zeros((2, 2), int), np.eye(2, dtype=int)], [-np.eye(2, dtype=int), np.zeros((2, 2), int)]])
E = np.eye(4, dtype=int)
e1, e2, f1, f2 = E[:, 0], E[:, 1], E[:, 2], E[:, 3]
om = lambda x, y: int(x @ J @ y)

def X(v):
    return np.array([om(v, E[:, j]) * e1 + om(e1, E[:, j]) * v for j in range(4)]).T

Zm = np.array([om(e1, E[:, j]) * e1 for j in range(4)]).T

def N(a, b, c):
    return (E + X(a * e2 + b * f2)) @ (E + c * Zm)

def L(p, q, r, s):
    M = E.copy()
    M[:, 1] = p * e2 + r * f2
    M[:, 3] = q * e2 + s * f2
    return M

def symp(M):
    return np.array_equal(M.T @ J @ M, J)

inv = lambda M: np.rint(np.linalg.inv(M)).astype(int)
rng = range(-2, 3)
ok = all(symp(N(a, b, c)) for a, b, c in itertools.product(rng, rng, rng))
print("N(a,b,c) symplectic:", ok)
gens = [(1, 1, 0, 1), (1, 0, 1, 1), (0, -1, 1, 0)]
print("L(g) symplectic:", all(symp(L(*g)) for g in gens))
A, B = N(1, 0, 0), N(0, 1, 0)
comm = A @ B @ inv(A) @ inv(B)
sign = [c for c in range(-4, 5) if np.array_equal(comm, N(0, 0, c))]
print("[N(1,0,0),N(0,1,0)] = N(0,0,c) with c =", sign, "(so U(Z) has commutator 2*omega: it is H_omega, not H_3(Z))")
law = all(np.array_equal(N(a,b,c) @ N(a2,b2,c2), N(a+a2, b+b2, c+c2+a*b2-b*a2)) for a,b,c,a2,b2,c2 in itertools.product(range(-1,2), repeat=6))
print("group law N(v,c)N(w,d) = N(v+w, c+d+omega(v,w)), omega(v,w)=a b2 - b a2:", law)
print("centre N(0,0,1) central in N:", all(np.array_equal(N(0, 0, 1) @ N(a, b, 0), N(a, b, 0) @ N(0, 0, 1)) for a, b in itertools.product(rng, rng)))
print("L fixes centre:", all(np.array_equal(L(*g) @ N(0, 0, 1) @ inv(L(*g)), N(0, 0, 1)) for g in gens))
# conjugation action on N/Z: L(g) N(a,b,0) L(g)^-1 = N(a',b',c'), (a',b') = g(a,b)
good = True
for g in gens:
    p, q, r, s = g
    for a, b in itertools.product(rng, rng):
        C = L(*g) @ N(a, b, 0) @ inv(L(*g))
        a2, b2 = p * a + q * b, r * a + s * b
        cs = [c for c in range(-20, 21) if np.array_equal(C, N(a2, b2, c))]
        good &= cs == [0]
print("L(g) N(v,0) L(g)^-1 = N(g v, 0) exactly:", good)
for k in (2, 3, 5, 12):
    Zk = N(0, 0, 1) % k
    P, order = E.copy(), 0
    while True:
        P = (P @ Zk) % k; order += 1
        if np.array_equal(P, E % k):
            break
    print("order of centre generator mod", k, "=", order)
