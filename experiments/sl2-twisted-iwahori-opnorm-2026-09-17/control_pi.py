"""Exact control theta = pi: the 2-dim rep of SL_2(F_3) = 2T < SU(2), pulled back to SL_2(Z[1/2]) -> SL_2(F_3).
It is an exact rep of G~ with z -> 1 and x^2 -> -1 (c = -1, theta = pi).  We build it, check the four relators
(and x^4 = 1), then form s = x/alpha, r = y/beta, S = X/alpha, R = Y/beta and print delta for gamma = beta/alpha
and for the normalised gamma = e^{-i pi/6} after the mu_6 relabelling (s -> -s and/or r -> w^-1 r, R -> w^-1 R).
Run: python3 control_pi.py
"""
import itertools, math
import numpy as np

P = 3
def mm(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(2)) % P for j in range(2)) for i in range(2))
I2 = ((1, 0), (0, 1))
A = ((0, 2), (1, 0))          # S mod 3
B = ((0, 2), (1, 1))          # ST mod 3
Xm = ((0, 1), (2, 0))         # [[0,-2],[1/2,0]] mod 3  (1/2 = 2)
Ym = ((0, 1), (2, 1))         # [[0,-2],[1/2,1]] mod 3

# binary tetrahedral group as 2x2 unitaries
q1 = np.eye(2, dtype=complex); qi = np.array([[1j, 0], [0, -1j]]); qj = np.array([[0, 1], [-1, 0]], dtype=complex)
qk = qi @ qj
T2 = []
for u in (q1, qi, qj, qk):
    T2 += [u, -u]
for e in itertools.product((1, -1), repeat=4):
    T2.append((e[0] * q1 + e[1] * qi + e[2] * qj + e[3] * qk) / 2)

def extend(a, b):
    """BFS: define phi on SL_2(F_3) from phi(A) = a, phi(B) = b; return dict or None if inconsistent."""
    phi = {I2: np.eye(2, dtype=complex)}
    frontier = [I2]
    while frontier:
        new = []
        for g in frontier:
            for h, m in ((A, a), (B, b)):
                gh = mm(g, h)
                v = phi[g] @ m
                if gh in phi:
                    if not np.allclose(phi[gh], v):
                        return None
                else:
                    phi[gh] = v; new.append(gh)
        frontier = new
    return phi if len(phi) == 24 else None

phi = None
for a in T2:
    for b in T2:
        if not np.allclose(a @ a, -np.eye(2)):      # faithful: x^2 = -I -> -1
            continue
        phi = extend(a, b)
        if phi is not None:
            break
    if phi is not None:
        break
assert phi is not None
x, y, X, Y = phi[A], phi[B], phi[Xm], phi[Ym]
inv = lambda m: m.conj().T
chk = {
    "x^4": np.linalg.norm(np.linalg.matrix_power(x, 4) - np.eye(2)),
    "x^2 = -1": np.linalg.norm(x @ x + np.eye(2)),
    "x^2 = y^3": np.linalg.norm(x @ x - y @ y @ y),
    "X^2 = Y^3": np.linalg.norm(X @ X - Y @ Y @ Y),
    "x^2 = X^2": np.linalg.norm(x @ x - X @ X),
    "T": np.linalg.norm(inv(x) @ y @ inv(x) @ y - inv(X) @ Y),
    "U": np.linalg.norm(inv(x) @ inv(y) @ x @ x - X @ inv(Y) @ X @ inv(Y)),
}
alpha = 1j                                   # alpha^2 = c = -1
beta = complex(math.cos(math.pi / 3), math.sin(math.pi / 3))   # beta^3 = -1
s, r, S, R = x / alpha, y / beta, X / alpha, Y / beta

def delta(s, r, S, R, g):
    DT = S @ R - g * (s @ r) @ (s @ r)
    DU = s @ inv(r) - (1 / g) * (S @ inv(R)) @ (S @ inv(R))
    return max(np.linalg.norm(DT, 2), np.linalg.norm(DU, 2))

w = complex(math.cos(2 * math.pi / 3), math.sin(2 * math.pi / 3))
g0 = beta / alpha
target = complex(math.cos(-math.pi / 6), math.sin(-math.pi / 6))
best = None
for es in (1, -1):
    for k in range(3):
        g = g0 * es * w ** k
        if abs(g - target) < 1e-9:
            best = delta(es * s, w ** (-k) * r, es * S, w ** (-k) * R, g)
if __name__ == "__main__":
    for kk, v in chk.items():
        print(f"{kk:10s} {v:.2e}")
    print("gamma = beta/alpha =", np.round(g0, 6), " delta =", f"{delta(s, r, S, R, g0):.2e}")
    print("normalised gamma = e^{-i pi/6}: delta =", f"{best:.2e}")
