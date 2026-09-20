"""Exact checks for thompson-t-square-central-quotients-have-no-small-corners.

1. In SL(2,Z), a = S = [[0,-1],[1,0]] and b = -ST (T = [[1,1],[0,1]]) satisfy a^4 = b^3 = 1,
   a^2 = -1 is central, so [a^2, b] = 1 and r_1 = [X, J X J] = 1 identically (J = a^2).
   S and ST generate SL(2,Z), and -1 = S^2, so a, b generate SL(2,Z).
2. Word lengths used in the proof: c = a^2 b a^-2 b^-1 has length 6; r_1, r_2, r_P have
   lengths 20, 34, 10 (letters a^{+-1}, b^{+-1}, with X = bab, J = aa, W = aa bb aa, W^-1 = aa b aa).
3. Calibration: the permutation representation of SL(2,Z/q) on (Z/q)^2 minus 0 is an exact pair with
   gamma = ||[A^2, B] - 1|| = 0; its defect D = max ||r - 1|| is printed for small q.
   (Whole finite-image representations have D >= 1/2 by the w19 record; the node concerns corners.)
"""
import json
import numpy as np

S = np.array([[0, -1], [1, 0]], dtype=object)
T = np.array([[1, 1], [0, 1]], dtype=object)
I2 = np.array([[1, 0], [0, 1]], dtype=object)
a = S
b = -(S.dot(T))


def mp(*ms):
    r = I2
    for m in ms:
        r = r.dot(m)
    return r


def pw(m, k):
    return mp(*([m] * k)) if k > 0 else I2


ainv, binv = pw(a, 3), pw(b, 2)
out = {}
out["a^4==1"] = bool((pw(a, 4) == I2).all())
out["b^3==1"] = bool((pw(b, 3) == I2).all())
out["a^2==-1 (central)"] = bool((pw(a, 2) == -I2).all())
J = pw(a, 2)
X = mp(b, a, b)
Xi = mp(binv, ainv, binv)
out["r1==1 in SL(2,Z)"] = bool((mp(X, J, X, J, Xi, J, Xi, J) == I2).all())

w_c = ["a", "a", "b", "A", "A", "B"]
X_w, Xi_w, J_w = ["b", "a", "b"], ["B", "A", "B"], ["a", "a"]
W_w, Wi_w = ["a", "a", "b", "b", "a", "a"], ["a", "a", "b", "a", "a"]
r1_w = X_w + J_w + X_w + J_w + Xi_w + J_w + Xi_w + J_w
r2_w = X_w + W_w + X_w + Wi_w + Xi_w + W_w + Xi_w + Wi_w
rP_w = ["b", "a"] * 5
out["len c, r1, r2, rP"] = [len(w_c), len(r1_w), len(r2_w), len(rP_w)]


def perm_rep(q):
    pts = [(x, y) for x in range(q) for y in range(q) if (x, y) != (0, 0)]
    idx = {p: i for i, p in enumerate(pts)}
    n = len(pts)

    def P(m):
        M = np.zeros((n, n))
        for p, i in idx.items():
            v = ((int(m[0][0]) * p[0] + int(m[0][1]) * p[1]) % q,
                 (int(m[1][0]) * p[0] + int(m[1][1]) * p[1]) % q)
            M[idx[v], i] = 1
        return M
    return P(a), P(b)


def ev(word, A, B):
    L = {"a": A, "b": B, "A": A.T, "B": B.T}
    M = np.eye(A.shape[0])
    for ch in word:
        M = M @ L[ch]
    return M


cal = []
for q in range(3, 12):
    A, B = perm_rep(q)
    one = np.eye(A.shape[0])
    g = np.linalg.norm(ev(w_c, A, B) - one, 2)
    D = max(np.linalg.norm(ev(w, A, B) - one, 2) for w in (r1_w, r2_w, rP_w))
    cal.append({"q": q, "dim": A.shape[0], "gamma": round(float(g), 12), "D": round(float(D), 6)})
out["perm_rep_calibration"] = cal
print(json.dumps(out, indent=1))
