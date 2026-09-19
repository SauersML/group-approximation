"""Sp_4(Z) = Mod(S_2)/<<(t1 t2)^6>> (Birman-Hilden presentation plus one separating twist).

Generators t1..t5 act on H_1(S_2) = Z^4 (basis a1,a2,b1,b2, omega(a_i,b_i)=1) as symplectic
transvections T_v(x) = x + omega(v,x) v for the chain classes v.  Relator values k_r are the
winding numbers of det(unitary part) along the lifted relator path in Sp_4(R); they define the
Maslov (Deligne) cocycle kappa: r~ = z^(k_r) in the universal-cover lattice.
"""
import numpy as np

J = np.zeros((4, 4))
J[0, 2] = J[1, 3] = 1
J[2, 0] = J[3, 1] = -1


def omega(x, y):
    return x @ J @ y


# chain classes in basis (a1, a2, b1, b2)
V = [np.array(v, dtype=float) for v in (
    (1, 0, 0, 0),    # c1 = a1
    (0, 0, 1, 0),    # c2 = b1
    (-1, 1, 0, 0),   # c3 = a2 - a1
    (0, 0, 0, 1),    # c4 = b2
    (0, 1, 0, 0),    # c5 = a2
)]


def nilp(v):
    # T_v(x) = x + omega(v, x) v  => N = v (v^T J)
    return np.outer(v, v @ J)


NIL = [nilp(v) for v in V]
GEN = [np.eye(4) + N for N in NIL]
GEN_INT = [np.rint(g).astype(np.int64) for g in GEN]

# words: list of (generator index 0..4, exponent +-1)


def w(*letters):
    out = []
    for L in letters:
        if isinstance(L, list):
            out.extend(L)
        else:
            i = abs(L) - 1
            out.append((i, 1 if L > 0 else -1))
    return out


def inv(word):
    return [(i, -e) for (i, e) in reversed(word)]


def comm(u, v):
    return u + v + inv(u) + inv(v)


IOTA = w(1, 2, 3, 4, 5, 5, 4, 3, 2, 1)
RELATORS = {}
for i in range(1, 6):
    for j in range(i + 2, 6):
        RELATORS[f"c{i}{j}"] = comm(w(i), w(j))
for i in range(1, 5):
    RELATORS[f"b{i}"] = w(i, i + 1, i) + inv(w(i + 1, i, i + 1))
RELATORS["chain6"] = w(1, 2, 3, 4, 5) * 6
RELATORS["iota2"] = IOTA * 2
RELATORS["iotac"] = comm(IOTA, w(1))
RELATORS["sep"] = w(1, 2) * 6


def mat(word):
    M = np.eye(4, dtype=np.int64)
    for (i, e) in word:
        g = GEN_INT[i] if e > 0 else np.rint(np.linalg.inv(GEN[i])).astype(np.int64)
        M = M @ g
    return M


def detu(M):
    # unitary part of M in Sp_4(R) under U(2) = Sp_4(R) cap O(4), complex coords a + i b
    U, _, Vt = np.linalg.svd(M)
    O = U @ Vt
    A = O[:2, :2]
    B = O[2:, :2]
    return np.linalg.det(A + 1j * B)


def winding(word, steps=400):
    M = np.eye(4)
    tot = 0.0
    prev = np.angle(detu(M))
    for (i, e) in word:
        for k in range(1, steps + 1):
            P = M @ (np.eye(4) + e * (k / steps) * NIL[i])
            cur = np.angle(detu(P))
            d = (cur - prev + np.pi) % (2 * np.pi) - np.pi
            assert abs(d) < 1.0, "step too coarse"
            tot += d
            prev = cur
        M = M @ (np.eye(4) + e * NIL[i])
    return tot / (2 * np.pi)


def kvalues():
    out = {}
    for name, r in RELATORS.items():
        M = mat(r)
        assert np.array_equal(M, np.eye(4, dtype=np.int64)), name
        k = winding(r)
        assert abs(k - round(k)) < 1e-6, (name, k)
        out[name] = int(round(k))
    return out


if __name__ == "__main__":
    for g in GEN_INT:
        assert np.allclose(g.T @ J @ g, J)
    K = kvalues()
    for name, r in RELATORS.items():
        print(name, len(r), K[name])
