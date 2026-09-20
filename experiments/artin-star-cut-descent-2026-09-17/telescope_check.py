"""Randomized check of the level-telescoping identity behind the star-cut descent lemma.

Group: G = Z^2 x|_M Z with M = [[2,1],[1,1]], chi(x, n) = n, H = Z^2 (level 0).
Elements of Z[G]^r are dicts {(coord, (x0, x1, n)): coeff}.  For u in G with chi(u) = c > 0,
and arbitrary finitely supported A, B in Z[G]^r, put X = A (u - 1) + B (right multiplication).
Identity checked (Step 2 of the route):

    X_0 = -A_0 + B_0 + sum_{m >= 1} (B_{-mc} - X_{-mc}) u^m ,

where Y_n is the level-n part.  When X = f is level-0 homogeneous (the situation of the
lemma), the X-terms vanish and f = -A_0 + B_0 + sum_m B_{-mc} u^m.

Also checked: the conjugation form t^{-mc} y u^m = h_m (u^{-m} y u^m) with h_m in H,
used to place B_{-mc} u^m in the left Z[H]-module u^{-m} M^0 u^m.
"""
import random

M = ((2, 1), (1, 1))
MI = ((1, -1), (-1, 2))


def mpow(n):
    P = ((1, 0), (0, 1))
    B = M if n >= 0 else MI
    for _ in range(abs(n)):
        P = ((P[0][0] * B[0][0] + P[0][1] * B[1][0], P[0][0] * B[0][1] + P[0][1] * B[1][1]),
             (P[1][0] * B[0][0] + P[1][1] * B[1][0], P[1][0] * B[0][1] + P[1][1] * B[1][1]))
    return P


def gmul(g, h):
    P = mpow(g[2])
    return (g[0] + P[0][0] * h[0] + P[0][1] * h[1], g[1] + P[1][0] * h[0] + P[1][1] * h[1], g[2] + h[2])


def ginv(g):
    P = mpow(-g[2])
    x = (-(P[0][0] * g[0] + P[0][1] * g[1]), -(P[1][0] * g[0] + P[1][1] * g[1]))
    return (x[0], x[1], -g[2])


def add(X, Y, s=1):
    Z = dict(X)
    for k, v in Y.items():
        Z[k] = Z.get(k, 0) + s * v
        if Z[k] == 0:
            del Z[k]
    return Z


def rmul(X, g):
    return {(i, gmul(h, g)): c for (i, h), c in X.items()}


def level(X, n):
    return {k: c for k, c in X.items() if k[1][2] == n}


def rand_vec(r, lo, hi, terms):
    X = {}
    for _ in range(terms):
        k = (random.randrange(r), (random.randint(-2, 2), random.randint(-2, 2), random.randint(lo, hi)))
        X = add(X, {k: random.randint(-3, 3) or 1})
    return X


def trial(c):
    r = 3
    u = (random.randint(-2, 2), random.randint(-2, 2), c)
    A = rand_vec(r, -4 * c, 3, 12)
    B = rand_vec(r, -4 * c - 2, 3, 12)
    X = add(add(rmul(A, u), A, -1), B)
    rhs = add(level(B, 0), level(A, 0), -1)
    um = (0, 0, 0)
    for m in range(1, 8):
        um = gmul(um, u)
        rhs = add(rhs, rmul(add(level(B, -m * c), level(X, -m * c), -1), um))
    ok1 = (rhs == level(X, 0))
    # conjugation form: t^{-mc} y u^m = h_m (u^{-m} y u^m), h_m = t^{-mc} u^m in H
    ok2 = True
    for m in range(1, 4):
        um = (0, 0, 0)
        for _ in range(m):
            um = gmul(um, u)
        y = (random.randint(-2, 2), random.randint(-2, 2), 0)
        t = (0, 0, -m * c)
        lhs = gmul(gmul(t, y), um)
        hm = gmul(t, um)
        conj = gmul(gmul(ginv(um), y), um)
        ok2 &= (hm[2] == 0 and conj[2] == 0 and gmul(hm, conj) == lhs)
    return ok1 and ok2


if __name__ == "__main__":
    random.seed(20260917)
    n_ok = 0
    N = 400
    for i in range(N):
        n_ok += trial(1 + (i % 3))
    print(f"telescoping identity + conjugation form: {n_ok}/{N} random trials passed (c in 1,2,3)")
    assert n_ok == N
    print("OK")
