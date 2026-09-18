"""Sanity check for the row-fault pair in Labbe's metallic mean Wang shift Omega_n.

Labbe, "Metallic mean Wang tiles II" (arXiv:2403.03197v3), Theorem C: for (x, y) in [0,1)^2,
c_(x,y)(i, j) = Tile_n(x + i/beta, y + j/beta) is a valid tiling by T_n, where
Tile_n(x, y) = (right, top, left, bottom)
             = (Lam({x},{y}), Lam({y},{x}), Lam({x - 1/beta},{y}), Lam({y - 1/beta},{x})),
Lam(x, y) = (floor(y - 1/beta + 1), floor(x/beta + y - 1/beta + 1), floor(beta x + y - 1/beta + 1)).

We compare c_(x,0) with c_(x,1-t) for small t on a window and print the rows where they differ.
Expected: differences only in rows j = 0 and j = 1, and every tile of row 1 differs.
Also checks the Wang matching conditions on the window. Numerical (decimal, 60 digits).
"""
from decimal import Decimal, getcontext, ROUND_FLOOR

getcontext().prec = 60
mpf = Decimal


def sqrt(z):
    return Decimal(z).sqrt()


def floor(z):
    return z.to_integral_value(rounding=ROUND_FLOOR)


def frac(z):
    return z - floor(z)


def run(n, x, t, W=40):
    beta = (Decimal(n) + sqrt(n * n + 4)) / 2
    ib = 1 / beta

    def lam(u, v):
        return (int(floor(v - ib + 1)), int(floor(ib * u + v - ib + 1)), int(floor(beta * u + v - ib + 1)))

    def tile(a, b):
        return (lam(frac(a), frac(b)), lam(frac(b), frac(a)), lam(frac(a - ib), frac(b)), lam(frac(b - ib), frac(a)))

    def conf(y):
        return {(i, j): tile(x + i * ib, y + j * ib) for i in range(-W, W + 1) for j in range(-W, W + 1)}

    cp, cm = conf(mpf(0)), conf(1 - t)
    for c in (cp, cm):
        for i in range(-W, W):
            for j in range(-W, W):
                assert c[(i, j)][0] == c[(i + 1, j)][2], "right/left mismatch"
                assert c[(i, j)][1] == c[(i, j + 1)][3], "top/bottom mismatch"
    rows = sorted({j for (i, j) in cp if cp[(i, j)] != cm[(i, j)]})
    row1_full = all(cp[(i, 1)] != cm[(i, 1)] for i in range(-W, W + 1))
    return rows, row1_full


if __name__ == "__main__":
    x = 1 / sqrt(3)  # not in Q(sqrt 5) or Q(sqrt 2)
    for n in (1, 2, 3):
        rows, full = run(n, x, mpf(10) ** -30)
        print(f"n={n}: differing rows {rows}; every tile of row 1 differs: {full}")
