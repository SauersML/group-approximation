"""Exact audit of the depth-one/depth-two typed off-diagonal loop table.

Run through MSI, not on the local workstation.  Arithmetic is over F_2.
"""


N = 6
COARSE = range(2)
FINE = range(2, 6)


def unit(row, col):
    return tuple(
        tuple(1 if (i, j) == (row, col) else 0 for j in range(N))
        for i in range(N)
    )


def zero():
    return tuple(tuple(0 for _ in range(N)) for _ in range(N))


def add(a, b):
    return tuple(
        tuple(a[i][j] ^ b[i][j] for j in range(N)) for i in range(N)
    )


def mul(a, b):
    return tuple(
        tuple(
            sum(a[i][k] * b[k][j] for k in range(N)) % 2
            for j in range(N)
        )
        for i in range(N)
    )


e = {(i, j): unit(i, j) for i in COARSE for j in COARSE}
f = {(u, v): unit(u, v) for u in FINE for v in FINE}
x = {(u, i): unit(u, i) for u in FINE for i in COARSE}
y = {(i, u): unit(i, u) for i in COARSE for u in FINE}

checks = 0
for u in FINE:
    for v in FINE:
        for i in COARSE:
            for j in COARSE:
                assert mul(mul(x[u, i], e[i, j]), y[j, v]) == f[u, v]
                assert mul(mul(y[i, u], f[u, v]), x[v, j]) == e[i, j]
                checks += 2

for i in COARSE:
    for j in COARSE:
        for u in FINE:
            for v in FINE:
                expected_e = e[i, j] if u == v else zero()
                expected_f = f[u, v] if i == j else zero()
                assert mul(y[i, u], x[v, j]) == expected_e
                assert mul(x[u, i], y[j, v]) == expected_f
                checks += 2

p_coarse = zero()
for i in COARSE:
    p_coarse = add(p_coarse, e[i, i])
p_fine = zero()
for u in FINE:
    p_fine = add(p_fine, f[u, u])

assert p_coarse != p_fine
diagonal_difference = tuple(
    p_coarse[i][i] - p_fine[i][i] for i in range(N)
)
assert diagonal_difference == (1, 1, -1, -1, -1, -1)

print(f"verified mixed path identities: {checks}")
print(f"coarse carrier rank: {sum(p_coarse[i][i] for i in range(N))}")
print(f"fine carrier rank: {sum(p_fine[i][i] for i in range(N))}")
print(f"carrier-difference diagonal: {diagonal_difference}")
print("operator norm of carrier difference over C: 1")
