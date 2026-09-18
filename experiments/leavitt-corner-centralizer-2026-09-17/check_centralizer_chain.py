"""Sanity check of the Steinberg identities used in
research/leavitt-mf-null-root-corner-is-equivalent-to-the-goal-proof.md.

We work in EL_n(A) with A = M_d(F_2) (a noncommutative coefficient ring with
random, non-commuting entries), represented as (n d) x (n d) matrices over F_2.
x_ij(a) = 1 + a e_ij.  Checked, for n = 20, J = {2,4,...,20}:
  (1) z = x_13(q) is an involution;
  (2) z commutes with x_kl(r) (k,l in J), with x_1m(a) and with x_m3(b) (m in J);
  (3) x_1m(q) = [x_1l(q), x_lm(1)] and z = [x_1m(q), x_m3(1)], with [g,h] = g h g^-1 h^-1.
These are images of the Steinberg relations, so they only sanity-check the
index bookkeeping; the proof uses the Steinberg relations themselves.
"""
import numpy as np

rng = np.random.default_rng(20260917)
n, d = 20, 3
N = n * d


def rnd():
    return rng.integers(0, 2, size=(d, d))


def x(i, j, a):
    g = np.eye(N, dtype=np.int64)
    g[(i - 1) * d:i * d, (j - 1) * d:j * d] = a % 2
    return g


def mul(*gs):
    out = np.eye(N, dtype=np.int64)
    for g in gs:
        out = (out @ g) % 2
    return out


def comm(i, j, a, k, l, b):
    # characteristic two: x_ij(a)^-1 = x_ij(-a) = x_ij(a)
    g, h = x(i, j, a), x(k, l, b)
    return mul(g, h, g, h)


I = np.eye(N, dtype=np.int64)
one = np.eye(d, dtype=np.int64)
J = [2] + list(range(4, n + 1))
q = rnd()
z = x(1, 3, q)
assert np.array_equal(mul(z, z), I), "z is not an involution"
checks = 1
for k in J:
    for l in J:
        if k == l:
            continue
        r = rnd()
        assert np.array_equal(mul(z, x(k, l, r)), mul(x(k, l, r), z))
        checks += 1
for m in J:
    a, b = rnd(), rnd()
    assert np.array_equal(mul(z, x(1, m, a)), mul(x(1, m, a), z))
    assert np.array_equal(mul(z, x(m, 3, b)), mul(x(m, 3, b), z))
    checks += 2
for m in J:
    for l in J:
        if l == m:
            continue
        assert np.array_equal(x(1, m, q), comm(1, l, q, l, m, one))
        checks += 1
    assert np.array_equal(z, comm(1, m, q, m, 3, one))
    checks += 1
# the chain fails if an index of {1,3} is used as the pivot (control)
assert not np.array_equal(mul(z, x(3, 1, one)), mul(x(3, 1, one), z))
print(f"all {checks} identities hold (n={n}, coefficient ring M_{d}(F_2)); control x_31 does not commute with z")
