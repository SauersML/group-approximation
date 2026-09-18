#!/usr/bin/env python3
"""Machine check of Lemma A in kt-compressor-stable-overgroups-polynomial-content-proof.

S is an F_q[x_1..x_d]-submodule of the Laurent ring R, stable under the monomial
semigroup SL_d(N) acting by x^v -> x^(Pv).  Lemma A: if S contains some f outside
A = F_q[x], then S contains every x_j^(-1).

The script runs the proof's algorithm on random Laurent polynomials f over F_q.
It uses only the moves the lemma allows:
  * subtract an element of A (the polynomial part),
  * multiply by a monomial with nonnegative exponents,
  * apply P = I + E_(ab) in SL_d(N).
It checks that the algorithm ends with a nonzero scalar multiple of x_j^(-1) for
every j.  A Laurent polynomial is a dict {exponent tuple: nonzero coefficient mod q}.
"""
import random

Q = 5  # prime, so the field is F_q = Z/q


def clean(f):
    return {v: c % Q for v, c in f.items() if c % Q}


def add(f, g, s=1):
    h = dict(f)
    for v, c in g.items():
        h[v] = h.get(v, 0) + s * c
    return clean(h)


def mono_mul(f, u):
    assert all(x >= 0 for x in u)
    return {tuple(a + b for a, b in zip(v, u)): c for v, c in f.items()}


def apply_elem(f, a, b):
    """P = I + E_ab acts on exponents by v -> v + v_b e_a."""
    assert a != b
    h = {}
    for v, c in f.items():
        w = list(v)
        w[a] += v[b]
        w = tuple(w)
        h[w] = h.get(w, 0) + c
    return clean(h)


def poly_part(f):
    return {v: c for v, c in f.items() if all(x >= 0 for x in v)}


def strip_poly(f):
    return add(f, poly_part(f), -1)


def is_scalar_inverse(f, i, d):
    target = tuple(-1 if k == i else 0 for k in range(d))
    return len(f) == 1 and target in f


def lemma_a(f, d):
    moves = 0
    f = strip_poly(f)
    assert f, "f must lie outside A"
    # Step 1: reach h / x_i with h a nonzero polynomial not involving x_i.
    i = next(k for k in range(d) if any(v[k] < 0 for v in f))
    m = min(v[i] for v in f)
    u = [max(0, -min(v[k] for v in f)) for k in range(d)]
    u[i] = -m - 1
    g = strip_poly(mono_mul(f, u))
    moves += 2
    assert g and all(v[i] == -1 and all(v[k] >= 0 for k in range(d) if k != i) for v in g)
    # Steps 2-4: reduce h to a constant, one variable j != i at a time.
    for j in range(d):
        if j == i:
            continue
        # R_j: while x_j divides h, apply I + E_(j i): x^w / x_i -> x^(w - e_j) / x_i.
        while all(v[j] >= 1 for v in g):
            g = apply_elem(g, j, i)
            moves += 1
        # X_j: apply I + E_(i j), then strip the polynomial part: keeps h(x_j = 0) / x_i.
        g = strip_poly(apply_elem(g, i, j))
        moves += 2
        assert g, "extraction must leave a nonzero remainder"
        assert all(v[j] == 0 and v[i] == -1 for v in g)
    assert is_scalar_inverse(g, i, d), g
    out = {i: g}
    # Step 5: x_j^(-1) from x_i^(-1): apply I + E_(j i), multiply by x_i.
    for j in range(d):
        if j == i:
            continue
        e = mono_mul(apply_elem(g, j, i), tuple(1 if k == i else 0 for k in range(d)))
        moves += 2
        assert is_scalar_inverse(e, j, d), e
        out[j] = e
    return out, moves


def random_laurent(d, terms, span):
    f = {}
    for _ in range(terms):
        v = tuple(random.randint(-span, span) for _ in range(d))
        f[v] = random.randint(1, Q - 1)
    return clean(f)


def main():
    random.seed(20260917)
    trials = 0
    for d in (2, 3, 4, 5):
        for _ in range(2000):
            f = random_laurent(d, random.randint(1, 8), random.randint(1, 4))
            if not strip_poly(f):
                continue
            out, _ = lemma_a(f, d)
            assert sorted(out) == list(range(d))
            trials += 1
    print(f"Lemma A algorithm succeeded on {trials} random Laurent polynomials, d in 2..5, q = {Q}")


if __name__ == "__main__":
    main()
