"""Audit the Leavitt sandwich for t_00 + s_0 t_00.

Run on MSI only.  Monomials (u,v) denote s_u t_v in the binary polycyclic
normal form, and coefficients are reduced modulo two.
"""


ONE = ("", "")


def monomial_product(left, right):
    u, v = left
    x, y = right
    if x.startswith(v):
        return u + x[len(v) :], y
    if v.startswith(x):
        return u, y + v[len(x) :]
    return None


def polynomial_product(left, right):
    out = set()
    for a in left:
        for b in right:
            value = monomial_product(a, b)
            if value is None:
                continue
            if value in out:
                out.remove(value)
            else:
                out.add(value)
    return frozenset(out)


def main():
    t1 = frozenset({("", "1")})
    t00 = frozenset({("", "00")})
    s0_t00 = frozenset({("0", "00")})
    s00_s1 = frozenset({("001", "")})
    discrepancy = t00 ^ s0_t00

    assert discrepancy
    sandwich = polynomial_product(
        polynomial_product(t1, discrepancy), s00_s1
    )
    assert sandwich == frozenset({ONE})
    print("t1 (t00 + s0 t00) (s00 s1) = 1; discrepancy is nonzero")


if __name__ == "__main__":
    main()
