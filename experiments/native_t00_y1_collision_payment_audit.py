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
    s1 = frozenset({("1", "")})
    t00 = frozenset({("", "00")})
    s0_t00 = frozenset({("0", "00")})
    s00_s1 = frozenset({("001", "")})
    s000 = frozenset({("000", "")})
    discrepancy = t00 ^ s0_t00

    assert discrepancy
    sandwich = polynomial_product(
        polynomial_product(t1, discrepancy), s00_s1
    )
    assert sandwich == frozenset({ONE})

    a1 = frozenset({("1", "0")})
    a2 = frozenset({("1", "00")})
    a3 = frozenset({("1", "000")})
    b2 = frozenset({("00", "1")})
    b1 = frozenset({("0", "1")})
    b0 = t1

    assert polynomial_product(a1, discrepancy) == a2 ^ a3
    assert polynomial_product(discrepancy, b2) == b0 ^ b1
    assert polynomial_product(
        polynomial_product(t1, a3), s000
    ) == frozenset({ONE})
    assert polynomial_product(b0, s1) == frozenset({ONE})
    print(
        "t1 (t00 + s0 t00) (s00 s1) = 1; "
        "a1*d=a2+a3; d*b2=b0+b1; "
        "ejected coefficients have one-sandwich inverses"
    )


if __name__ == "__main__":
    main()
