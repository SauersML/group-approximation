"""Audit the first native Hecke attachment to the paid t00 collision.

Run on MSI only.  The packet extends the marked GL10(F2) occurrence chart.
"""

from experiments.marked_t00_separation_gl10_audit import (
    ONE,
    commutator,
    multiply,
    power,
    swap_product,
    transvection,
)


def main():
    # Vertex order: (7_0,9,8_0,7_1,10,8_1,6,u,b,c).
    seven_0, _nine, eight_0, seven_1, _ten, eight_1, six, _u, b, _c = range(10)

    y = transvection(seven_0, eight_0)
    t = transvection(b, eight_0)
    discrepancy = multiply(t, y)

    # Literal first center-chain Hecke triangle.
    b2 = transvection(eight_0, six)
    a1 = transvection(six, seven_0)
    x1 = transvection(eight_0, seven_0)
    j1 = swap_product((seven_0, eight_0))
    assert commutator(b2, a1) == x1
    assert power(multiply(multiply(j1, b2), a1), 7) == ONE

    # d*b2=b0+b1: the paid collision ejects two literal root paths.
    h1 = transvection(seven_0, six)
    h0 = transvection(b, six)
    assert commutator(discrepancy, b2) == multiply(h0, h1)
    assert h0 != ONE

    # The paid discrepancy and the old marked child both survive.
    marked_child = transvection(seven_1, eight_1)
    assert discrepancy != ONE
    assert marked_child != ONE
    print(
        "first native B2 attachment ejects nontrivial b0 in the exact marked GL10(F2) fence"
    )


if __name__ == "__main__":
    main()
