"""Audit the dual-Heisenberg-blind spectator-dressed Gram fence.

Run through the MSI wrapper only.
"""


LABEL_DIM = 8
RESERVOIR_DIM = 12
DIMENSION = LABEL_DIM * RESERVOIR_DIM


def identity():
    return tuple(range(DIMENSION)), (1,) * DIMENSION


ONE = identity()


def multiply(left, right):
    lp, ls = left
    rp, rs = right
    return (
        tuple(lp[rp[j]] for j in range(DIMENSION)),
        tuple(rs[j] * ls[rp[j]] for j in range(DIMENSION)),
    )


def inverse(element):
    permutation, signs = element
    inverse_permutation = [0] * DIMENSION
    inverse_signs = [0] * DIMENSION
    for source, target in enumerate(permutation):
        inverse_permutation[target] = source
        inverse_signs[target] = signs[source]
    return tuple(inverse_permutation), tuple(inverse_signs)


def commutator(left, right):
    return multiply(multiply(multiply(left, right), inverse(left)), inverse(right))


def diagonal(sign_at):
    return tuple(range(DIMENSION)), tuple(
        sign_at(label, reservoir)
        for label in range(LABEL_DIM)
        for reservoir in range(RESERVOIR_DIM)
    )


def label_x(bit):
    permutation = []
    for label in range(LABEL_DIM):
        for reservoir in range(RESERVOIR_DIM):
            permutation.append((label ^ (1 << bit)) * RESERVOIR_DIM + reservoir)
    return tuple(permutation), (1,) * DIMENSION


def label_z(bit):
    return diagonal(lambda label, _reservoir: -1 if (label >> bit) & 1 else 1)


def negative_rank(element):
    permutation, signs = element
    assert permutation == tuple(range(DIMENSION))
    return sum(sign == -1 for sign in signs)


def positive_reservoir_rank(signs):
    return sum(sign == 1 for sign in signs)


def main():
    v1 = (1,) * 6 + (-1,) * 6
    v2 = (1,) * 10 + (-1,) * 2
    assert positive_reservoir_rank(v1) == 6
    assert positive_reservoir_rank(v2) == 10

    c1 = (-1,) * 2 + (1,) * 6
    c2 = (-1,) + (1,) * 7

    t1 = diagonal(lambda label, reservoir: c1[label] * v1[reservoir])
    t2 = diagonal(lambda label, reservoir: c2[label] * v2[reservoir])
    assert negative_rank(t1) == DIMENSION // 2
    assert negative_rank(t2) == DIMENSION // 4

    h1 = diagonal(lambda _label, reservoir: v1[reservoir])
    h2 = diagonal(lambda _label, reservoir: v2[reservoir])
    assert multiply(h1, h1) == ONE
    assert multiply(h2, h2) == ONE

    # Full primal/dual three-qubit Heisenberg menu is blind to both spectators.
    for bit in range(3):
        for pauli in (label_x(bit), label_z(bit)):
            assert commutator(h1, pauli) == ONE
            assert commutator(h2, pauli) == ONE

    # With R_i=T_i and W_i=1, right dressing W_i by H_i preserves the exact
    # selector conjugacy because H_i commutes with R_i.
    assert commutator(h1, t1) == ONE
    assert commutator(h2, t2) == ONE
    assert multiply(multiply(h1, t1), inverse(h1)) == t1
    assert multiply(multiply(h2, t2), inverse(h2)) == t2

    # But dressing the target word cancels its raw reservoir gauge.
    n1 = multiply(h1, t1)
    n2 = multiply(h2, t2)
    expected_n1 = diagonal(lambda label, _reservoir: c1[label])
    expected_n2 = diagonal(lambda label, _reservoir: c2[label])
    assert n1 == expected_n1
    assert n2 == expected_n2

    # Their cross Gram is a full unitary on the common carrier.
    gram = multiply(inverse(n1), n2)
    assert multiply(inverse(gram), gram) == ONE

    # The raw reservoir involutions cannot be conjugate: their positive ranks
    # differ, even though the label-stripped dressed gauges are both identity.
    assert positive_reservoir_rank(v1) != positive_reservoir_rank(v2)
    print(
        "dual-Heisenberg-blind dressed Gram is full; raw selector gauges remain nonconjugate"
    )


if __name__ == "__main__":
    main()
