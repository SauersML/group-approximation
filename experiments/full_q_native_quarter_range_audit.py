"""Audit the two literal native ranges of the full-Q quarter source.

Run through the MSI wrapper only.  The input components are the exact
Omega_0 signed-source components proved in
full-moving-hecke-q-kernel-profile-proof.md.  This tiny check deliberately
does not enumerate a new group or replace any group relation.
"""


Q_COMPONENTS = (
    frozenset(((17, 17), (19, 17))),
    frozenset(((17, 25), (19, 25))),
    frozenset(((21, 17), (23, 17))),
    frozenset(((21, 25), (23, 25))),
)


def swap_bits(value, left, right):
    if ((value >> left) & 1) == ((value >> right) & 1):
        return value
    return value ^ (1 << left) ^ (1 << right)


def swap_state(state, left, right):
    row, vector = state
    return swap_bits(row, left, right), swap_bits(vector, left, right)


def r_action(state):
    """Contragradient/vector action of x_58(a_2) on the Levi character."""
    row, vector = state
    if (row >> 0) & 1:
        row ^= 1 << 2
    if (vector >> 2) & 1:
        vector ^= 1 << 0
    return row, vector


def main():
    # l=x_69(a_3) reads vector bit u_3.  Its positive cut keeps two Q
    # components, and r exchanges them.  Their positive spectral vector is
    # the equal sum of both components.
    l_positive = tuple(
        component
        for component in Q_COMPONENTS
        if all(((vector >> 3) & 1) == 0 for _, vector in component)
    )
    assert len(l_positive) == 2
    assert frozenset(map(r_action, l_positive[0])) == l_positive[1]
    assert frozenset(map(r_action, l_positive[1])) == l_positive[0]

    quarter_source = frozenset().union(*l_positive)
    assert quarter_source == frozenset(
        ((17, 17), (19, 17), (21, 17), (23, 17))
    )

    j1_range_vector = frozenset(
        swap_state(state, 1, 2) for state in quarter_source
    )
    j2_range_vector = frozenset(
        swap_state(state, 2, 3) for state in quarter_source
    )
    assert j1_range_vector == quarter_source
    assert j2_range_vector == frozenset(
        ((17, 17), (19, 17), (25, 17), (27, 17))
    )
    assert j1_range_vector != j2_range_vector

    common_coordinates = len(j1_range_vector & j2_range_vector)
    normalized_inner = common_coordinates / len(quarter_source)
    assert normalized_inner == 0.5

    print("Q rank / l-positive rank / F rank =", 4, 2, 1)
    print("F vector =", tuple(sorted(quarter_source)))
    print("J1 F vector =", tuple(sorted(j1_range_vector)))
    print("J2 F vector =", tuple(sorted(j2_range_vector)))
    print("literal ranges equal =", j1_range_vector == j2_range_vector)
    print("rank-one projection meet rank =", 0)
    print("normalized cross coefficient / squared Gram =",
          normalized_inner, normalized_inner ** 2)


if __name__ == "__main__":
    main()
