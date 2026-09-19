"""Exact finite fence for spectral cuts of a native-arm return diamond.

Run on MSI only.  This is deliberately a fixed 32-dimensional signed-
permutation model, not a search.  It realizes the row-one diamond

    C=[U,A],  N=[C,Q],  C'=JCJ,  Q'=JQJ=[B,V]

together with the order-seven native head T=JBA.  On the marked N=-1
sector, the T-orbits of C and Q are the two three-qubit Pauli rows.  The
script also checks the exact finite spectral-cut dichotomy used in the
companion Cairn claim.
"""


def identity(size):
    return tuple(range(size)), (1,) * size


def multiply(left, right):
    """Composition left after right for signed permutations."""
    left_image, left_sign = left
    right_image, right_sign = right
    return (
        tuple(left_image[right_image[index]] for index in range(len(left_image))),
        tuple(right_sign[index] * left_sign[right_image[index]]
              for index in range(len(left_image))),
    )


def inverse(operator):
    image, sign = operator
    inverse_image = [0] * len(image)
    inverse_sign = [0] * len(image)
    for source, target in enumerate(image):
        inverse_image[target] = source
        inverse_sign[target] = sign[source]
    return tuple(inverse_image), tuple(inverse_sign)


def power(operator, exponent):
    answer = identity(len(operator[0]))
    for _ in range(exponent):
        answer = multiply(answer, operator)
    return answer


def conjugate(actor, occurrence):
    return multiply(multiply(actor, occurrence), inverse(actor))


def commutator(left, right):
    return multiply(multiply(multiply(left, right), inverse(left)), inverse(right))


def f2_apply(rows, vector):
    result = 0
    for output, row in enumerate(rows):
        if (row & vector).bit_count() & 1:
            result |= 1 << output
    return result


def f2_compose(left, right):
    columns = tuple(f2_apply(left, f2_apply(right, 1 << column))
                    for column in range(3))
    return columns_to_rows(columns)


def columns_to_rows(columns):
    return tuple(
        sum(((columns[column] >> row) & 1) << column for column in range(3))
        for row in range(3)
    )


def f2_rank(vectors):
    basis = [0, 0, 0]
    rank = 0
    for vector in vectors:
        value = vector
        while value:
            pivot = value.bit_length() - 1
            if basis[pivot]:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                rank += 1
                break
    return rank


def main():
    # An involutory factorization JBA=M^3 of the literal Singer head.  This
    # stage numbering is the one in the exact coefficient orbit table (NIO7).
    A_matrix = (0b101, 0b010, 0b100)
    B_matrix = (0b001, 0b010, 0b110)
    J_matrix = (0b010, 0b001, 0b100)

    coordinates = tuple(
        (gauge_bit, label, mark_bit)
        for gauge_bit in range(2)
        for label in range(8)
        for mark_bit in range(2)
    )
    position = {coordinate: index for index, coordinate in enumerate(coordinates)}

    def operator(action):
        images = []
        signs = []
        for coordinate in coordinates:
            target, sign = action(*coordinate)
            images.append(position[target])
            signs.append(sign)
        return tuple(images), tuple(signs)

    one = identity(len(coordinates))
    native_gauge = operator(lambda d, label, e: (
        (d, label, e), -1 if d else 1
    ))
    returned_mark = operator(lambda d, label, e: (
        (d, label, e), -1 if e else 1
    ))

    def label_permutation(matrix, gauge=False):
        return operator(lambda d, label, e: (
            (d, f2_apply(matrix, label), e),
            -1 if gauge and d else 1,
        ))

    # Two common native chart gauges cancel in the complete order-seven head.
    A = label_permutation(A_matrix, gauge=True)
    B = label_permutation(B_matrix)
    J = label_permutation(J_matrix, gauge=True)
    T = multiply(multiply(J, B), A)

    # U and V expose the two literal intermediate-arm commutators.  They are
    # switched off on the unmarked block, exactly as a central-character
    # packet decomposition permits.
    U = operator(lambda d, label, e: (
        (d, label ^ 0b100 if e else label, e), 1
    ))
    V = operator(lambda d, label, e: (
        (d, label, e),
        -1 if e and ((label & 0b100).bit_count() & 1) else 1,
    ))
    C = operator(lambda d, label, e: (
        (d, label ^ 0b001 if e else label, e), 1
    ))
    Q = operator(lambda d, label, e: (
        (d, label, e),
        -1 if e and ((label & 0b001).bit_count() & 1) else 1,
    ))

    assert power(A, 2) == one
    assert power(B, 2) == one
    assert power(J, 2) == one
    assert power(T, 7) == one
    assert commutator(U, A) == C
    assert commutator(C, Q) == returned_mark
    C_prime = conjugate(J, C)
    Q_prime = conjugate(J, Q)
    assert commutator(B, V) == Q_prime
    assert commutator(C_prime, Q_prime) == returned_mark
    assert commutator(T, returned_mark) == one
    assert native_gauge != returned_mark
    assert multiply(native_gauge, returned_mark) != one

    c_orbit = []
    q_orbit = []
    for exponent in range(7):
        actor = power(T, exponent)
        c_orbit.append(conjugate(actor, C))
        q_orbit.append(conjugate(actor, Q))
    c_product = one
    q_product = one
    for occurrence in c_orbit:
        c_product = multiply(c_product, occurrence)
    for occurrence in q_orbit:
        q_product = multiply(q_product, occurrence)
    assert c_product == one
    assert q_product == one

    # Read off the Pauli symplectic table on the N=-1 block.
    pairing = []
    for c_occurrence in c_orbit:
        row = []
        for q_occurrence in q_orbit:
            cross = commutator(c_occurrence, q_occurrence)
            if cross == one:
                row.append(0)
            elif cross == returned_mark:
                row.append(1)
            else:
                raise AssertionError("cross commutator left the central mark")
        pairing.append(tuple(row))
    expected_pairing = (
        (1, 1, 1, 0, 0, 1, 0),
        (0, 1, 1, 1, 0, 0, 1),
        (1, 0, 1, 1, 1, 0, 0),
        (0, 1, 0, 1, 1, 1, 0),
        (0, 0, 1, 0, 1, 1, 1),
        (1, 0, 0, 1, 0, 1, 1),
        (1, 1, 0, 0, 1, 0, 1),
    )
    assert tuple(pairing) == expected_pairing, pairing
    assert all(sum(row) == 4 for row in pairing)
    assert f2_rank(tuple(
        sum(bit << column for column, bit in enumerate(row[:3]))
        for row in pairing[:3]
    )) == 3

    # The C-orbit generates all translations of F_2^3.  In its Fourier
    # spectral algebra, T has precisely the orbits {0} and F_2^3\{0}.
    # These are the only two nonzero proper T-invariant hard cuts.
    M_matrix = f2_compose(J_matrix, f2_compose(B_matrix, A_matrix))
    assert f2_apply(M_matrix, 0) == 0
    nonzero_orbit = []
    value = 1
    for _ in range(7):
        nonzero_orbit.append(value)
        # Fourier characters transform by inverse transpose.  Its nonzero
        # orbit is still all seven vectors, so direct enumeration suffices.
        candidates = [candidate for candidate in range(1, 8)
                      if all(((candidate & f2_apply(M_matrix, vector)).bit_count() & 1)
                             == ((value & vector).bit_count() & 1)
                             for vector in range(8))]
        assert len(candidates) == 1
        value = candidates[0]
    assert set(nonzero_orbit) == set(range(1, 8))

    zero_cut = {0}
    nonzero_cut = set(range(1, 8))
    # Q=Z_(e1) translates Fourier labels by e1.  Hence neither proper
    # T-invariant C-orbit cut reduces the opposite arm.
    assert {label ^ 1 for label in zero_cut} != zero_cut
    assert {label ^ 1 for label in nonzero_cut} != nonzero_cut

    # All C/Q orbit operators ignore the native-gauge coordinate.  Therefore
    # every spectral projection in their finite group algebra is amplified
    # by I_2 on that bit and cannot identify native_gauge with returned_mark.
    for occurrence in c_orbit + q_orbit + [returned_mark, T]:
        image, sign = occurrence
        for label in range(8):
            for e in range(2):
                left = position[(0, label, e)]
                right = position[(1, label, e)]
                target_left = coordinates[image[left]]
                target_right = coordinates[image[right]]
                assert target_left[1:] == target_right[1:]
                assert sign[left] == sign[right]

    print("32-dimensional exact marked diamond and native order-seven head")
    print("C/Q orbit pairing has rank three and generates the full Pauli label algebra")
    print("the only proper T-invariant C spectral cuts have label ranks 1 and 7")
    print("Q crosses both proper cuts; the full two-arm block retains an independent gauge")


if __name__ == "__main__":
    main()
