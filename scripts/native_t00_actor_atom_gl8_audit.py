"""Exact GL_8 monomial fence for the paid t00 discrepancy.

Run through the MSI wrapper only.  The eight coordinates are the character
basis of the literal three-pair middle-index Heisenberg label packet.
"""


DIMENSION = 8


def dot(left, right):
    return bin(left & right).count("1") & 1


def linear_image(columns, vector):
    answer = 0
    for bit, column in enumerate(columns):
        if (vector >> bit) & 1:
            answer ^= column
    return answer


# A signed permutation is stored by its image (sign, output basis index) on
# every input basis vector.  These are exact integral GL_8 matrices.
def identity():
    return tuple((1, index) for index in range(DIMENSION))


ONE = identity()


def multiply(left, right):
    answer = []
    for right_sign, right_index in right:
        left_sign, left_index = left[right_index]
        answer.append((right_sign * left_sign, left_index))
    return tuple(answer)


def inverse(operator):
    answer = [None] * DIMENSION
    for source, (sign, target) in enumerate(operator):
        answer[target] = (sign, source)
    return tuple(answer)


def commutator(left, right):
    return multiply(multiply(multiply(left, right), inverse(left)), inverse(right))


def power(operator, exponent):
    answer = ONE
    for _ in range(exponent):
        answer = multiply(answer, operator)
    return answer


def diagonal(character):
    return tuple(((-1 if dot(character, x) else 1), x) for x in range(DIMENSION))


def translation(vector):
    return tuple((1, x ^ vector) for x in range(DIMENSION))


def linear(columns):
    return tuple((1, linear_image(columns, x)) for x in range(DIMENSION))


def transvection(target, source):
    columns = [1 << bit for bit in range(3)]
    columns[source] ^= 1 << target
    return linear(tuple(columns))


def swap(first, second):
    columns = [1 << bit for bit in range(3)]
    columns[first], columns[second] = columns[second], columns[first]
    return linear(tuple(columns))


def conjugate(actor, operator):
    return multiply(multiply(actor, operator), inverse(actor))


def fixes_constant_atom_pointwise(operator):
    # The all-positive C7,C8,C9 atom is the line spanned by delta_000.
    return operator[0] == (1, 0)


def main():
    c7, c8, c9 = diagonal(1), diagonal(2), diagonal(4)
    d7, d8 = translation(1), translation(2)
    mark = tuple((-1, index) for index in range(DIMENSION))

    # The two literal adjacent Whiteheads and collapsed native order-seven
    # heads.  For head one the auxiliary slot 4 is represented by bit 9; for
    # head two the auxiliary slot 5 is represented by bit 7.  This is a
    # quotient of the displayed occurrence table, not an added relation.
    j1 = swap(0, 1)
    j2 = swap(1, 2)
    a1 = transvection(2, 0)
    b2 = transvection(1, 2)
    a2 = transvection(0, 1)
    b3 = transvection(2, 0)
    head1 = multiply(multiply(j1, b2), a1)
    head2 = multiply(multiply(j2, b3), a2)
    assert power(head1, 7) == ONE
    assert power(head2, 7) == ONE

    # M fixes bit 7 and shears both bits 8 and 9 by bit 7.  Its implementer
    # fixes delta_000.  Dressing it by C8 gives an involutory, nonidentity
    # image of the paid discrepancy D.
    shear = linear((1, 3, 5))
    discrepancy = multiply(c8, shear)
    assert power(discrepancy, 2) == ONE
    assert discrepancy != ONE

    # The two coefficient-sensitive contacts from TYC8 can collapse exactly
    # as U=x_18(a3)=C9 and V=x_73(b0)=z in this finite occurrence quotient.
    forward = multiply(commutator(c7, discrepancy), c8)
    backward = multiply(commutator(discrepancy, d8), d7)
    assert forward == c9
    assert backward == mark

    # D has a genuine paid negative sector (four of eight dimensions), but
    # its negative projection has zero intersection with the common atom:
    # D fixes delta_000 with sign +1.  The forward full-scale contact does too.
    trace = sum(sign for index, (sign, target) in enumerate(discrepancy)
                if target == index)
    negative_dimension = (DIMENSION - trace) // 2
    assert negative_dimension == 4
    assert fixes_constant_atom_pointwise(discrepancy)
    assert fixes_constant_atom_pointwise(forward)

    actors = (j1, j2, head1, head2)
    assert all(fixes_constant_atom_pointwise(actor) for actor in actors)
    conjugates = tuple(conjugate(actor, discrepancy) for actor in actors)
    assert all(fixes_constant_atom_pointwise(word) for word in conjugates)
    assert fixes_constant_atom_pointwise(
        multiply(multiply(conjugates[0], conjugates[1]),
                 commutator(conjugates[2], conjugates[3]))
    )

    # This fence is actor-only.  The literal Heisenberg dual translations
    # cross it: their eight conjugates have nonzero aggregate compression
    # defect on the constant atom, exactly as in PAM5.
    pauli_conjugates = tuple(
        conjugate(translation(vector), discrepancy) for vector in range(8)
    )
    twice_compression_defect = []
    for word in pauli_conjugates:
        sign, target = word[0]
        twice_compression_defect.append(1 - sign if target == 0 else 1)
    assert sum(twice_compression_defect) > 0

    # The marked Pauli relation survives, so the model did not kill the mark.
    assert commutator(c7, d7) == mark
    print(
        "GL8 actor-normal-closure fence: paid D is nontrivial off the atom "
        "and fixes the common atom pointwise; Pauli flips cross the fence"
    )


if __name__ == "__main__":
    main()
