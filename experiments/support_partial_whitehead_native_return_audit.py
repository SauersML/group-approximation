"""Exact support-idempotent Whitehead return and signed-carrier audit.

Run on MSI only.  All coefficient comparisons use faithful prefix equality,
including coarse completeness reductions.
"""

from collections import deque

from depth_one_paired_leavitt_return_search import (
    COORDS, ZERO, add, canonical, equal, identity_matrix, left_elementary,
    multiply, signed_l0,
)
from individual_cross_whitehead_one_return_search import full_signed_signature


def root(row, column, coefficient):
    # Helper primitives store (source,column; target,row).
    return (column, row, coefficient)


def whitehead(first, second, projection):
    return (
        root(first, second, projection),
        root(second, first, projection),
        root(first, second, projection),
    )


def word_matrix(factors):
    matrix = identity_matrix()
    for factor in reversed(factors):
        matrix = left_elementary(matrix, *factor)
    return matrix


def matrices_equal(left, right):
    return all(equal(left[row][column], right[row][column])
               for row in range(7) for column in range(7))


def matrix_multiply(left, right):
    answer = [[ZERO for _ in range(7)] for _ in range(7)]
    for row in range(7):
        for column in range(7):
            entry = ZERO
            for middle in range(7):
                entry = add(entry, multiply(left[row][middle], right[middle][column]))
            answer[row][column] = entry
    return answer


def conjugate_matrix(actor, matrix):
    actor_matrix = word_matrix(actor)
    return matrix_multiply(matrix_multiply(actor_matrix, matrix), actor_matrix)


def set_intersection(left, right):
    return [matrix for matrix in left
            if any(matrices_equal(matrix, candidate) for candidate in right)]


def sets_equal(left, right):
    return len(left) == len(right) and len(set_intersection(left, right)) == len(left)


E0 = canonical((('0', '0'),))
E000 = canonical((('000', '000'),))
X1 = canonical((('00', '0'),))
Y1 = canonical((('0', '00'),))
X2 = canonical((('000', '00'),))
Y2 = canonical((('00', '000'),))
A1C = canonical((('1', '0'),))
A2C = canonical((('1', '00'),))
A3C = canonical((('1', '000'),))
B1C = canonical((('0', '1'),))
B2C = canonical((('00', '1'),))
B3C = canonical((('000', '1'),))


def matrix_key(matrix):
    return tuple(tuple(row) for row in matrix)


def pauli_closure(generators):
    identity = identity_matrix()
    seen = {matrix_key(identity): identity}
    queue = deque((identity,))
    while queue:
        current = queue.popleft()
        for generator in generators:
            successor = left_elementary(current, *generator)
            key = matrix_key(successor)
            if key not in seen:
                seen[key] = successor
                queue.append(successor)
    return seen


def conjugation_word(first, second, projection, row, column, coefficient):
    w = whitehead(first, second, projection)
    return w + (root(row, column, coefficient),) + w


def main():
    character = signed_l0()
    first_results = []
    whitehead_preserves = []
    for ell in (2, 4, 5, 6, 7):
        factors = conjugation_word(ell, 9, E000, 8, ell, Y2)
        expected = (root(8, 9, Y2),)
        ok = matrices_equal(word_matrix(factors), word_matrix(expected))
        first_results.append(ok)
        preserves = full_signed_signature(whitehead(ell, 9, E000), character) is not None
        whitehead_preserves.append(preserves)
        print('y2 support return ell', ell, ok,
              'W preserves signed Q', preserves)

    second_results = []
    for ell in (2, 4, 5, 6, 9):
        factors = conjugation_word(ell, 7, E0, ell, 8, Y1)
        expected = (root(7, 8, Y1),)
        ok = matrices_equal(word_matrix(factors), word_matrix(expected))
        second_results.append(ok)
        preserves = full_signed_signature(whitehead(ell, 7, E0), character) is not None
        whitehead_preserves.append(preserves)
        print('y1 support return ell', ell, ok,
              'W preserves signed Q', preserves)

    # The companion forward-arm returns needed to spell J1 and J2.
    x1_return = conjugation_word(9, 7, E0, 8, 9, X1)
    x2_return = conjugation_word(7, 9, E000, 7, 8, X2)
    assert matrices_equal(word_matrix(x1_return), word_matrix((root(8, 7, X1),)))
    assert matrices_equal(word_matrix(x2_return), word_matrix((root(9, 8, X2),)))

    native_factors = {
        'x87(x1)': (root(8, 7, X1),),
        'x78(y1)': (root(7, 8, Y1),),
        'x98(x2)': (root(9, 8, X2),),
        'x89(y2)': (root(8, 9, Y2),),
    }
    for name, factors in native_factors.items():
        print(name, 'preserves signed Q',
              full_signed_signature(factors, character) is not None)

    j1 = native_factors['x87(x1)'] + native_factors['x78(y1)'] + native_factors['x87(x1)']
    j2 = native_factors['x98(x2)'] + native_factors['x89(y2)'] + native_factors['x98(x2)']
    j_preserves = (
        full_signed_signature(j1, character) is not None,
        full_signed_signature(j2, character) is not None,
    )
    print('J1 preserves signed Q', j_preserves[0])
    print('J2 preserves signed Q', j_preserves[1])

    pauli_generators = (
        root(4, 7, A1C), root(4, 8, A2C), root(4, 9, A3C),
        root(7, 2, B1C), root(8, 2, B2C), root(9, 2, B3C),
    )
    pauli = pauli_closure(pauli_generators)
    assert len(pauli) == 128
    packet_words = {
        'W1': whitehead(7, 9, E0),
        'W2': whitehead(7, 9, E000),
        'Khat1': (root(8, 9, X1), root(9, 8, Y1), root(8, 9, X1)),
        'Khat2': (root(7, 8, X2), root(8, 7, Y2), root(7, 8, X2)),
        'J1': j1,
        'J2': j2,
    }
    normalization = {}
    for name, actor in packet_words.items():
        membership = []
        for generator in pauli_generators:
            image = word_matrix(actor + (generator,) + tuple(reversed(actor)))
            membership.append(any(matrices_equal(image, candidate)
                                  for candidate in pauli.values()))
        normalization[name] = tuple(membership)
        print(name, 'same-center Pauli image membership', membership,
              'normalizes', all(membership))

    assert all(first_results) and all(second_results)
    assert not any(whitehead_preserves)
    assert all(full_signed_signature(factors, character) is None
               for factors in native_factors.values())
    assert j_preserves == (False, False)
    assert not all(normalization['W1'])
    assert not all(normalization['W2'])
    assert not all(normalization['Khat1'])
    assert not all(normalization['Khat2'])
    assert all(normalization['J1']) and all(normalization['J2'])

    e_matrices = list(pauli.values())
    w1_word = packet_words['W1']
    w2_word = packet_words['W2']
    e1 = [conjugate_matrix(w1_word, matrix) for matrix in e_matrices]
    e2 = [conjugate_matrix(w2_word, matrix) for matrix in e_matrices]
    e12 = set_intersection(e1, e2)
    original_two_pair = list(pauli_closure((
        pauli_generators[1], pauli_generators[2],
        pauli_generators[4], pauli_generators[5],
    )).values())
    common_two_pair = [conjugate_matrix(w1_word, matrix)
                       for matrix in original_two_pair]
    print('chart sizes E,E1,E2', len(e_matrices), len(e1), len(e2))
    print('E1 equals E2', sets_equal(e1, e2), 'intersection', len(e12),
          'intersection equals transported pairs 2,3', sets_equal(e12, common_two_pair))

    support_difference = add(E0, E000)
    s_word = w1_word + w2_word
    s_expected = whitehead(7, 9, support_difference)
    assert matrices_equal(word_matrix(s_word), word_matrix(s_expected))
    s_membership = []
    for generator in pauli_generators:
        image = conjugate_matrix(s_word, word_matrix((generator,)))
        s_membership.append(any(matrices_equal(image, candidate)
                                for candidate in e_matrices))
    s_e1 = [conjugate_matrix(s_word, matrix) for matrix in e1]
    print('S same-center membership', s_membership,
          'normalizes E', all(s_membership),
          'maps E1 to E2', sets_equal(s_e1, e2))
    print('S centralizes common pairs 2,3', all(
        matrices_equal(conjugate_matrix(s_word, matrix), matrix)
        for matrix in common_two_pair))

    assert len(e1) == len(e2) == 128
    assert not sets_equal(e1, e2)
    assert len(e12) == 32 and sets_equal(e12, common_two_pair)
    assert s_membership == [False, True, True, False, True, True]
    assert sets_equal(s_e1, e2)
    assert all(matrices_equal(conjugate_matrix(s_word, matrix), matrix)
               for matrix in common_two_pair)


if __name__ == '__main__':
    main()
