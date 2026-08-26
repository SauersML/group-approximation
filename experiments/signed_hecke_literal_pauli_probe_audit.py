"""Exact Leavitt-coefficient audit of the fenced detector/Pauli probe seam.

Run on MSI only.  Unlike ``signed_hecke_middle_pauli_probe_audit.py``, this
uses faithful binary-prefix normal forms for every literal coefficient.  It
therefore tests the actual three Y translations, the actual two prefix
Whiteheads, and the actual three X return legs rather than their F_2 index
skeleton.
"""

from itertools import product

from depth_one_paired_leavitt_return_search import (
    ONE, ZERO, add, canonical, equal, multiply as coefficient_multiply,
    signed_l0,
)
from signed_hecke_detector_normal_closure_audit import (
    conjugacy_class, generated_subgroup,
)
from signed_hecke_root_normalizer_audit import (
    COORDS as ACTOR_COORDS,
    IDENTITY as ACTOR_IDENTITY,
    multiply as binary_multiply,
    transvection as actor_transvection,
)


COORDS = (1, 2, 3, 4, 5, 6, 7, 8, 9)
INDEX = {coordinate: index for index, coordinate in enumerate(COORDS)}
MIDDLE = (7, 8, 9)


def zero_matrix():
    return [[ZERO for _ in COORDS] for _ in COORDS]


def identity_matrix():
    matrix = zero_matrix()
    for index in range(len(COORDS)):
        matrix[index][index] = ONE
    return matrix


def matrix_multiply(left, right):
    answer = zero_matrix()
    for row in range(len(COORDS)):
        for column in range(len(COORDS)):
            entry = ZERO
            for middle in range(len(COORDS)):
                entry = add(
                    entry,
                    coefficient_multiply(left[row][middle], right[middle][column]),
                )
            answer[row][column] = entry
    return answer


def matrix_key(matrix):
    return tuple(tuple(entry for entry in row) for row in matrix)


def matrices_equal(left, right):
    return all(equal(left[row][column], right[row][column])
               for row in range(len(COORDS)) for column in range(len(COORDS)))


def left_elementary(matrix, source, target, coefficient):
    result = [row[:] for row in matrix]
    source_row = INDEX[source]
    target_row = INDEX[target]
    for column in range(len(COORDS)):
        result[target_row][column] = add(
            result[target_row][column],
            coefficient_multiply(coefficient, matrix[source_row][column]),
        )
    return result


def word_matrix(factors):
    matrix = identity_matrix()
    for source, target, coefficient in reversed(factors):
        matrix = left_elementary(matrix, source, target, coefficient)
    return matrix


def inverse_word_matrix(factors):
    return word_matrix(tuple(reversed(factors)))


def constant_matrix(binary_actor):
    matrix = identity_matrix()
    for target_index, target in enumerate(ACTOR_COORDS):
        for source_index, source in enumerate(ACTOR_COORDS):
            bit = (binary_actor[target_index] >> source_index) & 1
            matrix[INDEX[target]][INDEX[source]] = ONE if bit else ZERO
    return matrix


def binary_inverse(matrix):
    inverse = ACTOR_IDENTITY
    power = matrix
    # L0 is finite; multiplication until the identity is both exact and tiny.
    while power != ACTOR_IDENTITY:
        inverse = binary_multiply(inverse, matrix)
        power = binary_multiply(power, matrix)
    return inverse


def to_binary_actor(matrix):
    rows = []
    for target in (1, 3):
        for source in COORDS:
            expected = ONE if source == target else ZERO
            if not equal(matrix[INDEX[target]][INDEX[source]], expected):
                return None
    for target_index, target in enumerate(ACTOR_COORDS):
        bits = 0
        for source in COORDS:
            entry = matrix[INDEX[target]][INDEX[source]]
            if source in ACTOR_COORDS:
                if equal(entry, ONE):
                    bits |= 1 << ACTOR_COORDS.index(source)
                elif entry:
                    return None
            elif entry:
                return None
        rows.append(bits)
    return tuple(rows)


def is_elementary(matrix):
    off_diagonal = []
    for row in range(len(COORDS)):
        for column in range(len(COORDS)):
            entry = matrix[row][column]
            if row == column:
                if not equal(entry, ONE):
                    return False
            elif entry:
                off_diagonal.append(entry)
    return len(off_diagonal) == 1


def commutator(left, left_inverse, right, right_inverse):
    return matrix_multiply(
        matrix_multiply(matrix_multiply(left, right), left_inverse),
        right_inverse,
    )


def missed_classes(character):
    internal_roots = {
        actor_transvection(source, target)
        for source in ACTOR_COORDS for target in ACTOR_COORDS
        if source != target and actor_transvection(source, target) in character
    }
    unseen = {element for element, sign in character.items() if sign == 0}
    unseen.remove(ACTOR_IDENTITY)
    missed = []
    while unseen:
        representative = next(iter(unseen))
        conjugates = conjugacy_class(representative)
        unseen.difference_update(conjugates)
        closure, root_length = generated_subgroup(conjugates, internal_roots)
        if root_length is None:
            missed.append((representative, conjugates, closure))
    assert len(missed) == 31
    return missed


def signed_signature(word, character):
    actor_generators = tuple(
        actor_transvection(source, target)
        for source, target in (
            (6, 5), (5, 4), (4, 2), (8, 2), (9, 4),
            (9, 2), (9, 7), (5, 7), (6, 7), (6, 8),
        )
    )
    matrix = word_matrix(word)
    matrix_inverse = inverse_word_matrix(word)
    images = []
    for index, generator in enumerate(actor_generators):
        image = matrix_multiply(
            matrix_multiply(matrix, constant_matrix(generator)), matrix_inverse
        )
        binary = to_binary_actor(image)
        if binary is None or binary not in character or character[binary] != (index < 3):
            return None
        images.append(binary)
    return tuple(images)


def main():
    character = signed_l0()
    classes = missed_classes(character)

    coeff = lambda mu, nu: canonical(((mu, nu),))
    a = {m: coeff("1", "0" * m) for m in (1, 2, 3)}
    b = {m: coeff("0" * m, "1") for m in (1, 2, 3)}
    x = {middle: ((middle, 1, a[m]),)
         for m, middle in enumerate(MIDDLE, start=1)}
    y = {middle: ((3, middle, b[m]),)
         for m, middle in enumerate(MIDDLE, start=1)}

    whiteheads = []
    for m, (first, second) in enumerate(((7, 8), (8, 9)), start=1):
        c = coeff("0" * (m + 1), "0" * m)
        d = coeff("0" * m, "0" * (m + 1))
        whiteheads.append(((first, second, c), (second, first, d),
                           (first, second, c)))

    w1, w2 = whiteheads
    s3_words = ((), w1, w2, w1 + w2, w2 + w1, w1 + w2 + w1)
    s3_matrices = tuple(word_matrix(word) for word in s3_words)
    assert all(not matrices_equal(left, right)
               for index, left in enumerate(s3_matrices)
               for right in s3_matrices[index + 1:])
    assert matrices_equal(word_matrix(w1 + w1), identity_matrix())
    assert matrices_equal(word_matrix(w2 + w2), identity_matrix())
    assert matrices_equal(word_matrix(w1 + w2 + w1),
                          word_matrix(w2 + w1 + w2))
    y_translation_words = tuple(
        tuple(factor for bit, middle in zip(bits, MIDDLE) if bit
              for factor in y[middle])
        for bits in product((0, 1), repeat=3)
    )
    x_translation_words = tuple(
        tuple(factor for bit, middle in zip(bits, MIDDLE) if bit
              for factor in x[middle])
        for bits in product((0, 1), repeat=3)
    )

    dual_words = tuple(
        permutation + translation
        for permutation in s3_words for translation in y_translation_words
    )
    primal_words = tuple(
        permutation + translation
        for permutation in s3_words for translation in x_translation_words
    )
    dual = tuple((word_matrix(word), inverse_word_matrix(word), word)
                 for word in dual_words)
    primal = tuple((word_matrix(word), inverse_word_matrix(word), word)
                   for word in primal_words)
    assert all(not matrices_equal(left, right)
               for index, (left, _, _) in enumerate(dual)
               for right, _, _ in dual[index + 1:])
    assert all(not matrices_equal(left, right)
               for index, (left, _, _) in enumerate(primal)
               for right, _, _ in primal[index + 1:])

    preserving = tuple(word for word in dual_words
                       if signed_signature(word, character) is not None)
    source_types = {
        tuple(matrix_key(matrix_multiply(
            matrix_multiply(matrix, constant_matrix(actor_transvection(source, target))),
            matrix_inverse,
        )) for source, target in (
            (6, 5), (5, 4), (4, 2), (8, 2), (9, 4),
            (9, 2), (9, 7), (5, 7), (6, 7), (6, 8),
        ))
        for matrix, matrix_inverse, _ in dual
    }

    uncovered_first = []
    uncovered_dual_x = []
    uncovered_dual_primal = []
    uncovered_two_dual = []
    for representative, conjugates, _closure in classes:
        first_hit = False
        dual_x_hit = False
        dual_primal_hit = False
        two_dual_hit = False
        for element in conjugates:
            element_inverse = binary_inverse(element)
            element_matrix = constant_matrix(element)
            element_inverse_matrix = constant_matrix(element_inverse)
            for probe, probe_inverse, _word in dual:
                first = commutator(
                    element_matrix, element_inverse_matrix, probe, probe_inverse
                )
                first_inverse = commutator(
                    probe, probe_inverse, element_matrix, element_inverse_matrix
                )
                first_hit |= is_elementary(first)
                if not dual_x_hit:
                    for middle in MIDDLE:
                        x_matrix = word_matrix(x[middle])
                        extracted = commutator(first, first_inverse, x_matrix, x_matrix)
                        if is_elementary(extracted):
                            dual_x_hit = True
                            break
                if not dual_primal_hit:
                    for second, second_inverse, _ in primal:
                        extracted = commutator(
                            first, first_inverse, second, second_inverse
                        )
                        if is_elementary(extracted):
                            dual_primal_hit = True
                            break
                if not two_dual_hit:
                    for second, second_inverse, _ in dual:
                        extracted = commutator(
                            first, first_inverse, second, second_inverse
                        )
                        if is_elementary(extracted):
                            two_dual_hit = True
                            break
                if first_hit and dual_x_hit and dual_primal_hit and two_dual_hit:
                    break
            if first_hit and dual_x_hit and dual_primal_hit and two_dual_hit:
                break
        if not first_hit:
            uncovered_first.append(representative)
        if not dual_x_hit:
            uncovered_dual_x.append(representative)
        if not dual_primal_hit:
            uncovered_dual_primal.append(representative)
        if not two_dual_hit:
            uncovered_two_dual.append(representative)

    print("literal dual menu size =", len(dual))
    print("literal primal menu size =", len(primal))
    print("literal dual words preserving signed source =", len(preserving))
    print("distinct literal transported source types =", len(source_types))
    print("classes with no elementary first commutator =", len(uncovered_first))
    print("classes missed by dual-menu then one X leg =", len(uncovered_dual_x))
    print("classes missed by dual-48 then primal-48 =", len(uncovered_dual_primal))
    print("classes missed by two dual-48 probes =", len(uncovered_two_dual))
    print("first-commutator fence =", sorted(uncovered_first))
    print("dual-X fence =", sorted(uncovered_dual_x))
    print("dual-primal fence =", sorted(uncovered_dual_primal))
    print("dual-dual fence =", sorted(uncovered_two_dual))


if __name__ == "__main__":
    main()
