"""Exact signed-L0 conjugacy and depth-two head-factor return audit.

Run on MSI only.  The finite part closes all 8192 signed-L0 matrices and
records shortest generator words.  The Leavitt part checks all prefix
monomials with both prefix lengths at most two.
"""

from collections import deque
from itertools import product

from depth_one_paired_leavitt_return_search import (
    ARROWS, COORDS, INDEX, ONE, ZERO, binary_multiply, canonical,
    constant_transvection, equal, identity_matrix, left_elementary,
)


IDENTITY = tuple(1 << index for index in range(7))


def generator_matrix(source, target):
    rows = list(IDENTITY)
    rows[INDEX[target]] ^= 1 << INDEX[source]
    return tuple(rows)


GENERATORS = tuple(generator_matrix(*arrow) for arrow in ARROWS)


def closure_with_words():
    words = {IDENTITY: ()}
    queue = deque((IDENTITY,))
    while queue:
        current = queue.popleft()
        for index, generator in enumerate(GENERATORS):
            successor = binary_multiply(current, generator)
            if successor not in words:
                words[successor] = words[current] + (index,)
                queue.append(successor)
    assert len(words) == 8192
    return words


def inverse_from_word(word):
    result = IDENTITY
    for index in reversed(word):
        result = binary_multiply(result, GENERATORS[index])
    return result


def conjugate(matrix, group, word):
    return binary_multiply(binary_multiply(group, matrix), inverse_from_word(word))


def shortest_conjugator(words, source, target, wanted_source, wanted_target):
    start = generator_matrix(source, target)
    wanted = generator_matrix(wanted_source, wanted_target)
    hits = []
    for group, word in words.items():
        if conjugate(start, group, word) == wanted:
            hits.append((len(word), word, group))
    if not hits:
        return None, 0
    hits.sort(key=lambda item: (item[0], item[1]))
    return hits[0], len(hits)


def elementary_orbit(words, source, target):
    start = generator_matrix(source, target)
    positions = set()
    elementary = {
        generator_matrix(s, t): (s, t)
        for s in COORDS for t in COORDS if s != t
    }
    for group, word in words.items():
        image = conjugate(start, group, word)
        if image in elementary:
            positions.add(elementary[image])
    return tuple(sorted(positions))


def root(source, target, coefficient):
    return (source, target, coefficient)


def word_matrix(factors):
    matrix = identity_matrix()
    for factor in reversed(factors):
        matrix = left_elementary(matrix, *factor)
    return matrix


def single_root(matrix):
    answer = []
    for row in range(7):
        for column in range(7):
            expected = ONE if row == column else ZERO
            if not equal(matrix[row][column], expected):
                answer.append((COORDS[column], COORDS[row], matrix[row][column]))
    return answer[0] if len(answer) == 1 else None


P = canonical((('0', '1'),))
R = canonical((('1', '0'),))
B2 = canonical((('00', '1'),))
K0 = (root(8, 7, P), root(7, 8, R), root(8, 7, P))
K1 = (root(8, 7, R), root(7, 8, P), root(8, 7, R))


def monomials_depth_two():
    words = ('', '0', '1', '00', '01', '10', '11')
    return tuple(canonical(((mu, nu),)) for mu in words for nu in words
                 if (mu, nu) != ('', ''))


def coefficient_name(coefficient):
    assert len(coefficient) == 1
    mu, nu = next(iter(coefficient))
    return f"s{mu or 'eps'}t{nu or 'eps'}"


def main():
    words = closure_with_words()
    print('signed L0 size', len(words))
    tests = (
        ('R0(k=6)->A1', 6, 8, 7, 4),
        ('R0(k=9)->A1', 9, 8, 7, 4),
        ('O0(k=6)->A1', 6, 7, 7, 4),
        ('O0(k=9)->A1', 9, 7, 7, 4),
        ('O(k=6)->B2-position', 6, 7, 4, 8),
        ('O(k=9)->B2-position', 9, 7, 4, 8),
        ('R(k=6)->B2-position', 6, 8, 4, 8),
        ('R(k=9)->B2-position', 9, 8, 4, 8),
    )
    orbit_results = {}
    for name, source, target, wanted_source, wanted_target in tests:
        shortest, count = shortest_conjugator(
            words, source, target, wanted_source, wanted_target)
        orbit_results[name] = (shortest, count)
        if shortest is None:
            print(name, 'NO, hits 0')
        else:
            length, word, _ = shortest
            print(name, 'YES, hits', count, 'shortest length', length,
                  'word arrows', tuple(ARROWS[index] for index in word))
    for source, target in ((6, 8), (9, 8), (6, 7), (9, 7), (4, 8)):
        print('elementary orbit of', (source, target),
              elementary_orbit(words, source, target))

    depth_hits = []
    for branch, k_word in enumerate((K0, K1)):
        for k in (6, 9):
            for coefficient in monomials_depth_two():
                output = single_root(word_matrix(
                    k_word + (root(k, 8, coefficient),) + k_word))
                if output is not None and output[2] == B2:
                    depth_hits.append((branch, k, coefficient, output[:2]))
    print('depth-two B2 coefficient hits', len(depth_hits))
    for branch, k, coefficient, position in depth_hits:
        print('branch', branch, 'k', k, 'input', coefficient_name(coefficient),
              'output source,target', position)

    debug_coefficient = canonical((('10', '1'),))
    for k in (6, 9):
        matrix = word_matrix(K0 + (root(k, 8, debug_coefficient),) + K0)
        changed = []
        for row in range(7):
            for column in range(7):
                expected = ONE if row == column else ZERO
                if not equal(matrix[row][column], expected):
                    changed.append((COORDS[column], COORDS[row], matrix[row][column]))
        print('debug K0 s10t1 k', k, 'changed entries', changed)

    assert all(shortest is None for shortest, _ in orbit_results.values())
    assert [
        (branch, k, coefficient, position)
        for branch, k, coefficient, position in depth_hits
    ] == [
        (0, 6, canonical((('00', '1'),)), (6, 8)),
        (0, 6, canonical((('10', '1'),)), (6, 7)),
        (0, 9, canonical((('00', '1'),)), (9, 8)),
        (0, 9, canonical((('10', '1'),)), (9, 7)),
    ]


if __name__ == '__main__':
    main()
