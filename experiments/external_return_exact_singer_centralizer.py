"""Exact coset search for Singer centralizers in the external-return group."""

from collections import deque


COORDS = (2, 4, 5, 6, 7, 8, 9)
INDEX = {coordinate: index for index, coordinate in enumerate(COORDS)}
IDENTITY = tuple(1 << index for index in range(len(COORDS)))
ARROWS = (
    (6, 5), (5, 4), (4, 2), (8, 2), (9, 4),
    (9, 2), (9, 7), (5, 7), (6, 7), (6, 8),
)
EXTERNAL = (
    (4, 7), (5, 8), (6, 9), (7, 2),
    (8, 4), (8, 7), (9, 5), (9, 8),
)


def multiply(left, right):
    product = []
    for left_row in left:
        row = 0
        for index in range(len(COORDS)):
            if (left_row >> index) & 1:
                row ^= right[index]
        product.append(row)
    return tuple(product)


def inverse(matrix):
    size = len(COORDS)
    rows = [matrix[index] | (1 << (size + index)) for index in range(size)]
    for column in range(size):
        pivot = next(index for index in range(column, size) if (rows[index] >> column) & 1)
        rows[column], rows[pivot] = rows[pivot], rows[column]
        for index in range(size):
            if index != column and ((rows[index] >> column) & 1):
                rows[index] ^= rows[column]
    return tuple(row >> size for row in rows)


def transvection(source, target):
    matrix = list(IDENTITY)
    matrix[INDEX[target]] ^= 1 << INDEX[source]
    return tuple(matrix)


def swap(first, second):
    matrix = list(IDENTITY)
    a = INDEX[first]
    b = INDEX[second]
    matrix[a] = 1 << b
    matrix[b] = 1 << a
    return tuple(matrix)


def closure(generators):
    seen = {IDENTITY}
    queue = deque((IDENTITY,))
    while queue:
        current = queue.popleft()
        for generator in generators:
            successor = multiply(current, generator)
            if successor not in seen:
                seen.add(successor)
                queue.append(successor)
    return seen


def power(element, exponent):
    result = IDENTITY
    for _ in range(exponent):
        result = multiply(result, element)
    return result


def quotient_representatives(normal, generators):
    representatives = [IDENTITY]
    inverses = [IDENTITY]
    queue = deque((IDENTITY,))
    while queue:
        current = queue.popleft()
        for generator in generators:
            candidate = multiply(current, generator)
            if any(multiply(rep_inverse, candidate) in normal for rep_inverse in inverses):
                continue
            representatives.append(candidate)
            inverses.append(inverse(candidate))
            queue.append(candidate)
    return representatives


def centralizer_audit(number, singer, normal, reps, spectator, expected_generators):
    centralizers = set()
    for rep_index, representative in enumerate(reps):
        for coefficient in normal:
            element = multiply(representative, coefficient)
            if multiply(element, singer) == multiply(singer, element):
                centralizers.add(element)
        if (rep_index + 1) % 16 == 0:
            print("row", number, "cosets audited", rep_index + 1, "centralizers", len(centralizers))
    outside = centralizers.difference(spectator)
    expected = closure(expected_generators)
    print("row", number, "centralizer size", len(centralizers), "outside spectator", len(outside))
    print("row", number, "expected UT4 size", len(expected))
    assert centralizers == expected
    assert not outside


def main():
    l0_generators = tuple(transvection(*arrow) for arrow in ARROWS)
    external_generators = tuple(transvection(*arrow) for arrow in EXTERNAL)
    normal = closure(l0_generators)
    assert len(normal) == 8192
    for external in external_generators:
        external_inverse = inverse(external)
        for generator in l0_generators:
            assert multiply(multiply(external_inverse, generator), external) in normal
    reps = quotient_representatives(normal, external_generators)
    assert len(reps) == 256
    assert len(reps) * len(normal) == 1 << 21
    print("external quotient size", len(reps), "total group size", len(reps) * len(normal))

    j1 = swap(7, 8)
    t1 = multiply(multiply(j1, transvection(4, 8)), transvection(7, 4))
    j2 = swap(8, 9)
    t2 = multiply(multiply(j2, transvection(5, 9)), transvection(8, 5))
    assert power(t1, 7) == power(t2, 7) == IDENTITY
    spectator1 = closure(l0_generators + (external_generators[2], external_generators[6]))
    spectator2 = closure(l0_generators + (external_generators[3], external_generators[0]))
    assert len(spectator1) == len(spectator2) == 32768
    # In the topological external-arrow order (6,9,5,8,4,7,2), each
    # centralizer is the UT4 group on the four coordinates complementary to
    # the Singer three-space.  The listed arrows are its simple roots.
    expected1 = (
        transvection(6, 9), transvection(9, 5), transvection(5, 2),
    )
    expected2 = (
        transvection(6, 4), transvection(4, 7), transvection(7, 2),
    )
    centralizer_audit(1, t1, normal, reps, spectator1, expected1)
    centralizer_audit(2, t2, normal, reps, spectator2, expected2)


if __name__ == "__main__":
    main()
