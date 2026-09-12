"""Audit fixed-source two-scale endpoint profiles of all positive L0 classes."""

from collections import Counter, deque

from signed_hecke_literal_pauli_probe_audit import binary_inverse, missed_classes
from signed_hecke_root_normalizer_audit import (
    GENERATORS,
    IDENTITY,
    INDEX,
    multiply,
    signed_l0,
)


def conjugacy_class(representative: tuple[int, ...]) -> set[tuple[int, ...]]:
    result = {representative}
    queue = deque((representative,))
    while queue:
        current = queue.popleft()
        for generator in GENERATORS:
            conjugate = multiply(multiply(generator, current), generator)
            if conjugate not in result:
                result.add(conjugate)
                queue.append(conjugate)
    return result


def column_profile(matrix: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        depth
        for depth, middle in enumerate((7, 8, 9), start=1)
        if any(
            (matrix[INDEX[endpoint]] >> INDEX[middle]) & 1
            for endpoint in (2, 4)
        )
    )


def inverse_row_profile(matrix: tuple[int, ...]) -> tuple[int, ...]:
    inverse = binary_inverse(matrix)
    return tuple(
        depth
        for depth, middle in enumerate((7, 8, 9), start=1)
        if any(
            (inverse[INDEX[middle]] >> INDEX[endpoint]) & 1
            for endpoint in (2, 4)
        )
    )


def is_adjacent(profile: tuple[int, ...]) -> bool:
    return (1 in profile and 2 in profile) or (2 in profile and 3 in profile)


def profile_set(conjugates, profile):
    return tuple(sorted({profile(element) for element in conjugates}))


def main() -> None:
    signed = signed_l0()
    unseen = {element for element, sign in signed.items() if sign == 0}
    unseen.remove(IDENTITY)
    positive_classes = []
    while unseen:
        representative = min(unseen)
        conjugates = conjugacy_class(representative)
        unseen.difference_update(conjugates)
        positive_classes.append((representative, conjugates))
    assert len(positive_classes) == 511

    column_counts = Counter(
        profile_set(conjugates, column_profile)
        for _representative, conjugates in positive_classes
    )
    inverse_row_counts = Counter(
        profile_set(conjugates, inverse_row_profile)
        for _representative, conjugates in positive_classes
    )
    assert column_counts == Counter(
        {
            ((3,),): 176,
            ((2, 3),): 152,
            ((),): 63,
            ((2,),): 56,
            ((), (3,)): 32,
            ((2,), (2, 3)): 32,
        }
    )
    assert inverse_row_counts == Counter({((),): 511})
    adjacent_count = sum(
        1
        for _representative, conjugates in positive_classes
        if any(is_adjacent(column_profile(element)) for element in conjugates)
        or any(is_adjacent(inverse_row_profile(element)) for element in conjugates)
    )
    assert adjacent_count == 184

    root_free = missed_classes(signed)
    assert len(root_free) == 31
    root_free_column_counts = Counter(
        profile_set(conjugates, column_profile)
        for _representative, conjugates, _closure in root_free
    )
    root_free_inverse_row_counts = Counter(
        profile_set(conjugates, inverse_row_profile)
        for _representative, conjugates, _closure in root_free
    )
    assert root_free_column_counts == Counter({((3,),): 23, ((),): 8})
    assert root_free_inverse_row_counts == Counter({((),): 31})

    witness = (33, 66, 4, 8, 16, 32, 64)
    assert signed[witness] == 0
    assert column_profile(witness) == (2, 3)
    assert inverse_row_profile(witness) == ()
    assert (witness[INDEX[2]] >> INDEX[8]) & 1
    assert (witness[INDEX[4]] >> INDEX[9]) & 1

    print("positive nonidentity conjugacy classes =", len(positive_classes))
    print("fixed-source adjacent column classes =", adjacent_count)
    print("classes without an adjacent profile =", len(positive_classes) - adjacent_count)
    print("inverse-row profile counts =", inverse_row_counts)
    print("root-free column profile counts =", root_free_column_counts)
    print("root-free inverse-row profile counts =", root_free_inverse_row_counts)
    print("witness g=x_28(1)x_49(1): column profile =", column_profile(witness))


if __name__ == "__main__":
    main()
