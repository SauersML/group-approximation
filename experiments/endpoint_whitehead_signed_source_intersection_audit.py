"""Audit the constant part of an endpoint-Whitehead signed-source overlap."""

from collections import deque

from experiments.signed_hecke_root_normalizer_audit import (
    ARROWS,
    COORDS,
    GENERATORS,
    IDENTITY,
    INDEX,
    multiply,
    signed_l0,
    transvection,
)


def closure(generators: list[tuple[int, ...]]) -> set[tuple[int, ...]]:
    subgroup = {IDENTITY}
    queue = deque((IDENTITY,))
    while queue:
        current = queue.popleft()
        for generator in generators:
            successor = multiply(current, generator)
            if successor not in subgroup:
                subgroup.add(successor)
                queue.append(successor)
    return subgroup


def isolates(matrix: tuple[int, ...], coordinate: int) -> bool:
    index = INDEX[coordinate]
    if matrix[index] != 1 << index:
        return False
    return all(
        ((matrix[row] >> index) & 1) == (row == index)
        for row in range(len(COORDS))
    )


def add_relation(basis: list[int], relation: int) -> None:
    while relation:
        pivot = relation.bit_length() - 1
        if basis[pivot]:
            relation ^= basis[pivot]
        else:
            basis[pivot] = relation
            return


def character_masks() -> tuple[dict[tuple[int, ...], int], list[int]]:
    """Return parity words and all characters of L0 in generator coordinates."""

    representatives = {IDENTITY: 0}
    queue = deque((IDENTITY,))
    relation_basis = [0] * len(GENERATORS)
    while queue:
        current = queue.popleft()
        parity = representatives[current]
        for index, generator in enumerate(GENERATORS):
            successor = multiply(current, generator)
            successor_parity = parity ^ (1 << index)
            if successor in representatives:
                add_relation(
                    relation_basis,
                    successor_parity ^ representatives[successor],
                )
            else:
                representatives[successor] = successor_parity
                queue.append(successor)

    masks = [
        mask
        for mask in range(1 << len(GENERATORS))
        if all((mask & relation).bit_count() % 2 == 0 for relation in relation_basis)
    ]
    return representatives, masks


def main() -> None:
    signed = signed_l0()
    representatives, masks = character_masks()
    assert len(signed) == 8192
    assert len(representatives) == len(signed)

    for coordinate, expected_size, expected_twists in (
        (2, 256, {0, 1 << 2, 1 << 3, (1 << 2) | (1 << 3)}),
        (
            4,
            512,
            {
                0,
                1 << 1,
                1 << 2,
                (1 << 1) | (1 << 2),
                1 << 4,
                (1 << 1) | (1 << 4),
                (1 << 2) | (1 << 4),
                (1 << 1) | (1 << 2) | (1 << 4),
            },
        ),
    ):
        intersection = {matrix for matrix in signed if isolates(matrix, coordinate)}
        assert len(intersection) == expected_size
        assert sum(signed[matrix] for matrix in intersection) == expected_size // 2

        nonincident = [
            GENERATORS[index]
            for index, (source, target) in enumerate(ARROWS)
            if source != coordinate and target != coordinate
        ]
        if coordinate == 4:
            nonincident.append(transvection(5, 2))
        assert closure(nonincident) == intersection

        twists = {
            mask
            for mask in masks
            if all(
                (mask & representatives[matrix]).bit_count() % 2 == 0
                for matrix in intersection
            )
        }
        assert twists == expected_twists
        print(
            f"r={coordinate}: |K_r|={len(intersection)}, "
            f"sign split={expected_size // 2}+{expected_size // 2}, "
            f"character twists trivial on K_r={sorted(hex(mask) for mask in twists)}"
        )


if __name__ == "__main__":
    main()
