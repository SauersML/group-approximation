"""Exhaust the constant root transvections normalizing the signed L0 pair."""

from collections import deque


COORDS = (2, 4, 5, 6, 7, 8, 9)
ARROWS = (
    (6, 5),
    (5, 4),
    (4, 2),
    (8, 2),
    (9, 4),
    (9, 2),
    (9, 7),
    (5, 7),
    (6, 7),
    (6, 8),
)
EXPECTED_EXTERNAL = {
    (4, 7),
    (5, 8),
    (6, 9),
    (7, 2),
    (8, 4),
    (8, 7),
    (9, 5),
    (9, 8),
}

INDEX = {coordinate: index for index, coordinate in enumerate(COORDS)}
IDENTITY = tuple(1 << index for index in range(len(COORDS)))


def multiply(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    product = []
    for left_row in left:
        row = 0
        for index in range(len(COORDS)):
            if (left_row >> index) & 1:
                row ^= right[index]
        product.append(row)
    return tuple(product)


def transvection(source: int, target: int) -> tuple[int, ...]:
    matrix = list(IDENTITY)
    matrix[INDEX[target]] ^= 1 << INDEX[source]
    return tuple(matrix)


GENERATORS = tuple(transvection(source, target) for source, target in ARROWS)


def signed_l0() -> dict[tuple[int, ...], int]:
    character = {IDENTITY: 0}
    queue = deque((IDENTITY,))
    while queue:
        current = queue.popleft()
        for index, generator in enumerate(GENERATORS):
            successor = multiply(current, generator)
            sign = character[current] ^ (index < 3)
            if successor in character:
                assert character[successor] == sign
            else:
                character[successor] = sign
                queue.append(successor)
    return character


def main() -> None:
    character = signed_l0()
    assert len(character) == 8192

    normalizing = set()
    external = set()
    for source in COORDS:
        for target in COORDS:
            if source == target:
                continue
            candidate = transvection(source, target)
            preserves_pair = True
            for index, generator in enumerate(GENERATORS):
                conjugate = multiply(multiply(candidate, generator), candidate)
                if conjugate not in character or character[conjugate] != (index < 3):
                    preserves_pair = False
                    break
            if preserves_pair:
                normalizing.add((source, target))
                if candidate not in character:
                    external.add((source, target))

    assert len(normalizing) == 21
    assert external == EXPECTED_EXTERNAL
    print("|L0| =", len(character))
    print("signed root normalizers =", len(normalizing))
    print("external signed root normalizers =", sorted(external))


if __name__ == "__main__":
    main()
