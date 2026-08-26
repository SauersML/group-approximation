"""Audit the eight external signed-Hecke roots under J_i and t_i."""

COORDS = (2, 4, 5, 6, 7, 8, 9)
INDEX = {coordinate: index for index, coordinate in enumerate(COORDS)}
SIZE = len(COORDS)

EXTERNAL = {
    (7, 4), (8, 5), (9, 6), (2, 7),
    (4, 8), (7, 8), (5, 9), (8, 9),
}
L0_ROOTS = {
    (5, 6), (4, 5), (2, 4), (2, 8), (4, 9),
    (2, 9), (7, 9), (7, 5), (7, 6), (8, 6),
}


def identity():
    return tuple(tuple(int(i == j) for j in range(SIZE)) for i in range(SIZE))


def multiply(left, right):
    return tuple(
        tuple(
            sum(left[i][k] * right[k][j] for k in range(SIZE)) % 2
            for j in range(SIZE)
        )
        for i in range(SIZE)
    )


def root(row, column):
    matrix = [list(line) for line in identity()]
    matrix[INDEX[row]][INDEX[column]] ^= 1
    return tuple(tuple(line) for line in matrix)


def swap(first, second):
    matrix = [list(line) for line in identity()]
    a = INDEX[first]
    b = INDEX[second]
    matrix[a] = [0] * SIZE
    matrix[b] = [0] * SIZE
    matrix[a][b] = 1
    matrix[b][a] = 1
    return tuple(tuple(line) for line in matrix)


def inverse(matrix):
    augmented = [list(matrix[i]) + list(identity()[i]) for i in range(SIZE)]
    for column in range(SIZE):
        pivot = next(row for row in range(column, SIZE) if augmented[row][column])
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        for row in range(SIZE):
            if row != column and augmented[row][column]:
                augmented[row] = [a ^ b for a, b in zip(augmented[row], augmented[column])]
    return tuple(tuple(line[SIZE:]) for line in augmented)


def conjugate(actor, matrix):
    return multiply(multiply(actor, matrix), inverse(actor))


def root_position(matrix):
    positions = []
    unit = identity()
    for row in range(SIZE):
        for column in range(SIZE):
            if matrix[row][column] != unit[row][column]:
                positions.append((COORDS[row], COORDS[column]))
    return positions[0] if len(positions) == 1 else None


def classify(position):
    if position in EXTERNAL:
        return "external"
    if position in L0_ROOTS:
        return "L0"
    return "other"


def main():
    rows = (
        (1, swap(7, 8), root(4, 7), root(8, 4)),
        (2, swap(8, 9), root(5, 8), root(9, 5)),
    )
    expected_fixed = {1: {(5, 9), (9, 6)}, 2: {(2, 7), (7, 4)}}
    for number, whitehead, arm_a, arm_b in rows:
        singer = multiply(multiply(whitehead, arm_b), arm_a)
        fixed = set()
        print(f"row {number}")
        for position in sorted(EXTERNAL):
            j_image = root_position(conjugate(whitehead, root(*position)))
            t_image = root_position(conjugate(singer, root(*position)))
            print(position, "J:", j_image, classify(j_image),
                  "t:", t_image, classify(t_image))
            if j_image == position and t_image == position:
                fixed.add(position)
        assert fixed == expected_fixed[number]


if __name__ == "__main__":
    main()

