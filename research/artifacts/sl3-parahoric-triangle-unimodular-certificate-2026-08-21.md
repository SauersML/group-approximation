# Exact certificate: the signed parahoric triangle is unimodular

This dependency-free Python script works only with tuples, bitsets, and
integer arithmetic.  It verifies:

```text
orbit size = 42
triangle points = [0, 7, 17]
selected rows = 42
signed determinant = 1
```

The determinant is computed by fraction-free Bareiss elimination.  The
mod-two elimination only selects a square set of orbit rows; the final
determinant assertion is over the integers.

```python
from collections import deque
from itertools import product

modulus = 4


def matrix_vector(matrix, vector):
    return tuple(
        sum(matrix[i][j] * vector[j] for j in range(3)) % modulus
        for i in range(3)
    )


def act(matrix, lattice):
    return frozenset(matrix_vector(matrix, vector) for vector in lattice)


def elementary(i, j, value):
    matrix = [[int(row == column) for column in range(3)] for row in range(3)]
    matrix[i][j] = value % modulus
    return tuple(map(tuple, matrix))


generators = [
    elementary(i, j, value)
    for i in range(3)
    for j in range(3)
    if i != j
    for value in (1, -1)
]

base = frozenset((0, b, c) for b in (0, 2) for c in range(4))
index = {base: 0}
queue = deque([base])
while queue:
    lattice = queue.popleft()
    for generator in generators:
        target = act(generator, lattice)
        if target not in index:
            index[target] = len(index)
            queue.append(target)

assert len(index) == 42
lattices = [None] * 42
for lattice, number in index.items():
    lattices[number] = lattice

permutations = [
    [index[act(generator, lattice)] for lattice in lattices]
    for generator in generators
]


def coordinate_permutation(values):
    matrix = [[0] * 3 for _ in range(3)]
    for i in range(3):
        matrix[i][values[i]] = 1
    return tuple(map(tuple, matrix))


s12 = coordinate_permutation((1, 0, 2))
s23 = coordinate_permutation((0, 2, 1))
triangle_points = [0, index[act(s12, base)], index[act(s23, base)]]
assert triangle_points == [0, 7, 17]

relation = [0] * 42
relation[triangle_points[0]] = 1
relation[triangle_points[1]] = -1
relation[triangle_points[2]] = -1
relation = tuple(relation)


def permute(vector, permutation):
    target = [0] * 42
    for i, value in enumerate(vector):
        target[permutation[i]] = value
    return tuple(target)


def parity_bits(vector):
    return sum((value & 1) << i for i, value in enumerate(vector))


basis = {}
rows = []
queue = deque([relation])
while queue:
    row = queue.popleft()
    residue = parity_bits(row)
    while residue:
        pivot = residue.bit_length() - 1
        if pivot in basis:
            residue ^= basis[pivot]
        else:
            basis[pivot] = residue
            rows.append(row)
            for permutation in permutations:
                queue.append(permute(row, permutation))
            break

assert len(rows) == 42

# Fraction-free Bareiss determinant.
matrix = [list(row) for row in rows]
sign = 1
previous = 1
for column in range(41):
    if matrix[column][column] == 0:
        swap = next(
            row for row in range(column + 1, 42) if matrix[row][column] != 0
        )
        matrix[column], matrix[swap] = matrix[swap], matrix[column]
        sign = -sign
    pivot = matrix[column][column]
    for row in range(column + 1, 42):
        for target_column in range(column + 1, 42):
            matrix[row][target_column] = (
                matrix[row][target_column] * pivot
                - matrix[row][column] * matrix[column][target_column]
            ) // previous
        matrix[row][column] = 0
    previous = pivot

determinant = sign * matrix[41][41]
assert determinant == 1
print(len(index), triangle_points, len(rows), determinant)
```
