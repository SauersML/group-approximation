"""Exact four-bit audit for cyclic aggregation of the endpoint half Gram.

Run only through MSI.  Matrices are the exact conjugation actions on
V=<C3,s,t,sprime>.  Character masks are transported by the contragredient
action, so no Leavitt-prefix truncation is involved here.
"""


IDENTITY = (1, 2, 4, 8)


def apply(matrix, vector):
    answer = 0
    while vector:
        lowest = vector & -vector
        answer ^= matrix[lowest.bit_length() - 1]
        vector ^= lowest
    return answer


def multiply(left, right):
    return tuple(apply(left, column) for column in right)


def power(matrix, exponent):
    answer = IDENTITY
    for _ in range(exponent):
        answer = multiply(answer, matrix)
    return answer


def inverse(matrix):
    for candidate_number in range(16 ** 4):
        candidate = tuple(
            (candidate_number >> (4 * column)) & 15 for column in range(4)
        )
        if multiply(matrix, candidate) == IDENTITY:
            return candidate
    raise AssertionError("matrix is singular")


def transpose(matrix):
    return tuple(
        sum(((matrix[row] >> column) & 1) << row for row in range(4))
        for column in range(4)
    )


def character_action(matrix, character):
    return apply(transpose(inverse(matrix)), character)


def translate_set(matrix, characters):
    return {character_action(matrix, character) for character in characters}


def cyclic_join(matrix, order, characters):
    orbit_sets = []
    current = set(characters)
    for _ in range(order):
        orbit_sets.append(current)
        current = translate_set(matrix, current)
    assert current == set(characters)
    return orbit_sets, set().union(*orbit_sets)


def orbit_partition(matrix, order):
    remaining = set(range(16))
    orbits = []
    while remaining:
        first = min(remaining)
        orbit = []
        current = first
        for _ in range(order):
            if current in orbit:
                break
            orbit.append(current)
            current = character_action(matrix, current)
        assert current == first
        remaining.difference_update(orbit)
        orbits.append(tuple(orbit))
    return tuple(orbits)


def main():
    # Columns in the ordered group basis (C3,s,t,sprime).
    m = (1 ^ 4, 4, 1 ^ 2, 8)
    w = (1, 8, 4, 2)
    c = multiply(w, m)
    assert power(m, 7) == IDENTITY
    assert power(c, 5) == IDENTITY

    # Additive character masks: C3=-1, s=+1; Rstar also sprime=+1.
    r = {character for character in range(16)
         if character & 1 and not character & 2}
    rstar = {character for character in r if not character & 8}
    assert len(r) == 4 and len(rstar) == 2

    print("M character orbits", orbit_partition(m, 7), flush=True)
    print("C=WM character orbits", orbit_partition(c, 5), flush=True)
    for name, actor, order in (("M", m, 7), ("C", c, 5)):
        orbit_sets, join = cyclic_join(actor, order, r)
        translated_sizes = tuple(len(part) for part in orbit_sets)
        print(name, "R translate sizes", translated_sizes, flush=True)
        print(name, "R cyclic join", tuple(sorted(join)), len(join), flush=True)
        print(name, "join intersect Wjoin",
              len(join & translate_set(w, join)), flush=True)

        star_sets, star_join = cyclic_join(actor, order, rstar)
        print(name, "Rstar cyclic join", tuple(sorted(star_join)),
              len(star_join), flush=True)
        print(name, "Rstar join intersect Wjoin",
              len(star_join & translate_set(w, star_join)), flush=True)


if __name__ == "__main__":
    main()
