"""Audit the arbitrary-profile payment from a nine-pair Heisenberg frame.

This is intended for MSI, not local execution.
"""

from itertools import permutations, product


POINTS = tuple((i, j) for i in range(3) for j in range(3))
INDEX = {point: n for n, point in enumerate(POINTS)}


def compose(left, right):
    return tuple(left[right[i]] for i in range(3))


def inverse(sigma):
    out = [0] * 3
    for i, value in enumerate(sigma):
        out[value] = i
    return tuple(out)


def act_on_signs(sigma, signs):
    sigma_inv = inverse(sigma)
    return tuple(
        signs[INDEX[(sigma_inv[i], sigma_inv[j])]] for i, j in POINTS
    )


def flip(signs, coordinate):
    out = list(signs)
    out[coordinate] *= -1
    return tuple(out)


def main():
    s3 = tuple(permutations(range(3)))
    identity = (0, 1, 2)
    transpositions = tuple(
        sigma
        for sigma in s3
        if sigma != identity and compose(sigma, sigma) == identity
    )
    three_cycles = tuple(
        sigma
        for sigma in s3
        if sigma != identity and compose(sigma, sigma) != identity
    )
    assert len(transpositions) == 3
    assert len(three_cycles) == 2

    signs = tuple(product((-1, 1), repeat=9))
    assert len(signs) == 512

    # The nine dual roots connect the complete character cube.
    reached = {(-1,) * 9}
    frontier = list(reached)
    while frontier:
        current = frontier.pop()
        for coordinate in range(9):
            nxt = flip(current, coordinate)
            if nxt not in reached:
                reached.add(nxt)
                frontier.append(nxt)
    assert len(reached) == 512

    fixed_transpositions = [
        sum(act_on_signs(sigma, value) == value for value in signs)
        for sigma in transpositions
    ]
    fixed_three_cycles = [
        sum(act_on_signs(sigma, value) == value for value in signs)
        for sigma in three_cycles
    ]
    assert fixed_transpositions == [32, 32, 32]
    assert fixed_three_cycles == [8, 8]

    # The historical unique off-diagonal negative atom has a free orbit.
    marked = tuple(-1 if point == (2, 1) else 1 for point in POINTS)
    orbit = {act_on_signs(sigma, marked) for sigma in s3}
    assert len(orbit) == 6
    assert all(act_on_signs(sigma, marked) != marked for sigma in s3 if sigma != identity)

    print(
        "nine dual flips force 512 equal atoms; adjacent swaps fix 32, "
        "so the free S3 profile pays a 1/16 return sector"
    )


if __name__ == "__main__":
    main()
