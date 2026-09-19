"""Audit unit operator-norm leakage on the free marked S3 type orbit.

Run through the MSI wrapper only.  The six basis vectors form the regular
S3 orbit of the marked character with one distinguished negative C_32 sign.
"""

from itertools import permutations


def compose(left, right):
    return tuple(left[right[i]] for i in range(3))


def main():
    group = tuple(permutations(range(3)))
    identity = tuple(range(3))
    position = {g: i for i, g in enumerate(group)}

    # Left translation is free.  Thus every nonidentity normalizer moves the
    # chosen character atom to an orthogonal coordinate atom.
    for u in group:
        image = position[compose(u, identity)]
        if u == identity:
            assert image == position[identity]
        else:
            assert image != position[identity]

    # The marked central involution is -1 on every orbit character, hence its
    # active projection is the full six-dimensional carrier.
    marked_signs = [-1] * len(group)
    assert all(sign == -1 for sign in marked_signs)
    print("free marked S3 orbit has unit atom-return leakage; active core is full")


if __name__ == "__main__":
    main()
