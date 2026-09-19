"""Schreier--Sims order screen for finite-chart outside actors.

Run only through the MSI wrapper.  Matrices act on the 255 nonzero vectors
of F_2^8, giving a faithful permutation action suitable for SymPy's
Schreier--Sims implementation.
"""

from sympy.combinatorics import Permutation, PermutationGroup


DIMENSION = 8


def identity():
    return tuple(1 << index for index in range(DIMENSION))


def transvection(source, target):
    matrix = list(identity())
    matrix[source] ^= 1 << target
    return tuple(matrix)


def swap(first, second):
    matrix = list(identity())
    matrix[first], matrix[second] = matrix[second], matrix[first]
    return tuple(matrix)


def apply(matrix, vector):
    answer = 0
    for index in range(DIMENSION):
        if (vector >> index) & 1:
            answer ^= matrix[index]
    return answer


def as_permutation(matrix):
    return Permutation([apply(matrix, vector + 1) - 1 for vector in range(255)])


def main():
    q2, q4, q5, q6, u1, u2, u3, _u4 = range(DIMENSION)
    arrows = (
        (q5, q6), (q4, q5), (q2, q4), (q2, u2),
        (q4, u3), (q2, u3), (u1, u3), (u1, q5),
        (u1, q6), (u2, q6), (u2, q5), (u3, q6),
    )
    packet = [transvection(*arrow) for arrow in arrows]
    packet.extend((swap(u1, u2), swap(u2, u3),
                   transvection(q4, u2), transvection(q5, u3)))

    candidates = {
        "A1=u1->q4": transvection(u1, q4),
        "missing-a=q2->u1": transvection(q2, u1),
        "opposite-C1=q4->q2": transvection(q4, q2),
    }
    packet_permutations = tuple(as_permutation(matrix) for matrix in packet)
    packet_group = PermutationGroup(packet_permutations)
    print("P order", packet_group.order(), flush=True)
    for name, candidate in candidates.items():
        group = PermutationGroup(packet_permutations + (as_permutation(candidate),))
        print(name, "extension order", group.order(),
              "index over P", group.order() // packet_group.order(), flush=True)


if __name__ == "__main__":
    main()
