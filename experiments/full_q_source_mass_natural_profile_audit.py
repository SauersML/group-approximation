"""Audit source projections in the 127-point projective-head profile.

Run only through the MSI wrapper.  The seven active projective summands give
the natural action of the literal ``SL_7(F_2)`` head on the nonzero vectors of
``F_2^7``.  This script computes, without floating point arithmetic, the
multiplicity of the signed ``K`` character (the rank of ``F``) and the ranks
of the one- and three-root negative projections used by the marked-root-star
carrier.
"""

from collections import deque


DIMENSION = 7


def identity():
    return tuple(1 << index for index in range(DIMENSION))


def transvection(source, target):
    matrix = list(identity())
    matrix[target] ^= 1 << source
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


def multiply(left, right):
    return tuple(apply(right, row) for row in left)


def fixed_nonzero_vectors(matrix):
    return sum(apply(matrix, vector) == vector
               for vector in range(1, 1 << DIMENSION))


def permutation_compose(left, right):
    return tuple(left[right[index]] for index in range(len(left)))


def permutation(matrix):
    return tuple(apply(matrix, vector) - 1
                 for vector in range(1, 1 << DIMENSION))


def projection_rank_from_character(group_with_phase):
    numerator = sum((-1 if phase else 1) * fixed_nonzero_vectors(matrix)
                    for matrix, phase in group_with_phase.items())
    assert numerator % len(group_with_phase) == 0
    return numerator // len(group_with_phase)


def rational_rank(matrix):
    from fractions import Fraction

    work = [[Fraction(entry) for entry in row] for row in matrix]
    rank = 0
    column = 0
    while rank < len(work) and column < (len(work[0]) if work else 0):
        pivot = next((row for row in range(rank, len(work))
                      if work[row][column]), None)
        if pivot is None:
            column += 1
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        scale = work[rank][column]
        work[rank] = [entry / scale for entry in work[rank]]
        for row in range(len(work)):
            if row != rank and work[row][column]:
                scale = work[row][column]
                work[row] = [left - scale * right
                             for left, right in zip(work[row], work[rank])]
        rank += 1
        column += 1
    return rank


def main():
    q2, q4, q5, q6, u1, u2, u3 = range(DIMENSION)
    arrows = (
        (q5, q6), (q4, q5), (q2, q4), (q2, u2),
        (q4, u3), (q2, u3), (u1, u3), (u1, q5),
        (u1, q6), (u2, q6), (u2, q5), (u3, q6),
    )
    generators = tuple(transvection(*arrow) for arrow in arrows)

    # The first three arrows are C3, C2, C1 (in reverse displayed order)
    # and carry the negative sign; all remaining K generators are positive.
    signed_group = {identity(): 0}
    queue = deque([identity()])
    while queue:
        current = queue.popleft()
        for index, generator in enumerate(generators):
            following = multiply(current, generator)
            phase = signed_group[current] ^ (index < 3)
            if following not in signed_group:
                signed_group[following] = phase
                queue.append(following)
            else:
                assert signed_group[following] == phase
    assert len(signed_group) == 1 << 15

    # The signed source uses the chain C3=q5->q6, C2=q4->q5,
    # C1=q2->q4.  The marked-root star instead uses the commuting row
    # C1=q2->q4, C2star=q2->q5, C3star=q2->q6.
    _chain_c3, _chain_c2, c1 = generators[:3]
    one_negative_rank = (
        ((1 << DIMENSION) - 1 - fixed_nonzero_vectors(c1)) // 2
    )

    # Since C1,C2,C3 commute, the signed average over their C2^3 subgroup
    # is the triple-negative projection E.
    center_generators = (
        c1,
        transvection(q2, q5),
        transvection(q2, q6),
    )
    center_group = {identity(): 0}
    queue = deque([identity()])
    while queue:
        current = queue.popleft()
        for generator in center_generators:
            following = multiply(current, generator)
            phase = center_group[current] ^ 1
            if following not in center_group:
                center_group[following] = phase
                queue.append(following)
            else:
                assert center_group[following] == phase
    assert len(center_group) == 8

    print("K order", len(signed_group))
    print("rank F on 127-point natural profile",
          projection_rank_from_character(signed_group))
    print("rank p_C1 on 127-point natural profile", one_negative_rank)
    print("rank E on 127-point natural profile",
          projection_rank_from_character(center_group))

    # Build the signed orbit-sum basis for ran(E), then compute the exact
    # cross matrix against g=J1 J2.  Its rational rank is rank(E g E).
    remaining = set(range(1, 1 << DIMENSION))
    signed_orbits = []
    while remaining:
        representative = min(remaining)
        phases = {representative: 0}
        orbit_queue = deque([representative])
        consistent = True
        while orbit_queue:
            vector = orbit_queue.popleft()
            for generator in center_generators:
                following = apply(generator, vector)
                phase = phases[vector] ^ 1
                if following not in phases:
                    phases[following] = phase
                    orbit_queue.append(following)
                elif phases[following] != phase:
                    consistent = False
        remaining.difference_update(phases)
        if consistent:
            signed_orbits.append(phases)
    assert len(signed_orbits) == 8

    j1 = swap(u1, u2)
    j2 = swap(u2, u3)
    g = multiply(j1, j2)
    cross_matrix = []
    for left in signed_orbits:
        row = []
        for right in signed_orbits:
            coefficient = 0
            for vector, phase in right.items():
                image = apply(g, vector)
                if image in left:
                    coefficient += -1 if phase ^ left[image] else 1
            row.append(coefficient)
        cross_matrix.append(row)
    print("rank E(J1J2)E on 127-point natural profile",
          rational_rank(cross_matrix))

    unseen = set(range(1, 1 << DIMENSION))
    orbit_certificates = []
    while unseen:
        representative = min(unseen)
        orbit = {representative}
        orbit_queue = deque([representative])
        while orbit_queue:
            vector = orbit_queue.popleft()
            for generator in generators:
                following = apply(generator, vector)
                if following not in orbit:
                    orbit.add(following)
                    orbit_queue.append(following)
        unseen.difference_update(orbit)
        witness = next(
            matrix for matrix, phase in signed_group.items()
            if phase and apply(matrix, representative) == representative
        )
        orbit_certificates.append((representative, len(orbit), witness))

    print("K orbits / negative-stabilizer certificates")
    for representative, size, witness in orbit_certificates:
        print(hex(representative), size,
              ",".join(hex(row) for row in witness))


if __name__ == "__main__":
    main()
