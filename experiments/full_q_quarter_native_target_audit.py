"""Exact target audit for the full-Hecke quarter source.

Run only through the MSI wrapper.  This reuses the adjacent-character
monomial representations from ``full_q_moving_gl8_permutation_audit`` and
adds the literal operators

    r=x_58(a_2),  t=x_69(a_3),  J1=(e1 e2),  J2=(e2 e3).

It constructs F=Q(1+r)(1+t)/4 and computes the two actual range spaces
J1 F and J2 F inside each of the 465- and 496-state profiles.
"""

from full_q_moving_gl8_permutation_audit import (
    IDENTITY,
    integer_rank,
    signed_component_basis,
)


def matrix_multiply(left, right):
    return tuple(
        tuple(sum(left[i][k] * right[k][j] for k in range(len(right)))
              for j in range(len(right[0])))
        for i in range(len(left))
    )


def independent_columns(matrix):
    chosen = []
    current_rank = 0
    for column in zip(*matrix):
        trial = chosen + [column]
        trial_rank = integer_rank(tuple(zip(*trial)))
        if trial_rank > current_rank:
            chosen.append(column)
            current_rank = trial_rank
    return tuple(chosen)


def vector_rank(vectors, states):
    rows = tuple(
        tuple(vector.get(state, 0) for vector in vectors)
        for state in states
    )
    return integer_rank(rows)


def combine_q(column, q_basis):
    answer = {}
    for coefficient, component in zip(column, q_basis):
        for state, sign in component.items():
            answer[state] = answer.get(state, 0) + coefficient * (
                -1 if sign else 1
            )
    return {state: value for state, value in answer.items() if value}


def apply_permutation(vector, action):
    return {action(state): coefficient for state, coefficient in vector.items()}


def inner(left, right):
    return sum(coefficient * left.get(state, 0)
               for state, coefficient in right.items())


def profile(pairing):
    local_identity = tuple(1 << index for index in range(5))

    def local_multiply(left, right):
        answer = []
        for left_row in left:
            row = 0
            for index in range(5):
                if (left_row >> index) & 1:
                    row ^= right[index]
            answer.append(row)
        return tuple(answer)

    def local_apply(matrix, vector):
        answer = 0
        for row, mask in enumerate(matrix):
            if (mask & vector).bit_count() & 1:
                answer |= 1 << row
        return answer

    def local_row_apply(row, matrix):
        answer = 0
        for index in range(5):
            if (row >> index) & 1:
                answer ^= matrix[index]
        return answer

    def local_inverse(matrix):
        answer = local_identity
        power = matrix
        while power != local_identity:
            answer = local_multiply(answer, matrix)
            power = local_multiply(power, matrix)
        return answer

    def transvection(source, target):
        matrix = list(local_identity)
        matrix[target] ^= 1 << source
        return tuple(matrix)

    def swap(left, right):
        matrix = list(local_identity)
        matrix[left], matrix[right] = matrix[right], matrix[left]
        return tuple(matrix)

    def action(matrix):
        inverse = local_inverse(matrix)
        return lambda state: (
            local_row_apply(state[0], inverse),
            local_apply(matrix, state[1]),
        )

    states = tuple(
        (row, vector)
        for row in range(1, 32)
        for vector in range(1, 32)
        if ((row & vector).bit_count() & 1) == pairing
    )

    identity_action = lambda state: state
    identity_phase = lambda _state: 0
    phase = lambda side, bit: lambda state: (state[side] >> bit) & 1
    c = transvection(1, 3)
    v = transvection(1, 0)
    signed_generators = (
        (identity_action, phase(1, 0), 1),
        (identity_action, phase(0, 0), 1),
        (identity_action, lambda _state: 1, 1),
        (identity_action, identity_phase, 0),
        (identity_action, phase(0, 3), 0),
        (identity_action, identity_phase, 0),
        (action(c), identity_phase, 0),
        (action(v), identity_phase, 0),
        (identity_action, phase(1, 1), 0),
        (identity_action, phase(1, 2), 0),
    )
    q_basis = signed_component_basis(states, signed_generators)

    def q_matrix(permutation=None, diagonal=None):
        columns = []
        for right in q_basis:
            moved = {}
            for state, sign in right.items():
                target = permutation(state) if permutation else state
                coefficient = -1 if sign else 1
                if diagonal and diagonal(state):
                    coefficient = -coefficient
                moved[target] = coefficient
            column = []
            for left in q_basis:
                numerator = sum(
                    (-1 if left[state] else 1) * moved.get(state, 0)
                    for state in left
                )
                assert numerator % len(left) == 0
                column.append(numerator // len(left))
            columns.append(tuple(column))
        return tuple(zip(*columns))

    # Local node order is q5,e1,e2,e3,e3@2.  Thus r is A2 and t is the
    # vector character dual to B3 on the e3 coordinate.
    r_action = action(transvection(2, 0))
    t_phase = phase(1, 3)
    j1_action = action(swap(1, 2))
    j2_action = action(swap(2, 3))

    r_matrix = q_matrix(permutation=r_action)
    t_matrix = q_matrix(diagonal=t_phase)
    size = len(q_basis)
    identity = tuple(tuple(int(i == j) for j in range(size)) for i in range(size))
    plus_r = tuple(tuple(identity[i][j] + r_matrix[i][j] for j in range(size))
                   for i in range(size))
    plus_t = tuple(tuple(identity[i][j] + t_matrix[i][j] for j in range(size))
                   for i in range(size))
    projector_numerator = matrix_multiply(plus_r, plus_t)
    f_columns = independent_columns(projector_numerator)
    f_basis = tuple(combine_q(column, q_basis) for column in f_columns)

    j1_range = tuple(apply_permutation(vector, j1_action) for vector in f_basis)
    j2_range = tuple(apply_permutation(vector, j2_action) for vector in f_basis)
    q_vectors = tuple(combine_q(tuple(int(i == j) for i in range(size)), q_basis)
                      for j in range(size))

    rank_f = vector_rank(f_basis, states)
    rank_j1 = vector_rank(j1_range, states)
    rank_j2 = vector_rank(j2_range, states)
    rank_union = vector_rank(j1_range + j2_range, states)
    intersection = rank_j1 + rank_j2 - rank_union
    f_j1_union = vector_rank(f_basis + j1_range, states)
    f_j2_union = vector_rank(f_basis + j2_range, states)
    cross = tuple(tuple(inner(left, right) for right in j2_range)
                  for left in j1_range)
    self_gram = tuple(tuple(inner(left, right) for right in f_basis)
                      for left in f_basis)
    cross_rank = integer_rank(cross)
    q_j1_union = vector_rank(q_vectors + j1_range, states)
    q_j2_union = vector_rank(q_vectors + j2_range, states)

    print("pairing / Q / F =", pairing, size, rank_f, flush=True)
    print("range ranks J1F / J2F / intersection =",
          rank_j1, rank_j2, intersection, flush=True)
    print("range contained in Q =",
          q_j1_union == size, q_j2_union == size, flush=True)
    print("range equals F =",
          f_j1_union == rank_f, f_j2_union == rank_f, flush=True)
    print("source self Gram =", self_gram, flush=True)
    print("cross matrix / rank =", cross, cross_rank, flush=True)
    print("F basis supports =", tuple(
        tuple(sorted((row, vector, coefficient)
                     for (row, vector), coefficient in basis.items()))
        for basis in f_basis
    ), flush=True)
    print("J1 F supports =", tuple(
        tuple(sorted((row, vector, coefficient)
                     for (row, vector), coefficient in basis.items()))
        for basis in j1_range
    ), flush=True)
    print("J2 F supports =", tuple(
        tuple(sorted((row, vector, coefficient)
                     for (row, vector), coefficient in basis.items()))
        for basis in j2_range
    ), flush=True)


def main():
    profile(1)
    profile(0)


if __name__ == "__main__":
    main()
