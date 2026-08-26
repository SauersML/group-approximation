"""Test a nontrivial GL4(2)-stabilizer type of the native quarter Gram.

Run only through the MSI wrapper.  The pairing-one character orbit has
stabilizer GL4(2).  This script induces its permutation representation on
the 15 nonzero vectors of the fixed four-space, imposes the complete signed
L0 packet, cuts by the literal r and l signs, and computes the J1/J2 cross
matrix.  It tests a genuine nontrivial stabilizer multiplicity profile,
unlike the scalar-fiber adjacent-character audit.
"""

from collections import deque
from fractions import Fraction

from full_q_moving_gl8_permutation_audit import (
    integer_rank,
)


IDENTITY = tuple(1 << index for index in range(5))


def multiply(left, right):
    answer = []
    for left_row in left:
        row = 0
        for index in range(5):
            if (left_row >> index) & 1:
                row ^= right[index]
        answer.append(row)
    return tuple(answer)


def apply(matrix, vector):
    answer = 0
    for row, mask in enumerate(matrix):
        if (mask & vector).bit_count() & 1:
            answer |= 1 << row
    return answer


def inverse(matrix):
    answer = IDENTITY
    power = matrix
    while power != IDENTITY:
        answer = multiply(answer, matrix)
        power = multiply(power, matrix)
    return answer


def row_apply(row, matrix):
    answer = 0
    for index in range(5):
        if (row >> index) & 1:
            answer ^= matrix[index]
    return answer


def transvection(source, target):
    matrix = list(IDENTITY)
    matrix[target] ^= 1 << source
    return tuple(matrix)


def swap(left, right):
    matrix = list(IDENTITY)
    matrix[left], matrix[right] = matrix[right], matrix[left]
    return tuple(matrix)


def state_action(matrix, state):
    row, vector = state
    return row_apply(row, inverse(matrix)), apply(matrix, vector)


def orbit_transporters():
    generators = tuple(transvection(i, j)
                       for i in range(5) for j in range(5) if i != j)
    base = (1, 1)
    transport = {base: IDENTITY}
    queue = deque((base,))
    while queue:
        state = queue.popleft()
        for generator in generators:
            successor = state_action(generator, state)
            if successor not in transport:
                transport[successor] = multiply(generator, transport[state])
                queue.append(successor)
    assert len(transport) == 496
    return base, transport


def main():
    base, transport = orbit_transporters()
    fiber = tuple(range(2, 32, 2))
    extended_states = tuple((state, value)
                            for state in sorted(transport) for value in fiber)

    actor_cache = {}

    def actor(matrix):
        if matrix in actor_cache:
            return actor_cache[matrix]
        permutation = {}
        for state, value in extended_states:
            successor = state_action(matrix, state)
            cocycle = multiply(
                multiply(inverse(transport[successor]), matrix),
                transport[state],
            )
            assert state_action(cocycle, base) == base
            next_value = apply(cocycle, value)
            assert next_value in fiber
            permutation[(state, value)] = (successor, next_value)
        actor_cache[matrix] = permutation
        return permutation

    identity_phase = lambda _extended: 0
    coordinate_phase = lambda side, bit: (
        lambda extended: (extended[0][side] >> bit) & 1
    )
    identity_permutation = {state: state for state in extended_states}
    c = actor(transvection(1, 3))
    v = actor(transvection(1, 0))
    signed_generators = (
        (identity_permutation, coordinate_phase(1, 0), 1),
        (identity_permutation, coordinate_phase(0, 0), 1),
        (identity_permutation, lambda _state: 1, 1),
        (identity_permutation, identity_phase, 0),
        (identity_permutation, coordinate_phase(0, 3), 0),
        (identity_permutation, identity_phase, 0),
        (c, identity_phase, 0),
        (v, identity_phase, 0),
        (identity_permutation, coordinate_phase(1, 1), 0),
        (identity_permutation, coordinate_phase(1, 2), 0),
    )

    unseen = set(extended_states)
    q_basis = []
    component_of = {}
    while unseen:
        start = min(unseen)
        signs = {start: 0}
        queue = deque((start,))
        consistent = True
        while queue:
            state = queue.popleft()
            for permutation, phase, wanted in signed_generators:
                successor = permutation[state]
                successor_sign = signs[state] ^ phase(state) ^ wanted
                if successor in signs:
                    consistent &= signs[successor] == successor_sign
                else:
                    signs[successor] = successor_sign
                    queue.append(successor)
        unseen.difference_update(signs)
        if consistent:
            index = len(q_basis)
            for state in signs:
                component_of[state] = index
            q_basis.append(signs)

    def component_action(permutation, diagonal_phase=None):
        image = []
        for component in q_basis:
            start, start_sign = next(iter(component.items()))
            successor = permutation[start]
            target = component_of[successor]
            target_sign = q_basis[target][successor]
            phase = diagonal_phase(start) if diagonal_phase else 0
            relative = start_sign ^ target_sign ^ phase
            for state, sign in component.items():
                moved = permutation[state]
                moved_phase = diagonal_phase(state) if diagonal_phase else 0
                assert q_basis[target][moved] == (sign ^ moved_phase ^ relative)
            image.append((target, relative))
        return tuple(image)

    r_perm = actor(transvection(2, 0))
    j1_perm = actor(swap(1, 2))
    j2_perm = actor(swap(2, 3))
    r_on_q = component_action(r_perm)
    l_on_q = component_action(identity_permutation, coordinate_phase(1, 3))

    l_positive = {index for index, (target, sign) in enumerate(l_on_q)
                  if target == index and sign == 0}
    assert all(target == index for index, (target, _sign) in enumerate(l_on_q))

    f_basis = []
    unseen_components = set(l_positive)
    while unseen_components:
        index = min(unseen_components)
        target, sign = r_on_q[index]
        assert target in l_positive
        if target == index:
            if sign == 0:
                f_basis.append({state: (-1 if phase else 1)
                                for state, phase in q_basis[index].items()})
            unseen_components.remove(index)
            continue
        target_back, back_sign = r_on_q[target]
        assert target_back == index and back_sign == sign
        vector = {state: (-1 if phase else 1)
                  for state, phase in q_basis[index].items()}
        coefficient = -1 if sign else 1
        for state, phase in q_basis[target].items():
            vector[state] = coefficient * (-1 if phase else 1)
        f_basis.append(vector)
        unseen_components.remove(index)
        unseen_components.remove(target)

    def move(vector, permutation):
        return {permutation[state]: coefficient
                for state, coefficient in vector.items()}

    def inner(left, right):
        return sum(coefficient * left.get(state, 0)
                   for state, coefficient in right.items())

    j1_basis = tuple(move(vector, j1_perm) for vector in f_basis)
    j2_basis = tuple(move(vector, j2_perm) for vector in f_basis)
    self_gram = tuple(tuple(inner(left, right) for right in f_basis)
                      for left in f_basis)
    cross = tuple(tuple(inner(left, right) for right in j2_basis)
                  for left in j1_basis)
    norms = tuple(self_gram[index][index]
                  for index in range(len(f_basis)))
    energy = sum(
        Fraction(cross[left][right] ** 2,
                 norms[left] * norms[right])
        for left in range(len(f_basis))
        for right in range(len(f_basis))
    )
    print("stabilizer permutation fiber / total dimension =",
          len(fiber), len(extended_states), flush=True)
    print("Q rank / F rank =", len(q_basis), len(f_basis), flush=True)
    print("self diagonal =", tuple(self_gram[i][i]
                                    for i in range(len(f_basis))), flush=True)
    print("cross rank / F rank =", integer_rank(cross), len(f_basis), flush=True)
    print("cross energy / relative energy =", energy,
          energy / len(f_basis), flush=True)
    # The 15-point permutation fiber is 1 plus its irreducible 14-dimensional
    # zero-sum constituent.  The scalar fiber has Q/F ranks 12/3, cross rank
    # 3, and energy 3/4 (the companion adjacent-character audit).  Block
    # additivity therefore gives the exact nontrivial-constituent profile.
    standard_q_rank = len(q_basis) - 12
    standard_f_rank = len(f_basis) - 3
    standard_cross_rank = integer_rank(cross) - 3
    standard_energy = energy - Fraction(3, 4)
    print("14-dimensional stabilizer constituent Q / F / cross rank =",
          standard_q_rank, standard_f_rank, standard_cross_rank, flush=True)
    print("14-dimensional stabilizer constituent energy / relative =",
          standard_energy, standard_energy / standard_f_rank, flush=True)
    print("cross matrix =", cross, flush=True)


if __name__ == "__main__":
    main()
