"""Audit the complete moving signed-Hecke packet in its literal GL8(F2) chart.

Run through the MSI wrapper only.  The eight projective summands are

    q@2, q@4, q@5, q@6, e1@7, e2@8, e3@9, e3@2.

The first seven carry the faithful constant chart of L0.  The endpoint
Whitehead W swaps the last two relevant prefix summands, J1 swaps e1@7 and
e2@8, and M=J2 B3 A2 acts on q@5,e2@8,e3@9,e3@2.  We use the 496- and
465-state monomial representations induced from the two nonzero
vector/covector character orbits of the four-block parabolic.  Integer Gram
rank is enough: diagonal orbit-size rescaling does not change whether
Q W Q has a kernel.
"""

from collections import deque


DIM = 8
IDENTITY = tuple(1 << index for index in range(DIM))


def multiply(left, right):
    product = []
    for left_row in left:
        row = 0
        for index in range(DIM):
            if (left_row >> index) & 1:
                row ^= right[index]
        product.append(row)
    return tuple(product)


def transvection(source, target):
    matrix = list(IDENTITY)
    matrix[target] ^= 1 << source
    return tuple(matrix)


def swap(left, right):
    matrix = list(IDENTITY)
    matrix[left], matrix[right] = matrix[right], matrix[left]
    return tuple(matrix)


def conjugate(actor, root):
    # All actors below are products of involutory elementary matrices.  Find
    # the inverse by the tiny finite order loop, rather than importing a
    # field-matrix package.
    inverse = IDENTITY
    power = actor
    while power != IDENTITY:
        inverse = multiply(inverse, actor)
        power = multiply(power, actor)
    return multiply(multiply(actor, root), inverse)


def closure_with_character(generators, negative_count):
    character = {IDENTITY: 0}
    queue = deque((IDENTITY,))
    while queue:
        current = queue.popleft()
        for index, generator in enumerate(generators):
            successor = multiply(current, generator)
            sign = character[current] ^ (index < negative_count)
            if successor in character:
                assert character[successor] == sign
            else:
                character[successor] = sign
                queue.append(successor)
    return character


def signed_component_basis(states, signed_generators):
    """Common eigenspace basis for signed monomial permutations.

    A basis vector is represented by its coefficient signs on one connected
    state component.  Inconsistent components contribute nothing.
    """
    state_set = set(states)
    unseen = set(states)
    basis = []
    while unseen:
        start = min(unseen)
        signs = {start: 0}
        queue = deque((start,))
        consistent = True
        while queue:
            state = queue.popleft()
            for action, phase, wanted_sign in signed_generators:
                successor = action(state)
                assert successor in state_set
                successor_sign = signs[state] ^ phase(state) ^ wanted_sign
                if successor in signs:
                    if signs[successor] != successor_sign:
                        consistent = False
                else:
                    signs[successor] = successor_sign
                    queue.append(successor)
        unseen.difference_update(signs)
        if consistent:
            basis.append(signs)
    return basis


def moving_character_model(W, J1, M, pairing):
    """One nonzero vector/covector adjacent-character orbit representation.

    Quotient the four-block parabolic's unipotent radical by its commutator.
    Apart from the fixed scalar C1 character, a character is a covector/vector
    pair (r,s) on the five-node Levi block with fixed pairing.  GL5 acts by
    (r,s)->(r g^-1,g s).  This is an exact representation of the complete
    moving packet, not merely of its return table.
    """
    levi_nodes = (2, 4, 5, 6, 7)  # q5,e1,e2,e3,e3@2 in the GL8 chart
    local = {node: index for index, node in enumerate(levi_nodes)}

    def restrict(matrix):
        rows = []
        for target in levi_nodes:
            row = 0
            for source in levi_nodes:
                if (matrix[target] >> source) & 1:
                    row |= 1 << local[source]
            rows.append(row)
        return tuple(rows)

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

    W5, J15, M5 = map(restrict, (W, J1, M))

    states = tuple(
        (row, vector)
        for row in range(1, 32)
        for vector in range(1, 32)
        if ((row & vector).bit_count() & 1) == pairing
    )
    assert len(states) == (496 if pairing else 465)

    def levi_action(matrix):
        matrix_inverse = local_inverse(matrix)
        return lambda state: (
            local_row_apply(state[0], matrix_inverse),
            local_apply(matrix, state[1]),
        )

    identity_phase = lambda _state: 0
    coordinate_phase = lambda side, bit: (
        lambda state: (state[side] >> bit) & 1
    )
    identity_action = lambda state: state

    # L0 signs in generator order C3,C2,C1,d,f,k,c,v,w,s.  C1 is the
    # fixed nontrivial scalar character and so already has phase one on all
    # states.  The skip-block roots d,k vanish in the abelianized radical.
    c_levi = restrict(transvection(4, 6))  # e1@7 -> e3@9
    v_levi = restrict(transvection(4, 2))  # e1@7 -> q@5
    signed_generators = (
        (identity_action, coordinate_phase(1, 0), 1),  # C3
        (identity_action, coordinate_phase(0, 0), 1),  # C2
        (identity_action, lambda _state: 1, 1),         # C1
        (identity_action, identity_phase, 0),           # d
        (identity_action, coordinate_phase(0, 3), 0),  # f
        (identity_action, identity_phase, 0),           # k
        (levi_action(c_levi), identity_phase, 0),       # c
        (levi_action(v_levi), identity_phase, 0),       # v
        (identity_action, coordinate_phase(1, 1), 0),  # w
        (identity_action, coordinate_phase(1, 2), 0),  # s
    )
    q_basis = signed_component_basis(states, signed_generators)

    def compressed_gram(actor):
        actor_action = levi_action(actor)
        gram = []
        for left in q_basis:
            row = []
            for right in q_basis:
                value = 0
                for state, right_sign in right.items():
                    moved = actor_action(state)
                    if moved in left:
                        value += (-1 if right_sign ^ left[moved] else 1)
                row.append(value)
            gram.append(row)
        return gram, integer_rank(gram)

    gram, rank = compressed_gram(W5)
    j1_gram, j1_rank = compressed_gram(J15)

    # These checks ensure all three native actors really act on this same
    # state set.  J1 and M need not occur in the displayed Gram to constrain
    # the representation: their monomial operators are part of it exactly.
    assert {levi_action(J15)(state) for state in states} == set(states)
    assert {levi_action(M5)(state) for state in states} == set(states)
    print("adjacent-character pairing / states =", pairing, len(states))
    print("full-packet Q components =", len(q_basis),
          "sizes", tuple(len(component) for component in q_basis))
    print("full-packet Q signed components =", tuple(
        tuple(sorted((row, vector, sign)
                     for (row, vector), sign in component.items()))
        for component in q_basis
    ))
    print("full-packet integer QWQ Gram =",
          tuple(tuple(row) for row in gram))
    print("full-packet Q rank / QWQ rank / kernel =",
          len(q_basis), rank, len(q_basis) - rank)
    print("full-packet integer QJ1Q Gram =",
          tuple(tuple(row) for row in j1_gram))
    print("full-packet Q rank / QJ1Q rank / kernel =",
          len(q_basis), j1_rank, len(q_basis) - j1_rank)
    return len(q_basis), rank


def integer_rank(matrix):
    """Fraction-free rank over Q for a small integer matrix."""
    if not matrix:
        return 0
    rows = [list(row) for row in matrix]
    rank = 0
    column_count = len(rows[0])
    for column in range(column_count):
        pivot = next((row for row in range(rank, len(rows))
                      if rows[row][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        pivot_value = rows[rank][column]
        for row in range(len(rows)):
            if row == rank or rows[row][column] == 0:
                continue
            coefficient = rows[row][column]
            rows[row] = [
                pivot_value * rows[row][j] - coefficient * rows[rank][j]
                for j in range(column_count)
            ]
            common = 0
            for value in rows[row]:
                common = gcd(common, abs(value))
            if common > 1:
                rows[row] = [value // common for value in rows[row]]
        rank += 1
        if rank == len(rows):
            break
    return rank


def gcd(left, right):
    while right:
        left, right = right, left % right
    return left


def main():
    # Node order: q2,q4,q5,q6,e1@7,e2@8,e3@9,e3@2.
    q2, q4, q5, q6, e1, e2, e3, e3_at_2 = range(DIM)

    arrows = (
        (q5, q6), (q4, q5), (q2, q4),
        (q2, e2), (q4, e3), (q2, e3), (e1, e3),
        (e1, q5), (e1, q6), (e2, q6),
    )
    l0_generators = tuple(transvection(*arrow) for arrow in arrows)
    character = closure_with_character(l0_generators, 3)
    assert len(character) == 8192

    W = swap(e2, e3_at_2)
    J1 = swap(e1, e2)
    J2 = swap(e2, e3)
    B3 = transvection(q5, e3)
    A2 = transvection(e2, q5)
    M = multiply(multiply(J2, B3), A2)

    # Authenticate the exact four-bit action quoted in the endpoint audit.
    roots = (
        transvection(q5, q6),
        transvection(e2, q6),
        transvection(e3, q6),
        transvection(e3_at_2, q6),
    )
    root_lookup = {
        IDENTITY: 0,
    }
    for mask in range(1, 16):
        product = IDENTITY
        for index, root in enumerate(roots):
            if (mask >> index) & 1:
                product = multiply(product, root)
        root_lookup[product] = mask
    m_action = tuple(root_lookup[conjugate(M, root)] for root in roots)
    w_action = tuple(root_lookup[conjugate(W, root)] for root in roots)
    assert m_action == (1 ^ 4, 4, 1 ^ 2, 8), m_action
    assert w_action == (1, 8, 4, 2), w_action

    # J1 is included in the represented packet even though QWQ itself uses W.
    assert multiply(J1, J1) == IDENTITY

    print("literal actor actions M,W =", m_action, w_action)
    print("signed L0 size =", len(character))
    moving_character_model(W, J1, M, 1)
    moving_character_model(W, J1, M, 0)


if __name__ == "__main__":
    main()
