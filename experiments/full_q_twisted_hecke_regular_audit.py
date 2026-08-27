"""Faithful-regular audit of the full-Q native twisted Hecke corner.

Run only through the MSI wrapper.  The finite eight-summand binary chart is
the one used by ``full_q_moving_gl8_permutation_audit``.  We form

    K=<L0,r,l>,  F=e_(L0,lambda0)(1+r)(1+l)/4,  g=J1 J2,

enumerate the left K-cosets of H=<K,g> by a pattern-group row normal form,
and construct the exact twisted Hecke algebra F C[H] F.  This audits only
the relative-word interface H; it does not assert extension of its simple
types to a larger packet containing J1, J2, B2, and B3 separately.
"""

from collections import Counter, deque
from math import gcd

from full_q_moving_gl8_permutation_audit import (
    DIM,
    IDENTITY,
    closure_with_character,
    multiply,
    swap,
    transvection,
)


def pattern_normalizer(character):
    """Return the canonical left-K representative and its character phase.

    K is the full pattern group for the acyclic arrow closure below.  Left
    multiplication performs the corresponding predecessor row additions.
    Reducing each row to the least integer in its predecessor affine space
    gives one canonical representative per left coset.
    """

    q2, q4, q5, q6, u1, u2, u3, u4 = range(DIM)
    order = (q2, u1, q4, u2, u3, q5, q6, u4)
    predecessors = {
        q2: (),
        u1: (),
        q4: (q2,),
        u2: (q2,),
        u3: (q2, q4, u1),
        q5: (q2, q4, u1, u2),
        q6: (q2, q4, u1, u2, u3, q5),
        u4: (),
    }

    def normalize(matrix):
        rows = list(matrix)
        multiplier = list(IDENTITY)
        for target in order:
            sources = predecessors[target]
            best_row = rows[target]
            best_mask = 0
            for mask in range(1, 1 << len(sources)):
                candidate = rows[target]
                for bit, source in enumerate(sources):
                    if (mask >> bit) & 1:
                        candidate ^= rows[source]
                if candidate < best_row:
                    best_row = candidate
                    best_mask = mask
            if best_mask:
                for bit, source in enumerate(sources):
                    if (best_mask >> bit) & 1:
                        rows[target] ^= rows[source]
                        multiplier[target] ^= multiplier[source]
        multiplier = tuple(multiplier)
        assert multiplier in character
        return tuple(rows), character[multiplier]

    return normalize


def main():
    q2, q4, q5, q6, u1, u2, u3, u4 = range(DIM)
    arrows = (
        (q5, q6), (q4, q5), (q2, q4),
        (q2, u2), (q4, u3), (q2, u3), (u1, u3),
        (u1, q5), (u1, q6), (u2, q6),
        (u2, q5), (u3, q6),
    )
    k_generators = tuple(transvection(*arrow) for arrow in arrows)
    character = closure_with_character(k_generators, 3)
    assert len(character) == 1 << 15, len(character)
    normalize = pattern_normalizer(character)

    # Authenticate the normal form on every element of K.
    for element, phase in character.items():
        canonical, canonical_phase = normalize(element)
        assert canonical == IDENTITY
        assert canonical_phase == phase

    j1 = swap(u1, u2)
    j2 = swap(u2, u3)
    g = multiply(j1, j2)
    g_inverse = multiply(g, g)
    assert multiply(g_inverse, g) == IDENTITY

    # Enumerate K\H, H=<K,g>, by right multiplication.
    coset_generators = k_generators + (g, g_inverse)
    representatives = [IDENTITY]
    index = {IDENTITY: 0}
    queue = deque((IDENTITY,))
    while queue:
        representative = queue.popleft()
        for generator in coset_generators:
            successor, _phase = normalize(multiply(representative, generator))
            if successor not in index:
                index[successor] = len(representatives)
                representatives.append(successor)
                queue.append(successor)

    # Decompose K\H into right-K orbits, i.e. double cosets.  A double
    # coset contributes to the twisted corner exactly when the right
    # chi-eigenvector is sign-consistent around the orbit.
    k_generator_phases = tuple(index < 3 for index in range(len(k_generators)))
    unseen = set(range(len(representatives)))
    compatible_orbits = []
    incompatible_sizes = []
    coset_to_compatible = {}
    while unseen:
        start = min(unseen)
        signs = {start: 0}
        orbit_queue = deque((start,))
        consistent = True
        while orbit_queue:
            state = orbit_queue.popleft()
            for generator, generator_phase in zip(
                    k_generators, k_generator_phases):
                target, normalizer_phase = normalize(
                    multiply(representatives[state], generator)
                )
                target_index = index[target]
                target_sign = (
                    signs[state] ^ generator_phase ^ normalizer_phase
                )
                if target_index in signs:
                    if signs[target_index] != target_sign:
                        consistent = False
                else:
                    signs[target_index] = target_sign
                    orbit_queue.append(target_index)
        unseen.difference_update(signs)
        if consistent:
            compatible_index = len(compatible_orbits)
            compatible_orbits.append(signs)
            for state in signs:
                coset_to_compatible[state] = compatible_index
        else:
            incompatible_sizes.append(len(signs))

    # Expand h e_K=F g F in the signed left-coset basis.
    stencil_numerators = {}
    for element, element_phase in character.items():
        target, target_phase = normalize(multiply(g, element))
        target_index = index[target]
        stencil_numerators[target_index] = (
            stencil_numerators.get(target_index, 0)
            + (-1 if element_phase ^ target_phase else 1)
        )
    stencil_numerators = {
        target: value
        for target, value in stencil_numerators.items()
        if value
    }
    common = 0
    for value in stencil_numerators.values():
        common = gcd(common, abs(value))

    size = len(representatives)

    # Exact source-kernel witness.  The missing root a:q2->u1 normalizes
    # the signed pattern group, and g carries it to the positive K-root
    # d:q2->u2.  At stencil level this is the literal identity h a=h.
    a = transvection(q2, u1)
    a_coset, _a_phase = normalize(a)
    assert index[a_coset] != 0
    translated_stencil = {}
    for state, numerator in stencil_numerators.items():
        target, phase = normalize(multiply(representatives[state], a))
        target_index = index[target]
        translated_stencil[target_index] = (
            translated_stencil.get(target_index, 0)
            + (-numerator if phase else numerator)
        )
    translated_stencil = {
        state: value for state, value in translated_stencil.items() if value
    }
    assert translated_stencil == stencil_numerators

    # Build the exact 52-dimensional twisted Hecke algebra.  For each
    # compatible double coset use the signed orbit sum c_D.  These have
    # disjoint supports and form a basis of F C[H] F.
    hecke_basis = []
    for orbit in compatible_orbits:
        hecke_basis.append({
            state: (-1 if sign else 1)
            for state, sign in orbit.items()
        })
    identity_hecke = coset_to_compatible[0]
    g_coset, _g_phase = normalize(g)
    h_hecke = coset_to_compatible[index[g_coset]]

    def hecke_product(left, right):
        raw = {}
        for left_state, left_sign in hecke_basis[left].items():
            left_rep = representatives[left_state]
            for right_state, right_sign in hecke_basis[right].items():
                product, phase = normalize(multiply(
                    left_rep, representatives[right_state]
                ))
                product_state = index[product]
                value = left_sign * right_sign * (-1 if phase else 1)
                raw[product_state] = raw.get(product_state, 0) + value
        raw = {state: value for state, value in raw.items() if value}
        answer = {}
        seen = Counter()
        for state, value in raw.items():
            assert state in coset_to_compatible
            component = coset_to_compatible[state]
            scalar = value * (-1 if compatible_orbits[component][state] else 1)
            if component in answer:
                assert answer[component] == scalar
            else:
                answer[component] = scalar
            seen[component] += 1
        for component in answer:
            assert seen[component] == len(compatible_orbits[component])
        return answer

    hecke_size = len(hecke_basis)
    multiplication = tuple(
        tuple(hecke_product(left, right) for right in range(hecke_size))
        for left in range(hecke_size)
    )
    assert multiplication[identity_hecke][h_hecke] == {h_hecke: 1}
    assert multiplication[h_hecke][identity_hecke] == {h_hecke: 1}

    def primitive(vector):
        divisor = 0
        for value in vector:
            divisor = gcd(divisor, abs(value))
        if divisor > 1:
            vector = [value // divisor for value in vector]
        first = next((value for value in vector if value), 0)
        if first < 0:
            vector = [-value for value in vector]
        return vector

    echelon = {}
    pending = deque()

    def reduce_vector(vector):
        vector = list(vector)
        for pivot in sorted(echelon):
            if vector[pivot]:
                row = echelon[pivot]
                vector = [
                    row[pivot] * value - vector[pivot] * row_value
                    for value, row_value in zip(vector, row)
                ]
                vector = primitive(vector)
        return vector

    def add_to_ideal(vector):
        vector = reduce_vector(vector)
        pivot = next((index_ for index_, value in enumerate(vector) if value), None)
        if pivot is None:
            return False
        vector = primitive(vector)
        echelon[pivot] = vector
        pending.append(vector)
        return True

    h_vector = [0] * hecke_size
    h_vector[h_hecke] = 1
    add_to_ideal(h_vector)

    def multiply_vector(left_basis, vector, on_left):
        answer = [0] * hecke_size
        for right_basis, coefficient in enumerate(vector):
            if not coefficient:
                continue
            product = (
                multiplication[left_basis][right_basis]
                if on_left else multiplication[right_basis][left_basis]
            )
            for target, structure_coefficient in product.items():
                answer[target] += coefficient * structure_coefficient
        return answer

    while pending:
        vector = pending.popleft()
        for basis_element in range(hecke_size):
            add_to_ideal(multiply_vector(basis_element, vector, True))
            add_to_ideal(multiply_vector(basis_element, vector, False))

    identity_vector = [0] * hecke_size
    identity_vector[identity_hecke] = 1
    identity_remainder = reduce_vector(identity_vector)
    ideal_contains_identity = not any(identity_remainder)
    print("K order / H:K index / H order =",
          len(character), size, len(character) * size, flush=True)
    print("double cosets / compatible / incompatible =",
          len(compatible_orbits) + len(incompatible_sizes),
          len(compatible_orbits), len(incompatible_sizes), flush=True)
    print("compatible orbit-size histogram =",
          tuple(sorted(Counter(len(orbit) for orbit in compatible_orbits).items())),
          flush=True)
    print("incompatible orbit-size histogram =",
          tuple(sorted(Counter(incompatible_sizes).items())), flush=True)
    print("double-coset left-coset count =", len(stencil_numerators), flush=True)
    print("stencil numerator gcd / values =", common,
          tuple(sorted(set(stencil_numerators.values()))), flush=True)
    print("exact source kernel h(1-a)=0 / a coset =",
          True, index[a_coset], flush=True)
    print("Hecke dimension / identity index / h index =",
          hecke_size, identity_hecke, h_hecke, flush=True)
    print("two-sided ideal dimension / contains identity =",
          len(echelon), ideal_contains_identity, flush=True)
    print("identity remainder support =", tuple(
        (index_, value)
        for index_, value in enumerate(identity_remainder)
        if value
    ), flush=True)


if __name__ == "__main__":
    main()
