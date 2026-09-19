"""Exact two-endpoint signed-source character audit.  Run on MSI only."""

from collections import deque

from signed_hecke_root_normalizer_audit import (
    COORDS, GENERATORS, IDENTITY, INDEX, multiply,
)


def parity_table_and_character_masks():
    parity = {IDENTITY: 0}
    queue = deque((IDENTITY,))
    relations = set()
    while queue:
        current = queue.popleft()
        for index, generator in enumerate(GENERATORS):
            successor = multiply(current, generator)
            word = parity[current] ^ (1 << index)
            if successor in parity:
                relations.add(parity[successor] ^ word)
            else:
                parity[successor] = word
                queue.append(successor)
    assert len(parity) == 8192
    masks = tuple(
        mask for mask in range(1 << len(GENERATORS))
        if all((mask & relation).bit_count() % 2 == 0 for relation in relations)
    )
    return parity, masks


def character(parity, generator_bits):
    mask = sum(1 << index for index in generator_bits)
    return {g: (word & mask).bit_count() % 2 for g, word in parity.items()}


def fixes_coordinate(matrix, coordinate):
    r = INDEX[coordinate]
    for j in range(len(COORDS)):
        expected = 1 if j == r else 0
        if ((matrix[r] >> j) & 1) != expected:
            return False
        if ((matrix[j] >> r) & 1) != expected:
            return False
    return True


def main():
    parity, character_masks = parity_table_and_character_masks()
    lam = character(parity, {0, 1, 2})
    xi2 = character(parity, {2})       # negative only on 4 -> 2
    xi4 = character(parity, {1})       # negative only on 5 -> 4

    l0 = set(lam)
    k2 = {g for g in l0 if fixes_coordinate(g, 2)}
    k4 = {g for g in l0 if fixes_coordinate(g, 4)}
    k24 = k2 & k4

    assert len(k2) == 256
    assert len(k4) == 512
    assert all(xi2[g] == 0 for g in k2)
    assert all(xi4[g] == 0 for g in k4)
    assert any(xi4[g] for g in k2)

    annihilator_k2 = tuple(mask for mask in character_masks if all(
        (parity[g] & mask).bit_count() % 2 == 0 for g in k2
    ))
    annihilator_k4 = tuple(mask for mask in character_masks if all(
        (parity[g] & mask).bit_count() % 2 == 0 for g in k4
    ))
    annihilator_both = tuple(mask for mask in character_masks if all(
        (parity[g] & mask).bit_count() % 2 == 0 for g in k2 | k4
    ))

    profiles = {
        tuple((lam[g] ^ (a & xi2[g]) ^ (b & xi4[g])) for g in GENERATORS)
        for a in (0, 1) for b in (0, 1)
    }
    assert len(profiles) == 4

    endpoint_representatives = (
        (65, 74, 4, 8, 16, 32, 64),
        (73, 2, 4, 8, 16, 32, 64),
        (73, 74, 4, 8, 16, 32, 64),
    )
    detector_values = tuple(
        (representative, lam[representative], xi2[representative], xi4[representative])
        for representative in endpoint_representatives
    )
    detector_character_separators = tuple(
        (representative, sum(
            (parity[representative] & mask).bit_count() % 2
            for mask in character_masks
        ), parity[representative])
        for representative in endpoint_representatives
    )

    # Four character atoms indexed by (a,b).  The two endpoint Whiteheads
    # flip the corresponding bit.  Their images of the (0,0) atom are
    # distinct and orthogonal, and the three-way meet is zero.
    atom = {(a, b): 2 * a + b for a in (0, 1) for b in (0, 1)}
    q = 1 << atom[(0, 0)]
    q2 = 1 << atom[(1, 0)]
    q4 = 1 << atom[(0, 1)]
    q24 = 1 << atom[(1, 1)]
    assert q & q2 == q & q4 == q2 & q4 == 0
    assert q & q2 & q4 == 0

    print("|K2| =", len(k2))
    print("|K4| =", len(k4))
    print("|K2 intersect K4| =", len(k24))
    print("number of L0 characters =", len(character_masks))
    print("characters trivial on K2 =", len(annihilator_k2), annihilator_k2)
    print("characters trivial on K4 =", len(annihilator_k4), annihilator_k4)
    print("characters trivial on K2 and K4 =", len(annihilator_both), annihilator_both)
    print("xi2 nontrivial on K4 =", sum(xi2[g] for g in k4))
    print("xi4 nontrivial on K2 =", sum(xi4[g] for g in k2))
    print("four distinct source characters =", len(profiles))
    print("endpoint detector (lambda,xi2,xi4) values =", detector_values)
    print("endpoint detector character separators =", detector_character_separators)
    print("Q,Q2,Q4,Q24 atom masks =", q, q2, q4, q24)
    print("two-endpoint common meet = 0")


if __name__ == "__main__":
    main()
