"""Exact endpoint-return audit in G_X=<L0,eight external roots>.

Run on MSI only.  Conjugacy orbits are traversed as matrix states rather
than closing all 2^21 group elements separately for every endpoint.
"""

from collections import deque

from external_return_exact_singer_centralizer import (
    ARROWS, EXTERNAL, IDENTITY, inverse, multiply, quotient_representatives,
    closure, transvection,
)


GENERATOR_ARROWS = ARROWS + EXTERNAL
GENERATORS = tuple(transvection(*arrow) for arrow in GENERATOR_ARROWS)


def conjugate(state, generator):
    # Every generator is an involutory transvection.
    return multiply(multiply(generator, state), generator)


def orbit_with_shortest_words(source, target):
    start = transvection(source, target)
    words = {start: ()}
    queue = deque((start,))
    while queue:
        state = queue.popleft()
        for index, generator in enumerate(GENERATORS):
            successor = conjugate(state, generator)
            if successor not in words:
                words[successor] = words[state] + (index,)
                queue.append(successor)
    return words


def main():
    l0_generators = tuple(transvection(*arrow) for arrow in ARROWS)
    external_generators = tuple(transvection(*arrow) for arrow in EXTERNAL)
    l0 = closure(l0_generators)
    assert len(l0) == 8192
    for external in external_generators:
        external_inverse = inverse(external)
        for generator in l0_generators:
            assert multiply(multiply(external_inverse, generator), external) in l0
    reps = quotient_representatives(l0, external_generators)
    assert len(reps) == 256
    assert len(reps) * len(l0) == 2_097_152
    print('G_X size', len(reps) * len(l0), 'quotient size', len(reps))

    cases = []
    # x_(8,ell)(y2): source ell -> target 8; native x_89(y2): 9 -> 8.
    for ell in (2, 4, 5, 6, 7):
        cases.append(('y2', ell, 8, 9, 8))
    # x_(ell,8)(y1): source 8 -> target ell; native x_78(y1): 8 -> 7.
    for ell in (2, 4, 5, 6, 9):
        cases.append(('y1', 8, ell, 8, 7))

    results = []
    orbit_cache = {}
    for label, source, target, wanted_source, wanted_target in cases:
        key = (source, target)
        orbit = orbit_cache.setdefault(key, orbit_with_shortest_words(*key))
        wanted = transvection(wanted_source, wanted_target)
        word = orbit.get(wanted)
        results.append((label, source, target, word, len(orbit)))
        if word is None:
            print(label, (source, target), 'NO', 'orbit states', len(orbit))
        else:
            arrows = tuple(GENERATOR_ARROWS[index] for index in word)
            external_count = sum(index >= len(ARROWS) for index in word)
            print(label, (source, target), 'YES', 'orbit states', len(orbit),
                  'shortest length', len(word), 'external letters', external_count,
                  'word arrows', arrows)

    assert all(word is None for _, _, _, word, _ in results)
    assert [size for _, _, _, _, size in results] == [
        256, 64, 32, 8, 128,
        8, 32, 64, 256, 128,
    ]


if __name__ == '__main__':
    main()
