#!/usr/bin/env python3
"""Finite checks and a reference implementation for R-star two-tail peeling."""

from itertools import combinations, product


RSTAR = tuple(
    word
    for word in product((0, 1), repeat=4)
    if sum(word) % 2 == 1 and word != (1, 0, 0, 0)
)


def maximal_cap(tail_coordinate: int) -> tuple[tuple[int, ...], ...]:
    """The cap x_j=1, where tail_coordinate is one of 1,2,3 (zero based)."""
    assert tail_coordinate in (1, 2, 3)
    return tuple(word for word in RSTAR if word[tail_coordinate] == 1)


def verify_two_coordinate_sections() -> None:
    """Check that a fixed unused-tail cap covers every retained fibre."""
    positions = range(4)
    for retained_size in range(3):
        for retained in combinations(positions, retained_size):
            unused_tail = next(j for j in (1, 2, 3) if j not in retained)
            cap = maximal_cap(unused_tail)
            projection = {
                tuple(word[j] for j in retained)
                for word in cap
            }
            assert projection == set(product((0, 1), repeat=retained_size))


def two_tail_kernel(
    contexts: dict[str, tuple[str, ...]], pinned: frozenset[str] = frozenset()
) -> tuple[frozenset[str], tuple[str, ...]]:
    """Return the terminal contexts and one valid deletion order.

    A context is deleted when at least two of its unpinned variables have
    active occurrence degree one.
    """
    active = set(contexts)
    deletion_order: list[str] = []
    while True:
        degree: dict[str, int] = {}
        for name in active:
            for variable in contexts[name]:
                degree[variable] = degree.get(variable, 0) + 1
        eligible = sorted(
            name
            for name in active
            if sum(
                variable not in pinned and degree[variable] == 1
                for variable in contexts[name]
            )
            >= 2
        )
        if not eligible:
            break
        name = eligible[0]
        active.remove(name)
        deletion_order.append(name)
    return frozenset(active), tuple(deletion_order)


def smoke_test_kernel() -> None:
    # A cycle whose rows share two variables with neighbours but have two
    # leaves each peels completely; this is stricter than ordinary 2-core.
    cycle = {
        "c0": ("v0", "v1", "a0", "b0"),
        "c1": ("v1", "v2", "a1", "b1"),
        "c2": ("v2", "v0", "a2", "b2"),
    }
    kernel, order = two_tail_kernel(cycle)
    assert not kernel and len(order) == 3

    # Three shared coordinates per row survive.
    dense = {
        "c0": ("v0", "v1", "v2", "a0"),
        "c1": ("v0", "v1", "v2", "a1"),
    }
    kernel, order = two_tail_kernel(dense)
    assert kernel == frozenset(dense) and not order


if __name__ == "__main__":
    verify_two_coordinate_sections()
    smoke_test_kernel()
    print("verified all retained coordinate sets of size at most two")
    print("verified peeling and dense-kernel smoke certificates")
