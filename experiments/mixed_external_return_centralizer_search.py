"""Bounded search for active mixed external returns centralizing a Singer head.

This is a finite F_2 label-matrix probe.  It does not authenticate reservoir
gauges or assert a full EL20 representation.
"""

from collections import deque


COORDS = (2, 4, 5, 6, 7, 8, 9)
INDEX = {coordinate: index for index, coordinate in enumerate(COORDS)}
IDENTITY = tuple(1 << index for index in range(len(COORDS)))
ARROWS = (
    (6, 5), (5, 4), (4, 2), (8, 2), (9, 4),
    (9, 2), (9, 7), (5, 7), (6, 7), (6, 8),
)
EXTERNAL = (
    (4, 7), (5, 8), (6, 9), (7, 2),
    (8, 4), (8, 7), (9, 5), (9, 8),
)
MAX_DEPTH = 10
MAX_STATES = 500_000


def multiply(left, right):
    product = []
    for left_row in left:
        row = 0
        for index in range(len(COORDS)):
            if (left_row >> index) & 1:
                row ^= right[index]
        product.append(row)
    return tuple(product)


def inverse(matrix):
    size = len(COORDS)
    rows = [matrix[index] | (1 << (size + index)) for index in range(size)]
    for column in range(size):
        pivot = next(index for index in range(column, size) if (rows[index] >> column) & 1)
        rows[column], rows[pivot] = rows[pivot], rows[column]
        for index in range(size):
            if index != column and ((rows[index] >> column) & 1):
                rows[index] ^= rows[column]
    return tuple(row >> size for row in rows)


def transvection(source, target):
    matrix = list(IDENTITY)
    matrix[INDEX[target]] ^= 1 << INDEX[source]
    return tuple(matrix)


def swap(first, second):
    matrix = list(IDENTITY)
    a = INDEX[first]
    b = INDEX[second]
    matrix[a] = 1 << b
    matrix[b] = 1 << a
    return tuple(matrix)


def closure(generators, cap=MAX_STATES):
    seen = {IDENTITY}
    queue = deque((IDENTITY,))
    while queue:
        current = queue.popleft()
        for generator in generators:
            successor = multiply(current, generator)
            if successor not in seen:
                seen.add(successor)
                if len(seen) > cap:
                    raise RuntimeError(f"closure exceeded cap {cap}")
                queue.append(successor)
    return seen


def commutes(left, right):
    return multiply(left, right) == multiply(right, left)


def format_word(word):
    return " ".join(f"x_{EXTERNAL[index][1]}{EXTERNAL[index][0]}" for index in word)


def search_row(number, singer, fixed):
    generators = tuple(transvection(*arrow) for arrow in EXTERNAL)
    l0_generators = tuple(transvection(*arrow) for arrow in ARROWS)
    spectator = closure(l0_generators + tuple(generators[index] for index in fixed))
    print(f"row {number}: spectator closure size {len(spectator)}")

    seen = {IDENTITY}
    frontier = [(IDENTITY, (), -1)]
    hits = []
    for depth in range(1, MAX_DEPTH + 1):
        next_frontier = []
        for current, word, last in frontier:
            for index, generator in enumerate(generators):
                if index == last:
                    continue
                successor = multiply(current, generator)
                if successor in seen:
                    continue
                seen.add(successor)
                if len(seen) > MAX_STATES:
                    print(f"row {number}: state cap reached at depth {depth}")
                    return
                successor_word = word + (index,)
                if commutes(successor, singer) and successor not in spectator:
                    hits.append((depth, successor_word, successor))
                next_frontier.append((successor, successor_word, index))
        print(f"row {number}: depth {depth}, states {len(seen)}, active centralizers {len(hits)}")
        if hits:
            for hit_depth, word, _ in hits[:12]:
                print(f"  depth {hit_depth}: {format_word(word)}")
            return
        frontier = next_frontier
        if not frontier:
            break
    print(f"row {number}: no active centralizer through depth {MAX_DEPTH}")


def main():
    # Matrix convention matches external_return_whitehead_orbit_audit.py.
    j1 = swap(7, 8)
    t1 = multiply(multiply(j1, transvection(4, 8)), transvection(7, 4))
    j2 = swap(8, 9)
    t2 = multiply(multiply(j2, transvection(5, 9)), transvection(8, 5))
    assert multiply(t1, inverse(t1)) == IDENTITY
    assert multiply(t2, inverse(t2)) == IDENTITY
    search_row(1, t1, (2, 6))  # x_59 and x_96 in EXTERNAL order.
    search_row(2, t2, (3, 0))  # x_27 and x_74 in EXTERNAL order.


if __name__ == "__main__":
    main()
