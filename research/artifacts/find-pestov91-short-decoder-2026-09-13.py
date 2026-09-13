"""Breadth-first search of SL_3(F_2)^2 for short decoder certificates.

Run on MSI with Python 3.12. Uppercase C denotes c^{-1}; t is involutory.
"""
from collections import deque
import json
import time


def product(left, right):
    rows = [(right >> (3 * i)) & 7 for i in range(3)]
    result = 0
    for i in range(3):
        row = 0
        for j in range(3):
            if (left >> (3 * i + j)) & 1:
                row ^= rows[j]
        result |= row << (3 * i)
    return result


def root(i, j):
    return 273 ^ (1 << (3 * i + j))


def swap(i, j):
    return product(product(root(i, j), root(j, i)), root(i, j))


if __name__ == '__main__':
    started = time.monotonic()
    unit = 273  # diagonal bits 0,4,8
    c = (1 << 2) | (1 << 3) | (1 << 5) | (1 << 7)
    ci = unit
    for _ in range(6):
        ci = product(ci, c)
    assert product(c, ci) == unit
    generators = [('c', c, c), ('C', ci, ci), ('t', root(0, 1), root(0, 2))]
    actions = [(letter, [product(value, a) for value in range(512)],
                [product(value, b) for value in range(512)])
               for letter, a, b in generators]
    start = unit | (unit << 9)
    parent = {start: None}
    queue = deque([start])
    while queue:
        current = queue.popleft()
        for letter, left, right in actions:
            following = left[current & 511] | (right[current >> 9] << 9)
            if following not in parent:
                parent[following] = (current, letter)
                queue.append(following)
    assert len(parent) == 168 ** 2
    targets = {
        'root_zero': (root(0, 1), unit),
        'root_one': (unit, root(0, 1)),
        'swap_23': (swap(1, 2), swap(1, 2)),
        'swap_13': (swap(0, 2), swap(0, 2)),
        'bridge': (product(swap(0, 2), swap(1, 2)),
                   product(swap(0, 2), swap(1, 2))),
    }
    certificates = {}
    for name, (a, b) in targets.items():
        current = a | (b << 9)
        letters = []
        while parent[current] is not None:
            current, letter = parent[current]
            letters.append(letter)
        word = ''.join(reversed(letters))
        left, right = unit, unit
        table = {letter: (a, b) for letter, a, b in generators}
        for letter in word:
            ga, gb = table[letter]
            left, right = product(left, ga), product(right, gb)
        assert (left, right) == (a, b)
        certificates[name] = {'word': word, 'length': len(word), 'p0_matrix': a, 'p1_matrix': b}
    print(json.dumps({'group_size': len(parent), 'generator_alphabet': ['c', 'C', 't'],
                      'certificates': certificates,
                      'seconds': round(time.monotonic() - started, 6)}, indent=2))
