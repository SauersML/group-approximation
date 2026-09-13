"""Finite graph and delimiter checks; the group theorem is a written proof.

Run with Python 3.12 on MSI. No third-party packages are required.
"""
import itertools
import json
import time


def bad_edges(vertices, edges):
    reach = [[i == j for j in range(vertices)] for i in range(vertices)]
    for source, target in edges:
        reach[source][target] = True
    for mid in range(vertices):
        for source in range(vertices):
            for target in range(vertices):
                reach[source][target] |= reach[source][mid] and reach[mid][target]
    return [i for i, (source, target) in enumerate(edges) if not reach[target][source]]


def incidence_pairs(vertices, edges):
    pairs = set()
    for deleted in range(1 << len(edges)):
        for selected in range(1 << vertices):
            if all((deleted >> i) & 1 or not (selected & ((1 << a) | (1 << b)))
                   for i, (a, b) in enumerate(edges)):
                pairs.add((deleted, selected))
    for a in pairs:
        for b in pairs:
            assert (a[0] & b[0], a[1] & b[1]) in pairs
            assert (a[0] | b[0], a[1] | b[1]) in pairs
    return pairs


def check_delimiters(symbols):
    bits = (symbols - 1).bit_length()
    codes = ['11' + ''.join('0' + bit for bit in f'{i:0{bits}b}') + '00'
             for i in range(symbols)]
    length = 2 * bits + 4
    assert len(set(codes)) == symbols
    assert all(len(code) == length for code in codes)
    for a, b in itertools.product(codes, repeat=2):
        joined = a + b
        assert [i for i in range(len(joined) - 1) if joined[i:i + 2] == '11'] == [0, length]
    return {'symbols': symbols, 'code_length': length, 'pairs_checked': symbols ** 2}


if __name__ == '__main__':
    started = time.monotonic()
    triangle = [(0, 1), (1, 2), (0, 2)]
    common_pairs = incidence_pairs(3, triangle)
    assert len(common_pairs) == 18
    profile = [sum(deleted.bit_count() == count for deleted, _ in common_pairs)
               for count in range(4)]
    assert profile == [1, 3, 6, 8]
    orientations = []
    for reversals in itertools.product([False, True], repeat=3):
        edges = [tuple(reversed(edge)) if flip else edge
                 for edge, flip in zip(triangle, reversals)]
        assert incidence_pairs(3, edges) == common_pairs
        bad = bad_edges(3, edges)
        assert len(bad) in [0, 3]
        orientations.append({'edges': edges, 'bad_edges': bad})
    assert sum(not item['bad_edges'] for item in orientations) == 2
    two_cycle = [(0, 1), (1, 0)]
    one_edge = [(0, 1)]
    assert bad_edges(2, two_cycle) == []
    assert bad_edges(2, one_edge) == [0]
    assert len(incidence_pairs(2, two_cycle)) == 7
    assert len(incidence_pairs(2, one_edge)) == 5
    print(json.dumps({
        'triangle_orientations': orientations,
        'triangle_normal_count': 18, 'triangle_deletion_profile': profile,
        'two_cycle_normal_count': 7, 'one_edge_normal_count': 5,
        'delimiter_checks': [check_delimiters(6), check_delimiters(9)],
        'all_assertions_passed': True,
        'seconds': round(time.monotonic() - started, 6),
    }, indent=2))
