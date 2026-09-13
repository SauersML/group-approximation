"""Exact word and MF-consequence solver for a fixed Sturmian seam graph.

Input JSON: {"vertices": 2, "edges": [[0,1]], "premises": ["tt"],
             "output": "c"}. Words use c,C,t,w; C denotes c inverse.
Run with Python 3.12 on MSI. The polynomial bound is in expanded word
length for each fixed graph, not compressed straight-line program size.
"""
from functools import cache, cmp_to_key
from math import isqrt
import json
from pathlib import Path
import sys


def quadratic_floor(a, b, denominator=1):
    """Floor (a+b sqrt(2))/denominator, using integers only."""
    radical = isqrt(2 * b * b)
    if b < 0:
        radical = -radical - 1
    return (a + radical) // denominator


def compare_quadratics(left, right):
    a, b = left[0] - right[0], left[1] - right[1]
    if a == b == 0:
        return 0
    return -1 if quadratic_floor(a, b) < 0 else 1


def mechanical_bit(index):
    return (quadratic_floor(1 - 2 * (index + 1), 2 * (index + 1), 2)
            - quadratic_floor(1 - 2 * index, 2 * index, 2))


@cache
def sturmian_language(length):
    if length < 1:
        raise ValueError('Language length must be positive')
    cuts = [(0, 0)] + [(isqrt(2 * j * j) + 1, -j)
                       for j in range(1, length + 1)]
    cuts.sort(key=cmp_to_key(compare_quadratics))
    cuts.append((1, 0))
    words = set()
    for left, right in zip(cuts, cuts[1:]):
        a, b = left[0] + right[0], left[1] + right[1]
        heights = [quadratic_floor(a - 2 * j, b + 2 * j, 2)
                   for j in range(length + 1)]
        words.add(tuple(y - x for x, y in zip(heights, heights[1:])))
    return frozenset(words)


UNIT = frozenset((i, i, 0) for i in range(3))
CONSTANT_ROWS = {
    'c': ((2,), (0, 2), (1,)),
    'C': ((0, 1), (2,), (0,)),
}


def window_normal_form(word, window):
    """Evaluate Laurent coefficients at the central point of a window."""
    center = len(window) // 2
    if len(window) < 2 * len(word) + 1:
        raise ValueError('Window is too short')
    coefficients = UNIT
    for letter in word:
        updated = set()
        for row, column, degree in coefficients:
            if letter in CONSTANT_ROWS:
                terms = [(j, 0) for j in CONSTANT_ROWS[letter][column]]
            elif letter == 't':
                terms = [(column, 0)]
                if column == 0:
                    terms.append((1 + window[center - degree], 0))
            elif letter == 'w':
                terms = [((1, 1), (0, -1), (2, 0))[column]]
            else:
                raise ValueError('Word alphabet is c,C,t,w')
            for target, shift in terms:
                entry = (row, target, degree + shift)
                if entry in updated:
                    updated.remove(entry)
                else:
                    updated.add(entry)
        coefficients = updated
    return frozenset(coefficients)


class SeamGraph:
    def __init__(self, vertices, edges):
        if type(vertices) is not int or vertices < 1:
            raise ValueError('vertices must be a positive integer')
        self.vertices = tuple(range(vertices))
        self.edges = tuple(tuple(edge) for edge in edges)
        for edge in self.edges:
            if len(edge) != 2 or any(type(v) is not int or v not in self.vertices
                                     for v in edge):
                raise ValueError('Each edge must contain two valid vertex indices')
        size = 2 * vertices + len(edges)
        digits = (size - 1).bit_length()
        self.codes = tuple(tuple(map(int, '11' + ''.join('0' + bit for bit in
                           format(i, f'0{digits}b')) + '00')) for i in range(size))
        self.code_length = 2 * digits + 4

    def raw_language(self, length, vertices, edge_indices):
        words = {tuple(2 * vertex + bit for bit in word)
                 for vertex in vertices for word in sturmian_language(length)}
        for edge in edge_indices:
            source, target = self.edges[edge]
            for marker in range(length):
                words.add(tuple(2 * len(self.vertices) + edge if j == marker else
                                2 * (source if j < marker else target)
                                + mechanical_bit(j - marker)
                                for j in range(length)))
        return words

    def binary_language(self, length, vertices, edge_indices):
        # The original code table is retained for every restriction.
        raw_length = (length + 2 * self.code_length - 2) // self.code_length
        windows = set()
        for raw in self.raw_language(raw_length, vertices, edge_indices):
            encoded = tuple(bit for symbol in raw for bit in self.codes[symbol])
            for phase in range(self.code_length):
                windows.add(encoded[phase:phase + length])
        return windows

    def identity_on(self, word, vertices, edge_indices):
        if any(letter not in 'cCtw' for letter in word):
            raise ValueError('Word alphabet is c,C,t,w')
        windows = self.binary_language(2 * len(word) + 1, vertices, edge_indices)
        return all(window_normal_form(word, window) == UNIT for window in windows)

    def normal_label(self, word):
        vertices = {v for v in self.vertices if not self.identity_on(word, (v,), ())}
        edges = {e for e, endpoints in enumerate(self.edges)
                 if not self.identity_on(word, tuple(set(endpoints)), (e,))}
        return edges, vertices

    def noncycle_edges(self, deleted):
        adjacent = {v: [] for v in self.vertices}
        for edge, (source, target) in enumerate(self.edges):
            if edge not in deleted:
                adjacent[source].append(target)
        reachable = {}
        for start in self.vertices:
            seen, pending = {start}, [start]
            while pending:
                for target in adjacent[pending.pop()]:
                    if target not in seen:
                        seen.add(target)
                        pending.append(target)
            reachable[start] = seen
        return {e for e, (source, target) in enumerate(self.edges)
                if e not in deleted and source not in reachable[target]}

    def solve(self, premises, output):
        edges, vertices = set(), set()
        for word in premises:
            word_edges, word_vertices = self.normal_label(word)
            edges.update(word_edges)
            vertices.update(word_vertices)
        output_edges, output_vertices = self.normal_label(output)
        radical_edges = self.noncycle_edges(edges)
        return {
            'vertices': len(self.vertices), 'edges': self.edges,
            'code_length': self.code_length,
            'premise_normal_label': {'edges': sorted(edges), 'vertices': sorted(vertices)},
            'additional_mf_radical_edges': sorted(radical_edges),
            'output_normal_label': {'edges': sorted(output_edges),
                                    'vertices': sorted(output_vertices)},
            'output_is_identity': not output_edges and not output_vertices,
            'ordinary_consequence': output_edges <= edges and output_vertices <= vertices,
            'mf_consequence': (output_edges <= edges | radical_edges
                               and output_vertices <= vertices),
        }


if __name__ == '__main__':
    request = json.loads(Path(sys.argv[1]).read_text())
    graph = SeamGraph(request['vertices'], request['edges'])
    print(json.dumps(graph.solve(request['premises'], request['output']), indent=2))
