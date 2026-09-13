"""Bounded exact audit of the Sturmian solver and finite normal controller.

Run on MSI with Python 3.12; pass the solver path and finite-matrix audit
path as arguments. Finite checks do not prove the infinite-group theorems.
"""
import importlib.util
from itertools import product
import json
from pathlib import Path
import random
import sys
import time


def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def subsets(size):
    return [set(i for i in range(size) if mask >> i & 1) for mask in range(1 << size)]


if __name__ == '__main__':
    started = time.monotonic()
    solver = module(sys.argv[1], 'solver')
    matrices = module(sys.argv[2], 'matrices')
    graph = solver.SeamGraph(3, [(0, 1), (1, 2), (2, 0), (1, 1)])
    for length in range(1, 17):
        words = solver.sturmian_language(length)
        sampled = {tuple(solver.mechanical_bit(start + j) for j in range(length))
                   for start in range(-512, 512)}
        assert words == sampled
        assert len(words) == length + 1
        raw = graph.raw_language(length, graph.vertices, range(len(graph.edges)))
        assert len(raw) == 3 * (length + 1) + 4 * length
    # Compare the window evaluator with independently implemented finite
    # matrices. Fold Laurent degrees only after evaluating each orbit point.
    rng = random.Random(910913)
    words = ['c' * 7, 'tt', 'ww', 'cC', 'Cc', 'ctcctctctctctctCtC',
             'cctctcctcctccctcct', 'ctCtctcctCCt', 'ccctCCtCtctCtC']
    words += [''.join(rng.choice('cCtw') for _ in range(length))
              for length in range(1, 25)]
    matrix_cases = 0
    for bits in product((0, 1), repeat=3):
        sequence = ''.join(map(str, bits))
        base = matrices.generators(sequence)
        base['C'] = matrices.inverse(base['c'])
        for word in words:
            expected = matrices.identity(9)
            for letter in word:
                expected = matrices.multiply(expected, base[letter])
            actual = [0] * 9
            for point in range(3):
                window = tuple(bits[(point + j) % 3]
                               for j in range(-len(word), len(word) + 1))
                for row, col, degree in solver.window_normal_form(word, window):
                    actual[3 * row + point] ^= 1 << (3 * col + (point - degree) % 3)
            assert tuple(actual) == expected, (bits, word)
            matrix_cases += 1
    # Exhaust all elements of the proposed finite controller on graphs
    # with loops, parallel edges, isolated vertices and directed cycles.
    controller_cases = 0
    for count, edges in [(1, []), (1, [(0, 0)]), (2, [(0, 1)]),
                         (2, [(0, 1), (1, 0), (1, 0)]),
                         (3, [(0, 1), (1, 2), (2, 0)])]:
        def incident(selected):
            return {e for e, pair in enumerate(edges) if selected.intersection(pair)}
        normals = [(j, s) for j in subsets(len(edges)) for s in subsets(count)
                   if incident(s) <= j]
        for selected_vertices in subsets(count):
            for selected_edges in subsets(len(edges)):
                edge_support = selected_edges | incident(selected_vertices)
                containers = [(j, s) for j, s in normals
                              if selected_vertices <= s and edge_support <= j]
                minimal_edges = set.intersection(*(j for j, s in containers))
                minimal_vertices = set.intersection(*(s for j, s in containers))
                assert (minimal_edges, minimal_vertices) == (edge_support, selected_vertices)
                for j, s in normals:
                    assert ((selected_vertices <= s and edge_support <= j)
                            == (selected_vertices <= s and selected_edges <= j))
                controller_cases += 1
    identity_cases = 0
    for count, edges in [(1, []), (2, [(0, 1)]), (2, [(0, 1), (1, 0)])]:
        example = solver.SeamGraph(count, edges)
        for word in ['', 'c' * 7, 'tt', 'ww', 'cC', 'Cc']:
            assert example.normal_label(word) == (set(), set())
            identity_cases += 1
        assert example.normal_label('c') == (set(range(len(edges))), set(range(count)))
        assert example.solve(['c'], 't')['ordinary_consequence']
        assert not example.solve([], 'c')['mf_consequence']
    print(json.dumps({'language_lengths': [1, 16],
                      'exact_sturmian_and_raw_complexity_passed': True,
                      'finite_matrix_comparisons': matrix_cases,
                      'controller_elements_checked': controller_cases,
                      'restricted_identity_cases': identity_cases,
                      'all_checks_passed': True,
                      'solver': Path(sys.argv[1]).name,
                      'seconds': round(time.monotonic() - started, 6)}, indent=2))
