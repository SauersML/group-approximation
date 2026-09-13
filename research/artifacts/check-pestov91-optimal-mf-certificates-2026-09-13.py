"""Bounded exact checks of cut optimization and compiled vertex-cover instances.

Arguments: minimum-cut solver and existing formula compiler paths.
Run on MSI with Python 3.12. The finite checks are not group proofs.
"""
import importlib.util
from itertools import combinations
import json
import sys
import time


def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def subsets(items):
    items = list(items)
    for mask in range(1 << len(items)):
        yield {item for i, item in enumerate(items) if mask >> i & 1}


def has_return(edges, output, deleted):
    sink, source = edges[output]
    seen, pending = {source}, [source]
    while pending:
        vertex = pending.pop()
        for edge, (u, v) in enumerate(edges):
            if edge != output and edge not in deleted and u == vertex and v not in seen:
                seen.add(v)
                pending.append(v)
    return sink in seen


if __name__ == '__main__':
    started = time.monotonic()
    cut = module(sys.argv[1], 'cut')
    compiler = module(sys.argv[2], 'compiler')
    candidates = [(u, v) for u in range(3) for v in range(3)
                  if u != v and (u, v) != (0, 1)]
    graphs = [[(0, 1)] + [candidates[i] for i in selection]
              for selection in subsets(range(len(candidates)))]
    graphs += [[(0, 1), (1, 0), (1, 0), (1, 1)], [(0, 0), (0, 1), (1, 0)]]
    cut_cases = 0
    for edges in graphs:
        for mode in range(3):
            costs = [None] + [1 if mode == 0 else (i % 4) if mode == 1
                              else None if i % 2 else 2 for i in range(1, len(edges))]
            feasible = [sum(costs[e] for e in selection)
                        for selection in subsets(e for e, cost in enumerate(costs) if cost is not None)
                        if not has_return(edges, 0, selection)]
            actual = cut.minimum_certificate(3, edges, 0, costs)
            assert actual['feasible'] == bool(feasible)
            if feasible:
                assert actual['minimum_cost'] == min(feasible)
                assert not has_return(edges, 0, set(actual['selected_edges']))
            cut_cases += 1
    cover_graphs = assignments = 0
    max_expanded_length = 0
    for count in range(2, 5):
        possible = list(combinations(range(count), 2))
        for chosen in subsets(range(len(possible))):
            if not chosen:
                continue
            original = [possible[i] for i in chosen]
            active = sorted(set(v for pair in original for v in pair))
            remap = {v: i for i, v in enumerate(active)}
            clauses = [['or', ['x', remap[u]], ['x', remap[v]]] for u, v in original]
            formula = clauses[0]
            for clause in clauses[1:]:
                formula = ['and', formula, clause]
            compiled = compiler.compile_formula(formula)
            edges = [(edge['source'], edge['target']) for edge in compiled['edges']]
            optimum_cover = len(active)
            optimum_implication = len(active)
            for selection in subsets(range(len(active))):
                cover = all(remap[u] in selection or remap[v] in selection for u, v in original)
                deleted = {i for i, edge in enumerate(compiled['edges'])
                           if edge['variable'] in selection}
                implication = not has_return(edges, len(edges) - 1, deleted)
                assert implication == cover
                if cover:
                    optimum_cover = min(optimum_cover, len(selection))
                if implication:
                    optimum_implication = min(optimum_implication, len(selection))
                assignments += 1
            assert optimum_cover == optimum_implication
            assert compiled['total_expanded_length'] <= compiled['proven_total_length_bound']
            max_expanded_length = max(max_expanded_length, compiled['total_expanded_length'])
            cover_graphs += 1
    # The exact premise bound is the largest incidence-poset antichain.
    antichain_cases = 0
    for edges in graphs:
        normals = []
        for s in subsets(range(3)):
            incident = {i for i, pair in enumerate(edges) if s.intersection(pair)}
            for j in subsets(range(len(edges))):
                if incident <= j:
                    normals.append((j, s, len(s) + len(j - incident)))
        antichains = [(j, s) for j in subsets(range(len(edges))) for s in subsets(range(3))
                      if all(not s.intersection(edges[i]) for i in j)]
        assert max(bound for j, s, bound in normals) == max(len(j) + len(s) for j, s in antichains)
        antichain_cases += 1
    print(json.dumps({'cut_instances': cut_cases, 'vertex_cover_graphs': cover_graphs,
                      'compiled_selection_assignments': assignments,
                      'largest_compiled_expanded_length': max_expanded_length,
                      'incidence_width_graphs': antichain_cases,
                      'all_checks_passed': True,
                      'seconds': round(time.monotonic() - started, 6)}, indent=2))
