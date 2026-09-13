"""Compute a minimum-cost MF certificate for individual seam edge relations.

JSON input: vertices (count), edges (endpoint pairs), output (edge index),
costs (one nonnegative integer per edge, or null for a forbidden edge).
The output edge must have null cost. Run on MSI with Python 3.12.
"""
from collections import deque
import json
from pathlib import Path
import sys


def minimum_certificate(vertices, edges, output, costs):
    if type(vertices) is not int or vertices < 1:
        raise ValueError('vertices must be a positive integer')
    if type(output) is not int or not 0 <= output < len(edges):
        raise ValueError('output must be an edge index')
    if len(costs) != len(edges) or costs[output] is not None:
        raise ValueError('costs must label every edge; the output cost is null')
    for cost in costs:
        if cost is not None and (type(cost) is not int or cost < 0):
            raise ValueError('Allowed costs are nonnegative integers')
    for pair in edges:
        if len(pair) != 2 or any(type(v) is not int or not 0 <= v < vertices for v in pair):
            raise ValueError('Invalid edge endpoints')
    sink, source = edges[output]
    if source == sink:
        return {'feasible': False, 'reason': 'The output is a loop'}
    forbidden = 1 + sum(cost for cost in costs if cost is not None)
    residual = [[0] * vertices for _ in range(vertices)]
    for edge, (u, v) in enumerate(edges):
        if edge != output:
            residual[u][v] += forbidden if costs[edge] is None else costs[edge]
    value = 0
    while True:
        parents = {source: None}
        pending = deque([source])
        while pending and sink not in parents:
            u = pending.popleft()
            for v, capacity in enumerate(residual[u]):
                if capacity > 0 and v not in parents:
                    parents[v] = u
                    pending.append(v)
        if sink not in parents:
            break
        increment = forbidden
        v = sink
        while v != source:
            u = parents[v]
            increment = min(increment, residual[u][v])
            v = u
        v = sink
        while v != source:
            u = parents[v]
            residual[u][v] -= increment
            residual[v][u] += increment
            v = u
        value += increment
        if value >= forbidden:
            return {'feasible': False, 'reason': 'A return path uses only forbidden edges'}
    reachable = set(parents)
    cut = [edge for edge, (u, v) in enumerate(edges)
           if edge != output and u in reachable and v not in reachable]
    assert all(costs[edge] is not None for edge in cut)
    assert value == sum(costs[edge] for edge in cut)
    return {'feasible': True, 'minimum_cost': value, 'selected_edges': cut,
            'return_source_side': sorted(reachable)}


if __name__ == '__main__':
    request = json.loads(Path(sys.argv[1]).read_text())
    print(json.dumps(minimum_certificate(request['vertices'], request['edges'],
                                          request['output'], request['costs']), indent=2))
