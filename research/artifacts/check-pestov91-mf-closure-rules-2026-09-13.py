"""Finite audits of the path rules, not verification of the group theorem.

Run with Python 3.12 on MSI; standard library only.
"""
import json
import time


def evaluate(expr, inputs):
    if expr[0] == 'x':
        return inputs[expr[1]]
    left, right = evaluate(expr[1], inputs), evaluate(expr[2], inputs)
    return (left and right) if expr[0] == 'and' else (left or right)


def dual(expr):
    if expr[0] == 'x':
        return expr
    return ('or' if expr[0] == 'and' else 'and', dual(expr[1]), dual(expr[2]))


def network(expr):
    edges = []
    vertices = 2

    def build(item, source, sink):
        nonlocal vertices
        if item[0] == 'x':
            edges.append((source, sink, item[1]))
        elif item[0] == 'or':
            build(item[1], source, sink)
            build(item[2], source, sink)
        else:
            middle = vertices
            vertices += 1
            build(item[1], source, middle)
            build(item[2], middle, sink)

    build(expr, 0, 1)
    edges.append((1, 0, None))
    return vertices, edges


def closure(vertices, edges, deleted):
    reachable = [[i == j for j in range(vertices)] for i in range(vertices)]
    for index, (source, target, _) in enumerate(edges):
        if not (deleted >> index) & 1:
            reachable[source][target] = True
    for middle in range(vertices):
        for source in range(vertices):
            for target in range(vertices):
                reachable[source][target] |= reachable[source][middle] and reachable[middle][target]
    result = deleted
    for index, (source, target, _) in enumerate(edges):
        if not reachable[target][source]:
            result |= 1 << index
    return result


def audit_formula(name, expr, variables):
    vertices, edges = network(dual(expr))
    assert closure(vertices, edges, 0) == 0
    output_bit = 1 << (len(edges) - 1)
    rows = []
    for selected in range(1 << variables):
        inputs = [bool((selected >> i) & 1) for i in range(variables)]
        deleted = sum(1 << index for index, (_, _, label) in enumerate(edges)
                      if label is not None and inputs[label])
        invisible = bool(closure(vertices, edges, deleted) & output_bit)
        assert invisible == evaluate(expr, inputs)
        rows.append({'selected': selected, 'output_invisible': invisible})
    closures = [closure(vertices, edges, deleted) for deleted in range(1 << len(edges))]
    for deleted, closed in enumerate(closures):
        assert deleted & closed == deleted
        assert closures[closed] == closed
        for index in range(len(edges)):
            assert closed & closures[deleted | (1 << index)] == closed
    return {'name': name, 'vertices': vertices, 'edges': len(edges),
            'truth_table': rows, 'closure_inputs_checked': len(closures)}


def audit_parallel(inputs):
    edges = [(1, 0, i) for i in range(inputs)] + [(0, 1, None)]
    for selected in range(1 << inputs):
        closed = closure(2, edges, selected)
        assert closed == (selected if selected < (1 << inputs) - 1
                          else (1 << len(edges)) - 1)
    normals = sum(
        all((deleted >> index) & 1 or not (selected & ((1 << a) | (1 << b)))
            for index, (a, b, _) in enumerate(edges))
        for deleted in range(1 << len(edges)) for selected in range(4)
    )
    assert normals == (1 << (inputs + 1)) + 3
    return {'simple_inputs': inputs, 'input_subsets_checked': 1 << inputs,
            'normal_subgroups': normals}


if __name__ == '__main__':
    started = time.monotonic()
    x, y, z = ('x', 0), ('x', 1), ('x', 2)
    examples = [
        ('x AND (y OR z)', ('and', x, ('or', y, z))),
        ('(x AND y) OR (y AND z)', ('or', ('and', x, y), ('and', y, z))),
        ('at least two of three', ('or', ('and', x, y),
                                  ('or', ('and', x, z), ('and', y, z)))),
    ]
    formulas = [audit_formula(name, expr, 3) for name, expr in examples]
    parallel = [audit_parallel(count) for count in range(2, 7)]
    print(json.dumps({'formulas': formulas, 'parallel_families': parallel,
                      'all_assertions_passed': True,
                      'seconds': round(time.monotonic() - started, 6)}, indent=2))
