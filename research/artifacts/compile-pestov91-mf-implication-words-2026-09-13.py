"""Compile a positive Boolean formula to three-generator involution words.

Input JSON: ["x", i], ["and", left, right], or ["or", left, right].
Variable labels must be exactly 0,...,m-1 and each must occur.
Output words are a shared straight-line DAG with exact expanded lengths.
No endpoint language oracle or third-party package is needed.
"""
import argparse
import json
from pathlib import Path


class Words:
    def __init__(self):
        self.nodes = []
        self.interned = {}

    def node(self, key, length):
        if key not in self.interned:
            self.interned[key] = len(self.nodes)
            self.nodes.append((key, length))
        return self.interned[key]

    def gen(self, name):
        return self.node(('gen', name), 1)

    def mul(self, *args):
        return self.node(('mul', *args), sum(self.nodes[a][1] for a in args))

    def inv(self, arg):
        return self.node(('inv', arg), self.nodes[arg][1])

    def power(self, arg, exponent):
        assert exponent >= 0
        return self.node(('pow', arg, exponent), self.nodes[arg][1] * exponent)

    def comm(self, left, right):
        return self.mul(left, right, self.inv(left), self.inv(right))

    def export(self, inputs, output):
        needed = set()

        def visit(index):
            if index in needed:
                return
            needed.add(index)
            key, _ = self.nodes[index]
            children = key[1:] if key[0] == 'mul' else key[1:2] if key[0] != 'gen' else ()
            for child in children:
                visit(child)

        for index in [*inputs, output]:
            visit(index)
        order = sorted(needed)
        remap = {old: new for new, old in enumerate(order)}
        result = []
        for old in order:
            key, length = self.nodes[old]
            entry = {'op': key[0], 'expanded_length': length}
            if key[0] == 'gen':
                entry['name'] = key[1]
            elif key[0] == 'mul':
                entry['args'] = [remap[arg] for arg in key[1:]]
            else:
                entry['arg'] = remap[key[1]]
                if key[0] == 'pow':
                    entry['exponent'] = key[2]
            result.append(entry)
        return {'nodes': result, 'inputs': [remap[arg] for arg in inputs],
                'output': remap[output]}


def cylinder_compiler(words):
    c, t, w = [words.gen(name) for name in ('c', 't', 'w')]
    letters = {'c': c, 'C': words.inv(c), 't': t}

    def literal(text):
        return words.mul(*(letters[letter] for letter in text))

    # Exact certificates in F_2[p]/(p^2-p), checked at p=0 and p=1.
    leaves = {
        '0': literal('ctcctctctctctctCtC'),
        '1': literal('cctctcctcctccctcct'),
    }
    s23 = literal('ctCtctcctCCt')
    s13 = literal('ccctCCtCtctCtC')
    bridge = literal('ccctcctCCtCtctcc')  # s_13 s_23
    shift = words.mul(s23, w, bridge, w, s13)  # diag(u,u,u^{-2})
    inverse_shift = words.inv(shift)

    def balanced(symbols):
        if len(symbols) == 1:
            return leaves[symbols]
        half = len(symbols) // 2
        left = words.mul(s23, balanced(symbols[:half]), s23)
        right = words.mul(s13, words.power(inverse_shift, half),
                          balanced(symbols[half:]), words.power(shift, half), s13)
        return words.comm(left, right)

    def compile_code(code):
        result = balanced(code)
        assert words.nodes[result][1] <= (1 << 8) * len(code) ** 2
        return result

    return compile_code


def compile_formula(formula):
    labels = set()
    occurrences = 0

    def inspect(expr):
        nonlocal occurrences
        if not isinstance(expr, list) or not expr:
            raise ValueError('A formula node must be a nonempty JSON array')
        if expr[0] == 'x' and len(expr) == 2 and type(expr[1]) is int and expr[1] >= 0:
            labels.add(expr[1])
            occurrences += 1
        elif expr[0] in ('and', 'or') and len(expr) == 3:
            inspect(expr[1])
            inspect(expr[2])
        else:
            raise ValueError('Use ["x", i], ["and", left, right], or ["or", left, right]')

    inspect(formula)
    if labels != set(range(len(labels))):
        raise ValueError('Variable labels must be exactly 0,...,m-1, each occurring')
    vertices, edges = 2, []

    def build_dual(expr, source, sink):
        nonlocal vertices
        if expr[0] == 'x':
            edges.append({'source': source, 'target': sink, 'variable': expr[1]})
        elif expr[0] == 'and':  # dual OR: parallel branches
            build_dual(expr[1], source, sink)
            build_dual(expr[2], source, sink)
        else:  # dual AND: series branches
            middle = vertices
            vertices += 1
            build_dual(expr[1], source, middle)
            build_dual(expr[2], middle, sink)

    build_dual(formula, 0, 1)
    edges.append({'source': 1, 'target': 0, 'variable': None})
    alphabet_size = 2 * vertices + len(edges)
    bits = (alphabet_size - 1).bit_length()
    code_length = 2 * bits + 4
    words = Words()
    cylinder = cylinder_compiler(words)
    edge_words = []
    for index, edge in enumerate(edges):
        symbol = 2 * vertices + index
        code = '11' + ''.join('0' + bit for bit in f'{symbol:0{bits}b}') + '00'
        edge['marker_code'] = code
        edge_words.append(cylinder(code))
    inputs = [words.mul(*(edge_words[j] for j, edge in enumerate(edges)
                          if edge['variable'] == variable)) for variable in range(len(labels))]
    output = edge_words[-1]
    dag = words.export(inputs, output)
    total = sum(words.nodes[arg][1] for arg in [*inputs, output])
    bound = (1 << 8) * (occurrences + 1) * code_length ** 2
    assert total <= bound
    return {
        'formula': formula,
        'source': 'EL_3 of the binary-coded directed-seam ring over F_2',
        'endpoint_system': 'Sturmian slope sqrt(2)-1; mechanical intercept 1/2 at each vertex',
        'variables': len(labels), 'variable_occurrences': occurrences,
        'vertices': vertices, 'edges': edges, 'alphabet_size': alphabet_size,
        'code_length': code_length, 'original_ring_matrix_rank': 3 * code_length,
        'words': dag, 'total_expanded_length': total,
        'proven_total_length_bound': bound,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('formula_file', type=Path)
    args = parser.parse_args()
    print(json.dumps(compile_formula(json.loads(args.formula_file.read_text())), indent=2))
