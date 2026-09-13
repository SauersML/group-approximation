"""Evaluate the compiled word DAG exactly on finite cyclic F_2 models.

This checks the actual word compiler, not the infinite-group MF theorem.
Run on MSI with Python 3.12 and the compiled example JSON as argument.
"""
import json
from pathlib import Path
import sys
import time


def identity(size):
    return tuple(1 << i for i in range(size))


def multiply(left, right):
    output = []
    for bits in left:
        row = 0
        while bits:
            low = bits & -bits
            row ^= right[low.bit_length() - 1]
            bits ^= low
        output.append(row)
    return tuple(output)


def inverse(matrix):
    size = len(matrix)
    rows = [row | (1 << (size + i)) for i, row in enumerate(matrix)]
    for col in range(size):
        pivot = next(i for i in range(col, size) if (rows[i] >> col) & 1)
        rows[col], rows[pivot] = rows[pivot], rows[col]
        for row in range(size):
            if row != col and (rows[row] >> col) & 1:
                rows[row] ^= rows[col]
    return tuple(row >> size for row in rows)


def power(matrix, exponent):
    output = identity(len(matrix))
    while exponent:
        if exponent & 1:
            output = multiply(output, matrix)
        matrix = multiply(matrix, matrix)
        exponent >>= 1
    return output


def generators(sequence):
    period = len(sequence)
    c = [0] * (3 * period)
    t = list(identity(3 * period))
    w = [0] * (3 * period)
    for j, bit in enumerate(sequence):
        c[j] = 1 << (2 * period + j)
        c[period + j] = (1 << j) | (1 << (2 * period + j))
        c[2 * period + j] = 1 << (period + j)
        t[j] ^= 1 << ((2 if bit == '1' else 1) * period + j)
        w[j] = 1 << (period + (j - 1) % period)
        w[period + j] = 1 << ((j + 1) % period)
        w[2 * period + j] = 1 << (2 * period + j)
    return {'c': tuple(c), 't': tuple(t), 'w': tuple(w)}


def evaluate(dag, sequence):
    values, lengths = [], []
    base = generators(sequence)
    unit = identity(3 * len(sequence))
    for node in dag['nodes']:
        if node['op'] == 'gen':
            value, length = base[node['name']], 1
        elif node['op'] == 'mul':
            value, length = unit, 0
            for arg in node['args']:
                value = multiply(value, values[arg])
                length += lengths[arg]
        elif node['op'] == 'inv':
            value, length = inverse(values[node['arg']]), lengths[node['arg']]
        elif node['op'] == 'pow':
            value = power(values[node['arg']], node['exponent'])
            length = lengths[node['arg']] * node['exponent']
        else:
            raise AssertionError('Unknown word operation')
        assert length == node['expanded_length']
        values.append(value)
        lengths.append(length)
    return values, lengths


def expected(sequence, codes):
    period = len(sequence)
    root = list(identity(3 * period))
    for j in range(period):
        if any(''.join(sequence[(j + k) % period] for k in range(len(code))) == code
               for code in codes):
            root[j] ^= 1 << (period + j)
    return tuple(root)


if __name__ == '__main__':
    started = time.monotonic()
    compiled = json.loads(Path(sys.argv[1]).read_text())
    dag = compiled['words']
    codes = [edge['marker_code'] for edge in compiled['edges']]
    models = [code + '000' for code in codes] + [''.join(codes)]
    periods = []
    for sequence in models:
        values, lengths = evaluate(dag, sequence)
        unit = identity(3 * len(sequence))
        outputs = []
        for variable, word in enumerate(dag['inputs']):
            selected_codes = [edge['marker_code'] for edge in compiled['edges']
                              if edge['variable'] == variable]
            assert values[word] == expected(sequence, selected_codes)
            outputs.append(values[word])
        assert values[dag['output']] == expected(sequence, [codes[-1]])
        outputs.append(values[dag['output']])
        for left in outputs:
            assert multiply(left, left) == unit
            for right in outputs:
                assert multiply(left, right) == multiply(right, left)
        periods.append(len(sequence))
    total = sum(lengths[arg] for arg in [*dag['inputs'], dag['output']])
    assert total == compiled['total_expanded_length']
    assert total <= compiled['proven_total_length_bound']
    print(json.dumps({'formula': compiled['formula'],
                      'dag_nodes': len(dag['nodes']),
                      'input_word_lengths': [lengths[arg] for arg in dag['inputs']],
                      'output_word_length': lengths[dag['output']],
                      'total_expanded_length': total,
                      'proven_total_length_bound': compiled['proven_total_length_bound'],
                      'cyclic_model_periods': periods,
                      'all_matrix_and_length_checks_passed': True,
                      'seconds': round(time.monotonic() - started, 6)}, indent=2))
