#!/usr/bin/env sage
"""Bit-packed exact common-frame screen for the subfield A8 < GL(4,4)."""

import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from sage.all import GF, GL, Matrix, libgap

from atlas_a4_19243_component_localization import H6_LABELS, H18_LABELS, order
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word


MUL = (
    (0, 0, 0, 0),
    (0, 1, 2, 3),
    (0, 2, 3, 1),
    (0, 3, 1, 2),
)
INV = (0, 1, 3, 2)
IDENTITY = (1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1)


def mm(left, right):
    out = [0] * 16
    for i in range(4):
        for k in range(4):
            value = left[4 * i + k]
            if value:
                for j in range(4):
                    out[4 * i + j] ^= MUL[value][right[4 * k + j]]
    return tuple(out)


def matrix_inverse(value):
    rows = [[value[4 * i + j] for j in range(4)]
            + [1 if i == j else 0 for j in range(4)] for i in range(4)]
    for column in range(4):
        pivot = next((row for row in range(column, 4) if rows[row][column]), None)
        if pivot is None:
            return None
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = INV[rows[column][column]]
        rows[column] = [MUL[scale][entry] for entry in rows[column]]
        for row in range(4):
            if row == column or not rows[row][column]:
                continue
            scale = rows[row][column]
            rows[row] = [entry ^ MUL[scale][other]
                         for entry, other in zip(rows[row], rows[column])]
    return tuple(rows[i][4 + j] for i in range(4) for j in range(4))


def cube_is_one(value):
    return mm(mm(value, value), value) == IDENTITY


def to_bits(value):
    result = 0
    for index, entry in enumerate(value):
        result |= (entry & 1) << (2 * index)
        result |= ((entry >> 1) & 1) << (2 * index + 1)
    return result


def from_bits(value):
    return tuple(((value >> (2 * index)) & 1)
                 | (((value >> (2 * index + 1)) & 1) << 1)
                 for index in range(16))


def kernel_basis(rows):
    rows = [row for row in rows if row]
    pivot_columns = []
    pivot_row = 0
    for column in range(32):
        found = next((index for index in range(pivot_row, len(rows))
                      if (rows[index] >> column) & 1), None)
        if found is None:
            continue
        rows[pivot_row], rows[found] = rows[found], rows[pivot_row]
        for index in range(len(rows)):
            if index != pivot_row and ((rows[index] >> column) & 1):
                rows[index] ^= rows[pivot_row]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == len(rows):
            break
    free_columns = [column for column in range(32) if column not in pivot_columns]
    basis = []
    for free in free_columns:
        vector = 1 << free
        for index, pivot in enumerate(pivot_columns):
            if (rows[index] >> free) & 1:
                vector |= 1 << pivot
        basis.append(vector)
    return basis


def equation_columns(left, right):
    columns = []
    zero = (0,) * 16
    for variable in range(32):
        entry = variable // 2
        coefficient = 1 << (variable & 1)
        basis = list(zero)
        basis[entry] = coefficient
        basis = tuple(basis)
        columns.append(to_bits(tuple(a ^ b for a, b in zip(mm(left, basis), mm(basis, right)))))
    rows = [0] * 32
    for variable, column in enumerate(columns):
        while column:
            low = column & -column
            equation = low.bit_length() - 1
            rows[equation] |= 1 << variable
            column ^= low
    return rows


def intertwiner_basis(lefts, rights):
    rows = []
    for left, right in zip(lefts, rights):
        rows.extend(equation_columns(left, right))
    return kernel_basis(rows)


def invertible_from_span(basis):
    span = [0]
    for vector in basis:
        span += [value ^ vector for value in span]
    for value in span[1:]:
        matrix = from_bits(value)
        if matrix_inverse(matrix) is not None:
            return matrix
    return None


def projective_centralizer(generators):
    basis = intertwiner_basis(generators, generators)
    span = [0]
    for vector in basis:
        span += [value ^ vector for value in span]
    representatives = {}
    for value in span[1:]:
        matrix = from_bits(value)
        if matrix_inverse(matrix) is None:
            continue
        pivot = next(entry for entry in matrix if entry)
        normalized = tuple(MUL[INV[pivot]][entry] for entry in matrix)
        representatives[normalized] = normalized
    return list(representatives)


def binary_matrix(value):
    return tuple(int(entry) for row in value for entry in row)


def sage_matrix(value, field):
    image = (field.zero(), field.one(), field.gen(), field.gen() + 1)
    return Matrix(field, 4, 4, [image[entry] for entry in value])


def gap_matrix(value):
    generator = libgap.Z(4)
    entries = []
    for row in value:
        for entry in row:
            if bool(entry.IsZero()):
                entries.append(0)
            elif bool(entry.IsOne()):
                entries.append(1)
            elif entry == generator:
                entries.append(2)
            else:
                entries.append(3)
    return tuple(entries)


def relation_words():
    states, _ = enumerate_ball(5)
    spanning, _, _ = spanning_tree_kernel_words(states)
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])
    return collision, spanning[14]


def bit_word(word, outer):
    return [(factor, graph_automorphism(binary_matrix(matrix))
             if outer and factor == 2 else binary_matrix(matrix))
            for factor, matrix in word]


def evaluate(word, conjugator, inverse):
    value = IDENTITY
    for factor, matrix in word:
        letter = matrix
        if factor == 2:
            letter = mm(mm(inverse, letter), conjugator)
        value = mm(value, letter)
    return value


def matrix_order(value):
    current = IDENTITY
    for exponent in range(1, 256):
        current = mm(current, value)
        if current == IDENTITY:
            return exponent
    raise AssertionError("matrix order exceeded 255")


def graph_automorphism(value):
    inverse = matrix_inverse(value)
    return tuple(inverse[4 * j + i] for i in range(4) for j in range(4))


def is_projectively_binary(value):
    pivot = next(entry for entry in value if entry)
    normalized = tuple(MUL[INV[pivot]][entry] for entry in value)
    return all(entry in (0, 1) for entry in normalized)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--outer", action="store_true")
    args = parser.parse_args()
    base_h6_involutions = [binary_matrix(value) for value in H6_LABELS if order(value) == 2]
    base_h6_threes = [binary_matrix(value) for value in H6_LABELS if order(value) == 3]
    base_h18_involutions = [binary_matrix(value) for value in H18_LABELS if order(value) == 2]
    base_h18_threes = [binary_matrix(value) for value in H18_LABELS if order(value) == 3]
    transform = graph_automorphism if args.outer else (lambda value: value)
    h6_involutions = [transform(value) for value in base_h6_involutions]
    h6_threes = [transform(value) for value in base_h6_threes]
    h18_involutions = [transform(value) for value in base_h18_involutions]
    h18_threes = [transform(value) for value in base_h18_threes]
    field = GF(4, "z")
    ambient = GL(4, field)
    scanner = libgap.eval(r"""
function(G, representative, movingInvolutions, fixedInvolutions, fixedThrees)
  local class,candidates,pairs,x,y,good,a,b,mappedThrees;
  class:=ConjugacyClass(G,representative); candidates:=[];
  for x in class do
    good:=ForAll(fixedThrees,a->(x*a)^3=One(G));
    if good then Add(candidates,x); fi;
  od;
  pairs:=[];
  for x in candidates do for y in candidates do
    if x<>y and (x*y)^3=One(G) then
      mappedThrees:=[x*y,y*x];
      good:=ForAll(fixedInvolutions,b->ForAll(mappedThrees,a->(b*a)^3=One(G)));
      if good then Add(pairs,[x,y]); fi;
    fi;
  od; od;
  return [Length(candidates),pairs];
end
""")
    sage_h6_i = [Matrix(field, 4, 4, value) for value in h6_involutions]
    sage_base_h6_t = [Matrix(field, 4, 4, value) for value in base_h6_threes]
    raw = scanner(ambient, sage_h6_i[0]._libgap_(),
                  libgap([value._libgap_() for value in sage_h6_i]),
                  libgap([Matrix(field, 4, 4, value)._libgap_()
                          for value in base_h6_involutions]),
                  libgap([value._libgap_() for value in sage_base_h6_t]))
    pairs = [(gap_matrix(pair[0]), gap_matrix(pair[1])) for pair in raw[1]]
    centralizer = projective_centralizer(h6_involutions)
    assert int(raw[0]) == 336 and len(pairs) == 1262 and len(centralizer) == 180

    collision_raw, q14_raw = relation_words()
    collision = bit_word(collision_raw, args.outer)
    q14 = bit_word(q14_raw, args.outer)
    liftable = packet = collision_good = q14_good = joint = 0
    collision_orders = {}
    q14_collision_orders = {}
    packet_frame_cells = {"subfield": 0, "extension": 0}
    pinned = []
    for pair_index, pair in enumerate(pairs):
        basis = intertwiner_basis(h6_involutions, pair)
        conjugator0 = invertible_from_span(basis)
        if conjugator0 is None:
            continue
        liftable += 1
        if pair_index < 5:
            inverse0 = matrix_inverse(conjugator0)
            assert all(mm(mm(inverse0, left), conjugator0) == right
                       for left, right in zip(h6_involutions, pair))
            sage_conjugator = sage_matrix(conjugator0, field)
            assert all(sage_conjugator.inverse() * sage_matrix(left, field)
                       * sage_conjugator == sage_matrix(right, field)
                       for left, right in zip(h6_involutions, pair))
            pinned.append((pair_index, len(basis)))
        for central in centralizer:
            conjugator = mm(central, conjugator0)
            inverse = matrix_inverse(conjugator)
            moved_i = [mm(mm(inverse, value), conjugator) for value in h18_involutions]
            moved_t = [mm(mm(inverse, value), conjugator) for value in h18_threes]
            if not all(cube_is_one(mm(value, three))
                       for value in moved_i for three in base_h18_threes):
                continue
            if not all(cube_is_one(mm(value, three))
                       for value in base_h18_involutions for three in moved_t):
                continue
            packet += 1
            packet_frame_cells["subfield" if is_projectively_binary(conjugator)
                               else "extension"] += 1
            collision_value = evaluate(collision, conjugator, inverse)
            q14_value = evaluate(q14, conjugator, inverse)
            cg = collision_value == IDENTITY
            qg = q14_value == IDENTITY
            collision_good += int(cg)
            q14_good += int(qg)
            joint += int(cg and qg)
            value_order = matrix_order(collision_value)
            collision_orders[value_order] = collision_orders.get(value_order, 0) + 1
            if qg:
                q14_collision_orders[value_order] = q14_collision_orders.get(value_order, 0) + 1

    output = {
        "H6_fan_candidates": int(raw[0]),
        "H6_rectangle_pairs": len(pairs),
        "H6_liftable_pairs": liftable,
        "projective_centralizer": len(centralizer),
        "structured_candidates": liftable * len(centralizer),
        "full_packet_survivors": packet,
        "packet_collision_survivors": collision_good,
        "packet_q14_survivors": q14_good,
        "packet_collision_q14_survivors": joint,
        "collision_order_histogram": collision_orders,
        "q14_survivor_collision_order_histogram": q14_collision_orders,
        "packet_frame_cells": packet_frame_cells,
        "pinned_intertwiner_checks": pinned,
        "marking_parity": "graph" if args.outer else "inner",
    }
    expected = {
        "H6_fan_candidates": 336,
        "H6_rectangle_pairs": 1262,
        "H6_liftable_pairs": 1262,
        "projective_centralizer": 180,
        "structured_candidates": 227160,
        "full_packet_survivors": 2754,
        "packet_collision_survivors": 0,
        "packet_q14_survivors": 486 if args.outer else 729,
        "packet_collision_q14_survivors": 0,
        "collision_order_histogram": {2: 1863, 4: 891},
        "q14_survivor_collision_order_histogram": {
            2: 486 if args.outer else 729
        },
        "packet_frame_cells": {"subfield": 30, "extension": 2724},
        "pinned_intertwiner_checks": [(index, 10) for index in range(5)],
        "marking_parity": "graph" if args.outer else "inner",
    }
    assert output == expected
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
