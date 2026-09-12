#!/usr/bin/env sage
"""Emit exact GF(2) data for the multiplicity-two Atlas packet screen."""

import argparse

from sage.all import GF, GL, Matrix, libgap

from atlas_a4_19243_component_localization import H6_LABELS, H18_LABELS, order
from atlas_a4_l44_bitpacked_screen import (
    binary_matrix,
    gap_matrix,
    graph_automorphism,
    intertwiner_basis,
    invertible_from_span,
    matrix_inverse,
    relation_words,
)
from atlas_two_chart_search import factor_generators


MULTIPLICATION_BLOCKS = (
    (0b00, 0b00),
    (0b01, 0b10),
    (0b10, 0b11),
    (0b11, 0b01),
)


def f4_to_f2(value):
    rows = [0] * 8
    for i in range(4):
        for j in range(4):
            first, second = MULTIPLICATION_BLOCKS[value[4 * i + j]]
            rows[2 * i] |= first << (2 * j)
            rows[2 * i + 1] |= second << (2 * j)
    return sum(row << (8 * i) for i, row in enumerate(rows))


def emit_vector(name, values):
    print(name, len(values), *(f"{value:016x}" for value in values))


def f2_matrix(value):
    return Matrix(GF(2), 8, 8,
                  [(value >> (8 * i + j)) & 1 for i in range(8) for j in range(8)])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--outer", action="store_true")
    args = parser.parse_args()
    transform = graph_automorphism if args.outer else (lambda value: value)
    base_h6_i = [binary_matrix(value) for value in H6_LABELS if order(value) == 2]
    base_h6_t = [binary_matrix(value) for value in H6_LABELS if order(value) == 3]
    base_h18_i = [binary_matrix(value) for value in H18_LABELS if order(value) == 2]
    base_h18_t = [binary_matrix(value) for value in H18_LABELS if order(value) == 3]
    source_h6_i = [transform(value) for value in base_h6_i]
    source_h18_i = [transform(value) for value in base_h18_i]
    source_h18_t = [transform(value) for value in base_h18_t]

    field = GF(4, "z")
    ambient = GL(4, field)
    scanner = libgap.eval(r"""
function(G, representative, fixedInvolutions, fixedThrees)
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
  return pairs;
end
""")
    sage_source_i = [Matrix(field, 4, 4, value) for value in source_h6_i]
    pairs_raw = scanner(
        ambient,
        sage_source_i[0]._libgap_(),
        libgap([Matrix(field, 4, 4, value)._libgap_() for value in base_h6_i]),
        libgap([Matrix(field, 4, 4, value)._libgap_() for value in base_h6_t]),
    )
    pairs = [(gap_matrix(pair[0]), gap_matrix(pair[1])) for pair in pairs_raw]
    conjugators = []
    for pair in pairs:
        value = invertible_from_span(intertwiner_basis(source_h6_i, pair))
        assert value is not None
        conjugators.append(f4_to_f2(value))
    assert len(conjugators) == 1262
    for pair, conjugator in zip(pairs[:5], conjugators[:5]):
        lifted = f2_matrix(conjugator)
        assert all(lifted.inverse() * f2_matrix(f4_to_f2(left)) * lifted
                   == f2_matrix(f4_to_f2(right))
                   for left, right in zip(source_h6_i, pair))

    a8_source = []
    for _, word in factor_generators():
        factor, matrix = word[0]
        if factor == 1:
            a8_source.append(f4_to_f2(transform(binary_matrix(matrix))))

    collision_raw, q14_raw = relation_words()
    def encode_word(word):
        result = []
        for factor, matrix in word:
            value = binary_matrix(matrix)
            if factor == 2:
                value = transform(value)
            result.append((factor, f4_to_f2(value)))
        return result

    print("PARITY", "graph" if args.outer else "inner")
    emit_vector("H6", [f4_to_f2(value) for value in source_h6_i])
    emit_vector("A8", a8_source)
    emit_vector("SOURCE_H18_I", [f4_to_f2(value) for value in source_h18_i])
    emit_vector("SOURCE_H18_T", [f4_to_f2(value) for value in source_h18_t])
    emit_vector("FIXED_H18_I", [f4_to_f2(value) for value in base_h18_i])
    emit_vector("FIXED_H18_T", [f4_to_f2(value) for value in base_h18_t])
    for name, word in (("COLLISION", encode_word(collision_raw)),
                       ("Q14", encode_word(q14_raw))):
        print(name, len(word), *(f"{factor}:{value:016x}" for factor, value in word))
    emit_vector("CONJUGATORS", conjugators)
    print("END")


if __name__ == "__main__":
    main()
