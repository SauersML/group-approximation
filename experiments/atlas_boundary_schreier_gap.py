"""Emit the exact Schreier quotient for the rank-three fold kernel.

For the fold map ``H*H -> H``, write the two copies as ``a(h),b(h)`` and

    n_h = b(h) a(h)^-1,  h != 1.

The kernel is free on the 167 elements ``n_h``.  Conjugation by ``a(g)`` is

    g . n_h = n_g^-1 n_(gh).

Thus the normal closure in ``H*H`` of collision words ``q_i`` is the normal
closure in the free kernel of the 168 conjugates of each rewritten ``q_i``.
This exporter gives GAP that presentation directly, avoiding Todd--Coxeter
on the original long four-generator presentation.
"""

import argparse

import numpy as np

from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


GREEDY_INDICES = (0, 11, 30, 44, 55)
TRANSVECTIONS = ((0, 1), (1, 0), (1, 2), (2, 1))


def h_generators():
    result = []
    for row, column in TRANSVECTIONS:
        value = I4.copy()
        value[row, column] ^= 1
        result.append(value)
    return result


def enumerate_h():
    elements = [I4.copy()]
    seen = {matrix_key(I4)}
    for value in elements:
        for generator in h_generators():
            target = gf2_mul(value, generator)
            key = matrix_key(target)
            if key not in seen:
                seen.add(key)
                elements.append(target)
    if len(elements) != 168:
        raise AssertionError("H enumeration changed")
    return elements


def lies_in_h(matrix):
    expected = I4.copy()
    expected[:3, :3] = matrix[:3, :3]
    return np.array_equal(matrix, expected)


def append_letter(word, letter):
    if not letter:
        return
    if word and word[-1] == -letter:
        word.pop()
    else:
        word.append(letter)


def append_word(target, source):
    for letter in source:
        append_letter(target, letter)


def inverse_word(word):
    return [-letter for letter in reversed(word)]


def n_letter(value, generator_index):
    if np.array_equal(value, I4):
        return 0
    return generator_index[matrix_key(value)]


def rewrite_kernel_word(word, alignment, alignment_inverse, generator_index):
    prefix = I4.copy()
    output = []
    for factor, value in word:
        image = value if factor == 1 else gf2_mul(
            gf2_mul(alignment, value), alignment_inverse)
        if not lies_in_h(image):
            raise ValueError("word escapes H*H")
        if factor == 2:
            append_letter(output, -n_letter(prefix, generator_index))
            append_letter(output, n_letter(
                gf2_mul(prefix, image), generator_index))
        prefix = gf2_mul(prefix, image)
    if not np.array_equal(prefix, I4):
        raise AssertionError("collision word has nontrivial fold image")
    return output


def act_on_generator(g, h, generator_index):
    output = []
    append_letter(output, -n_letter(g, generator_index))
    append_letter(output, n_letter(gf2_mul(g, h), generator_index))
    return output


def act_on_word(g, word, element_by_generator, generator_index):
    output = []
    for letter in word:
        image = act_on_generator(
            g, element_by_generator[abs(letter)], generator_index)
        append_word(output, image if letter > 0 else inverse_word(image))
    return output


def gap_word(word):
    if not word:
        return "One(F)"
    return "*".join(
        "F.%d" % letter if letter > 0 else "F.%d^-1" % -letter
        for letter in word)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--all-h", action="store_true")
    parser.add_argument("--abelian-only", action="store_true")
    args = parser.parse_args()
    elements = enumerate_h()
    generator_index = {
        matrix_key(value): index
        for index, value in enumerate(elements[1:], start=1)
    }
    element_by_generator = {
        index: value for index, value in enumerate(elements[1:], start=1)
    }
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    collisions = boundary_words()
    base_relators = []
    selected_indices = []
    candidate_indices = (range(len(collisions))
                         if args.all_h else GREEDY_INDICES)
    for index in candidate_indices:
        try:
            rewritten = rewrite_kernel_word(
                collisions[index], alignment, alignment_inverse,
                generator_index)
        except ValueError:
            continue
        selected_indices.append(index)
        base_relators.append(rewritten)
    relators = []
    seen = set()
    for relator in base_relators:
        for g in elements:
            conjugate = act_on_word(
                g, relator, element_by_generator, generator_index)
            key = tuple(conjugate)
            inverse_key = tuple(inverse_word(conjugate))
            canonical = min(key, inverse_key)
            if canonical not in seen:
                seen.add(canonical)
                relators.append(conjugate)

    print("F:=FreeGroup(%d);;" % (len(elements) - 1))
    print("rels:=[%s];;" % ",".join(map(gap_word, relators)))
    print("Q:=F/rels;;")
    print('Print("base_relators %d\\n");' % len(base_relators))
    print('Print("orbit_relators %d\\n");' % len(relators))
    print('Print("abelian_invariants ",AbelianInvariants(Q),"\\n");')
    if args.abelian_only:
        print("QUIT;")
        return
    print("s:=IsomorphismSimplifiedFpGroup(Q);; R:=Image(s);;")
    print('Print("simplified_generators ",Length(GeneratorsOfGroup(R)),"\\n");')
    print('Print("simplified_relators ",Length(RelatorsOfFpGroup(R)),"\\n");')
    print('Print("is_trivial ",IsTrivial(R),"\\n");')
    print("QUIT;")


if __name__ == "__main__":
    main()
