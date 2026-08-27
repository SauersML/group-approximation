"""Emit a short two-generator GAP presentation for the rank-three audit.

We find explicit ``x,y in H`` satisfying the standard presentation

    PSL(2,7) = <x,y | x^2, y^3, (xy)^7, [x,y]^4>.

A breadth-first word table rewrites the five selected collision words in
``x,y``.  The resulting quotient uses four free generators and thirteen
short relators, avoiding the poor generic presentations that obstructed the
first Todd--Coxeter attempt.
"""

import argparse
from collections import deque

import numpy as np

from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


INDICES = (0, 11, 30, 44, 55)
TRANSVECTIONS = ((0, 1), (1, 0), (1, 2), (2, 1))


def generators():
    result = []
    for row, column in TRANSVECTIONS:
        value = I4.copy()
        value[row, column] ^= 1
        result.append(value)
    return result


def enumerate_group(seed_generators):
    elements = [I4.copy()]
    seen = {matrix_key(I4)}
    for value in elements:
        for generator in seed_generators:
            target = gf2_mul(value, generator)
            key = matrix_key(target)
            if key not in seen:
                seen.add(key)
                elements.append(target)
    if len(elements) != 168:
        raise AssertionError("rank-three subgroup does not have order 168")
    return elements


def order(value):
    power = I4.copy()
    for exponent in range(1, 9):
        power = gf2_mul(power, value)
        if np.array_equal(power, I4):
            return exponent
    raise AssertionError("unexpected H element order")


def commutator(left, right):
    return gf2_mul(gf2_mul(gf2_mul(
        left, right), gf2_inv(left)), gf2_inv(right))


def generated_order(seed_generators):
    return len(enumerate_group(seed_generators))


def hurwitz_pair(elements):
    for x in elements:
        if order(x) != 2:
            continue
        for y in elements:
            if (order(y) == 3 and order(gf2_mul(x, y)) == 7
                    and order(commutator(x, y)) == 4
                    and generated_order((x, y)) == 168):
                return x, y
    raise AssertionError("no (2,3,7;4) pair found")


def word_table(x, y):
    letters = ((1, x), (2, y), (-2, gf2_inv(y)))
    words = {matrix_key(I4): ()}
    queue = deque([I4.copy()])
    while queue:
        value = queue.popleft()
        source_word = words[matrix_key(value)]
        for letter, generator in letters:
            target = gf2_mul(value, generator)
            key = matrix_key(target)
            if key not in words:
                words[key] = source_word + (letter,)
                queue.append(target)
    if len(words) != 168:
        raise AssertionError("Hurwitz words do not cover H")
    return words


def gap_word(word, first, second):
    names = {1: first, 2: second, -1: first + "^-1",
             -2: second + "^-1"}
    return "*".join(names[letter] for letter in word) if word else "One(F)"


def transported_word(word, alignment, alignment_inverse, words):
    output = []
    for factor, value in word:
        image = value if factor == 1 else gf2_mul(
            gf2_mul(alignment, value), alignment_inverse)
        output.append(gap_word(
            words[matrix_key(image)], "a" if factor == 1 else "c",
            "b" if factor == 1 else "d"))
    return "*".join(output)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--low-index", type=int,
        help=("enumerate permutation actions through subgroups of index at "
              "most this value, instead of asking for the quotient size"))
    args = parser.parse_args()
    elements = enumerate_group(generators())
    x, y = hurwitz_pair(elements)
    words = word_table(x, y)
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    collisions = boundary_words()
    selected = [transported_word(
        collisions[index], alignment, alignment_inverse, words)
                for index in INDICES]

    print("F:=FreeGroup(\"a\",\"b\",\"c\",\"d\");;")
    print("a:=F.1;; b:=F.2;; c:=F.3;; d:=F.4;;")
    print("cm:=function(u,v) return u*v*u^-1*v^-1; end;;")
    print("rels:=[a^2,b^3,(a*b)^7,cm(a,b)^4,"
          "c^2,d^3,(c*d)^7,cm(c,d)^4,%s];;" % ",".join(selected))
    print("Q:=F/rels;;")
    print("K:=Subgroup(Q,[Q.1,Q.2]);;")
    if args.low_index is None:
        print('Print("first_factor_size ",Size(K),"\\n");')
        print('Print("first_factor_index ",Index(Q,K),"\\n");')
        print('Print("quotient_size ",Size(Q),"\\n");')
    else:
        print("subs:=LowIndexSubgroupsFpGroup(Q,%d);;" % args.low_index)
        print('Print("low_index_subgroups ",Length(subs),"\\n");')
        print("bridge1:=Q.1*Q.3^-1;; bridge2:=Q.2*Q.4^-1;;")
        print("records:=[];;")
        print("for subgroup in subs do")
        print("  cosets:=RightCosets(Q,subgroup);;")
        print("  action:=ActionHomomorphism(Q,cosets,OnRight);;")
        print("  if not IsOne(Image(action,bridge1)) or ")
        print("     not IsOne(Image(action,bridge2)) then")
        print("    Add(records,[Length(cosets),Size(Image(action)),")
        print("      Image(action,bridge1),Image(action,bridge2)]);")
        print("  fi;")
        print("od;")
        print('Print("separating_actions ",Length(records),"\\n");')
        print('Print("separating_records ",records,"\\n");')
    print("QUIT;")


if __name__ == "__main__":
    main()
