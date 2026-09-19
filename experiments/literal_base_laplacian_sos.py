"""Proof-carrying finite reductions for the literal affine-base Laplacian.

This program never identifies words merely because their affine matrices are
equal.  Every identification is a sequence of local rewrites, and every
rewrite records a conjugate of one of the twenty defining relators (or its
inverse).  The emitted JSON atoms are self-contained records with fields:

* ``conjugator``: a free word;
* ``relator_index``: an index into the displayed literal relator list;
* ``inverted``: whether the inverse relator is used.

The script currently supplies dimension discovery and exact reduction-data
emission.  It intentionally has no SDP solver: numerical discovery should be
added only after the support quotient is large enough and every collision is
covered by one of these checked reductions.
"""

import argparse
import json
from collections import namedtuple
from typing import Tuple


NAMES = ("v1", "v2", "v3", "x", "y", "z")
V1, V2, V3, X, Y, Z = range(1, 7)
Word = Tuple[int, ...]


def free_reduce(word):
    stack = []
    for letter in word:
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def inverse(word):
    return tuple(-letter for letter in reversed(word))


def multiply(left, right):
    return free_reduce(left + right)


def power(word, exponent):
    answer = ()
    for _ in range(exponent):
        answer = multiply(answer, word)
    return answer


def commutator(left, right):
    return multiply(multiply(multiply(left, right), inverse(left)),
                    inverse(right))


v1, v2, v3, x, y, z = ((letter,) for letter in range(1, 7))


class Relator(namedtuple("RelatorData", "name lhs rhs")):
    __slots__ = ()

    @property
    def word(self):
        return multiply(self.lhs, inverse(self.rhs))


RELATORS = (
    Relator("x_cube", power(x, 3), ()),
    Relator("y_cube", power(y, 3), ()),
    Relator("z_square", power(z, 2), ()),
    Relator("xz_cube", power(x + z, 3), ()),
    Relator("yz_cube", power(y + z, 3), ()),
    Relator("x_inv_z_x_y_square", power(inverse(x) + z + x + y, 2), ()),
    Relator("y_inv_z_y_x_square", power(inverse(y) + z + y + x, 2), ()),
    Relator("xy_six", power(x + y, 6), ()),
    Relator("v1_v2_commute", v1 + v2, v2 + v1),
    Relator("v1_v3_commute", v1 + v3, v3 + v1),
    Relator("v2_v3_commute", v2 + v3, v3 + v2),
    Relator("x_v1", x + v1, v3 + x),
    Relator("x_v2", x + v2, v1 + x),
    Relator("x_v3", x + v3, v2 + x),
    Relator("y_v1", y + v1, v1 + y),
    Relator("y_v2", y + v2, inverse(v2) + v3 + y),
    Relator("y_v3", y + v3, v1 + inverse(v2) + y),
    Relator("z_v1", z + v1, v2 + inverse(v3) + z),
    Relator("z_v2", z + v2, v1 + inverse(v3) + z),
    Relator("z_v3", z + v3, inverse(v3) + z),
)


class Rule(namedtuple(
        "RuleData", "lhs rhs relator_index inverted local_conjugator")):
    __slots__ = ()

    def __new__(cls, lhs, rhs, relator_index, inverted=False,
                local_conjugator=()):
        return super(Rule, cls).__new__(
            cls, lhs, rhs, relator_index, inverted, local_conjugator)

    def validate(self):
        signed = (inverse(RELATORS[self.relator_index].word)
                  if self.inverted else RELATORS[self.relator_index].word)
        represented = multiply(
            multiply(self.local_conjugator, signed),
            inverse(self.local_conjugator),
        )
        if multiply(self.lhs, inverse(self.rhs)) != represented:
            raise AssertionError("rewrite rule is not justified by its relator")


# Natural orientations of all twenty relations.  The three extra rules make
# the inverses of the finite-order rotation generators canonical without
# appealing to the affine matrix quotient.
RULES = tuple(
    [Rule(relator.lhs, relator.rhs, index)
     for index, relator in enumerate(RELATORS)]
    + [
        Rule(inverse(x), power(x, 2), 0, inverted=True),
        Rule(inverse(y), power(y, 2), 1, inverted=True),
        Rule(inverse(z), z, 2, inverted=True),
    ]
)

for rule in RULES:
    rule.validate()


class Atom(namedtuple("AtomData", "conjugator relator_index inverted")):
    __slots__ = ()

    @property
    def word(self):
        relator = RELATORS[self.relator_index].word
        signed = inverse(relator) if self.inverted else relator
        return multiply(multiply(self.conjugator, signed),
                        inverse(self.conjugator))


def certificate_word(atoms):
    answer = ()
    for atom in atoms:
        answer = multiply(answer, atom.word)
    return answer


def rewrite_once(word):
    # Longer left sides first makes the reduction deterministic and avoids a
    # short torsion rewrite hiding a displayed longer relation.
    ordered = sorted(RULES, key=lambda rule: -len(rule.lhs))
    for position in range(len(word) + 1):
        for rule in ordered:
            width = len(rule.lhs)
            if width and word[position:position + width] == rule.lhs:
                prefix = word[:position]
                rewritten = free_reduce(
                    prefix + rule.rhs + word[position + width:])
                conjugator = multiply(prefix, rule.local_conjugator)
                atom = Atom(conjugator, rule.relator_index, rule.inverted)
                return rewritten, atom
    return None


def reduce_with_certificate(word, max_steps=10000):
    original = free_reduce(word)
    current = original
    atoms = []
    seen = {current}
    for _ in range(max_steps):
        step = rewrite_once(current)
        if step is None:
            break
        current, atom = step
        atoms.append(atom)
        if current in seen:
            raise RuntimeError("oriented relator rewriting entered a cycle")
        seen.add(current)
    else:
        raise RuntimeError("relator reduction exceeded the step bound")
    expected = multiply(original, inverse(current))
    if expected != certificate_word(atoms):
        raise AssertionError("relator certificate failed exact free-word replay")
    return current, tuple(atoms)


SYMMETRIC_GENERATORS = (
    v1, inverse(v1), v2, inverse(v2), v3, inverse(v3),
    x, inverse(x), y, inverse(y), z,
)


class ReductionRegistry:
    def __init__(self):
        self._reductions = {}

    def reduce(self, word):
        original = free_reduce(word)
        reduced, atoms = reduce_with_certificate(original)
        self._reductions.setdefault((original, reduced), atoms)
        return reduced

    @property
    def reductions(self):
        return self._reductions


def ball(radius, registry):
    support = {()}
    frontier = {()}
    for _ in range(radius):
        new_frontier = set()
        for word in frontier:
            for generator in SYMMETRIC_GENERATORS:
                reduced = registry.reduce(word + generator)
                if reduced not in support:
                    new_frontier.add(reduced)
        support.update(new_frontier)
        frontier = new_frontier
    return tuple(sorted(support))


def add_term(element, word, coefficient):
    if coefficient:
        element[word] = element.get(word, 0) + coefficient
        if element[word] == 0:
            del element[word]


def laplacian(registry):
    answer = {(): len(SYMMETRIC_GENERATORS)}
    for generator in SYMMETRIC_GENERATORS:
        add_term(answer, registry.reduce(generator), -1)
    return answer


def ring_product(left, right, registry):
    answer = {}
    for first, first_coefficient in left.items():
        for second, second_coefficient in right.items():
            reduced = registry.reduce(first + second)
            add_term(answer, reduced, first_coefficient * second_coefficient)
    return answer


def coefficient_pairs(support, registry):
    answer = {}
    for row, left in enumerate(support):
        for column, right in enumerate(support):
            reduced = registry.reduce(inverse(left) + right)
            answer.setdefault(reduced, []).append((row, column))
    return answer


def word_json(word):
    return [
        {"generator": NAMES[abs(letter) - 1], "inverse": letter < 0}
        for letter in word
    ]


def atom_json(atom):
    return {
        "conjugator": word_json(atom.conjugator),
        "relator_index": atom.relator_index,
        "relator_name": RELATORS[atom.relator_index].name,
        "inverted": atom.inverted,
    }


def certificate_json(registry):
    reductions = []
    for (original, reduced), atoms in sorted(registry.reductions.items()):
        reductions.append({
            "original": word_json(original),
            "reduced": word_json(reduced),
            "atoms": [atom_json(atom) for atom in atoms],
        })
    return {
        "generators": list(NAMES),
        "relators": [
            {"index": index, "name": relator.name,
             "word": word_json(relator.word)}
            for index, relator in enumerate(RELATORS)
        ],
        "reductions": reductions,
    }


def describe(radius):
    registry = ReductionRegistry()
    support = ball(radius, registry)
    pairs = coefficient_pairs(support, registry)
    delta = laplacian(registry)
    delta_square = ring_product(delta, delta, registry)
    atoms = [
        len(certificate)
        for certificate in registry.reductions.values()
    ]
    result = {
        "radius": radius,
        "literal_generators": len(NAMES),
        "symmetric_generator_elements": len(SYMMETRIC_GENERATORS),
        "relators": len(RELATORS),
        "support": len(support),
        "gram_dimension": len(support),
        "pair_product_groups": len(pairs),
        "delta_support": len(delta),
        "delta_square_support": len(delta_square),
        "checked_reductions": len(registry.reductions),
        "certificate_atoms": sum(atoms),
        "max_atoms_per_reduction": max(atoms, default=0),
    }
    return result, registry


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=0)
    parser.add_argument("--describe", action="store_true")
    parser.add_argument("--certificate-output")
    args = parser.parse_args()
    if not args.describe:
        parser.error("only --describe is implemented before the SDP stage")
    result, registry = describe(args.radius)
    if args.certificate_output:
        with open(args.certificate_output, "w", encoding="utf-8") as handle:
            json.dump(certificate_json(registry), handle, sort_keys=True)
            handle.write("\n")
        result["certificate_output"] = args.certificate_output
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
