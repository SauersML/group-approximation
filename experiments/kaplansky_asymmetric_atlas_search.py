"""Exact bounded search for a Kaplansky/Gottschalk counterexample.

The ambient group is the subgroup of the binary Leavitt unit group generated
by the two explicit GL(4,2) atlas charts.  We first force a group-algebra
element ``a`` to contain generators of both charts and to evaluate to ``s0``.
For that fixed ``a`` we solve the *literal* convolution equation ``b*a = 1``
over F2, with ``b`` supported in a bounded Cayley ball.  A hit is therefore a
genuine finite certificate in F2[G], rather than an invalid lift from the
Leavitt quotient.  Its reverse product is automatically nontrivial: if an
element ``x`` satisfied both ``x*s0=1`` and ``s0*x=1``, uniqueness of a
two-sided inverse and ``t0*s0=1`` would give ``x=t0``, contradicting
``s0*t0 != 1``.

This is a bounded experiment, not a proof when it reports no hit.
"""

import argparse
from collections import deque
from functools import lru_cache

from atlas_two_chart_search import (
    I4,
    factor_generators,
    leavitt_chart_element,
    transvection,
)
from depth_one_paired_leavitt_return_search import (
    ONE,
    add,
    canonical,
    equal,
    multiply,
)


S0 = canonical((("0", ""),))


@lru_cache(maxsize=None)
def _reduced_key(canonical_terms):
    # Canonical() expands to the deepest right prefix *present in x*.  That
    # depth is not intrinsic, so it is unsuitable as a hash key.  Contract
    # every complete binary sibling pair; the resulting reduced prefix table
    # is independent of prior expansion depth.
    terms = set(canonical_terms)
    pending = list(terms)
    while pending:
        term = pending.pop()
        if term not in terms:
            continue
        mu, nu = term
        if not mu or not nu or mu[-1] != nu[-1]:
            continue
        parent = (mu[:-1], nu[:-1])
        sibling_bit = "1" if mu[-1] == "0" else "0"
        sibling = (parent[0] + sibling_bit, parent[1] + sibling_bit)
        if sibling not in terms:
            continue
        terms.remove(term)
        terms.remove(sibling)
        if parent in terms:
            terms.remove(parent)
        else:
            terms.add(parent)
            pending.append(parent)
    return tuple(sorted(terms))


def key(x):
    return _reduced_key(tuple(sorted(canonical(x))))


@lru_cache(maxsize=None)
def multiply_keys(left, right):
    """Multiply reduced exact group keys, memoizing the expensive prefix work."""
    return key(multiply(frozenset(left), frozenset(right)))


def from_key(value_key):
    return frozenset(value_key)


def chart_value(factor, matrix):
    raw = leavitt_chart_element(factor, matrix)
    return canonical(
        (("".join(map(str, left)), "".join(map(str, right)))
         for left, right in raw)
    )


def atlas_generators():
    answer = []
    for name, word in factor_generators():
        assert len(word) == 1
        factor, matrix = word[0]
        answer.append((name, chart_value(factor, matrix)))
    return tuple(answer)


def cayley_ball(radius):
    generators = atlas_generators()
    identity_key = key(ONE)
    words = {identity_key: ()}
    queue = deque([(identity_key, ())])
    generator_keys = tuple(key(generator) for _, generator in generators)
    while queue:
        value_key, word = queue.popleft()
        if len(word) == radius:
            continue
        for index, generator_key in enumerate(generator_keys):
            successor_key = multiply_keys(value_key, generator_key)
            if successor_key not in words:
                successor_word = word + (index,)
                words[successor_key] = successor_word
                queue.append((successor_key, successor_word))
    ordered_keys = sorted(words, key=lambda k: (len(words[k]), words[k]))
    return generators, [from_key(k) for k in ordered_keys], [words[k] for k in ordered_keys]


def expanded_terms(element, depth):
    terms = set()
    for mu, nu in element:
        stack = [(mu, nu)]
        while stack:
            left, right = stack.pop()
            if len(right) == depth:
                term = (left, right)
                if term in terms:
                    terms.remove(term)
                else:
                    terms.add(term)
            else:
                stack.append((left + "0", right + "0"))
                stack.append((left + "1", right + "1"))
    return terms


def solve_leavitt_sum(columns, target, parity):
    depth = max(
        [len(nu) for value in columns + [target] for _, nu in value],
        default=0,
    )
    all_terms = set()
    expanded = []
    for value in columns + [target]:
        terms = expanded_terms(value, depth)
        expanded.append(terms)
        all_terms.update(terms)
    coordinate = {term: i for i, term in enumerate(sorted(all_terms))}
    parity_bit = len(coordinate)

    def vector(terms, extra):
        result = (extra & 1) << parity_bit
        for term in terms:
            result ^= 1 << coordinate[term]
        return result

    basis = {}
    for index, terms in enumerate(expanded[:-1]):
        value = vector(terms, 1)
        combination = 1 << index
        while value:
            pivot = value.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (value, combination)
                break
            value ^= basis[pivot][0]
            combination ^= basis[pivot][1]

    value = vector(expanded[-1], parity)
    combination = 0
    while value:
        pivot = value.bit_length() - 1
        if pivot not in basis:
            return None
        value ^= basis[pivot][0]
        combination ^= basis[pivot][1]
    return tuple(i for i in range(len(columns)) if (combination >> i) & 1)


def xor_support(left, right):
    result = set(left)
    for item in right:
        if item in result:
            result.remove(item)
        else:
            result.add(item)
    return result


def solve_left_inverse(ball, a_support):
    # Each column is the exact support of g*a in the group algebra.
    product_supports = []
    universe = {key(ONE)}
    a_keys = tuple(key(a) for a in a_support)
    for g in ball:
        g_key = key(g)
        support = {multiply_keys(g_key, a_key) for a_key in a_keys}
        product_supports.append(support)
        universe.update(support)
    coordinate = {term: i for i, term in enumerate(sorted(universe))}

    basis = {}
    for index, support in enumerate(product_supports):
        value = 0
        for term in support:
            value ^= 1 << coordinate[term]
        combination = 1 << index
        while value:
            pivot = value.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = (value, combination)
                break
            value ^= basis[pivot][0]
            combination ^= basis[pivot][1]

    value = 1 << coordinate[key(ONE)]
    combination = 0
    while value:
        pivot = value.bit_length() - 1
        if pivot not in basis:
            return None
        value ^= basis[pivot][0]
        combination ^= basis[pivot][1]
    return tuple(i for i in range(len(ball)) if (combination >> i) & 1)


def group_algebra_product(left, right):
    support = set()
    for x in left:
        for y in right:
            term = multiply_keys(key(x), key(y))
            if term in support:
                support.remove(term)
            else:
                support.add(term)
    return support


def evaluate_sum(support):
    result = canonical(())
    for value in support:
        result = add(result, value)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=3)
    args = parser.parse_args()

    generators, ball, words = cayley_ball(args.radius)
    generator_keys = {key(value) for _, value in generators}
    mandatory = [value for _, value in generators]
    mandatory_sum = evaluate_sum(mandatory)
    residual = add(S0, mandatory_sum)
    candidate_records = [
        (value, word) for value, word in zip(ball, words)
        if key(value) not in generator_keys
    ]
    candidates = [value for value, _ in candidate_records]

    # Twelve mandatory generators have even cardinality.  Ask for an odd
    # residual support so that augmentation(a)=1.
    solution = solve_leavitt_sum(candidates, residual, parity=1)
    print("ball", len(ball), "radius", args.radius)
    print("Leavitt linear coordinates searched", len(candidates))
    if solution is None:
        print("NO_FORCED_S0_LIFT")
        return

    a_support = mandatory + [candidates[i] for i in solution]
    # Remove accidental duplicate terms modulo 2.
    by_key = {}
    for value in a_support:
        k = key(value)
        if k in by_key:
            del by_key[k]
        else:
            by_key[k] = value
    a_support = list(by_key.values())
    assert equal(evaluate_sum(a_support), S0)
    assert len(a_support) % 2 == 1
    assert generator_keys.issubset({key(value) for value in a_support})
    print("forced s0 lift support", len(a_support))
    print("a words", [(i,) for i in range(len(generators))] +
          [candidate_records[i][1] for i in solution])

    inverse = solve_left_inverse(ball, a_support)
    if inverse is None:
        print("NO_LEFT_INVERSE_IN_BALL")
        return
    b_support = [ball[i] for i in inverse]
    forward = group_algebra_product(b_support, a_support)
    reverse = group_algebra_product(a_support, b_support)
    assert forward == {key(ONE)}
    b_value = evaluate_sum(b_support)
    assert equal(multiply(b_value, S0), ONE)
    assert not equal(multiply(S0, b_value), ONE)
    assert reverse != {key(ONE)}
    print("COUNTEREXAMPLE_FOUND")
    print("a support", len(a_support), "b support", len(b_support))
    print("reverse support", len(reverse))
    print("b words", [words[i] for i in inverse])


if __name__ == "__main__":
    main()
