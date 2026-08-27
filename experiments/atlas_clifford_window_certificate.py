"""Exact character certificate for a coherent atlas wall crossing.

For the 64-dimensional A8 character W=(5,2,1), the relative unitary

    U = rho(k) (1 - i rho(d)) / sqrt(2),  d^2=1,

is evaluated in the rational Gaussian group algebra.  Conjugation by U
cancels the square roots, so every coefficient lies in Q(i).  The script
uses the exact W-character to certify which shortest one-sided atlas words
act as scalars.  No floating-point matrix identity is used.
"""

from fractions import Fraction
import json
import sys

sys.path.insert(0, "experiments")

from atlas_clifford_window_search import inversion_count  # noqa: E402
from atlas_kernel_collision_enumerator import (  # noqa: E402
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import (  # noqa: E402
    I4,
    factor_generators,
    gf2_inv,
    gf2_mul,
    matrix_key,
)


ZERO = (Fraction(0), Fraction(0))
ONE = (Fraction(1), Fraction(0))
GAUSSIAN_I = (Fraction(0), Fraction(1))


def gaussian_add(left, right):
    return left[0] + right[0], left[1] + right[1]


def gaussian_neg(value):
    return -value[0], -value[1]


def gaussian_mul(left, right):
    return (left[0] * right[0] - left[1] * right[1],
            left[0] * right[1] + left[1] * right[0])


def gaussian_conjugate(value):
    return value[0], -value[1]


def gaussian_scale(value, scalar):
    return value[0] * scalar, value[1] * scalar


def gaussian_abs_squared(value):
    return value[0] ** 2 + value[1] ** 2


def add_term(value, key, coefficient):
    total = gaussian_add(value.get(key, ZERO), coefficient)
    if total == ZERO:
        value.pop(key, None)
    else:
        value[key] = total


def main():
    generators = [word[0][1] for _, word in factor_generators()[:6]]
    with open("experiments/atlas-a8-natural.json", "r",
              encoding="utf-8") as stream:
        exported = json.load(stream)["matrices"]
    generator_permutations = [
        tuple(value - 1 for value in exported[matrix_key(generator).hex()])
        for generator in generators]

    elements = [I4.copy()]
    indices = {matrix_key(I4): 0}
    permutations = [tuple(range(8))]
    cursor = 0
    while cursor < len(elements):
        element = elements[cursor]
        permutation = permutations[cursor]
        cursor += 1
        for generator, generator_permutation in zip(
                generators, generator_permutations):
            target = gf2_mul(element, generator)
            target_key = matrix_key(target)
            target_permutation = tuple(
                generator_permutation[permutation[index]]
                for index in range(8))
            if target_key not in indices:
                indices[target_key] = len(elements)
                elements.append(target)
                permutations.append(target_permutation)
            elif permutations[indices[target_key]] != target_permutation:
                raise AssertionError("exceptional isomorphism is inconsistent")
    if len(elements) != 20160:
        raise AssertionError("GL(4,2) enumeration failed")

    def cycle_type(permutation):
        seen = set()
        lengths = []
        for start in range(8):
            if start in seen:
                continue
            point = start
            length = 0
            while point not in seen:
                seen.add(point)
                length += 1
                point = permutation[point]
            lengths.append(length)
        return tuple(sorted(lengths, reverse=True))

    character_by_cycle_type = {
        (1, 1, 1, 1, 1, 1, 1, 1): 64,
        (2, 2, 1, 1, 1, 1): 0,
        (2, 2, 2, 2): 0,
        (3, 1, 1, 1, 1, 1): 4,
        (3, 2, 2, 1): 0,
        (3, 3, 1, 1): -2,
        (4, 2, 1, 1): 0,
        (4, 4): 0,
        (5, 1, 1, 1): -1,
        (5, 3): -1,
        (6, 2): 0,
        (7, 1): 1,
    }
    characters = [character_by_cycle_type[cycle_type(permutation)]
                  for permutation in permutations]

    def multiply_keys(left, right):
        return matrix_key(gf2_mul(
            elements[indices[left]], elements[indices[right]]))

    def inverse_key(key):
        return matrix_key(gf2_inv(elements[indices[key]]))

    def algebra_multiply(left, right):
        out = {}
        for left_key, left_coefficient in left.items():
            for right_key, right_coefficient in right.items():
                add_term(out, multiply_keys(left_key, right_key),
                         gaussian_mul(left_coefficient, right_coefficient))
        return out

    def algebra_adjoint(value):
        return {inverse_key(key): gaussian_conjugate(coefficient)
                for key, coefficient in value.items()}

    def trace(value):
        total = ZERO
        for key, coefficient in value.items():
            total = gaussian_add(total, gaussian_scale(
                coefficient, Fraction(characters[indices[key]], 64)))
        return total

    identity_key = matrix_key(I4)
    k_key = bytes.fromhex("00000100000100000000000101000000")
    d_key = bytes.fromhex("01000000000100000000010001000001")
    if multiply_keys(d_key, d_key) != identity_key:
        raise AssertionError("the coherent wall element is not an involution")
    k_inverse_key = inverse_key(k_key)
    sign = -1

    def first_image(matrix):
        return {matrix_key(matrix): ONE}

    def second_image(matrix):
        """Exact expansion of k(1+s i d)h(1-s i d)k^-1/2."""
        h_key = matrix_key(matrix)
        inside = {}
        half = Fraction(1, 2)
        add_term(inside, h_key, (half, Fraction(0)))
        add_term(inside, multiply_keys(
            multiply_keys(d_key, h_key), d_key), (half, Fraction(0)))
        add_term(inside, multiply_keys(d_key, h_key),
                 gaussian_scale(GAUSSIAN_I, Fraction(sign, 2)))
        add_term(inside, multiply_keys(h_key, d_key),
                 gaussian_scale(GAUSSIAN_I, Fraction(-sign, 2)))
        return {
            multiply_keys(multiply_keys(k_key, key), k_inverse_key): coefficient
            for key, coefficient in inside.items()
        }

    states, _ = enumerate_ball(5)
    kernel_words, _, _ = spanning_tree_kernel_words(states)
    shortest = []
    for word in kernel_words:
        projections = factor_projections(word)
        one_sided = ((matrix_key(projections[0]) == identity_key)
                     ^ (matrix_key(projections[1]) == identity_key))
        if len(word) == 6 and inversion_count(word) == 3 and one_sided:
            shortest.append(word)
    if len(shortest) != 34:
        raise AssertionError("shortest parity window changed")

    def incidence_rank(edges, vertices):
        vertex_index = {vertex: index for index, vertex in enumerate(vertices)}
        rows = []
        for edge in edges:
            row = 0
            for vertex in edge:
                row ^= 1 << vertex_index[vertex]
            rows.append(row)
        rank = 0
        for column in range(len(vertices)):
            pivot = next((index for index in range(rank, len(rows))
                          if (rows[index] >> column) & 1), None)
            if pivot is None:
                continue
            rows[rank], rows[pivot] = rows[pivot], rows[rank]
            for index in range(len(rows)):
                if index != rank and ((rows[index] >> column) & 1):
                    rows[index] ^= rows[rank]
            rank += 1
        return rank

    hypergraph = {}
    for repeated_factor in (1, 2):
        edges = set()
        raw_edges = 0
        for word in shortest:
            projections = factor_projections(word)
            if matrix_key(projections[repeated_factor - 1]) == identity_key:
                continue
            raw_edges += 1
            repeated = [matrix for factor, matrix in word
                        if factor == repeated_factor]
            zero_letters = [matrix for factor, matrix in word
                            if factor != repeated_factor]
            if (len(repeated) != 3 or len(zero_letters) != 3
                    or any(matrix_key(matrix) != matrix_key(repeated[0])
                           for matrix in repeated[1:])):
                raise AssertionError("shortest word is not a parity triple")
            if matrix_key(gf2_mul(gf2_mul(
                    zero_letters[0], zero_letters[1]),
                    zero_letters[2])) != identity_key:
                raise AssertionError("zero projection factor does not close")
            conjugators = (
                zero_letters[0],
                gf2_mul(zero_letters[0], zero_letters[1]),
                I4,
            )
            edge = frozenset(
                (matrix_key(repeated[0]).hex(), matrix_key(value).hex())
                for value in conjugators)
            if len(edge) != 3:
                raise AssertionError("parity edge has repeated vertices")
            edges.add(edge)
        vertices = sorted(set().union(*edges))
        adjacency = {vertex: set() for vertex in vertices}
        for edge in edges:
            for vertex in edge:
                adjacency[vertex].update(edge.difference((vertex,)))
        components = []
        unseen = set(vertices)
        while unseen:
            component = {unseen.pop()}
            frontier = list(component)
            while frontier:
                vertex = frontier.pop()
                new = adjacency[vertex].intersection(unseen)
                unseen.difference_update(new)
                component.update(new)
                frontier.extend(new)
            components.append(component)
        rank = incidence_rank(sorted(edges, key=lambda edge: sorted(edge)), vertices)
        hypergraph[str(repeated_factor)] = {
            "raw_edges": raw_edges,
            "distinct_edges": len(edges),
            "vertices": len(vertices),
            "component_sizes": sorted(len(component)
                                      for component in components),
            "incidence_rank_f2": rank,
            "incidence_nullity_f2": len(vertices) - rank,
        }

    certificate = []
    for word_index, word in enumerate(shortest):
        value = {identity_key: ONE}
        for factor, matrix in word:
            value = algebra_multiply(
                value, first_image(matrix) if factor == 1
                else second_image(matrix))
        scalar = trace(value)
        centered = dict(value)
        add_term(centered, identity_key, gaussian_neg(scalar))
        square = algebra_multiply(algebra_adjoint(centered), centered)
        centered_norm_squared = trace(square)
        if centered_norm_squared[1] != 0 or centered_norm_squared[0] < 0:
            raise AssertionError("character norm is not nonnegative real")
        certificate.append({
            "word_index": word_index,
            "support_size": len(value),
            "trace": [str(scalar[0]), str(scalar[1])],
            "centered_hs_norm_squared": str(centered_norm_squared[0]),
            "distance_from_identity_squared": str(
                1 + gaussian_abs_squared(scalar) - 2 * scalar[0]
                if centered_norm_squared[0] == 0 else "not-scalar"),
        })

    scalar = [entry for entry in certificate
              if entry["centered_hs_norm_squared"] == "0"]
    nontrivial = [entry for entry in scalar
                  if entry["trace"] != ["1", "0"]]
    nonscalar = [entry for entry in certificate
                 if entry["centered_hs_norm_squared"] != "0"]
    print(json.dumps({
        "representation": "A8 irrep (5,2,1), dimension 64",
        "k_f2_hex": k_key.hex(),
        "d_f2_hex": d_key.hex(),
        "root_sign": sign,
        "shortest_words": len(certificate),
        "scalar_words": len(scalar),
        "nontrivial_scalar_words": len(nontrivial),
        "nonscalar_word_indices": [entry["word_index"] for entry in nonscalar],
        "parity_hypergraph_by_repeated_factor": hypergraph,
        "certificate": certificate,
    }, indent=2))


if __name__ == "__main__":
    main()
