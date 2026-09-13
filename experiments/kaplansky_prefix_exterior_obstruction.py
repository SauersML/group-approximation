"""Exact exterior-square obstruction to the fixed prefix two-shear ansatz.

Run on MSI.  V has basis the eventually-zero binary rays, encoded by their
finite prefix with trailing zeroes removed.  Group units act on V by their
literal Leavitt prefix tables and on exterior powers by determinants over F2.
An explicit vector v with q^*v=v, d^*v=0 and c^*v!=0 disproves d*n=c in
every parameter support.  Here d=q*W0*q and c=q*W0*e; star transposes the
representation.  Any hit is rechecked from literal group-algebra supports.
"""

import argparse
from functools import lru_cache
from itertools import combinations, product as cartesian_product
import json
import math
import time

from depth_one_paired_leavitt_return_search import ONE, canonical, multiply
from kaplansky_asymmetric_atlas_search import (
    atlas_generators, from_key, key, multiply_keys,
)
from kaplansky_unipotent_product_search import A_WORDS, literal_product


def xor(left, right):
    return left.symmetric_difference(right)


def transpose(unit):
    return key(canonical((nu, mu) for mu, nu in unit))


@lru_cache(maxsize=None)
def ray_action(unit, ray):
    result = set()
    for mu, nu in unit:
        padded = ray + "0" * max(0, len(nu) - len(ray))
        if padded.startswith(nu):
            value = (mu + padded[len(nu):]).rstrip("0")
            result.symmetric_difference_update((value,))
    return frozenset(result)


@lru_cache(maxsize=None)
def pair_action(unit, pair):
    result = set()
    for left in ray_action(unit, pair[0]):
        for right in ray_action(unit, pair[1]):
            if left != right:
                result.symmetric_difference_update((tuple(sorted((left, right))),))
    return frozenset(result)


def apply_unit(unit, vector):
    result = set()
    for pair in vector:
        result.symmetric_difference_update(pair_action(unit, pair))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, required=True)
    parser.add_argument("--seconds", type=float, default=600)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    if args.depth < 1 or not math.isfinite(args.seconds) or args.seconds <= 0:
        parser.error("depth must be positive and seconds must be finite and positive")
    started = time.monotonic()
    identity = key(ONE)
    g = key(canonical((("", ""), ("00", "01"),
                       ("01", "00"), ("00", "00"))))
    g2 = multiply_keys(g, g)
    assert multiply_keys(g2, g) == identity
    u = key(canonical((("00", "0"), ("01", "10"), ("1", "11"))))
    generators = tuple(key(value) for _, value in atlas_generators())
    generators_star = tuple(transpose(value) for value in generators)
    g_star, g2_star, u_star = transpose(g), transpose(g2), transpose(u)

    def e_star(vector):
        return xor(apply_unit(g_star, vector), apply_unit(g2_star, vector))

    def q_star(vector):
        return xor(vector, e_star(vector))

    def actor_star(word, vector):
        for index in word:
            vector = apply_unit(generators_star[index], vector)
        return vector

    def n_star(vector):
        projected = q_star(vector)
        combined = set(projected)
        for word in A_WORDS[:4]:
            combined.symmetric_difference_update(actor_star(word, projected))
        combined ^= apply_unit(generators_star[1], combined)
        combined ^= apply_unit(generators_star[4], combined)
        return e_star(combined)

    def w_star(vector):
        return apply_unit(u_star, xor(vector, n_star(vector)))

    rays = sorted({"".join(bits).rstrip("0")
                   for bits in cartesian_product("01", repeat=args.depth)})
    input_pairs = list(combinations(rays, 2))
    result = {"status": "searching", "representation": "exterior_square",
              "ray_depth": args.depth, "ray_count": len(rays),
              "candidate_pairs": len(input_pairs), "completed_columns": 0,
              "budget_seconds": args.seconds}

    def record():
        result["elapsed_seconds"] = time.monotonic() - started
        with open(args.output, "w") as stream:
            json.dump(result, stream, indent=2)

    def literal_star(support, vector):
        answer = set()
        for unit in support:
            answer.symmetric_difference_update(apply_unit(transpose(unit), vector))
        return answer

    record()
    basis = {}
    for index, pair in enumerate(input_pairs):
        source = q_star({pair})
        vector = q_star(w_star(source))
        witness = 1 << index
        while vector:
            pivot = max(vector)
            if pivot not in basis:
                basis[pivot] = set(vector), set(source), witness
                break
            row, old_source, old_witness = basis[pivot]
            vector ^= row
            source ^= old_source
            witness ^= old_witness
        result.update(completed_columns=index + 1, rank=len(basis))
        if not vector and source:
            assert q_star(source) == source
            assert not q_star(w_star(source))
            c_image = e_star(w_star(source))
            assert c_image

            # Independently rebuild d,c in F2[Q], and evaluate each literal
            # group label on the exterior square instead of using the circuit.
            e = {g, g2}
            q = {identity} ^ e
            actors = {identity}
            for word in A_WORDS[:4]:
                actor = identity
                for letter in word:
                    actor = key(multiply(from_key(actor), from_key(generators[letter])))
                actors.symmetric_difference_update((actor,))
            kernel_d = literal_product({identity, generators[1]},
                                       {identity, generators[4]})
            kernel_k = literal_product(actors, kernel_d)
            n_left = literal_product(literal_product(q, kernel_k), e)
            w0 = {u} ^ literal_product(n_left, {u})
            d_support = literal_product(literal_product(q, w0), q)
            c_support = literal_product(literal_product(q, w0), e)
            assert literal_star(q, source) == source
            assert not literal_star(d_support, source)
            assert literal_star(c_support, source) == c_image
            result.update(status="ALL_PARAMETER_SUPPORTS_OBSTRUCTED",
                          witness_pairs=sorted(source), c_star_witness=sorted(c_image),
                          parameter_pair_indices=[i for i in range(len(input_pairs))
                                                  if witness >> i & 1],
                          literal_d_support=len(d_support), literal_c_support=len(c_support),
                          literal_verification=True)
            record()
            print(json.dumps(result), flush=True)
            return
        if (index + 1) % 10 == 0:
            record()
        if time.monotonic() - started > args.seconds:
            result["status"] = "budget_expired"
            record()
            print(json.dumps(result), flush=True)
            return
    result["status"] = "no_obstruction_on_prescribed_ray_pair_span"
    record()
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
