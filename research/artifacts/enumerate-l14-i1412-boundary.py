#!/usr/bin/env python3
"""Push the exact inverse I1;412 carrier states through one-copy boundary DP."""

import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PAIRS = load("i1412_pairs", "enumerate-l14-i1412-carrier-pairs.py")
EQ3 = PAIRS.EQ3
Q = 13


def syllable(copy, *letters):
    return copy, tuple(EQ3.NUMBER[name] * sign for name, sign in letters)


def multiply(left, right):
    out = list(left)
    for copy, coefficient in right:
        if not coefficient:
            continue
        if out and out[-1][0] == copy:
            coefficient = EQ3.reduce_word(out[-1][1] + coefficient)
            out.pop()
            if coefficient:
                out.append((copy, coefficient))
        else:
            out.append((copy, coefficient))
    return tuple(out)


def inverse(word):
    return tuple((copy, EQ3.inverse(coefficient))
                 for copy, coefficient in reversed(word))


H = (
    syllable(0, ("g11", 1)),
    syllable(1, ("g12", 1)),
    syllable(2, ("g13", 1), ("g1", 1)),
    syllable(1, ("g2", 1), ("g4", 1)),
    syllable(2, ("g5", 1)), syllable(1, ("g6", 1)),
    syllable(2, ("g7", 1)), syllable(1, ("g8", 1)),
    syllable(2, ("g9", 1)), syllable(3, ("g10", 1)),
)
A0 = (
    syllable(3, ("g1", 1)),
    syllable(2, ("g2", 1), ("g4", 1)),
    syllable(3, ("g5", 1)), syllable(2, ("g6", 1)),
    syllable(3, ("g7", 1)), syllable(2, ("g8", 1)),
    syllable(3, ("g9", 1)),
)
C1 = (
    syllable(0, ("g12", 1)),
    syllable(1, ("g13", 1), ("g1", 1)),
    syllable(0, ("g2", 1)),
)
E5 = (syllable(3, ("g8", 1)),)
E4 = (syllable(0, ("g7", 1)),)
E3 = (syllable(3, ("g6", 1)),)
E2 = (syllable(0, ("g5", 1)),)

# K=A0^-1 H^-1 C1^-1 H E5^-1 H^-1 E4^-1 H
#   E3^-1 H^-1 E2^-1 H.
K = ()
for factor in (inverse(A0), inverse(H), inverse(C1), H, inverse(E5),
               inverse(H), inverse(E4), H, inverse(E3), inverse(H),
               inverse(E2), H):
    K = multiply(K, factor)

# These endpoint checks replay the two most error-prone raw terms: A0^-1 and
# C1^-1/H^-1 merge into copy 3 and copy 0 respectively.
assert K[0] == syllable(3, ("g9", -1))
assert len(K) == 63


def main():
    carriers = PAIRS.carrier_states(report=True)
    results = set()
    counts = {}
    for carrier_index, (residual, images) in enumerate(sorted(carriers), 1):
        word = PAIRS.transformed_free_product(
            tuple(copy for copy, _ in K), tuple(coefficient for _, coefficient in K),
            images)
        for target in range(4):
            augmented = PAIRS.transformed_free_product(
                tuple(copy for copy, _ in word) + (target,),
                tuple(coefficient for _, coefficient in word) + ((-Q,),),
                PAIRS.initial_images() + ((Q,),))
            colors = tuple(copy for copy, _ in augmented)
            coefficients = tuple(coefficient for _, coefficient in augmented)
            _, boundary_schemes = PAIRS.schemes(colors)
            counts[target] = counts.get(target, 0) + len(boundary_schemes)
            for scheme in boundary_schemes:
                relations = residual + PAIRS.block_relations(scheme, coefficients)
                state = PAIRS.close_tietze(relations, images + ((Q,),))
                q_image = state[1][-1]
                results.add((target, state[0], q_image, state[1][:-1]))
        if carrier_index % 5 == 0:
            print(f"carrier={carrier_index} boundary_states={len(results)}", flush=True)
    print(f"boundary_schemes_by_target={counts}")
    print(f"boundary_states={len(results)}")
    nontrivial = [state for state in results if state[2]]
    free_nontrivial = [state for state in nontrivial if not state[1]]
    print(f"nontrivial_q_images={len(nontrivial)}")
    print(f"free_nontrivial_q_images={len(free_nontrivial)}")
    for state in sorted(free_nontrivial)[:100]:
        print("FREE", state)
    for state in sorted(nontrivial)[:100]:
        print("NONTRIVIAL", state)


if __name__ == "__main__":
    main()
