#!/usr/bin/env python3
"""Push the inverse I1;412 minimum-block carrier screen through cyclic boundary DP.

The cyclic rotations cover conjugate one-copy boundaries.  The upstream
carrier states are exhaustive by the exact all-maximal counts (jobs 16679815
and 16679829), and this stage itself uses all maximal forests.
"""

import importlib.util
from math import gcd
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PAIRS = load("i1412_pairs", "enumerate-l14-i1412-carrier-pairs.py")
FORESTS = load("maximal_nc_forests", "enumerate-maximal-noncrossing-forests.py")
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


def cyclic_reduce(word):
    word = list(EQ3.reduce_word(word))
    while len(word) > 1 and word[0] == -word[-1]:
        word = word[1:-1]
    return tuple(word)


def cyclic_key(word):
    word = cyclic_reduce(word)
    if not word:
        return ()
    variants = []
    for candidate in (word, EQ3.inverse(word)):
        variants.extend(candidate[offset:] + candidate[:offset]
                        for offset in range(len(candidate)))
    return min(variants)


def primitive_power(word):
    word = cyclic_key(word)
    if not word:
        return None
    for period in range(1, len(word) + 1):
        if len(word) % period == 0:
            root = word[:period]
            exponent = len(word) // period
            if root * exponent == word:
                return root, exponent
    raise AssertionError("finite word has no primitive period")


def killed_by_power_relators(q_image, residual):
    target = primitive_power(q_image)
    if target is None:
        return False
    root, exponent = target
    modulus = 0
    for relation in residual:
        power = primitive_power(relation)
        if power is not None and power[0] == root:
            modulus = gcd(modulus, abs(power[1]))
    return modulus != 0 and exponent % modulus == 0


def cyclic_free_product_forms(word):
    """All normalized syllable rotations, hence all cyclic conjugacy cuts."""
    pending = [tuple(word)]
    seen = set()
    identity = PAIRS.initial_images()
    while pending:
        candidate = pending.pop()
        candidate = PAIRS.transformed_free_product(
            tuple(copy for copy, _ in candidate),
            tuple(coefficient for _, coefficient in candidate), identity)
        if candidate in seen:
            continue
        seen.add(candidate)
        for offset in range(1, len(candidate)):
            pending.append(candidate[offset:] + candidate[:offset])
    return tuple(sorted(seen))


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
        rotations = cyclic_free_product_forms(word)
        for rotation in rotations:
            for target in range(4):
                augmented = PAIRS.transformed_free_product(
                    tuple(copy for copy, _ in rotation) + (target,),
                    tuple(coefficient for _, coefficient in rotation) + ((-Q,),),
                    PAIRS.initial_images() + ((Q,),))
                colors = tuple(copy for copy, _ in augmented)
                coefficients = tuple(coefficient for _, coefficient in augmented)
                boundary_schemes, _ = FORESTS.maximal_forests(colors)
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
    directly_killed = [state for state in nontrivial
                       if cyclic_key(state[2]) in
                       {cyclic_key(relation) for relation in state[1]}]
    power_killed = [state for state in nontrivial
                    if state not in directly_killed
                    and killed_by_power_relators(state[2], state[1])]
    unresolved = [state for state in nontrivial
                  if state not in directly_killed and state not in power_killed]
    print(f"nontrivial_q_images={len(nontrivial)}")
    print(f"free_nontrivial_q_images={len(free_nontrivial)}")
    print(f"cyclic_relator_killed_q_images={len(directly_killed)}")
    print(f"power_relator_killed_q_images={len(power_killed)}")
    print(f"unresolved_q_images={len(unresolved)}")
    for state in sorted(free_nontrivial)[:100]:
        print("FREE", state)
    for state in sorted(power_killed):
        print("POWER", state)
    for state in sorted(nontrivial)[:100]:
        print("NONTRIVIAL", state)


if __name__ == "__main__":
    main()
