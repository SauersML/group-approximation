#!/usr/bin/env python3
"""Run the audited Q-first cyclic boundary solver for I(0;131)."""

import argparse
import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


S = load("profile18_i0131_states", "solve-l14-profile18-i0131-maximal.py")
B = load("audited_boundary", "solve-l14-three-winner-boundary.py")

# Reuse the audited Q-first close, relative all-maximal forest, primitive-root
# saturation, involution Tietze, and relator-difference classifiers with this
# class's state module.  The free rank is eight in both pipelines and Q=9.
B.S = S
B.C = S.C
B.ALG = S.ALG
B.ENCODED_K = tuple((copy, S.encode(coefficient))
                    for copy, coefficient in S.C.K)


def carrier_states():
    left, _ = S.maximal_states(S.WORDS["r2"])
    right, _ = S.maximal_states(S.WORDS["r4"])
    return tuple(sorted({S.combine(a, b) for a in left for b in right}))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--carrier-start", type=int)
    parser.add_argument("--carrier-end", type=int)
    parser.add_argument("--rotation-start", type=int)
    parser.add_argument("--rotation-end", type=int)
    parser.add_argument("--target-start", type=int)
    parser.add_argument("--target-end", type=int)
    parser.add_argument("--trace-words", action="store_true")
    args = parser.parse_args()
    results, augmented_words = set(), set()
    carriers = carrier_states()
    for index, (residual, images) in enumerate(carriers, 1):
        if args.carrier_start is not None and index < args.carrier_start:
            continue
        if args.carrier_end is not None and index > args.carrier_end:
            continue
        transformed = B.normalize_fp(
            (copy, B.transform(coefficient, images))
            for copy, coefficient in B.ENCODED_K)
        base = residual, images + ((B.Q,),)
        cuts = B.rotations(transformed)
        if args.trace_words:
            print(f"TRACE carrier={index} rotations={len(cuts)} "
                  f"syllables={len(transformed)}", flush=True)
        for rotation_index, rotation in enumerate(cuts):
            if (args.rotation_start is not None
                    and rotation_index < args.rotation_start):
                continue
            if (args.rotation_end is not None
                    and rotation_index > args.rotation_end):
                continue
            for target in range(4):
                if args.target_start is not None and target < args.target_start:
                    continue
                if args.target_end is not None and target > args.target_end:
                    continue
                augmented = B.normalize_fp(rotation + ((target, (-B.Q,)),))
                augmented_words.add(augmented)
                choices = B.maximal_states_relative(augmented, base)
                if args.trace_words:
                    print(f"TRACE carrier={index} rotation={rotation_index} "
                          f"target={target} states={len(choices)}", flush=True)
                for final in choices:
                    results.add((target, final[0], final[1][-1],
                                 final[1][:-1]))
        print(f"carrier={index} words={len(augmented_words)} "
              f"states={len(results)}", flush=True)

    nonempty = [state for state in results if state[2]]
    free = [state for state in nonempty if not state[1]]
    direct = [state for state in nonempty
              if B.cyclic_key(state[2]) in
              {B.cyclic_key(relation) for relation in state[1]}]
    powers = [state for state in nonempty
              if state not in direct and B.power_killed(state[2], state[1])]
    saturated, involutions, differences, post = [], [], [], {}
    for state in nonempty:
        if state in direct or state in powers:
            continue
        reduced_q, reduced_residual = B.saturate_primitive_roots(
            state[2], state[1])
        post[state] = reduced_q, reduced_residual
        if (not reduced_q
                or B.cyclic_key(reduced_q) in
                {B.cyclic_key(relation) for relation in reduced_residual}
                or B.power_killed(reduced_q, reduced_residual)):
            saturated.append(state)
        elif B.involution_substitution_killed(reduced_q, reduced_residual):
            involutions.append(state)
        elif B.relator_difference_killed(reduced_q, reduced_residual):
            differences.append(state)
    unresolved = [state for state in nonempty
                  if state not in direct and state not in powers
                  and state not in saturated and state not in involutions
                  and state not in differences]
    print(f"carrier_states={len(carriers)}")
    print(f"distinct_augmented_words={len(augmented_words)}")
    print(f"boundary_states={len(results)}")
    print(f"nonempty_q={len(nonempty)}")
    print(f"free_nonempty_q={len(free)}")
    print(f"direct_killed_q={len(direct)}")
    print(f"power_killed_q={len(powers)}")
    print(f"saturation_killed_q={len(saturated)}")
    print(f"involution_killed_q={len(involutions)}")
    print(f"difference_killed_q={len(differences)}")
    print(f"unresolved_q={len(unresolved)}")
    for state in sorted(free)[:100]:
        print("FREE", state)
    for state in sorted(unresolved)[:100]:
        print("UNRESOLVED", state)
        print("POST_SATURATION", post[state])


if __name__ == "__main__":
    main()
