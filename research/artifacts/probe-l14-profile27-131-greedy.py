#!/usr/bin/env python3
"""Probe exact greedy maximal forests for profile27 boundary-only classes."""

import argparse
import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("class_name", choices=("n0131", "i0131"))
    args = parser.parse_args()
    W = load(f"profile27_{args.class_name}_boundary",
             f"solve-l14-profile27-{args.class_name}-boundary.py").W
    B, S = W.B, W.S
    encoded = tuple((copy, S.encode(coefficient))
                    for copy, coefficient in S.C.K)

    def greedy_relations(word):
        colors = tuple(copy for copy, _ in word)
        coefficients = tuple(coefficient for _, coefficient in word)

        def visit(left, right, forbidden):
            if left >= right:
                return ()
            color = colors[left]
            if forbidden & (1 << color):
                return None
            peers = tuple(index for index in range(left + 1, right)
                          if colors[index] == color)
            block = (left,) + peers
            relation = S.ALG.reduce_word(sum(
                (coefficients[index] for index in block), ()))
            relations = (relation,) if relation else ()
            previous = left
            for bound in peers:
                nested = visit(previous + 1, bound, 1 << color)
                if nested is None:
                    return None
                relations += nested
                previous = bound
            suffix = visit(previous + 1, right, forbidden | (1 << color))
            if suffix is None:
                return None
            relations += suffix
            return relations

        return visit(0, len(word), 0)

    hits = 0
    for rotation_index, rotation in enumerate(B.rotations(encoded)):
        for target in range(4):
            augmented = B.normalize_fp(rotation + ((target, (-B.Q,)),))
            relations = greedy_relations(augmented)
            if relations is None:
                continue
            residual, images = B.close_prefer_q(
                relations, B.IDENTITY)
            q_image = images[-1]
            if not q_image:
                continue
            killed = (B.cyclic_key(q_image) in
                      {B.cyclic_key(relation) for relation in residual}
                      or B.power_killed(q_image, residual))
            reduced_q, reduced_residual = B.saturate_primitive_roots(
                q_image, residual)
            killed = killed or not reduced_q or (
                B.cyclic_key(reduced_q) in
                {B.cyclic_key(relation) for relation in reduced_residual})
            if not killed:
                hits += 1
                print("GREEDY_CANDIDATE", rotation_index, target,
                      reduced_q, reduced_residual, images[:-1], flush=True)
    print(f"greedy_candidates={hits}")


if __name__ == "__main__":
    main()
