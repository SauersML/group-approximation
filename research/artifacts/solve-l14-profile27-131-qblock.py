#!/usr/bin/env python3
"""Disjoint root-block shards for profile27 N/I(0;131) boundaries.

Every maximal noncrossing forest has one unique block containing syllable zero.
This driver fixes the same-color peers in that block and runs the audited
recurrence independently in the intervening gaps and exterior.  Thus the root
block masks are an exact disjoint partition of the original search, without
changing the cyclic cut used by the audited driver.
"""

import argparse
import importlib.util
from functools import lru_cache
from itertools import combinations
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def forced_root_states(B, word, base, tail):
    """Return exactly the forest states whose root block is (0,)+tail."""
    colors = tuple(copy for copy, _ in word)
    coefficients = tuple(coefficient for _, coefficient in word)
    assert word and all(0 < index < len(word) for index in tail)
    assert tuple(sorted(tail)) == tuple(tail)
    assert all(colors[index] == colors[0] for index in tail)

    @lru_cache(maxsize=None)
    def visit(left, right, forbidden):
        if left >= right:
            return (base,)
        color = colors[left]
        if forbidden & (1 << color):
            return ()
        peers = [index for index in range(left + 1, right)
                 if colors[index] == color]
        answers = set()
        for width in range(len(peers) + 1):
            for inner_tail in combinations(peers, width):
                block = (left,) + inner_tail
                block_word = B.ALG.reduce_word(sum(
                    (coefficients[index] for index in block), ()))
                states = {B.combine(base, B.relation_state(block_word))}
                previous, valid = left, True
                for bound in inner_tail:
                    choices = visit(previous + 1, bound, 1 << color)
                    if not choices:
                        valid = False
                        break
                    states = {B.combine(prefix, choice)
                              for prefix in states for choice in choices}
                    previous = bound
                if not valid:
                    continue
                suffixes = visit(previous + 1, right,
                                 forbidden | (1 << color))
                answers.update(B.combine(prefix, suffix)
                               for prefix in states for suffix in suffixes)
        return tuple(sorted(answers))

    color = colors[0]
    block = (0,) + tuple(tail)
    block_word = B.ALG.reduce_word(sum(
        (coefficients[index] for index in block), ()))
    states = {B.combine(base, B.relation_state(block_word))}
    previous = 0
    for bound in tail:
        choices = visit(previous + 1, bound, 1 << color)
        if not choices:
            return ()
        states = {B.combine(prefix, choice)
                  for prefix in states for choice in choices}
        previous = bound
    suffixes = visit(previous + 1, len(word), 1 << color)
    return tuple(sorted(B.combine(prefix, suffix)
                        for prefix in states for suffix in suffixes))


def audit_forced_root(B, base):
    """Independent finite equality audit against the original recurrence."""
    samples = (
        ((0, (1,)),),
        ((0, (1,)), (1, (2,)), (0, (3,))),
        ((0, (1,)), (1, (2,)), (2, (3,)), (1, (4,)), (0, (5,))),
        ((0, (1,)), (1, (2,)), (0, (3,)), (2, (4,)),
         (1, (5,)), (0, (6,))),
    )
    for word in samples:
        peers = tuple(index for index in range(1, len(word))
                      if word[index][0] == word[0][0])
        split = set()
        for width in range(len(peers) + 1):
            for tail in combinations(peers, width):
                split.update(forced_root_states(B, word, base, tail))
        original = set(B.maximal_states_relative(word, base))
        assert split == original, (word, len(split), len(original))


def classify(B, state):
    residual, images = state
    q_image = images[-1]
    if not q_image:
        return "empty"
    if not residual:
        return "free"
    keys = {B.cyclic_key(relation) for relation in residual}
    if B.cyclic_key(q_image) in keys:
        return "direct"
    if B.power_killed(q_image, residual):
        return "power"
    reduced_q, reduced_residual = B.saturate_primitive_roots(q_image, residual)
    if (not reduced_q
            or B.cyclic_key(reduced_q) in
            {B.cyclic_key(relation) for relation in reduced_residual}
            or B.power_killed(reduced_q, reduced_residual)):
        return "saturation"
    if B.involution_substitution_killed(reduced_q, reduced_residual):
        return "involution"
    if B.relator_difference_killed(reduced_q, reduced_residual):
        return "difference"
    return "unresolved", reduced_q, reduced_residual


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("class_name", choices=("n0131", "i0131"))
    parser.add_argument("--rotation", type=int)
    parser.add_argument("--target", type=int, choices=range(4))
    parser.add_argument("--prefix", type=int)
    parser.add_argument("--prefix-bits", type=int, default=4)
    parser.add_argument("--self-audit", action="store_true")
    args = parser.parse_args()
    W = load(f"profile27_{args.class_name}_qblock_boundary",
             f"solve-l14-profile27-{args.class_name}-boundary.py").W
    B, S = W.B, W.S
    carriers = W.carrier_states()
    assert len(carriers) == 1
    residual, images = carriers[0]
    transformed = B.normalize_fp(
        (copy, B.transform(coefficient, images))
        for copy, coefficient in B.ENCODED_K)
    base = residual, images + ((B.Q,),)
    if args.self_audit:
        audit_forced_root(B, base)
        print("forced_root_audit=pass")
        if args.rotation is None:
            return
    assert args.rotation is not None and args.target is not None
    assert args.prefix is not None and 0 <= args.prefix < 2 ** args.prefix_bits
    cuts = B.rotations(transformed)
    assert 0 <= args.rotation < len(cuts)
    augmented = B.normalize_fp(
        cuts[args.rotation] + ((args.target, (-B.Q,)),))
    peers = tuple(index for index in range(1, len(augmented))
                  if augmented[index][0] == augmented[0][0])
    bits = min(args.prefix_bits, len(peers))
    if args.prefix >= 2 ** bits:
        print("rootblock_masks=0")
        print("forest_states=0")
        print("free_nonempty_q=0")
        print("unresolved_q=0")
        return
    counts = {name: 0 for name in (
        "empty", "free", "direct", "power", "saturation", "involution",
        "difference", "unresolved")}
    masks = states = 0
    for rest in range(2 ** (len(peers) - bits)):
        mask = args.prefix | (rest << bits)
        tail = tuple(peer for bit, peer in enumerate(peers)
                     if mask & (1 << bit))
        masks += 1
        for state in forced_root_states(B, augmented, base, tail):
            states += 1
            result = classify(B, state)
            name = result if isinstance(result, str) else result[0]
            counts[name] += 1
            if name == "unresolved":
                print("UNRESOLVED", args.rotation, args.target, mask,
                      state, result[1], result[2], flush=True)
            elif name == "free":
                print("FREE", args.rotation, args.target, mask, state,
                      flush=True)
        # A root mask is an exact disjoint shard.  No canonical state from it is
        # needed by the next mask, so discard cross-mask memo keys here rather
        # than recreating the original monolithic union in the caches.
        B.combine.cache_clear()
        B.relation_state.cache_clear()
    print(f"rotation={args.rotation}")
    print(f"target={args.target}")
    print(f"rootblock_peers={len(peers)}")
    print(f"prefix_bits={bits}")
    print(f"prefix={args.prefix}")
    print(f"rootblock_masks={masks}")
    print(f"forest_states={states}")
    for name, count in counts.items():
        print(f"{name}_q={count}")
    print(f"free_nonempty_q={counts['free']}")
    print(f"unresolved_q={counts['unresolved']}")


if __name__ == "__main__":
    main()
