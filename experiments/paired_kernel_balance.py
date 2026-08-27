#!/usr/bin/env python3
"""Check whether paired permutation generators define a balanced relation subgroup.

Input JSON:
{
  "left_degree": 3,
  "right_degree": 3,
  "pairs": [
    {"left": [1,0,2], "right": [1,0,2]},
    {"left": [1,2,0], "right": [1,2,0]}
  ]
}

The algorithm explores only the left generated subgroup. Along each Cayley
edge it propagates the right value of the same word. A conflicting right label
on one left state is exactly a witness that the paired subgroup has a
nontrivial kernel under the left projection. If propagation is path-independent,
it constructs the induced surjection H_left -> H_right; balance is equivalent
to that map being injective.
"""
from __future__ import annotations

import argparse
import json
from collections import deque
from pathlib import Path
from typing import Iterable

Perm = tuple[int, ...]


def identity(n: int) -> Perm:
    return tuple(range(n))


def compose(p: Perm, q: Perm) -> Perm:
    """Composition p o q."""
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p: Perm) -> Perm:
    out = [0] * len(p)
    for i, j in enumerate(p):
        out[j] = i
    return tuple(out)


def parse_perm(raw: object, n: int, where: str) -> Perm:
    if not isinstance(raw, list) or len(raw) != n:
        raise ValueError(f"{where}: expected a list of length {n}")
    try:
        p = tuple(int(x) for x in raw)
    except (TypeError, ValueError) as e:
        raise ValueError(f"{where}: entries must be integers") from e
    if sorted(p) != list(range(n)):
        raise ValueError(f"{where}: not a permutation of 0..{n-1}")
    return p


def word_string(word: Iterable[int]) -> str:
    w = list(word)
    if not w:
        return "1"
    return " ".join(f"g{abs(x)}{'^-1' if x < 0 else ''}" for x in w)


def check(data: dict) -> dict:
    nl = int(data["left_degree"])
    nr = int(data["right_degree"])
    raw_pairs = data.get("pairs")
    if not isinstance(raw_pairs, list) or not raw_pairs:
        raise ValueError("pairs must be a nonempty list")

    gens: list[tuple[Perm, Perm, int]] = []
    for idx, pair in enumerate(raw_pairs, start=1):
        if not isinstance(pair, dict):
            raise ValueError(f"pairs[{idx-1}] must be an object")
        a = parse_perm(pair.get("left"), nl, f"pairs[{idx-1}].left")
        b = parse_perm(pair.get("right"), nr, f"pairs[{idx-1}].right")
        gens.append((a, b, idx))
        gens.append((inverse(a), inverse(b), -idx))

    e_l, e_r = identity(nl), identity(nr)
    label: dict[Perm, Perm] = {e_l: e_r}
    word: dict[Perm, tuple[int, ...]] = {e_l: ()}
    q: deque[Perm] = deque([e_l])
    conflict = None

    while q and conflict is None:
        x = q.popleft()
        y = label[x]
        wx = word[x]
        for a, b, letter in gens:
            nx = compose(x, a)
            ny = compose(y, b)
            nw = wx + (letter,)
            if nx not in label:
                label[nx] = ny
                word[nx] = nw
                q.append(nx)
            elif label[nx] != ny:
                conflict = {
                    "left_state": list(nx),
                    "first_right": list(label[nx]),
                    "second_right": list(ny),
                    "first_word": list(word[nx]),
                    "second_word": list(nw),
                    "first_word_text": word_string(word[nx]),
                    "second_word_text": word_string(nw),
                }
                break

    if conflict is not None:
        return {
            "balanced": False,
            "well_defined_left_to_right": False,
            "left_states_seen_before_conflict": len(label),
            "conflict": conflict,
            "interpretation": (
                "Two words evaluate to the same left element but different right "
                "elements; their quotient witnesses ker(p_left) != {1}."
            ),
        }

    right_values = set(label.values())
    injective = len(right_values) == len(label)
    return {
        "balanced": injective,
        "well_defined_left_to_right": True,
        "injective": injective,
        "left_group_size": len(label),
        "right_group_size": len(right_values),
        "kernel_size": len(label) // len(right_values),
        "interpretation": (
            "The paired generators are the graph of an isomorphism."
            if injective
            else "They define a surjection H_left -> H_right with nontrivial kernel."
        ),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path, help="JSON paired-generator instance")
    ap.add_argument("--compact", action="store_true")
    args = ap.parse_args()
    try:
        data = json.loads(args.input.read_text())
        result = check(data)
    except (OSError, KeyError, TypeError, ValueError, json.JSONDecodeError) as e:
        print(json.dumps({"status": "error", "error": str(e)}))
        return 2
    print(json.dumps(result, indent=None if args.compact else 2, sort_keys=True))
    return 0 if result["balanced"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
