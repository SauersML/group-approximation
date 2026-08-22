#!/usr/bin/env python3
"""Enumerate every coarsening-maximal colored NC partition for I1;412.

Starting from the singleton partition, every allowed edge merges two
same-colored blocks whose union remains noncrossing.  Leaves are therefore
exactly the partitions maximal under coarsening, including locally maximal
partitions with more than the global minimum number of blocks.
"""

import argparse
import importlib.util
from pathlib import Path


HERE = Path(__file__).resolve().parent


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


EQ3 = load("i1412_eq3", "enumerate-l14-i1412-eq3-maximal.py")
EQ1 = load("i1412_eq1", "enumerate-l14-i1412-eq1-maximal.py")


def crosses(left, right):
    for a_index, a in enumerate(left):
        for c in left[a_index + 1:]:
            for b_index, b in enumerate(right):
                for d in right[b_index + 1:]:
                    if a < b < c < d or b < a < d < c:
                        return True
    return False


def merge_if_noncrossing(partition, left_index, right_index):
    merged = tuple(sorted(partition[left_index] + partition[right_index]))
    for index, block in enumerate(partition):
        if index not in (left_index, right_index) and crosses(merged, block):
            return None
    blocks = [block for index, block in enumerate(partition)
              if index not in (left_index, right_index)]
    blocks.append(merged)
    return tuple(sorted(blocks, key=lambda block: block[0]))


def enumerate_leaves(colors):
    initial = tuple((index,) for index in range(len(colors)))
    pending, visited, leaves = [initial], {initial}, set()
    while pending:
        partition = pending.pop()
        children = []
        for left_index, left in enumerate(partition):
            color = colors[left[0]]
            for right_index in range(left_index + 1, len(partition)):
                right = partition[right_index]
                if colors[right[0]] != color:
                    continue
                child = merge_if_noncrossing(partition, left_index, right_index)
                if child is not None:
                    children.append(child)
        if not children:
            leaves.add(partition)
        for child in children:
            if child not in visited:
                visited.add(child)
                pending.append(child)
        if len(visited) % 100000 == 0:
            print(f"visited={len(visited)} pending={len(pending)} leaves={len(leaves)}",
                  flush=True)
    return visited, leaves


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("equation", choices=("eq1", "eq3"))
    args = parser.parse_args()
    module = EQ1 if args.equation == "eq1" else EQ3
    visited, leaves = enumerate_leaves(module.COLORS)
    histogram = {}
    for leaf in leaves:
        histogram[len(leaf)] = histogram.get(len(leaf), 0) + 1
    print(f"equation={args.equation}")
    print(f"visited_partitions={len(visited)}")
    print(f"coarsening_maximal_partitions={len(leaves)}")
    print(f"block_histogram={dict(sorted(histogram.items()))}")


if __name__ == "__main__":
    main()
