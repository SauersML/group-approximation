#!/usr/bin/env python3
"""Exact finite search for area-ten three-gate Leavitt disks.

This script is intended for MSI, not a laptop.  It restores one gate digon
into every planar rotation of the five area-eight bipartite cubic cores,
then exhausts edge orientations and the two relator colours.  A hit has six
trivial region labels in

    Q = V4(h0,h2) * V4(k0,k1) * F(h1,k2)

and one nontrivial label (the outer boundary).  Every face, including a
digon, is allowed to be outer.
"""

from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import product
from collections import Counter
import argparse
import json


CORES = (
    "0012/0111/1110/2100",
    "0012/0111/1200/2010",
    "0012/0120/1200/2001",
    "0012/0210/1101/2010",
    "0111/1011/1101/1110",
)

TARGETS = (
    (2, 2, 2, 2, 2, 10, 10),
    (2, 2, 2, 2, 4, 8, 10),
    (2, 2, 2, 2, 6, 6, 10),
    (2, 2, 2, 2, 6, 8, 8),
    (2, 2, 2, 4, 4, 6, 10),
    (2, 2, 2, 4, 4, 8, 8),
    (2, 2, 2, 4, 6, 6, 8),
    (2, 2, 4, 4, 4, 4, 10),
    (2, 2, 4, 4, 4, 6, 8),
    (2, 2, 4, 4, 6, 6, 6),
    (2, 4, 4, 4, 4, 6, 6),
)

POSITIVE = (
    (("h1", 1), ("h2", 1), ("h0", 1)),
    (("k1", 1), ("k2", 1), ("k0", 1)),
)
INVOLUTIONS = frozenset(("h0", "h2", "k0", "k1"))


def rotation(dart):
    return 3 * (dart // 3) + (dart % 3 + 1) % 3


def core_alpha(core, bits):
    matrix = [[int(entry) for entry in row] for row in core.split("/")]
    edges = []
    for left in range(4):
        for right in range(4):
            edges.extend([(left, 4 + right)] * matrix[left][right])
    incident = [[] for _ in range(8)]
    for edge, (left, right) in enumerate(edges):
        incident[left].append(edge)
        incident[right].append(edge)
    slots = {}
    for vertex in range(8):
        order = incident[vertex]
        if bits[vertex]:
            order = [order[0], order[2], order[1]]
        for index, edge in enumerate(order):
            slots[edge, vertex] = 3 * vertex + index
    alpha = [None] * 24
    for edge, (left, right) in enumerate(edges):
        first, second = slots[edge, left], slots[edge, right]
        alpha[first], alpha[second] = second, first
    return tuple(alpha)


def faces(alpha):
    seen = set()
    result = []
    for start in range(len(alpha)):
        if start in seen:
            continue
        face = []
        dart = start
        while dart not in seen:
            seen.add(dart)
            face.append(dart)
            dart = rotation(alpha[dart])
        result.append(tuple(face))
    return tuple(result)


def restore_digon(alpha, dart):
    twin = alpha[dart]
    size = len(alpha)
    result = list(alpha) + [None] * 6
    x0, x1, x2, y0, y1, y2 = range(size, size + 6)
    for first, second in (
        (dart, x0), (y0, twin), (x1, y2), (x2, y1)
    ):
        result[first], result[second] = second, first
    return tuple(result)


def connected(alpha):
    adjacency = [set() for _ in range(len(alpha) // 3)]
    for dart, twin in enumerate(alpha):
        if dart < twin:
            first, second = dart // 3, twin // 3
            adjacency[first].add(second)
            adjacency[second].add(first)
    reached = {0}
    stack = [0]
    while stack:
        vertex = stack.pop()
        for other in adjacency[vertex] - reached:
            reached.add(other)
            stack.append(other)
    return len(reached) == len(adjacency)


def generate_maps():
    rotations = 0
    restorations = 0
    maps = {}
    for core_index, core in enumerate(CORES):
        # Fixing the last bit quotients only global reflection.  Relator
        # orientations below are still enumerated without a further quotient.
        for seven_bits in product((0, 1), repeat=7):
            alpha = core_alpha(core, seven_bits + (0,))
            if len(faces(alpha)) != 6:
                continue
            rotations += 1
            for dart in range(24):
                if dart > alpha[dart]:
                    continue
                restored = restore_digon(alpha, dart)
                restorations += 1
                assert len(restored) == 30
                assert all(restored[restored[i]] == i and restored[i] != i
                           for i in range(30))
                assert connected(restored)
                restored_faces = faces(restored)
                assert len(restored_faces) == 7
                assert sum(map(len, restored_faces)) == 30
                partition = tuple(sorted(map(len, restored_faces)))
                assert partition in TARGETS
                maps.setdefault(restored, (partition, core_index, seven_bits, dart))
    assert rotations == 33, rotations
    assert restorations == 396, restorations
    return rotations, restorations, maps


def inverse(letter):
    name, sign = letter
    return (name, 1) if name in INVOLUTIONS else (name, -sign)


def corner(colour, orientation, occurrence):
    positive = POSITIVE[colour]
    if orientation == 1:
        return positive[occurrence]
    negative = (inverse(positive[1]), inverse(positive[0]),
                inverse(positive[2]))
    return negative[occurrence]


def q_reduce(word):
    """Free-product normal form for V4 * V4 * F2."""
    stack = []
    for name, sign in word:
        if name in ("h0", "h2", "k0", "k1"):
            block = name[0].upper()
            value = 1 if name[1] == "0" else 2
            if stack and stack[-1][0] == block:
                value ^= stack.pop()[1]
                if value:
                    stack.append((block, value))
            else:
                stack.append((block, value))
        else:
            item = (name, sign)
            if stack and stack[-1][0] == "F" and stack[-1][1:] == inverse(item):
                stack.pop()
            else:
                stack.append(("F", name, sign))
    normal = []
    for item in stack:
        if item[0] == "H":
            if item[1] & 1:
                normal.append(("h0", 1))
            if item[1] & 2:
                normal.append(("h2", 1))
        elif item[0] == "K":
            if item[1] & 1:
                normal.append(("k0", 1))
            if item[1] & 2:
                normal.append(("k1", 1))
        else:
            normal.append(item[1:])
    return tuple(normal)


# Lookup from the signs on a vertex's three incident darts to its relator
# orientation and occurrence shift.  There are exactly six allowed patterns.
PATTERNS = {}
for _orientation, _pattern in ((1, (1, 1, -1)), (-1, (1, -1, -1))):
    for _shift in range(3):
        _signs = tuple(_pattern[(i + _shift) % 3] for i in range(3))
        assert _signs not in PATTERNS
        PATTERNS[_signs] = (_orientation, _shift)


def orientation_data(alpha, direction_bits):
    edge_darts = [(dart, alpha[dart]) for dart in range(30)
                  if dart < alpha[dart]]
    signs = [0] * 30
    for edge, (dart, twin) in enumerate(edge_darts):
        signs[dart] = 1 if (direction_bits >> edge) & 1 else -1
        signs[twin] = -signs[dart]
    orientations = []
    occurrences = [None] * 30
    for vertex in range(10):
        datum = PATTERNS.get(tuple(signs[3 * vertex:3 * vertex + 3]))
        if datum is None:
            return None
        orientation, shift = datum
        orientations.append(orientation)
        for local in range(3):
            occurrences[3 * vertex + local] = (local + shift) % 3
    return edge_darts, tuple(orientations), tuple(occurrences)


def face_word(face, alpha, colours, orientations, occurrences):
    return tuple(
        corner(colours[alpha[dart] // 3], orientations[alpha[dart] // 3],
               occurrences[alpha[dart]])
        for dart in face
    )


def search_map(task):
    map_index, alpha, provenance = task
    partition, core_index, bits, restored_dart = provenance
    fs = faces(alpha)
    valid_orientations = 0
    colourings = 0
    for direction_bits in range(1 << 15):
        datum = orientation_data(alpha, direction_bits)
        if datum is None:
            continue
        valid_orientations += 1
        edge_darts, orientations, occurrences = datum

        # A dipole edge with equal endpoint colours is forbidden.  Encode all
        # such requirements as inequalities before evaluating any face word.
        unequal = []
        for dart, twin in edge_darts:
            if (orientations[dart // 3] == -orientations[twin // 3]
                    and occurrences[dart] + occurrences[twin] == 2):
                unequal.append((dart // 3, twin // 3))

        for colour_bits in range(1 << 10):
            colours = tuple((colour_bits >> vertex) & 1
                            for vertex in range(10))
            if any(colours[first] == colours[second]
                   for first, second in unequal):
                continue
            colourings += 1
            raw = tuple(face_word(face, alpha, colours, orientations, occurrences)
                        for face in fs)
            normal = tuple(q_reduce(word) for word in raw)
            nontrivial = tuple(index for index, word in enumerate(normal) if word)
            if len(nontrivial) == 1:
                outer = nontrivial[0]
                return {
                    "candidate": True,
                    "map_index": map_index,
                    "partition": partition,
                    "core_index": core_index,
                    "rotation_bits": bits,
                    "restored_dart": restored_dart,
                    "alpha": alpha,
                    "face_lengths": tuple(map(len, fs)),
                    "direction_bits": direction_bits,
                    "orientations": orientations,
                    "occurrences": occurrences,
                    "colours": colours,
                    "outer_face": outer,
                    "raw_labels": raw,
                    "normal_labels": normal,
                    "valid_orientations": valid_orientations,
                    "colourings": colourings,
                }
    return {
        "candidate": False,
        "map_index": map_index,
        "partition": partition,
        "valid_orientations": valid_orientations,
        "colourings": colourings,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--min-digons", type=int, default=1)
    parser.add_argument("--max-digons", type=int, default=5)
    parser.add_argument("--include-five-digon", action="store_true")
    args = parser.parse_args()

    rotations, restorations, maps = generate_maps()
    census = Counter(provenance[0] for provenance in maps.values())
    print("ROTATIONS", rotations, "ROOTED_RESTORATIONS", restorations,
          "EXACT_ALPHA_MAPS", len(maps), flush=True)
    for partition in TARGETS:
        print("PARTITION", partition, "MAPS", census[partition], flush=True)

    tasks = []
    for map_index, (alpha, provenance) in enumerate(maps.items()):
        digons = provenance[0].count(2)
        if not (args.min_digons <= digons <= args.max_digons):
            continue
        if digons == 5 and not args.include_five_digon:
            continue
        tasks.append((map_index, alpha, provenance))
    tasks.sort(key=lambda task: (-task[2][0].count(2), task[2][0], task[0]))
    print("TASKS", len(tasks), flush=True)

    totals = Counter()
    if args.workers == 1:
        iterator = map(search_map, tasks)
    else:
        pool = ProcessPoolExecutor(max_workers=args.workers)
        futures = [pool.submit(search_map, task) for task in tasks]
        iterator = (future.result() for future in as_completed(futures))
    try:
        for done, result in enumerate(iterator, 1):
            if result["candidate"]:
                print("CANDIDATE", json.dumps(result), flush=True)
                if args.workers != 1:
                    pool.shutdown(wait=False)
                return 1
            partition = tuple(result["partition"])
            totals[(partition, "maps")] += 1
            totals[(partition, "orientations")] += result["valid_orientations"]
            totals[(partition, "colourings")] += result["colourings"]
            print("DONE", done, "/", len(tasks), "PARTITION", partition,
                  "ORIENTATIONS", result["valid_orientations"],
                  "ADMISSIBLE_COLOURINGS", result["colourings"], flush=True)
    finally:
        if args.workers != 1:
            pool.shutdown(wait=True)

    for partition in TARGETS:
        if totals[(partition, "maps")]:
            print("ZERO", partition,
                  "MAPS", totals[(partition, "maps")],
                  "ORIENTATIONS", totals[(partition, "orientations")],
                  "ADMISSIBLE_COLOURINGS", totals[(partition, "colourings")],
                  flush=True)
    print("NO_CANDIDATE", len(tasks), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
