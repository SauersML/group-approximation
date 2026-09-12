#!/usr/bin/env python3
"""Exact search for the sole odd area-ten long-residue budget.

The structural residue is internal lengths (2,4,4,4,4,11) and outer length
one.  Contracting the unique internal digon leaves one of three eight-vertex
face partitions.  We generate those cores from the complete sixteen-type
six-vertex planar cubic atlas by restoring either a digon or a loop gadget,
restore the distinguished digon, and test all exact labels.
"""

from concurrent.futures import ProcessPoolExecutor, as_completed
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
import argparse
import json


HERE = Path(__file__).parent


def definitions(path, marker):
    source = path.read_text().split(marker, 1)[0]
    namespace = {"__file__": str(path), "__name__": path.stem}
    exec(compile(source, str(path), "exec"), namespace)
    return namespace


atlas = definitions(HERE / "search-leavitt-area-ten-short-atlas.py",
                    "def main():")
actual = definitions(HERE / "classify-leavitt-odd-five-seven-corners.py",
                     "lengths = tuple(map(int, sys.argv[1:]))")

CORE_TARGETS = {
    (1, 4, 4, 4, 4, 7),
    (1, 2, 4, 4, 4, 9),
    (1, 2, 2, 4, 4, 11),
}
FINAL_TARGET = (1, 2, 4, 4, 4, 4, 11)
SIX_VERTEX_PARTITIONS = {
    (1, 1, 1, 1, 14), (1, 1, 1, 2, 13), (1, 1, 1, 3, 12),
    (1, 1, 1, 5, 10), (1, 1, 1, 6, 9), (1, 1, 2, 2, 12),
    (1, 1, 2, 3, 11), (1, 1, 2, 4, 10), (1, 1, 2, 5, 9),
    (1, 1, 2, 7, 7), (1, 1, 3, 3, 10), (1, 1, 3, 6, 7),
    (1, 1, 4, 6, 6), (1, 1, 5, 5, 6), (1, 2, 2, 3, 10),
    (1, 2, 2, 5, 8), (1, 2, 3, 4, 8), (1, 2, 3, 5, 7),
    (1, 2, 4, 5, 6), (1, 3, 3, 4, 7), (2, 2, 2, 6, 6),
    (2, 2, 3, 3, 8), (2, 2, 4, 4, 6), (2, 3, 3, 5, 5),
    (3, 3, 4, 4, 4),
}


def six_vertex_types():
    """One planar ribbon representative of each cubic multigraph type."""
    orientations = (1, 1, 1, -1, -1, -1)
    signs = sum(([1, 1, -1] if value == 1 else [1, -1, -1]
                 for value in orientations), [])
    positive = tuple(i for i, value in enumerate(signs) if value == 1)
    negative = tuple(i for i, value in enumerate(signs) if value == -1)
    vertex_permutations = tuple(permutations(range(6)))

    def graph_flat(alpha):
        matrix = [[0] * 6 for _ in range(6)]
        for dart, twin in enumerate(alpha):
            if dart > twin:
                continue
            first, second = dart // 3, twin // 3
            if first == second:
                matrix[first][first] += 1
            else:
                matrix[first][second] += 1
                matrix[second][first] += 1
        return tuple(sum(matrix, []))

    def canonical_graph(flat):
        matrix = [flat[6 * i:6 * i + 6] for i in range(6)]
        return min(tuple(matrix[p[i]][p[j]]
                         for i in range(6) for j in range(i, 6))
                   for p in vertex_permutations)

    raw_representatives = {}
    for targets in permutations(negative):
        alpha = [None] * 18
        for left, right in zip(positive, targets):
            alpha[left], alpha[right] = right, left
        alpha = tuple(alpha)
        if not atlas["connected"](alpha):
            continue
        if len(atlas["faces"](alpha)) != 5:
            continue
        raw_representatives.setdefault(graph_flat(alpha), alpha)
    representatives = {}
    for flat, alpha in raw_representatives.items():
        representatives.setdefault(canonical_graph(flat), alpha)
    assert len(representatives) == 16
    return tuple(representatives.values())


def flip_rotations(alpha):
    """All planar rotations of one fixed abstract cubic multigraph."""
    result = set()
    for bits in product((0, 1), repeat=5):
        bits += (0,)  # global reflection
        rename = list(range(18))
        for vertex, flip in enumerate(bits):
            if flip:
                rename[3 * vertex + 1], rename[3 * vertex + 2] = (
                    rename[3 * vertex + 2], rename[3 * vertex + 1]
                )
        inverse = [None] * 18
        for old, new in enumerate(rename):
            inverse[new] = old
        changed = tuple(rename[alpha[inverse[dart]]] for dart in range(18))
        if len(atlas["faces"](changed)) == 5:
            result.add(changed)
    return result


def restore_loop(alpha, dart):
    """Insert a cubic loop-lollipop gadget on one edge."""
    twin = alpha[dart]
    size = len(alpha)
    result = list(alpha) + [None] * 6
    x0, x1, x2, y0, y1, y2 = range(size, size + 6)
    for first, second in (
        (dart, y0), (y1, twin), (y2, x0), (x1, x2)
    ):
        result[first], result[second] = second, first
    return tuple(result)


def generate_final_maps():
    ribbons6 = set()
    for representative in six_vertex_types():
        ribbons6.update(flip_rotations(representative))
    assert {tuple(sorted(map(len, atlas["faces"](alpha))))
            for alpha in ribbons6} == SIX_VERTEX_PARTITIONS

    cores8 = set()
    loop_cores = digon_cores = 0
    loop_partitions = set()
    digon_partitions = set()
    for alpha in ribbons6:
        for dart in range(18):
            if dart > alpha[dart]:
                continue
            loop = restore_loop(alpha, dart)
            loop_partition = tuple(sorted(map(len, atlas["faces"](loop))))
            loop_partitions.add(loop_partition)
            if loop_partition in CORE_TARGETS:
                cores8.add(loop)
                loop_cores += 1
            digon = atlas["restore_digon"](alpha, dart)
            digon_partition = tuple(sorted(map(len, atlas["faces"](digon))))
            digon_partitions.add(digon_partition)
            if digon_partition in CORE_TARGETS:
                cores8.add(digon)
                digon_cores += 1
    assert CORE_TARGETS.isdisjoint(loop_partitions | digon_partitions)

    finals = set()
    for alpha in cores8:
        for dart in range(24):
            if dart > alpha[dart]:
                continue
            restored = atlas["restore_digon"](alpha, dart)
            if tuple(sorted(map(len, atlas["faces"](restored)))) == FINAL_TARGET:
                finals.add(restored)
    return len(ribbons6), loop_cores, digon_cores, cores8, finals


@lru_cache(None)
def is_actual_identity(word):
    blocks = actual["reduced_syllables"](word)
    if not blocks:
        return True
    unknown = [tokens for _, tokens in blocks
               if not actual["witnessed_nonidentity"](tokens)]
    if unknown:
        raise AssertionError((word, blocks, unknown))
    return False


def search_map(task):
    map_index, alpha = task
    fs = atlas["faces"](alpha)
    outer = next(i for i, face in enumerate(fs) if len(face) == 1)
    long_face = next(i for i, face in enumerate(fs) if len(face) == 11)
    valid_orientations = admissible_colours = 0
    long_words = set()
    for direction_bits in range(1 << 15):
        datum = atlas["orientation_data"](alpha, direction_bits)
        if datum is None:
            continue
        valid_orientations += 1
        edge_darts, orientations, occurrences = datum
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
            admissible_colours += 1
            raw = tuple(atlas["face_word"](
                face, alpha, colours, orientations, occurrences
            ) for face in fs)
            # The five short internal identities are exactly Q-trivial.
            if any(atlas["q_reduce"](raw[index])
                   for index in range(7)
                   if index not in (outer, long_face)):
                continue
            if not atlas["q_reduce"](raw[long_face]):
                continue
            canonical = actual["canonical"](raw[long_face])
            long_words.add(canonical)
            if (is_actual_identity(raw[long_face])
                    and not is_actual_identity(raw[outer])):
                return {
                    "candidate": True,
                    "map_index": map_index,
                    "alpha": alpha,
                    "direction_bits": direction_bits,
                    "colours": colours,
                    "outer": outer,
                    "long_face": long_face,
                    "raw": raw,
                }
    return {
        "candidate": False,
        "map_index": map_index,
        "valid_orientations": valid_orientations,
        "admissible_colours": admissible_colours,
        "long_words": long_words,
        "actual_long_identities": tuple(
            word for word in long_words if is_actual_identity(word)
        ),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    r6, loops, digons, cores8, finals = generate_final_maps()
    print("SIX_VERTEX_RIBBONS", r6)
    print("RAW_LOOP_CORES", loops, "RAW_DIGON_CORES", digons,
          "EXACT_EIGHT_CORES", len(cores8))
    print("EXACT_FINAL_MAPS", len(finals), flush=True)

    pool = ProcessPoolExecutor(max_workers=args.workers)
    futures = [pool.submit(search_map, task)
               for task in enumerate(sorted(finals))]
    long_words = set()
    orientations = colours = 0
    try:
        for done, future in enumerate(as_completed(futures), 1):
            result = future.result()
            if result["candidate"]:
                print("CANDIDATE", json.dumps(result), flush=True)
                pool.shutdown(wait=False)
                return 1
            orientations += result["valid_orientations"]
            colours += result["admissible_colours"]
            long_words.update(result["long_words"])
            assert not result["actual_long_identities"], result
            print("DONE", done, "/", len(finals), flush=True)
    finally:
        pool.shutdown(wait=True)
    identities = tuple(word for word in long_words if is_actual_identity(word))
    print("VALID_ORIENTATIONS", orientations)
    print("ADMISSIBLE_COLOURS", colours)
    print("REQUIRED_LENGTH_ELEVEN_WORDS", len(long_words))
    print("ACTUAL_LENGTH_ELEVEN_IDENTITIES", len(identities))
    print("NO_CANDIDATE", len(finals))
    assert not identities
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
