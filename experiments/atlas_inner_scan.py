"""Exhaust all inner relative alignments of the two GL_4(F_2) charts."""

import collections
import json

import numpy as np

import atlas_two_chart_search as atlas


def all_gl4():
    for bits in range(1 << 16):
        flat = np.array([(bits >> i) & 1 for i in range(16)],
                        dtype=np.uint8)
        g = flat.reshape(4, 4)
        try:
            inverse = atlas.gf2_inv(g)
        except ValueError:
            continue
        yield bits, g, inverse


def evaluate(word, h, h_inverse):
    value = atlas.I4.copy()
    for factor, g in word:
        image = g if factor == 1 else atlas.gf2_mul(
            atlas.gf2_mul(h, g), h_inverse)
        value = atlas.gf2_mul(value, image)
    return value


def main():
    names, words = atlas.relation_family()
    atlas.validate_relation_words(names, words)
    histogram = collections.Counter()
    best = []
    best_count = -1
    total = 0
    for bits, h, h_inverse in all_gl4():
        total += 1
        satisfied = [name for name, word in zip(names, words)
                     if np.array_equal(evaluate(word, h, h_inverse), atlas.I4)]
        count = len(satisfied)
        histogram[count] += 1
        if count > best_count:
            best_count = count
            best = [(bits, h.copy(), satisfied)]
        elif count == best_count:
            best.append((bits, h.copy(), satisfied))
    record = {
        "alignments": total,
        "relations": len(words),
        "best_exact": best_count,
        "best_count": len(best),
        "histogram": sorted(histogram.items()),
        "best": [{"bits": bits, "matrix": h.tolist(),
                  "failed": [name for name in names if name not in satisfied]}
                 for bits, h, satisfied in best[:8]],
    }
    print(json.dumps(record, sort_keys=True))


if __name__ == "__main__":
    main()
