"""Read-only exact collision audit for the first full-Leavitt CA seed.

Run only through the MSI wrapper, never locally. This compares the two
composition rectangles with their marked A8*A8 source. If both partitions
agree, no finite alphabet or choice of local rules on these memories can
produce a strict split CA: the same rule pair would do so on a virtually
free, hence surjunctive, group.
"""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "experiments"))

from atlas_two_chart_search import (
    factor_generators, product, inverse, matrix_key, q, commutator,
    transvection, gf2_mul,
)
from atlas_kernel_collision_enumerator import (
    evaluate_word, common_right_depths, exact_image_key,
)

def word_key(word):
    return tuple((factor, matrix_key(matrix)) for factor, matrix in word)

def partition(keys):
    labels = {}
    answer = []
    for key in keys:
        answer.append(labels.setdefault(key, len(labels)))
    return answer

def audit_rectangle(source_left, source_right, target_left, target_right):
    source_words = [product(a, b) for a in source_left for b in source_right]
    target_words = [product(a, b) for a in target_left for b in target_right]
    values = [evaluate_word(word) for word in target_words]
    depths = common_right_depths(list(zip(target_words, values)))
    source = partition([word_key(word) for word in source_words])
    target = partition([exact_image_key(value, depths) for value in values])
    extra = []
    lost = []
    for i in range(len(source_words)):
        for j in range(i):
            if target[i] == target[j] and source[i] != source[j]:
                extra.append([divmod(j, len(source_right)), divmod(i, len(source_right))])
            if source[i] == source[j] and target[i] != target[j]:
                lost.append([divmod(j, len(source_right)), divmod(i, len(source_right))])
    return {
        "shape": [len(source_left), len(source_right)],
        "source_partition": source,
        "target_partition": target,
        "source_products": len(set(source)),
        "target_products": len(set(target)),
        "extra_target_collisions": extra,
        "source_collisions_absent_in_target": lost,
        "same_collision_partition": source == target,
    }

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("seed", choices=("first", "fresh-v4"))
    args = parser.parse_args()
    factors = [word for _, word in factor_generators()]
    pair = []
    for offset in (0, 6):
        for indices in ((0, 1, 2), (3, 5, 4)):
            pair.append(product(*(factors[offset + i] for i in indices)))
    encoder = [[]] + pair
    decoder = [inverse(word) for word in encoder]
    source_encoder = encoder
    source_decoder = decoder
    encoder_names = ["1", "a1=012", "b1=354", "a2=012", "b2=354"]
    decoder_names = ["1", "a1^-1", "b1^-1", "a2^-1", "b2^-1"]
    source_name = "A8*A8"
    if args.seed == "fresh-v4":
        target_a = commutator(q(1, 3, "e"), q(3, 2, "E"))
        target_b = commutator(q(1, 3, "f"), q(3, 2, "F"))
        target_c = commutator(q(1, 3, "1"), q(3, 2, "1"))
        matrix_a = transvection(0, 1)
        matrix_b = transvection(0, 2)
        fresh_a = [(3, matrix_a)]
        fresh_b = [(3, matrix_b)]
        fresh_c = [(3, gf2_mul(matrix_a, matrix_b))]
        source_encoder = encoder + [fresh_b]
        source_decoder = decoder + [fresh_a, fresh_c]
        encoder = encoder + [target_b]
        decoder = decoder + [target_a, target_c]
        encoder_names += ["B=[q13(f),q32(F)]"]
        decoder_names += ["A=[q13(e),q32(E)]", "C=[q13(1),q32(1)]"]
        source_name = "(A8*A8)*V4, fresh A,B with C=AB"
    forward = audit_rectangle(source_decoder, source_encoder, decoder, encoder)
    backward = audit_rectangle(source_encoder, source_decoder, encoder, decoder)
    lifted = forward["same_collision_partition"] and backward["same_collision_partition"]
    answer = {
        "seed": args.seed,
        "source": source_name,
        "encoder_memory": encoder_names,
        "decoder_memory": decoder_names,
        "forward": forward,
        "backward": backward,
        "both_rectangles_lift_to_virtually_free_source": lifted,
        "conclusion": (
            "No strict split CA on these memories over any finite alphabet."
            if lifted else
            "Source-lift obstruction does not decide this seed; no CA rule has been found."
        ),
    }
    print(json.dumps(answer, indent=2))

if __name__ == "__main__":
    main()
