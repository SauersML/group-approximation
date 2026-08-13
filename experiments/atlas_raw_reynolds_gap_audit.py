"""Certify that the compiled raw swap directly detects H-misalignment.

After the classical inner alignment, every second-chart syllable of the raw
source word lies in H.  Replacing those twelve syllables by their first-chart
copies makes the word trivial.  Unitary invariance and telescoping therefore
bound the normalized Hilbert--Schmidt distance of the raw word from one by
twelve times the maximum H-covariance defect.
"""

import json
import sys

sys.path.insert(0, "experiments")

from atlas_raw_compressor_amalgam_audit import decode_word  # noqa: E402
from atlas_boundary_amalgam_normal_form import (  # noqa: E402
    amalgam_normal_form,
    lies_in_h,
    record_normal_form,
    transported_word,
)
from atlas_boundary_group_algebra_audit import matrix_from_key  # noqa: E402
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX  # noqa: E402
from atlas_two_chart_search import gf2_inv, matrix_key, product  # noqa: E402


def main():
    with open("experiments/atlas-raw-compressor-source-words.json",
              "r", encoding="utf-8") as stream:
        source = json.load(stream)

    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    raw = transported_word(
        decode_word(source["raw_source_word"]),
        alignment, alignment_inverse)

    second = [(index, matrix) for index, (factor, matrix) in enumerate(raw)
              if factor == 2]
    if not second or not all(lies_in_h(matrix) for _index, matrix in second):
        raise AssertionError("a second-chart raw syllable is transverse to H")

    folded = product(*[[(1, matrix)] for _factor, matrix in raw])
    folded_normal = amalgam_normal_form(folded)
    if folded_normal:
        raise AssertionError("the H-folded raw word is not the identity")

    print(json.dumps({
        "word": "compiled scalarized raw swap",
        "source_syllables": len(raw),
        "second_chart_syllables": len(second),
        "all_second_chart_syllables_lie_in_H": True,
        "second_chart_H_letters": [
            {
                "source_position": index,
                "matrix_hex": matrix_key(matrix).hex(),
            }
            for index, matrix in second
        ],
        "word_after_replacing_chart_2_H_by_chart_1":
            record_normal_form(folded_normal),
        "replacement_count": len(second),
        "normalized_HS_consequence":
            "hsNorm(raw(U)-1) <= 12 * Delta_H",
        "tracial_separation_consequence":
            "Delta_H >= sqrt(2)/12 - o(1)",
        "reynolds_consequence":
            "1-hsNorm(E_H(U))^2 >= 1/24192 - o(1)",
    }, indent=2))


if __name__ == "__main__":
    main()

