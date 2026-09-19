"""Compile the two-S3 covariance-collapse question into one GPU packet.

`research/atlas-two-s3-covariance-collapse` asks for the dimension-free
implication

    max_(s in bar_S) ||pi_U(s)-1||_2 -> 0   ==>   a^2+b^2 -> 0,

where pi_U is the canonical regular-A8 relative-unitary model of
`leavitt-regular-atlas-hyperlinearity-criterion`,

    pi_U(h) = lambda(h) (x) I_k          (h in K_1),
    pi_U(h) = U (lambda(h) (x) I_k) U^*  (h in K_2),

and a,b are the covariance defects of the two raw S_3 involutions of
`TRUE_RAW_WORD_REYNOLDS_GAP`.  `raw-swap-forces-two-s3-covariance-energy`
supplies the opposite bound a^2+b^2 >= 1/40-o(1), so the two sides cannot
both hold and a numerically achievable low-defect point with large
covariance is a refutation of the route, while a clean trade-off curve is
evidence for it.

This script does the exact finite half on CPU and freezes it:

  * enumerate GL(4,2) = A_8 and index it;
  * transport every packet word through the certified inner alignment;
  * merge adjacent syllables into strict K1/K2 alternation;
  * emit the left-regular gather index of every element that occurs.

Everything downstream is then dense linear algebra on one unitary, which
is what `atlas_asc_covariance_gpu.py` runs.  Nothing here is a proof: the
packet is exact, the search over U is evidence only.
"""

import argparse
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_boundary_amalgam_normal_form import (  # noqa: E402
    lies_in_h, transported_word)
from atlas_boundary_group_algebra_audit import matrix_from_key  # noqa: E402
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX  # noqa: E402
from atlas_boundary_inner_alignment import enumerate_gl4  # noqa: E402
from atlas_certified_a8_alignment import (  # noqa: E402
    CERTIFIED_REPRESENTATIVE_INDICES, PHASE_INDEX, boundary_words)
from atlas_raw_compressor_amalgam_audit import decode_word  # noqa: E402
from atlas_two_chart_search import (  # noqa: E402
    I4, gf2_inv, gf2_mul, matrix_key)

ORDER = 20160


# ---------------------------------------------------------------- encoding

def rows_of(matrix):
    """Encode a 4x4 F2 matrix as four nibbles, bit j of row i = m[i][j]."""
    bits = (matrix & 1).astype(np.uint16)
    return (bits[:, 0] | (bits[:, 1] << 1) |
            (bits[:, 2] << 2) | (bits[:, 3] << 3)).astype(np.uint16)


def code_of(matrix):
    r = rows_of(matrix)
    return int(r[0] | (r[1] << 4) | (r[2] << 8) | (r[3] << 12))


def index_group():
    """Return (rows[20160,4] uint16, code->index table, elements list)."""
    elements = enumerate_gl4()
    rows = np.zeros((ORDER, 4), dtype=np.uint16)
    table = np.full(1 << 16, -1, dtype=np.int32)
    for position, element in enumerate(elements):
        rows[position] = rows_of(element)
        table[code_of(element)] = position
    if int((table >= 0).sum()) != ORDER:
        raise AssertionError("group indexing lost elements")
    return rows, table, elements


def left_gather(matrix, rows, table):
    """Gather index of lambda(g): (lambda(g) v)[x] = v[gather[x]].

    lambda is the left regular representation, so gather[x] = index of
    g^{-1} m_x.  The product is computed on all 20160 elements at once by
    XOR-ing nibble rows, which is the only step that would otherwise cost
    a Python loop over the group.
    """
    inverse = rows_of(gf2_inv(matrix))
    out = np.zeros((ORDER, 4), dtype=np.uint16)
    for i in range(4):
        acc = np.zeros(ORDER, dtype=np.uint16)
        mask = int(inverse[i])
        for j in range(4):
            if mask & (1 << j):
                acc ^= rows[:, j]
        out[:, i] = acc
    codes = (out[:, 0] | (out[:, 1] << 4) |
             (out[:, 2] << 8) | (out[:, 3] << 12)).astype(np.int64)
    gather = table[codes]
    if int((gather < 0).sum()):
        raise AssertionError("left translation escaped the group")
    return gather.astype(np.int32)


# ------------------------------------------------------------------- words

def merge(word):
    """Strict K1/K2 alternation with adjacent syllables multiplied out."""
    out = []
    for factor, matrix in word:
        if out and out[-1][0] == factor:
            out[-1] = (factor, gf2_mul(out[-1][1], matrix))
        else:
            out.append((factor, matrix.copy()))
        if np.array_equal(out[-1][1], I4):
            out.pop()
            if len(out) >= 2 and out[-1][0] == out[-2][0]:
                tail = out.pop()
                out[-1] = (tail[0], gf2_mul(out[-1][1], tail[1]))
    return out


def invert(word):
    return [(factor, gf2_inv(matrix)) for factor, matrix in reversed(word)]


def commutator(left, right):
    return merge(left + right + invert(left) + invert(right))


def folded(word):
    """Value in A_8 when both charts are read in the first one (U = I)."""
    value = I4.copy()
    for _factor, matrix in word:
        value = gf2_mul(value, matrix)
    return value


def raw_s3_letters(alignment, alignment_inverse):
    """The two second-chart involutions of the compiled raw source word."""
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-raw-compressor-source-words.json"),
              "r", encoding="utf-8") as stream:
        source = json.load(stream)
    raw = transported_word(decode_word(source["raw_source_word"]),
                           alignment, alignment_inverse)
    second = [matrix for factor, matrix in raw if factor == 2]
    if not second or not all(lies_in_h(matrix) for matrix in second):
        raise AssertionError("a second-chart raw syllable is transverse to H")
    distinct = {matrix_key(matrix): matrix for matrix in second}
    if len(distinct) != 2:
        raise AssertionError("the raw H-letter count changed")
    letters = [distinct[key] for key in sorted(distinct)]
    counts = sorted(sum(1 for matrix in second
                        if matrix_key(matrix) == matrix_key(letter))
                    for letter in letters)
    if counts != [4, 8]:
        raise AssertionError("the raw H-letter multiplicities changed")
    if not np.array_equal(folded([(1, matrix) for _f, matrix in raw]), I4):
        raise AssertionError("the H-folded raw word is not the identity")
    return letters, raw


def interior_word(alignment, alignment_inverse):
    """c_19243 = [p1_12, q_19243], the interior separator of the audit."""
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"),
              "r", encoding="utf-8") as stream:
        record = json.load(stream)[0]
    q = [(int(entry["factor"]),
          np.frombuffer(bytes.fromhex(entry["matrix_f2_hex"]),
                        dtype=np.uint8).reshape(4, 4).copy())
         for entry in record["word"]]
    q = transported_word(q, alignment, alignment_inverse)
    x = I4.copy()
    x[1, 2] = 1                                     # p1_12 = I + E_12
    return commutator([(1, x)], q), q


# -------------------------------------------------------------------- main

def build(out_path):
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    rows, table, _elements = index_group()

    boundary = [merge(transported_word(word, alignment, alignment_inverse))
                for word in boundary_words()]
    interior, q19243 = interior_word(alignment, alignment_inverse)
    letters, _raw = raw_s3_letters(alignment, alignment_inverse)

    names, words = [], []
    for index, word in enumerate(boundary):
        tag = "boundary"
        if index in CERTIFIED_REPRESENTATIVE_INDICES:
            tag = "certified"
        elif index == PHASE_INDEX:
            tag = "phase"
        names.append("%s:%d" % (tag, index))
        words.append(word)
    names.append("interior:19243")
    words.append(interior)

    # every distinct group element that any syllable or covariance needs
    keyed = {}

    def element_index(matrix):
        key = matrix_key(matrix)
        if key not in keyed:
            keyed[key] = (len(keyed), matrix.copy())
        return keyed[key][0]

    encoded = [[(factor, element_index(matrix)) for factor, matrix in word]
               for word in words]
    cov = [element_index(letter) for letter in letters]

    gathers = np.zeros((len(keyed), ORDER), dtype=np.int32)
    for position, matrix in sorted(keyed.values()):
        gathers[position] = left_gather(matrix, rows, table)

    lengths = np.array([len(word) for word in encoded], dtype=np.int32)
    offsets = np.concatenate(([0], np.cumsum(lengths))).astype(np.int64)
    flat_factor = np.array([factor for word in encoded for factor, _ in word],
                           dtype=np.int8)
    flat_element = np.array([elem for word in encoded for _, elem in word],
                            dtype=np.int32)

    # U = I baseline: pi_I(word) = lambda(product of all syllables)
    fold_trivial = np.array([bool(np.array_equal(folded(word), I4))
                             for word in words])
    certified_ok = all(fold_trivial[i] for i in CERTIFIED_REPRESENTATIVE_INDICES)
    phase_ok = not fold_trivial[PHASE_INDEX]

    np.savez_compressed(
        out_path,
        gathers=gathers,
        offsets=offsets,
        flat_factor=flat_factor,
        flat_element=flat_element,
        cov_elements=np.array(cov, dtype=np.int32),
        fold_trivial=fold_trivial,
        names=np.array(names),
    )

    summary = {
        "order": ORDER,
        "words": len(words),
        "distinct_elements": len(keyed),
        "syllables_total": int(lengths.sum()),
        "syllable_length_histogram": {
            str(int(value)): int(count) for value, count
            in zip(*np.unique(lengths, return_counts=True))},
        "k2_syllables_max": int(max(
            sum(1 for factor, _ in word if factor == 2) for word in encoded)),
        "identity_baseline": {
            "words_trivial_at_U_eq_I": int(fold_trivial.sum()),
            "certified_all_trivial": bool(certified_ok),
            "phase_word_survives": bool(phase_ok),
            "interior_word_trivial": bool(fold_trivial[-1]),
        },
        "interior_word_syllables": len(interior),
        "q19243_syllables": len(q19243),
        "covariance_letters_hex": [
            matrix_key(letter).hex() for letter in letters],
        "out": out_path,
    }
    if not certified_ok or not phase_ok:
        summary["gate"] = "FAILED: certified/phase baseline moved"
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default="experiments/atlas-asc-packet.npz")
    args = parser.parse_args()
    print(json.dumps(build(args.out), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
