"""The local (ASCq) constant exactly: two group-algebra elements, one GEP.

Every one of the 234 first-boundary atlas words is trivial at the certified
classical fold `U = I`, so for a word `s = (f_1,g_1)...(f_L,g_L)` with total
product 1 and K2 syllables at the positions j, writing

    u_j = g_1...g_(j-1),      v_j = u_j g_j,

the suffix is forced: `q_j = (u_j g_j)^(-1)`, and the first-order term of
`pi_s(exp(eps A))` telescopes into a difference of CONJUGATIONS,

    lambda(u_j) [A, lambda(g_j)] lambda(q_j)
        = lambda(u_j) A lambda(u_j)^(-1) - lambda(v_j) A lambda(v_j)^(-1).

So with the conjugation representation `rho(x)A = lambda(x) A lambda(x)^(-1)`
and the group-algebra elements

    z_s     = sum_j (u_j - v_j)              in Z[A_8],
    W_pkt   = sum_s z_s^* z_s,
    W_cov   = sum_(h in {h_a,h_b}) (h-1)^*(h-1) = 4 - 2 h_a - 2 h_b,

the two quadratic forms of `atlas_asc_tangent_ratio.py` are exactly

    D(A) = <A, rho(W_pkt) A>,     Ncov(A) = <A, rho(W_cov) A>,

and the local constant is a generalized eigenvalue problem for one pair of
positive elements of Z[A_8]:

    C_loc = max { lambda : rho(W_cov) x = lambda rho(W_pkt) x }.

Because both are group-algebra elements, the answer is the same computed in
ANY representation containing every irreducible constituent -- the
conjugation module and the left regular module both do -- so this script
builds the two 20160 x 20160 group matrices and solves the GEP there in
double precision.  That replaces the whole stochastic search: no probes, no
optimizer, no manifold.

Two outputs, both certificates in the sense the lane needs:

  * ker(W_pkt) subseteq ker(W_cov)?  This is the quantitative form of the
    tangent statement recorded in `research/atlas-two-s3-covariance-collapse`
    ("the common derivative kernel is the H-fixed space in every irrep").
    If it FAILS there is a first-order escape and the collapse claim is
    refuted outright.
  * C_loc itself, the sharp first-order constant of (ASCq) restricted to the
    fold-trivial sub-packet.

Still not the theorem: this is the FIRST-ORDER constant at the classical
fold.  The exact characteristic-two countermodel in the same node is a
global object and is untouched by any local statement.
"""

import argparse
import json
import math
import os
import sys
import time

import numpy as np
import torch

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_asc_packet_build import (ORDER, code_of, index_group, merge,  # noqa
                                    raw_s3_letters, rows_of)
from atlas_boundary_amalgam_normal_form import transported_word  # noqa: E402
from atlas_boundary_group_algebra_audit import matrix_from_key  # noqa: E402
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX  # noqa: E402
from atlas_certified_a8_alignment import (  # noqa: E402
    CERTIFIED_REPRESENTATIVE_INDICES, boundary_words)
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key  # noqa


def group_algebra_of_packet(alignment, alignment_inverse, table,
                            selected=None):
    """z_s for every fold-trivial boundary word, as index -> integer dicts."""
    elements = {}

    def key_index(matrix):
        key = matrix_key(matrix)
        elements[key] = matrix.copy()
        return key

    words, skipped = [], []
    for index, raw in enumerate(boundary_words()):
        if selected is not None and index not in selected:
            continue
        word = merge(transported_word(raw, alignment, alignment_inverse))
        prefix = I4.copy()
        vector = {}
        for factor, matrix in word:
            image = gf2_mul(prefix, matrix)
            if factor == 2:
                before, after = key_index(prefix), key_index(image)
                vector[before] = vector.get(before, 0) + 1
                vector[after] = vector.get(after, 0) - 1
            prefix = image
        if not np.array_equal(prefix, I4):
            skipped.append(index)          # not trivial at the fold: no form
            continue
        words.append({key: value for key, value in vector.items() if value})
    return words, skipped, elements


def convolve_square(vector, elements):
    """Coefficients of z^* z for an integer z, keyed by matrix key."""
    out = {}
    items = [(elements[key], value) for key, value in vector.items()]
    for left, coefficient_left in items:
        left_inverse = gf2_inv(left)
        for right, coefficient_right in items:
            key = matrix_key(gf2_mul(left_inverse, right))
            out[key] = out.get(key, 0) + coefficient_left * coefficient_right
    return out


def group_matrices(weights, rows, table):
    """L_w[i,j] = w(m_i m_j^{-1}) for each weight vector, built row by row.

    The full multiplication table is 20160^2 int32 = 1.6 GiB and is never
    needed: one row of it is four XOR reductions over the nibble-encoded
    rows of the inverses, vectorized across the whole group.
    """
    inverse_rows = np.zeros((ORDER, 4), dtype=np.uint16)
    # rows of m_j^{-1}: recover m_j from its code, invert, re-encode
    codes = np.flatnonzero(table >= 0)
    order_of_code = table[codes]
    for code, position in zip(codes, order_of_code):
        matrix = np.zeros((4, 4), dtype=np.uint8)
        for r in range(4):
            nibble = (int(code) >> (4 * r)) & 15
            for c in range(4):
                matrix[r, c] = (nibble >> c) & 1
        inverse_rows[position] = rows_of(gf2_inv(matrix))

    out = [np.zeros((ORDER, ORDER), dtype=np.float64) for _ in weights]
    acc = np.zeros((ORDER, 4), dtype=np.uint16)
    for i in range(ORDER):
        for r in range(4):
            mask = int(rows[i, r])
            value = np.zeros(ORDER, dtype=np.uint16)
            for l in range(4):
                if mask & (1 << l):
                    value = value ^ inverse_rows[:, l]
            acc[:, r] = value
        index = table[(acc[:, 0] | (acc[:, 1] << 4) | (acc[:, 2] << 8)
                       | (acc[:, 3] << 12)).astype(np.int64)]
        for slot, weight in enumerate(weights):
            out[slot][i] = weight[index]
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tol", type=float, default=1e-9,
                        help="relative kernel threshold for W_pkt")
    parser.add_argument("--words", default="all",
                        help="all | tangent5 | certified24 | i,j,k")
    parser.add_argument("--out", default="")
    args = parser.parse_args()
    started = time.time()
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")

    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    rows, table, _elements = index_group()

    selected = None
    if args.words == "tangent5":
        selected = {0, 11, 30, 44, 55}
    elif args.words == "certified24":
        selected = set(CERTIFIED_REPRESENTATIVE_INDICES)
    elif args.words != "all":
        selected = {int(value) for value in args.words.split(",")}
    vectors, skipped, elements = group_algebra_of_packet(
        alignment, alignment_inverse, table, selected)
    packet = {}
    for vector in vectors:
        for key, value in convolve_square(vector, elements).items():
            packet[key] = packet.get(key, 0) + value

    letters, _raw = raw_s3_letters(alignment, alignment_inverse)
    cov = {}
    identity_key = matrix_key(I4)
    for letter in letters:
        cov[identity_key] = cov.get(identity_key, 0) + 2
        key = matrix_key(letter)
        cov[key] = cov.get(key, 0) - 2

    report = {
        "word_selection": args.words,
        "words_with_a_form": len(vectors),
        "words_skipped_nontrivial_at_fold": skipped,
        "support_W_pkt": len(packet),
        "support_W_cov": len(cov),
        "trace_W_pkt": packet.get(identity_key, 0),
        "trace_W_cov": cov.get(identity_key, 0),
        "sum_W_pkt": sum(packet.values()),
        "sum_W_cov": sum(cov.values()),
        "device": str(device),
        "seconds_to_algebra": round(time.time() - started, 1),
    }

    def as_vector(coefficients):
        vector = np.zeros(ORDER, dtype=np.float64)
        for key, value in coefficients.items():
            matrix = np.frombuffer(key, dtype=np.uint8).reshape(4, 4)
            vector[int(table[code_of(matrix)])] = float(value)
        return vector

    host_left, host_right = group_matrices(
        [as_vector(packet), as_vector(cov)], rows, table)
    report["seconds_to_matrices"] = round(time.time() - started, 1)
    left = torch.from_numpy(host_left).to(device)
    right = torch.from_numpy(host_right).to(device)
    del host_left, host_right
    values, basis = torch.linalg.eigh(left)
    top = float(values.max())
    keep = values > args.tol * top
    report["W_pkt_rank"] = int(keep.sum())
    report["W_pkt_kernel_dim"] = int(ORDER - keep.sum())
    report["W_pkt_max_eigenvalue"] = top
    report["W_pkt_min_positive_eigenvalue"] = float(values[keep].min())

    kernel = basis[:, ~keep]
    if kernel.shape[1]:
        leak = kernel.t() @ (right @ kernel)
        report["cov_energy_on_packet_kernel"] = float(
            torch.linalg.matrix_norm(leak, ord=2))
    else:
        report["cov_energy_on_packet_kernel"] = 0.0

    # a nonzero covariance energy on the kernel IS a first-order escape: the
    # supremum is then infinite and the value on the support is not the
    # constant of anything.  (Measured: the 24 certified representatives leak
    # exactly 6, the five tangent words and the full 234 leak 1e-17.)
    report["first_order_escape"] = bool(
        report["cov_energy_on_packet_kernel"] > 1e-8)
    support = basis[:, keep]
    scale = values[keep].rsqrt()
    reduced = (support * scale).t() @ (right @ (support * scale))
    reduced = 0.5 * (reduced + reduced.t())
    spectrum = torch.linalg.eigvalsh(reduced)
    report["C_loc_on_support"] = float(spectrum.max())
    report["C_loc"] = (float("inf") if report["first_order_escape"]
                       else float(spectrum.max()))
    report["C_loc_second"] = float(spectrum[-2]) if spectrum.numel() > 1 else 0.0
    report["elapsed_s"] = round(time.time() - started, 1)
    text = json.dumps(report, indent=2, sort_keys=True)
    print(text)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as stream:
            stream.write(text + "\n")


if __name__ == "__main__":
    main()
