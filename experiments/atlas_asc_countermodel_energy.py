"""Evaluate the (LINK+) energies inside the exact characteristic-two countermodel.

The countermodel of the rank-three audit is `E = M semidirect A_8` with
`M = F_2[A_8]/I`, `I = sum_q F_2[A_8] d_q`, `m = 1+I`, and second chart
`beta(g) = ((1+g)m, g)`.  That chart is conjugation of the first by the group
element `mu = (m, e)`, so the intertwining unitary is `U = lambda_E(mu)` and
everything the (LINK+) question asks about becomes a membership test:

    rho(x)U = lambda_E(x . m),
    <U, rho(x)U> = tr(lambda_E(mu^(-1) (x.m))) = delta( (1+x)m = 0 ),

because normalized traces of a regular representation are `delta_(h,e)` and
the trace is conjugation invariant.  Hence, exactly,

    sum_s l_s^2 = sum_(x in Z) (W_pkt)_x,      Z = { x : 1+x in I },
    a^2 + b^2   = 4 - 2[h_a in Z] - 2[h_b in Z],

with `W_pkt` the integral group-algebra element of
`atlas_asc_tangent_exact.py` (support 101).  Every boundary defect is zero in
this model and the interior separator's defect is `sqrt(2)`, so the model
gives a hard lower bound on the constant of (LINK+):

    C' >= (sum_s l_s^2) / ||pi_U(c_19243)-1||_2^2 = (sum_s l_s^2) / 2.

It also checks the established global bound `a^2+b^2 <= (1/14) sum_s l_s^2` at
a point that is nowhere near the classical fold -- a falsifiable prediction of
the whole framework, since the two sides are computed here by completely
different means (GF(2) ideal membership) than the eigenvalue problem that
produced 1/14.
"""

import argparse
import json
import os
import sys
import time
from collections import deque

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_asc_packet_build import raw_s3_letters  # noqa: E402
from atlas_asc_tangent_exact import (convolve_square,  # noqa: E402
                                     group_algebra_of_packet)
from atlas_asc_packet_build import code_of, index_group  # noqa: E402
from atlas_boundary_group_algebra_audit import matrix_from_key  # noqa: E402
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX  # noqa: E402
from atlas_boundary_inner_alignment import enumerate_gl4  # noqa: E402
from atlas_certified_a8_alignment import boundary_words  # noqa: E402
from atlas_two_chart_search import (I4, factor_generators,  # noqa: E402
                                    gf2_inv, gf2_mul, matrix_key)
from atlas_universal_modular_group_algebra import (  # noqa: E402
    LeftTranslations, aligned_derivative, insert_row, reduce_row)


def build_ideal(alignment, alignment_inverse, elements, index_by_key,
                budget):
    """Close the boundary derivatives under left translation (rank 20005)."""
    generators = [word[0][1] for _name, word in factor_generators()[:6]]
    permutations = [[index_by_key[matrix_key(gf2_mul(generator, element))]
                     for element in elements] for generator in generators]
    translations = LeftTranslations(permutations, len(elements))
    seeds = [aligned_derivative(word, alignment, alignment_inverse,
                                index_by_key)
             for word in boundary_words()]
    basis, rows, queue = {}, [], deque()
    for seed in seeds:
        residual, _ = insert_row(basis, seed)
        if residual:
            basis[residual.bit_length() - 1] = (residual, len(rows))
            rows.append(residual)
            queue.append(len(rows) - 1)
    started = time.monotonic()
    processed = 0
    while queue and time.monotonic() - started < budget:
        parent = queue.popleft()
        for image in translations.all_images(rows[parent]):
            processed += 1
            residual, _ = insert_row(basis, image)
            if residual:
                basis[residual.bit_length() - 1] = (residual, len(rows))
                rows.append(residual)
                queue.append(len(rows) - 1)
    return basis, len(rows), len(queue), processed


# --------------------------------------------------------------- subgroups

def subgroup_energy(packet, generators_keys, rows, table):
    """E(Z) = sum over Z of the W_pkt coefficients, Z = <generators>."""
    seen = {matrix_key(I4): I4.copy()}
    frontier = [I4.copy()]
    generators = [np.frombuffer(key, dtype=np.uint8).reshape(4, 4).copy()
                  for key in generators_keys]
    while frontier:
        current = frontier.pop()
        for generator in generators:
            value = gf2_mul(current, generator)
            key = matrix_key(value)
            if key not in seen:
                seen[key] = value
                frontier.append(value)
    return sum(packet.get(key, 0) for key in seen), len(seen)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--budget", type=float, default=900.0)
    parser.add_argument("--out", default="")
    args = parser.parse_args()
    started = time.time()

    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    elements = list(enumerate_gl4())
    index_by_key = {matrix_key(element): index
                    for index, element in enumerate(elements)}

    basis, rank, remaining, processed = build_ideal(
        alignment, alignment_inverse, elements, index_by_key, args.budget)

    # the packet element W_pkt over Z, from the same signed prefix sums
    _rows, table, _elements = index_group()
    vectors, skipped, matrices = group_algebra_of_packet(
        alignment, alignment_inverse, table)
    packet = {}
    for vector in vectors:
        for key, value in convolve_square(vector, matrices).items():
            packet[key] = packet.get(key, 0) + value

    identity_index = index_by_key[matrix_key(I4)]

    def in_stabilizer(key):
        """Is 1 + x in the ideal, i.e. does x fix m?"""
        row = (1 << identity_index) ^ (1 << index_by_key[key])
        residual, _ = reduce_row(basis, row)
        return residual == 0

    membership = {}
    linear_energy = 0
    for key, coefficient in packet.items():
        if key == matrix_key(I4):
            membership[key] = True
        else:
            membership[key] = in_stabilizer(key)
        if membership[key]:
            linear_energy += coefficient

    letters, _raw = raw_s3_letters(alignment, alignment_inverse)
    cov_in = [in_stabilizer(matrix_key(letter)) for letter in letters]
    covariance = 4 - 2 * sum(1 for flag in cov_in if flag)

    stabilized = sum(1 for flag in membership.values() if flag)
    report = {
        "left_ideal_rank": rank,
        "queue_remaining": remaining,
        "translations_processed": processed,
        "support_W_pkt": len(packet),
        "support_in_stabilizer": stabilized,
        "sum_linear_energy_in_countermodel": linear_energy,
        "covariance_energy_in_countermodel": covariance,
        "raw_S3_letters_fix_m": cov_in,
        "boundary_defect_sq": 0,
        "interior_defect_sq": 2,
        "global_bound_1_over_14_holds":
            bool(covariance <= linear_energy / 14.0 + 1e-9),
        "implied_lower_bound_on_C_prime":
            (linear_energy / 2.0) if linear_energy else 0.0,
        "words_skipped_nontrivial_at_fold": skipped,
        "elapsed_s": round(time.time() - started, 1),
    }
    # E(Z) = 0 should hold exactly when H <= Z, since ker rho(W_pkt) is the
    # H-fixed space: for a group model rho(x)U = U iff x fixes mu, so U lies
    # in the kernel iff H <= Z iff both raw letters fix mu iff cov = 0.
    h_keys = []
    for entry in range(1 << 9):
        block = np.array([[(entry >> (3 * r + c)) & 1 for c in range(3)]
                          for r in range(3)], dtype=np.uint8)
        matrix = I4.copy()
        matrix[:3, :3] = block
        try:
            gf2_inv(matrix)
        except ValueError:
            continue
        h_keys.append(matrix_key(matrix))
    energy_h, order_h = subgroup_energy(packet, h_keys[:], None, None)
    report["H_order"] = order_h
    report["E_of_H"] = energy_h
    report["E_of_trivial"] = packet.get(matrix_key(I4), 0)

    support = sorted(packet)
    singles = []
    for key in support:
        energy, order = subgroup_energy(packet, [key], None, None)
        singles.append((energy, order, key.hex()))
    singles.sort()
    report["cyclic_min"] = {"energy": singles[0][0], "order": singles[0][1],
                            "element_hex": singles[0][2]}
    report["cyclic_max"] = {"energy": singles[-1][0], "order": singles[-1][1],
                            "element_hex": singles[-1][2]}
    report["cyclic_zero_energy_count"] = sum(1 for e, _o, _k in singles
                                             if e == 0)

    contains_h = set(h_keys)
    violations = []
    best = None
    for i, left in enumerate(support):
        for right in support[i + 1:]:
            energy, order = subgroup_energy(packet, [left, right], None, None)
            if best is None or energy < best[0]:
                best = (energy, order, left.hex(), right.hex())
            if energy == 0 and order < order_h:
                violations.append({"order": order, "a": left.hex(),
                                   "b": right.hex()})
    report["pair_subgroup_min"] = {"energy": best[0], "order": best[1],
                                   "a": best[2], "b": best[3]} if best else None
    report["pair_zero_energy_below_H_order"] = violations[:5]
    report["equivalence_survived_pair_search"] = not violations

    text = json.dumps(report, indent=2, sort_keys=True)
    print(text)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as stream:
            stream.write(text + "\n")

if __name__ == "__main__":
    main()
