"""Repair an index-two projective packet using unused exact short cycles.

The input boundary-reduced certificate contains a rationally spanning packet
and a few unused cycles.  This script first screens replacements in true
homology over ``F_2`` and then computes their exact integral projected index
using the sparse index profiler.  If a mod-2-full replacement has odd index
``m > 1``, one of

    incoming +/- ((m - 1) / 2) outgoing

has index one: determinant is linear in the replacement row, the original
packet determinant has absolute value two, and the trial determinant has
absolute value ``m``.  The script tests both signs exactly and exports the
first resulting ``Q``-basis packet.

Run with Sage's Python on MSI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

from sage.all import GF, ZZ, matrix, vector

from sl3_projective_cellular_analyze import build_boundaries, parse
from sl3_projective_packet_index_sparse import profile


def record_vector(record, dimension):
    result = vector(ZZ, dimension)
    for entry in record["representative"]:
        result[entry["coordinate"]] = entry["coefficient"]
    return result


def vector_stats(value):
    coefficients = [abs(int(entry)) for entry in value if entry]
    return {
        "l1": sum(coefficients),
        "l2_squared": sum(entry * entry for entry in coefficients),
        "maximum_absolute_coefficient": max(coefficients, default=0),
        "support_size": len(coefficients),
    }


def combination_record(value, incoming, outgoing, multiplier):
    stats = vector_stats(value)
    return {
        "added_boundary": [],
        "improved": False,
        "initial": stats,
        "reduced": stats,
        "packet_source": "integral index-two parity correction",
        "construction": {
            "formula": "incoming + multiplier * outgoing",
            "incoming_record_index": incoming,
            "outgoing_record_index": outgoing,
            "multiplier": multiplier,
        },
        "representative": [
            {"coordinate": int(index), "coefficient": int(entry)}
            for index, entry in enumerate(value) if entry
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("packet", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--time-limit", type=float, default=60.0)
    args = parser.parse_args()

    started = time.monotonic()
    level, degree, orbit_dimensions, cells = parse(args.cellular_input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)
    d2 = boundaries[2].change_ring(ZZ)
    d3 = boundaries[3].change_ring(ZZ)
    packet_bytes = args.packet.read_bytes()
    packet = json.loads(packet_bytes)
    if packet["level"] != level:
        raise ValueError("level mismatch")
    candidates = [
        record_vector(record, dimensions[2]) for record in packet["records"]]
    if any(candidate * d2 != 0 for candidate in candidates):
        raise AssertionError("input packet contains a noncycle")
    selected = list(packet["shortest_spanning_packet_indices"])
    rank = dimensions[2] - d2.rank() - d3.rank()
    if len(selected) != rank:
        raise AssertionError("selected packet has the wrong rational rank")
    boundary_basis = d3.matrix_from_rows(packet["selected_boundary_rows"])
    boundary_index, boundary_diagnostics, boundary_seconds = profile(
        boundary_basis, args.time_limit)
    initial_cycles = matrix(ZZ, [candidates[index] for index in selected])
    initial_total_index, initial_diagnostics, initial_seconds = profile(
        boundary_basis.stack(initial_cycles), args.time_limit)
    if initial_total_index % boundary_index:
        raise AssertionError("boundary index does not divide initial total index")
    initial_projected_index = initial_total_index // boundary_index
    if initial_projected_index != 2:
        raise ValueError(
            "index-two correction requires an initial projected index of two")

    field = GF(2)
    cycle_matrix = d2.transpose().change_ring(field)
    cycle_basis = cycle_matrix.right_kernel_matrix()
    cycle_pivots = list(cycle_basis.pivots())
    pivot_inverse = cycle_basis.matrix_from_columns(cycle_pivots).inverse()
    boundary_coordinates = (
        d3.change_ring(field).matrix_from_columns(cycle_pivots)
        * pivot_inverse)
    quotient_dual = boundary_coordinates.right_kernel_matrix()
    signatures = []
    for candidate in candidates:
        coordinates = (
            vector(field, [candidate[column] for column in cycle_pivots])
            * pivot_inverse)
        signatures.append(quotient_dual * coordinates.column())

    def signature_rank(indices):
        return matrix(field, [
            list(signatures[index].column(0)) for index in indices]).rank()

    initial_mod2_rank = signature_rank(selected)
    candidate_mod2_span_rank = signature_rank(list(range(len(candidates))))
    if candidate_mod2_span_rank < rank:
        raise AssertionError("candidate cycles do not span integral homology mod 2")
    attempts = []
    chosen = None
    unused = sorted(
        (index for index in range(len(candidates)) if index not in selected),
        key=lambda index: (
            packet["records"][index]["reduced"]["l2_squared"], index),
    )
    for incoming in unused:
        for position, outgoing in enumerate(selected):
            trial = list(selected)
            trial[position] = incoming
            mod2_rank = signature_rank(trial)
            if mod2_rank != rank:
                attempts.append({
                    "incoming": incoming,
                    "outgoing": outgoing,
                    "outgoing_position": position,
                    "mod2_rank": int(mod2_rank),
                    "exact_profile_run": False,
                    "rejection": "does not repair the mod-2 parity defect",
                })
                continue
            trial_cycles = matrix(ZZ, [candidates[index] for index in trial])
            rational_rank = boundary_basis.stack(trial_cycles).rank()
            expected_rational_rank = boundary_basis.nrows() + rank
            if rational_rank != expected_rational_rank:
                attempts.append({
                    "incoming": incoming,
                    "outgoing": outgoing,
                    "outgoing_position": position,
                    "mod2_rank": int(mod2_rank),
                    "rational_rank": int(rational_rank),
                    "expected_rational_rank": expected_rational_rank,
                    "exact_profile_run": False,
                    "rejection": "torsion-derived mod-2 direction",
                })
                continue
            total_index, diagnostics, seconds = profile(
                boundary_basis.stack(trial_cycles), args.time_limit)
            if total_index % boundary_index:
                raise AssertionError("boundary index does not divide total index")
            projected_index = total_index // boundary_index
            attempts.append({
                "incoming": incoming,
                "outgoing": outgoing,
                "outgoing_position": position,
                "mod2_rank": int(mod2_rank),
                "rational_rank": int(rational_rank),
                "exact_profile_run": True,
                "boundary_plus_packet_index": total_index,
                "projected_packet_index_in_q": projected_index,
                "profile_seconds": seconds,
                "diagnostics": diagnostics,
            })
            if projected_index == 1:
                chosen = trial
                break
            if projected_index % 2 == 0:
                attempts[-1]["rejection"] = (
                    "mod-2 signature is supported by torsion; free packet "
                    "index remains even")
                continue

            correction_size = (projected_index - 1) // 2
            for sign in (-1, 1):
                multiplier = sign * correction_size
                adjusted = (
                    candidates[incoming]
                    + multiplier * candidates[outgoing])
                adjusted_cycles = [candidates[index] for index in trial]
                adjusted_cycles[position] = adjusted
                adjusted_index, adjusted_diagnostics, adjusted_seconds = profile(
                    boundary_basis.stack(matrix(ZZ, adjusted_cycles)),
                    args.time_limit)
                if adjusted_index % boundary_index:
                    raise AssertionError(
                        "boundary index does not divide corrected total index")
                adjusted_projected_index = adjusted_index // boundary_index
                attempts.append({
                    "incoming": incoming,
                    "outgoing": outgoing,
                    "outgoing_position": position,
                    "mod2_rank": int(mod2_rank),
                    "exact_profile_run": True,
                    "parity_corrected": True,
                    "correction_multiplier": multiplier,
                    "boundary_plus_packet_index": adjusted_index,
                    "projected_packet_index_in_q": adjusted_projected_index,
                    "profile_seconds": adjusted_seconds,
                    "diagnostics": adjusted_diagnostics,
                })
                if adjusted_projected_index == 1:
                    chosen_record = combination_record(
                        adjusted, incoming, outgoing, multiplier)
                    chosen_index = len(candidates)
                    candidates.append(adjusted)
                    adjusted_coordinates = (
                        vector(field, [
                            adjusted[column] for column in cycle_pivots])
                        * pivot_inverse)
                    signatures.append(
                        quotient_dual * adjusted_coordinates.column())
                    packet["records"].append(chosen_record)
                    chosen = list(trial)
                    chosen[position] = chosen_index
                    break
            if chosen is not None:
                break
        if chosen is not None:
            break
    if chosen is None:
        raise ValueError("no exact saturated replacement packet found")

    chosen_cycles = matrix(ZZ, [candidates[index] for index in chosen])
    chosen_gram = chosen_cycles * chosen_cycles.transpose()
    output = dict(packet)
    output.update({
        "source_packet_sha256": hashlib.sha256(packet_bytes).hexdigest(),
        "shortest_spanning_packet_indices": chosen,
        "shortest_spanning_packet_gram": [
            [int(entry) for entry in row] for row in chosen_gram.rows()],
        "shortest_spanning_packet_absolute_gram_row_sums": [
            sum(abs(int(entry)) for entry in row)
            for row in chosen_gram.rows()],
        "shortest_spanning_packet_maximum_absolute_gram_row_sum": max(
            sum(abs(int(entry)) for entry in row)
            for row in chosen_gram.rows()),
        "shortest_spanning_packet_maximum_squared_norm": max(
            int(chosen_gram[index, index]) for index in range(rank)),
        "shortest_spanning_packet_maximum_support": max(
            packet["records"][index]["reduced"]["support_size"]
            for index in chosen),
        "shortest_spanning_packet_maximum_coefficient": max(
            packet["records"][index]["reduced"][
                "maximum_absolute_coefficient"]
            for index in chosen),
        "integral_saturation_repair": {
            "initial_selected_indices": selected,
            "initial_mod2_homology_rank": int(initial_mod2_rank),
            "ambient_mod2_homology_dimension": int(quotient_dual.nrows()),
            "candidate_mod2_span_rank": int(candidate_mod2_span_rank),
            "final_mod2_homology_rank": int(signature_rank(chosen)),
            "selected_boundary_lattice_index_in_saturation": boundary_index,
            "initial_boundary_plus_packet_index": initial_total_index,
            "initial_projected_packet_index_in_q": initial_projected_index,
            "final_projected_packet_index_in_q": 1,
            "attempts": attempts,
            "boundary_profile_diagnostics": boundary_diagnostics,
            "boundary_profile_seconds": boundary_seconds,
            "initial_packet_profile_diagnostics": initial_diagnostics,
            "initial_packet_profile_seconds": initial_seconds,
        },
        "elapsed_seconds_with_saturation_repair": time.monotonic() - started,
        "scope": (
            "exact boundary-reduced cycle packet repaired to projected index "
            "one using F_2 screening, the index-two determinant correction, "
            "and exact sparse HNF indices"),
    })
    args.output.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(json.dumps({
        "level": level,
        "initial_selected_indices": selected,
        "initial_mod2_homology_rank": int(initial_mod2_rank),
        "ambient_mod2_homology_dimension": int(quotient_dual.nrows()),
        "candidate_mod2_span_rank": int(candidate_mod2_span_rank),
        "initial_projected_packet_index_in_q": initial_projected_index,
        "final_selected_indices": chosen,
        "final_mod2_homology_rank": int(signature_rank(chosen)),
        "projected_packet_index_in_q": 1,
        "maximum_squared_norm": output[
            "shortest_spanning_packet_maximum_squared_norm"],
        "maximum_absolute_gram_row_sum": output[
            "shortest_spanning_packet_maximum_absolute_gram_row_sum"],
        "elapsed_seconds": output["elapsed_seconds_with_saturation_repair"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
