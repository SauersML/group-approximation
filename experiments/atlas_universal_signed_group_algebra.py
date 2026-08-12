"""Certify signed atlas phase ideal membership at exceptional odd primes.

Together with the characteristic-two certificate and the cross-characteristic
rational certificates, these are the only remaining primes.  Rows are sparse
elements of F_p[A8].  The left ideal is closed under six generating left
translations until the marked derivative reduces to zero.  The optional
certificate records every source, modular elimination coefficient, pivot,
and final phase reduction for independent replay.
"""

import argparse
from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import time

import numpy as np

from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_certified_a8_alignment import (
    CERTIFIED_REPRESENTATIVE_INDICES,
    PHASE_INDEX,
    boundary_words,
)
from atlas_certified_dual_number_certificate import ALIGNMENT_KEY
from atlas_subset_dual_central_no_go import SURVIVOR_REPRESENTATIVES
from atlas_two_chart_search import (
    I4,
    factor_generators,
    gf2_inv,
    gf2_mul,
    matrix_key,
)


def add_scaled(target, source, coefficient, prime):
    for index, value in source.items():
        updated = (target.get(index, 0) + coefficient * value) % prime
        if updated:
            target[index] = updated
        elif index in target:
            del target[index]


def signed_derivative(word, alignment, alignment_inverse, index_by_key):
    prefix = I4.copy()
    coefficients = Counter()
    for factor, source_matrix in word:
        image = source_matrix
        if factor == 2:
            image = gf2_mul(gf2_mul(
                alignment, source_matrix
            ), alignment_inverse)
        before = prefix
        prefix = gf2_mul(prefix, image)
        if factor == 2:
            coefficients[index_by_key[matrix_key(before)]] += 1
            coefficients[index_by_key[matrix_key(prefix)]] -= 1
    if matrix_key(prefix) != matrix_key(I4):
        raise AssertionError("aligned boundary word is nontrivial")
    return {index: value for index, value in coefficients.items() if value}


def normalize_input(row, prime):
    return {
        index: value % prime
        for index, value in row.items() if value % prime
    }


def translate(row, permutation):
    return {permutation[index]: value for index, value in row.items()}


def reduce_row(row, basis_by_pivot, basis_rows, prime):
    reductions = []
    while row:
        pivot = max(row)
        row_id = basis_by_pivot.get(pivot)
        if row_id is None:
            return row, reductions
        factor = row[pivot]
        add_scaled(row, basis_rows[row_id], -factor, prime)
        reductions.append([row_id, factor])
    return row, reductions


def insert_source(source, row, basis_by_pivot, basis_rows, operations, prime):
    residual, reductions = reduce_row(
        row, basis_by_pivot, basis_rows, prime
    )
    if not residual:
        return None
    pivot = max(residual)
    inverse = pow(residual[pivot], prime - 2, prime)
    residual = {
        index: value * inverse % prime
        for index, value in residual.items()
    }
    row_id = len(basis_rows)
    basis_by_pivot[pivot] = row_id
    basis_rows.append(residual)
    operations.append({
        "source": source,
        "reductions": reductions,
        "normalization_inverse": inverse,
        "pivot": pivot,
    })
    return row_id


def verify_record(record, seeds, translations, phase):
    prime = record["prime"]
    basis_by_pivot = {}
    rows = []
    for expected_id, operation in enumerate(record["basis_operations"]):
        source = operation["source"]
        if source[0] == "seed":
            row = normalize_input(seeds[source[1]], prime)
        elif source[0] == "translate":
            _kind, generator_index, parent_id = source
            if parent_id >= expected_id:
                raise AssertionError("translation points forward")
            row = translate(rows[parent_id], translations[generator_index])
        else:
            raise AssertionError("unknown certificate source")
        for row_id, factor in operation["reductions"]:
            if row_id >= expected_id:
                raise AssertionError("reduction points forward")
            add_scaled(row, rows[row_id], -factor, prime)
        inverse = operation["normalization_inverse"]
        row = {
            index: value * inverse % prime
            for index, value in row.items() if value * inverse % prime
        }
        if not row:
            raise AssertionError("certificate inserts zero")
        pivot = max(row)
        if (
            pivot != operation["pivot"]
            or row[pivot] != 1
            or pivot in basis_by_pivot
        ):
            raise AssertionError("certificate pivot is invalid")
        basis_by_pivot[pivot] = expected_id
        rows.append(row)

    remainder = normalize_input(phase, prime)
    for row_id, factor in record["phase_reductions"]:
        if row_id >= len(rows):
            raise AssertionError("phase reduction uses unknown row")
        add_scaled(remainder, rows[row_id], -factor, prime)
    if remainder:
        raise AssertionError("certificate does not reduce phase to zero")


def solve_prime(prime, seeds, translations, phase):
    basis_by_pivot = {}
    basis_rows = []
    operations = []
    queue = deque()
    for seed_index, seed in enumerate(seeds):
        row_id = insert_source(
            ["seed", seed_index], normalize_input(seed, prime),
            basis_by_pivot, basis_rows, operations, prime
        )
        if row_id is not None:
            queue.append(row_id)
    remainder, phase_reductions = reduce_row(
        normalize_input(phase, prime), basis_by_pivot, basis_rows, prime
    )
    translations_processed = 0
    while remainder and queue:
        parent_id = queue.popleft()
        for generator_index, permutation in enumerate(translations):
            translations_processed += 1
            row_id = insert_source(
                ["translate", generator_index, parent_id],
                translate(basis_rows[parent_id], permutation),
                basis_by_pivot, basis_rows, operations, prime,
            )
            if row_id is not None:
                queue.append(row_id)
                remainder, reductions = reduce_row(
                    remainder, basis_by_pivot, basis_rows, prime
                )
                phase_reductions.extend(reductions)
                if not remainder:
                    break
    record = {
        "prime": prime,
        "basis_operations": operations,
        "phase_reductions": phase_reductions,
    }
    verify_record(record, seeds, translations, phase)
    return record, {
        "prime": prime,
        "left_ideal_rank_reached": len(basis_rows),
        "queued_rows_remaining": len(queue),
        "left_translations_processed": translations_processed,
        "phase_in_generated_left_ideal": not remainder,
        "maximum_row_support": max(len(row) for row in basis_rows),
        "average_row_support": round(
            sum(map(len, basis_rows)) / len(basis_rows), 6
        ),
        "certificate_basis_operations": len(operations),
        "certificate_phase_reductions": len(phase_reductions),
    }


def build_problem():
    elements = list(enumerate_gl4())
    if len(elements) != 20160:
        raise AssertionError("GL(4,2) enumeration changed")
    index_by_key = {
        matrix_key(element): index for index, element in enumerate(elements)
    }
    generators = [word[0][1] for _name, word in factor_generators()[:6]]
    translations = [
        [
            index_by_key[matrix_key(gf2_mul(generator, element))]
            for element in elements
        ]
        for generator in generators
    ]
    alignment = np.frombuffer(
        bytes.fromhex(ALIGNMENT_KEY), dtype=np.uint8
    ).reshape(4, 4).copy()
    alignment_inverse = gf2_inv(alignment)
    words = boundary_words()
    selected = sorted(set(
        CERTIFIED_REPRESENTATIVE_INDICES
        + SURVIVOR_REPRESENTATIVES
        + (PHASE_INDEX,)
    ))
    derivatives = {
        index: signed_derivative(
            words[index], alignment, alignment_inverse, index_by_key
        )
        for index in selected
    }
    seeds = [
        derivatives[index].copy()
        for index in CERTIFIED_REPRESENTATIVE_INDICES
    ]
    for index in SURVIVOR_REPRESENTATIVES:
        derivative = derivatives[index]
        for permutation in translations:
            centrality = translate(derivative, permutation)
            for source, value in derivative.items():
                centrality[source] = centrality.get(source, 0) - value
                if not centrality[source]:
                    del centrality[source]
            seeds.append(centrality)
    return elements, translations, seeds, derivatives[PHASE_INDEX]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--primes", default="3,5,7,11,13,1181")
    parser.add_argument("--certificate")
    parser.add_argument("--verify-certificate")
    args = parser.parse_args()
    started = time.monotonic()
    elements, translations, seeds, phase = build_problem()
    if args.verify_certificate:
        certificate_text = Path(args.verify_certificate).read_text()
        certificate = json.loads(certificate_text)
        if certificate.get("format") != "atlas-fp-a8-left-ideal-dag-v1":
            raise AssertionError("unknown certificate format")
        if certificate.get("group_order") != len(elements):
            raise AssertionError("certificate group order changed")
        if certificate.get("seed_rows") != len(seeds):
            raise AssertionError("certificate seed packet changed")
        for record in certificate["prime_records"]:
            verify_record(record, seeds, translations, phase)
        print(json.dumps({
            "certificate_verified": True,
            "certificate_sha256": hashlib.sha256(
                certificate_text.encode("utf-8")
            ).hexdigest(),
            "verified_primes": [
                record["prime"] for record in certificate["prime_records"]
            ],
            "elapsed_seconds": round(time.monotonic() - started, 3),
        }, indent=2))
        return

    primes = [int(value) for value in args.primes.split(",")]
    records = []
    summaries = []
    for prime in primes:
        record, summary = solve_prime(
            prime, seeds, translations, phase
        )
        records.append(record)
        summaries.append(summary)
    certificate_sha256 = None
    if args.certificate:
        certificate = {
            "format": "atlas-fp-a8-left-ideal-dag-v1",
            "group_order": len(elements),
            "seed_rows": len(seeds),
            "prime_records": records,
        }
        certificate_text = json.dumps(
            certificate, sort_keys=True, separators=(",", ":")
        ) + "\n"
        certificate_sha256 = hashlib.sha256(
            certificate_text.encode("utf-8")
        ).hexdigest()
        Path(args.certificate).write_text(certificate_text)
    print(json.dumps({
        "coefficient_fields": ["F_%d" % prime for prime in primes],
        "group": "GL(4,2) ~= A8",
        "group_order": len(elements),
        "certified_zero_derivatives": len(
            CERTIFIED_REPRESENTATIVE_INDICES
        ),
        "central_survivors": list(SURVIVOR_REPRESENTATIVES),
        "centrality_generators": len(translations),
        "seed_rows": len(seeds),
        "prime_summaries": summaries,
        "all_phases_in_generated_left_ideal": all(
            summary["phase_in_generated_left_ideal"]
            for summary in summaries
        ),
        "certificate_sha256": certificate_sha256,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }, indent=2))


if __name__ == "__main__":
    main()
