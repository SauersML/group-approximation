"""Reduce an ambient integral lift in a compact projective cellular model.

The cellular analysis exports a rank-two basis of ``Q^#`` together with one
integral lift of each basis vector.  Those HNF lifts are deliberately crude.
For a selected harmonic vector, every other integral lift differs by the
saturated boundary lattice

    ker(cycle_pairing) = ran_Q(d_2^T) intersect Z^{C_2}.

This MSI-only experiment constructs that saturated lattice exactly and uses
fpylll's LLL/BKZ plus Babai reduction to find a shorter representative of the
same affine lattice coset.  Every reported candidate is checked with exact
integer arithmetic before it is written.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path

from fpylll import BKZ, CVP, IntegerMatrix, LLL
from sage.all import GF, MixedIntegerLinearProgram, QQ, ZZ, matrix, vector

from sl3_projective_cellular_analyze import build_boundaries, parse


def read_export(path: Path):
    qsharp_columns = [[], []]
    lift_columns = [[], []]
    with path.open(encoding="ascii") as stream:
        header = stream.readline().split()
        if header != ["coordinate", "qsharp_0", "qsharp_1", "lift_0", "lift_1"]:
            raise ValueError("unexpected Q-sharp/lift export header")
        for expected_coordinate, line in enumerate(stream):
            fields = line.split()
            if len(fields) != 5 or int(fields[0]) != expected_coordinate:
                raise ValueError("malformed Q-sharp/lift export")
            qsharp_columns[0].append(QQ(fields[1]))
            qsharp_columns[1].append(QQ(fields[2]))
            lift_columns[0].append(ZZ(fields[3]))
            lift_columns[1].append(ZZ(fields[4]))
    return matrix(QQ, qsharp_columns), matrix(ZZ, lift_columns)


def to_fpylll(basis):
    result = IntegerMatrix(basis.nrows(), basis.ncols())
    for row in range(basis.nrows()):
        for column in range(basis.ncols()):
            result[row, column] = int(basis[row, column])
    return result


def from_fpylll(basis):
    return matrix(ZZ, [
        [ZZ(basis[row, column]) for column in range(basis.ncols)]
        for row in range(basis.nrows)
    ])


def squared_norm(candidate):
    return ZZ(candidate.dot_product(candidate))


def exact_plane_round(candidate, basis):
    """Round orthogonal projection coordinates in the displayed basis."""
    gram = basis * basis.transpose()
    right_hand_side = basis * candidate.column()
    coordinates = gram.change_ring(QQ).solve_right(right_hand_side).column(0)
    rounded = vector(ZZ, [entry.round() for entry in coordinates])
    return candidate - rounded * basis


def certify_low_norm_minimum(cycle_basis, required_pairing, candidate_squared_norm):
    """Certify a minimum of squared norm at most four by support exhaustion.

    A vector of squared norm below four is a signed sum of at most three
    distinct coordinate vectors.  Its cycle-pairing profile is therefore a
    signed sum of at most three columns of ``cycle_basis``.  A
    meet-in-the-middle table makes this exact exhaustion tiny at the present
    328-coordinate level.
    """
    minimum = int(candidate_squared_norm)
    if not 1 <= minimum <= 4:
        raise ValueError("low-norm certification requires a candidate norm in 1..4")
    target = tuple(int(entry) for entry in required_pairing)
    if not any(target):
        raise AssertionError("the zero vector has the required cycle pairing")
    columns = [
        tuple(int(entry) for entry in cycle_basis.column(index))
        for index in range(cycle_basis.ncols())
    ]
    signed_singletons = []
    singleton_profiles = set()
    for index, column in enumerate(columns):
        for sign in (-1, 1):
            profile = tuple(sign * entry for entry in column)
            signed_singletons.append((profile, index, sign))
            singleton_profiles.add(profile)

    if minimum >= 2 and target in singleton_profiles:
        raise AssertionError("a norm-one lift exists")

    pair_profiles = {}
    signed_pair_count = 0
    if minimum >= 3:
        for left in range(len(columns)):
            for right in range(left + 1, len(columns)):
                for left_sign in (-1, 1):
                    for right_sign in (-1, 1):
                        profile = tuple(
                            left_sign * left_entry + right_sign * right_entry
                            for left_entry, right_entry in zip(
                                columns[left], columns[right])
                        )
                        pair_profiles.setdefault(profile, []).append((left, right))
                        signed_pair_count += 1

    if minimum >= 3 and target in pair_profiles:
        raise AssertionError("a norm-two lift exists")

    complement_matches = 0
    if minimum >= 4:
        for singleton, singleton_index, _ in signed_singletons:
            complement = tuple(
                target_entry - singleton_entry
                for target_entry, singleton_entry in zip(target, singleton)
            )
            for left, right in pair_profiles.get(complement, []):
                complement_matches += 1
                if singleton_index not in (left, right):
                    raise AssertionError("a norm-three lift exists")

    return {
        "certified_no_integral_lift_squared_norm_below": minimum,
        "minimum_lift_squared_norm": minimum,
        "ambient_coordinate_count": len(columns),
        "signed_singleton_count": len(signed_singletons),
        "signed_pair_count": signed_pair_count,
        "unique_signed_singleton_profile_count": len(singleton_profiles),
        "unique_signed_pair_profile_count": len(pair_profiles),
        "triple_complement_matches_with_repeated_coordinate_only": complement_matches,
    }


def centered_residue(value, modulus):
    residue = int(value) % modulus
    if 2 * residue > modulus:
        residue -= modulus
    return residue


def modular_coset_minimum(cycle_basis, candidate, modulus):
    """Compute a rigorous modular lower bound with GLPK branch-and-bound."""
    if modulus < 2 or not ZZ(modulus).is_prime():
        raise ValueError("certification moduli must be prime")
    finite_field = GF(modulus)
    check = cycle_basis.change_ring(finite_field)
    if check.rank() != cycle_basis.nrows():
        raise ValueError("cycle checks lose rank modulo the selected prime")
    syndrome_integer = cycle_basis * candidate
    syndrome = check * candidate.change_ring(finite_field)

    if modulus == 2:
        residues = [1]
    else:
        residues = list(range(-(modulus // 2), modulus // 2 + 1))
        residues.remove(0)
    problem = MixedIntegerLinearProgram(maximization=False, solver="GLPK")
    selected = problem.new_variable(binary=True, nonnegative=True)
    quotients = problem.new_variable(integer=True, nonnegative=False)
    coordinate_expressions = []
    objective = 0
    for column in range(cycle_basis.ncols()):
        problem.add_constraint(problem.sum(
            selected[column, residue] for residue in residues) <= 1)
        expression = problem.sum(
            residue * selected[column, residue] for residue in residues)
        coordinate_expressions.append(expression)
        objective += problem.sum(
            residue * residue * selected[column, residue]
            for residue in residues)
    problem.set_objective(objective)

    for row in range(cycle_basis.nrows()):
        coefficients = [
            centered_residue(cycle_basis[row, column], modulus)
            for column in range(cycle_basis.ncols())
        ]
        syndrome_value = centered_residue(syndrome_integer[row], modulus)
        expression = problem.sum(
            coefficients[column] * coordinate_expressions[column]
            for column in range(cycle_basis.ncols()) if coefficients[column]
        )
        absolute_bound = sum(abs(value) for value in coefficients) * (
            modulus // 2)
        quotient_bound = (absolute_bound + abs(syndrome_value)) // modulus + 1
        problem.set_min(quotients[row], -quotient_bound)
        problem.set_max(quotients[row], quotient_bound)
        problem.add_constraint(
            expression - modulus * quotients[row] == syndrome_value)

    candidate_cost = sum(
        centered_residue(entry, modulus) ** 2 for entry in candidate)
    problem.add_constraint(objective <= candidate_cost)
    optimum = int(round(problem.solve(log=0)))
    solution_values = problem.get_values(selected)
    solution = vector(ZZ, cycle_basis.ncols())
    solution_entries = []
    for (column, residue), value in solution_values.items():
        if value <= 0.5:
            continue
        solution[column] = residue
        solution_entries.append([int(column), int(residue)])
    if sum(int(entry) ** 2 for entry in solution) != optimum:
        raise AssertionError("modular solution cost differs from the optimum")
    if check * solution.change_ring(finite_field) != syndrome:
        raise AssertionError("modular solution has the wrong syndrome")
    return {
        "modulus": modulus,
        "parity_check_rank": int(check.rank()),
        "candidate_centered_residue_cost": candidate_cost,
        "modular_coset_leader_squared_cost": optimum,
        "modular_coset_leader_entries": solution_entries,
        "syndrome_support": [
            row for row, entry in enumerate(syndrome) if entry],
        "solver": "GLPK branch-and-bound",
        "exact_lower_bound": (
            "every integral lift has squared norm at least the modular cost"),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("cellular_input", type=Path)
    parser.add_argument("qsharp_lifts", type=Path)
    parser.add_argument("summary", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("lift_output", type=Path)
    parser.add_argument("--basis-row", type=int, choices=(0, 1), default=0)
    parser.add_argument("--bkz-block-size", type=int, action="append", default=[])
    parser.add_argument("--bkz-loops", type=int, default=1)
    parser.add_argument("--certify-modulus", type=int, action="append", default=[])
    args = parser.parse_args()

    started = time.monotonic()
    prime, degree, orbit_dimensions, cells = parse(args.cellular_input)
    dimensions, boundaries = build_boundaries(degree, orbit_dimensions, cells)

    d2_integer = boundaries[2].change_ring(ZZ)
    cycle_basis = d2_integer.transpose().right_kernel_matrix()
    saturated_range_basis = cycle_basis.right_kernel_matrix()
    if saturated_range_basis * cycle_basis.transpose() != 0:
        raise AssertionError("purported saturated range does not annihilate cycles")
    if saturated_range_basis.nrows() + cycle_basis.nrows() != dimensions[2]:
        raise AssertionError("cycle/range ranks do not complement each other")

    qsharp_basis, lift_basis = read_export(args.qsharp_lifts)
    summary = json.loads(args.summary.read_text(encoding="utf-8"))
    if summary["prime"] != prime or summary["projective_degree"] != degree:
        raise ValueError("the summary and cellular export describe different charts")
    if qsharp_basis.nrows() != 2 or qsharp_basis.ncols() != dimensions[2]:
        raise ValueError("the lift reducer requires a rank-two harmonic export")
    coordinates = vector(
        ZZ,
        summary["harmonic_lift_sequence"]["qsharp_gauss_transform"][args.basis_row],
    )
    qsharp = coordinates * qsharp_basis
    initial_lift = coordinates * lift_basis
    required_pairing = initial_lift * cycle_basis.transpose()
    if required_pairing != qsharp * cycle_basis.transpose():
        raise AssertionError("exported lift has the wrong cycle pairings")
    if boundaries[3].change_ring(ZZ) * initial_lift.column() != 0:
        raise AssertionError("exported lift does not annihilate degree-three boundaries")

    history = []

    def record(label, candidate):
        norm = squared_norm(candidate)
        history.append({
            "stage": label,
            "squared_norm": str(norm),
            "norm_approx": float(norm.sqrt()),
            "maximum_absolute_coefficient": max(abs(int(entry)) for entry in candidate),
            "support_size": sum(1 for entry in candidate if entry),
            "elapsed_seconds": time.monotonic() - started,
        })
        print(json.dumps(history[-1], sort_keys=True), flush=True)

    candidate = initial_lift
    record("exported_hnf", candidate)
    candidate = exact_plane_round(candidate, saturated_range_basis)
    record("saturated_plane_round", candidate)

    reduced_basis = to_fpylll(saturated_range_basis)
    LLL.reduction(reduced_basis, delta=0.99)
    lll_basis = from_fpylll(reduced_basis)
    plane_candidate = exact_plane_round(candidate, lll_basis)
    if squared_norm(plane_candidate) < squared_norm(candidate):
        candidate = plane_candidate
    record("lll_plane_round", candidate)
    babai_vector = vector(ZZ, CVP.babai(
        reduced_basis, tuple(-int(entry) for entry in candidate), delta=0.99))
    babai_candidate = candidate + babai_vector
    if squared_norm(babai_candidate) < squared_norm(candidate):
        candidate = babai_candidate
    record("lll_babai", candidate)

    for block_size in args.bkz_block_size:
        if not 2 <= block_size <= saturated_range_basis.nrows():
            raise ValueError("invalid BKZ block size")
        BKZ.reduction(
            reduced_basis,
            BKZ.Param(block_size=block_size, max_loops=args.bkz_loops),
        )
        bkz_basis = from_fpylll(reduced_basis)
        plane_candidate = exact_plane_round(candidate, bkz_basis)
        if squared_norm(plane_candidate) < squared_norm(candidate):
            candidate = plane_candidate
        record(f"bkz_{block_size}_plane_round", candidate)
        babai_vector = vector(ZZ, CVP.babai(
            reduced_basis, tuple(-int(entry) for entry in candidate), delta=0.99))
        babai_candidate = candidate + babai_vector
        if squared_norm(babai_candidate) < squared_norm(candidate):
            candidate = babai_candidate
        record(f"bkz_{block_size}_babai", candidate)

    if candidate * cycle_basis.transpose() != required_pairing:
        raise AssertionError("reduction changed the harmonic projection")
    if boundaries[3].change_ring(ZZ) * candidate.column() != 0:
        raise AssertionError("reduced lift does not annihilate degree-three boundaries")
    if any(entry.denominator() != 1 for entry in candidate):
        raise AssertionError("reduced lift is not integral")

    support_certificate = None
    if squared_norm(candidate) <= 4:
        support_certificate = certify_low_norm_minimum(
            cycle_basis, required_pairing, squared_norm(candidate))
    modular_certificates = [
        modular_coset_minimum(cycle_basis, candidate, modulus)
        for modulus in args.certify_modulus
    ]

    digest = hashlib.sha256()
    with args.lift_output.open("w", encoding="ascii") as stream:
        header = "coordinate qsharp lift\n"
        stream.write(header)
        digest.update(header.encode("ascii"))
        for coordinate, (qsharp_coefficient, lift_coefficient) in enumerate(
                zip(qsharp, candidate)):
            line = f"{coordinate} {qsharp_coefficient} {lift_coefficient}\n"
            stream.write(line)
            digest.update(line.encode("ascii"))

    qsharp_squared_norm = qsharp.dot_product(qsharp)
    candidate_squared_norm = squared_norm(candidate)
    result = {
        "prime": prime,
        "qsharp_gauss_basis_row": args.basis_row,
        "projective_degree": degree,
        "ambient_dimension": dimensions[2],
        "cycle_lattice_rank": cycle_basis.nrows(),
        "saturated_range_lattice_rank": saturated_range_basis.nrows(),
        "saturated_range_basis_maximum_absolute_coefficient": max(
            abs(int(entry)) for entry in saturated_range_basis.list()),
        "bkz_block_sizes": args.bkz_block_size,
        "bkz_loops": args.bkz_loops,
        "history": history,
        "qsharp_squared_norm": str(qsharp_squared_norm),
        "reduced_lift_squared_norm": str(candidate_squared_norm),
        "paired_distortion_upper_squared": str(
            candidate_squared_norm / qsharp_squared_norm),
        "paired_distortion_upper": float(
            (candidate_squared_norm / qsharp_squared_norm).sqrt()),
        "lift_sha256": digest.hexdigest(),
        "support_exhaustion_certificate": support_certificate,
        "modular_coset_certificates": modular_certificates,
        "exact_cycle_pairing_verified": True,
        "exact_degree_three_annihilation_verified": True,
        "elapsed_seconds": time.monotonic() - started,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
