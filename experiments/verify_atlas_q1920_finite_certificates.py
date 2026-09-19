#!/usr/bin/env python3
"""Audit the exact finite certificates for five Q1920 Atlas claims.

The primary enumerations are the committed GAP programs.  This independent,
stdlib-only pass binds each program to its archived JSON output and recomputes
all arithmetic and cross-certificate consistency used by the proof routes.
It intentionally fails closed when either a program or an output changes.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

EXPECTED_SHA256 = {
    "experiments/atlas_a4_q1920_kernel_homology.g":
        "6526e876944c3d01c0a9c32e63dc342cec8bec95fd5fcdc612789226760ed0f7",
    "experiments/atlas_a4_q1920_f3_module_fixed_spaces.g":
        "476ed6f34f4f9bc347d60a43957bb9c83e8582bc1276f5a2a5bfaafe959a654b",
    "experiments/atlas_a4_q1920_f3_dim6_seam_search.g":
        "75917992ea1e8f61a0359ae6ff0f1243d8d7b3714d8dbff1353ce50aedbb056d",
    "experiments/atlas_a4_q1920_split_2byA5_gl4_classification.g":
        "db64ace0b98f7022dc49eaef441e08648895498e77e1a11e93e8ee8c955dda59",
    "experiments/atlas_a4_q1920_all_solvable_A5_gl4_classification.g":
        "f5870a20fb6ab6f6a92b0a1e6a83271b0b7bff6f9a7bb5acf7b82328f2674181",
    "research/artifacts/atlas-a4-q1920-seam-kernel-homology.json":
        "7d486f31fa82f0c4aafdcaa5120cecdca9a0ea4b00d3b194fd75280d893e6b39",
    "research/artifacts/atlas-a4-q1920-f3-module-fixed-spaces.json":
        "8401011d393ec283ac65448538b01ea1ce25c31faf12a1d2b5aeabf3857c59b4",
    "research/artifacts/atlas-a4-q1920-f3-dim6-seam.json":
        "58dd7b4966541e3597a3ad070376989c67ff0faec749abec13b2353864066932",
    "research/artifacts/atlas-a4-q1920-split-2byA5-gl4.json":
        "dc0f61eb70c04421ccedef29d2e29d8a7f78295b8bfbc23383a37b8cdb65d209",
    "research/artifacts/atlas-a4-q1920-all-solvable-a5-gl4.json":
        "4b6f6ff01f0f7fcfa37d273699cd2d7e1b15cb8543f0180c7a353ff448f4ced3",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(relative: str) -> dict:
    return json.loads((ROOT / relative).read_text(encoding="utf-8"))


def valuation(value: int, prime: int) -> int:
    exponent = 0
    while value % prime == 0:
        value //= prime
        exponent += 1
    return exponent


def multiplicative_order(value: int, modulus: int) -> int:
    residue = 1
    for exponent in range(1, modulus + 1):
        residue = residue * value % modulus
        if residue == 1:
            return exponent
    raise AssertionError("multiplicative order not found")


def check_hashes() -> None:
    actual = {name: digest(ROOT / name) for name in EXPECTED_SHA256}
    assert actual == EXPECTED_SHA256


def check_kernel_homology() -> None:
    data = load("research/artifacts/atlas-a4-q1920-seam-kernel-homology.json")
    profile = data["common_profile"]
    assert data["marking_count"] == 2
    assert profile["P_abelian_invariants"] == []
    assert profile["Q_retraction_image_order"] == 1920
    assert profile["kernel_index"] == 60
    assert profile["kernel_abelian_invariants"] == [2] * 9

    # The connected 60-sheeted cover has six edge orbits and sixty vertices.
    cycle_dimension = 6 * 60 - 60 + 1
    assert cycle_dimension == 301 == profile["cover_cycle_dimension"]
    assert profile["cover_relator_boundary_rank"] == 292
    assert cycle_dimension - profile["cover_relator_boundary_rank"] == 9
    assert profile["cover_h1_dimension"] == 9

    assert profile["V_image_dimension"] == 5
    assert profile["V_c_image_dimension"] == 5
    assert profile["V_and_V_c_image_intersection_dimension"] == 5
    assert profile["A5_orbit_span_of_c_dimension"] == 4
    assert profile["A5_orbit_span_of_z_dimension"] == 0
    assert profile["V_intersection_A5_orbit_span_of_c_dimension"] == 0
    assert profile["V_plus_A5_orbit_span_of_c_dimension"] == 9


def check_module_profiles() -> None:
    data = load("research/artifacts/atlas-a4-q1920-f3-module-fixed-spaces.json")
    assert data["marking_count"] == 2
    fields = data["profile_fields"]
    assert fields == [
        "dimension", "image_order", "absolutely_irreducible",
        "A_fixed_dimension", "B_fixed_dimension",
        "A_indecomposable_dimensions",
    ]
    first = data["marking_1_profiles"]
    second = data["marking_2_profiles"]
    assert len(first) == len(second) == 12

    def faithful_a_profiles(rows: list[list[object]]) -> list[tuple[int, int, int]]:
        return sorted(
            (int(row[0]), int(row[3]), int(row[4]))
            for row in rows if row[1] == 1920 and row[3] > 0
        )

    assert faithful_a_profiles(first) == [
        (6, 2, 0), (10, 1, 3), (10, 3, 1), (24, 4, 4),
    ]
    assert faithful_a_profiles(second) == [
        (6, 2, 0), (10, 1, 3), (10, 3, 1), (24, 4, 4),
    ]

    first_sixes = sorted((row[3], row[4]) for row in first if row[0] == 6)
    second_sixes = sorted((row[4], row[3]) for row in second if row[0] == 6)
    assert first_sixes == second_sixes


def check_dim6_screen() -> None:
    data = load("research/artifacts/atlas-a4-q1920-f3-dim6-seam.json")
    profile = data["common_profile"]
    assert data["marking_count"] == 2
    assert profile["A_centralizer_order"] == 3888 == 2**4 * 3**5
    assert profile["involution_count_including_identity"] == 110
    assert profile["triangle_solution_count"] == 1
    assert profile["collision_solution_count"] == 1
    assert profile["nonidentity_collision_solution_count"] == 0
    assert profile["signal_solution_count"] == 0


def check_split_2by_a5_census() -> None:
    data = load("research/artifacts/atlas-a4-q1920-split-2byA5-gl4.json")
    gl4_order = (3**4 - 1) * (3**4 - 3) * (3**4 - 3**2) * (3**4 - 3**3)
    assert gl4_order == 24_261_120 == data["GL4_3_order"]
    assert valuation(gl4_order, 2) == 9
    assert data["GL4_3_2_part"] == 2**9

    profiles = data[
        "profiles_as_order_id_radical_order_complement_classes_"
        "four_dimensional_modules_faithful_four_dimensional_modules_image_orders"
    ]
    assert len(profiles) == data["split_perfect_candidate_count"] == 9
    assert data["faithful_nontrivial_2_kernel_count"] == 0
    exponents = {valuation(row[0] // 60, 2) for row in profiles}
    assert exponents == {0, 4, 5, 6, 7}
    assert all(exponent <= 7 for exponent in exponents)
    assert all(row[4] == 1 and row[6] == [60] for row in profiles)
    assert all(row[5] == 0 for row in profiles if row[2] > 1)

    exception = data["nearby_nonsplit_order_1920_exception"]
    assert exception["radical_order"] == 32
    assert exception["A5_complement_classes"] == 0
    assert exception["four_dimensional_representation_image_orders"] == [1920, 60]


def check_solvable_by_a5_census() -> None:
    data = load("research/artifacts/atlas-a4-q1920-all-solvable-a5-gl4.json")
    gl4_order = (3**4 - 1) * (3**4 - 3) * (3**4 - 3**2) * (3**4 - 3**3)
    assert valuation(gl4_order, 2) - valuation(60, 2) == 7
    assert valuation(gl4_order, 3) - valuation(60, 3) == 5
    assert multiplicative_order(2, 13) == 12
    assert multiplicative_order(3, 13) == 3

    assert data["candidate_count"] == 29
    assert data["nontrivial_3_core_count"] == 20
    assert data["zero_3_core_count"] == 9
    assert sum(data["nontrivial_3_core_histogram"].values()) == 20
    assert data["candidate_count"] == (
        data["nontrivial_3_core_count"] + data["zero_3_core_count"]
    )
    assert data["faithful_nontrivial_solvable_radical_count"] == 0

    profiles = data[
        "zero_3_core_profiles_as_order_id_radical_order_complement_classes_"
        "four_dimensional_image_orders"
    ]
    assert len(profiles) == 9
    assert all(row[4] == [60] for row in profiles)
    assert all(row[2] == (row[0] // 60) for row in profiles)


def main() -> None:
    check_hashes()
    check_kernel_homology()
    check_module_profiles()
    check_dim6_screen()
    check_split_2by_a5_census()
    check_solvable_by_a5_census()
    print(json.dumps({
        "claims_certified": [
            "atlas-q1920-universal-seam-splits-over-a5",
            "atlas-q1920-clifford-four-dimensional-shortcut-fails",
            "atlas-q1920-six-dimensional-f3-seam-is-signal-free",
            "atlas-no-split-perfect-2-extension-of-a5-acts-on-f3-four-space",
            "atlas-no-perfect-solvable-a5-action-on-f3-four-space",
        ],
        "input_sha256": EXPECTED_SHA256,
        "status": "ok",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
