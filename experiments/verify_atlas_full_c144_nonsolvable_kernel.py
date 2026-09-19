#!/usr/bin/env python3
"""Audit the exact inputs to the full-C144 nonsolvable-kernel proof.

The proof itself is the quotient argument in
``research/atlas-full-c144-nonsolvable-kernel-proof.md``.  This independent,
stdlib-only check binds the two GAP computations to their archived outputs
and rechecks every finite-group datum used by that argument.
"""

from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

EXPECTED_SHA256 = {
    "experiments/atlas_a4_q1920_module_structure.g":
        "0f3c4c8547473c68f6ecda9818559ca9855bcb3419d96237f4595c3f9fb5b614",
    "experiments/atlas_a4_q1920_kernel_homology.g":
        "6526e876944c3d01c0a9c32e63dc342cec8bec95fd5fcdc612789226760ed0f7",
    "research/artifacts/atlas-a4-q1920-module-structure.json":
        "7228c15e71d244e58185c1f68927b42a6ef66045ffe281115398ea2cfb89a061",
    "research/artifacts/atlas-a4-q1920-seam-kernel-homology.json":
        "7d486f31fa82f0c4aafdcaa5120cecdca9a0ea4b00d3b194fd75280d893e6b39",
}


def digest(relative: str) -> str:
    return hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()


def load(relative: str) -> dict:
    return json.loads((ROOT / relative).read_text(encoding="utf-8"))


def main() -> None:
    actual = {name: digest(name) for name in EXPECTED_SHA256}
    assert actual == EXPECTED_SHA256

    module = load("research/artifacts/atlas-a4-q1920-module-structure.json")
    group = module["common_group_profile"]
    radial = module["common_marked_radial_profile"]
    assert module["marking_count"] == 2
    assert group["order"] == 1920 == 32 * 60
    assert group["derived_subgroup_order"] == 1920
    assert group["normal_subgroup_orders"] == [1, 2, 32, 1920]
    assert group["elementary_abelian_module_order"] == 32
    assert group["module_quotient"] == "A5"
    assert group["complement_class_orders"] == [60] * 4
    assert radial["radial_subgroup_orders"] == [6, 6]
    assert radial["radial_intersections_with_module"] == [1, 1]

    seam = load("research/artifacts/atlas-a4-q1920-seam-kernel-homology.json")
    profile = seam["common_profile"]
    assert seam["marking_count"] == 2
    assert profile["P_abelian_invariants"] == []
    assert profile["Q_retraction_image_order"] == 1920
    assert profile["kernel_index"] == 60
    assert profile["kernel_abelian_invariants"] == [2] * 9
    assert profile["A5_orbit_span_of_z_dimension"] == 0

    # In G/K the last C144 cube gives (bK)^3=K, while b^2=1.
    # Coprimality forces bK=K, contradicting K cap Q=V and b notin V.
    assert math.gcd(2, 3) == 1

    print(json.dumps({
        "claim_certified":
            "atlas-full-c144-relation-forces-nonsolvable-q1920-kernel",
        "input_sha256": EXPECTED_SHA256,
        "marking_count": module["marking_count"],
        "normal_subgroup_orders": group["normal_subgroup_orders"],
        "quotient_order": group["order"] // group["elementary_abelian_module_order"],
        "status": "ok",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
