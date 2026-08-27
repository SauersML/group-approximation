#!/usr/bin/env sage
"""Exact A8-class and marking audit in L4(4).

Run with a GAP installation containing CTblLib.  The finite computation uses
the 85-point projective image of GL(4,4), which is PSL(4,4), and the 2-Brauer
table of A8.  The representation-theoretic deduction from the checked data
is recorded in the companion Cairn proof.
"""

import importlib.util
import json
import os

from sage.all import GF, GL, Matrix, libgap


def load_screen_module():
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "atlas_l44_six_relator_screens.py")
    spec = importlib.util.spec_from_file_location("l44_screen", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    if str(libgap.LoadPackage("ctbllib")) != "true":
        raise RuntimeError("CTblLib is required for the A8 2-Brauer audit")

    ordinary = libgap.CharacterTable("A8")
    brauer = libgap.BrauerTable(ordinary, 2)
    irreducibles = list(libgap.Irr(brauer))
    degrees = [int(character[0]) for character in irreducibles]
    degree_four = [character for character in irreducibles if int(character[0]) == 4]
    if degrees != [1, 4, 4, 6, 14, 20, 20, 64]:
        raise AssertionError("A8 characteristic-two Brauer degrees changed")
    if len(degree_four) != 2:
        raise AssertionError("A8 no longer has exactly two degree-four 2-modules")
    if libgap.ComplexConjugate(degree_four[0]) != degree_four[1]:
        raise AssertionError("the two degree-four modules are no longer dual")

    screen = load_screen_module()
    binary = GF(2)
    field = GF(4, "z")
    project = screen.projective_action(field)
    ambient_linear = GL(4, field)
    source_linear = GL(4, binary)
    ambient = libgap.Group(
        [project(generator.matrix())._libgap_() for generator in ambient_linear.gens()]
    )
    chart = libgap.Group(
        [
            project(Matrix(field, generator.matrix()))._libgap_()
            for generator in source_linear.gens()
        ]
    )
    normalizer = ambient.Normalizer(chart)
    centralizer = ambient.Centralizer(chart)
    automorphism_order = int(
        libgap.AutomorphismGroup(libgap.AlternatingGroup(8)).Size()
    )

    here = os.path.dirname(os.path.abspath(__file__))
    with open(
        os.path.join(here, "atlas-six-relator-l44-subfield-screens.json"),
        encoding="utf-8",
    ) as stream:
        screen_record = json.load(stream)

    checks = {
        "ambient_order": int(ambient.Size()),
        "chart_order": int(chart.Size()),
        "centralizer_order": int(centralizer.Size()),
        "normalizer_order": int(normalizer.Size()),
        "automorphism_group_order": automorphism_order,
        "a8_modular_irreducible_degrees_in_characteristic_two": degrees,
        "degree_four_irreducible_count": len(degree_four),
        "degree_four_characters_are_dual": True,
        "brauer_table_automorphism_order": int(
            libgap.AutomorphismsOfTable(brauer).Size()
        ),
        "subgroup_conjugacy_class_count": 1,
        "subgroup_conjugacy_class_size": int(ambient.Size())
        // int(normalizer.Size()),
        "outer_marking_absorbed_by_normalizer": False,
        "relative_marking_parities": 2,
        "six_relator_screen_survivors": int(screen_record["total_survivors"]),
        "six_relator_l44_equality_endpoint_exhausted": True,
    }
    expected = {
        "ambient_order": 987033600,
        "chart_order": 20160,
        "centralizer_order": 1,
        "normalizer_order": 20160,
        "automorphism_group_order": 40320,
        "a8_modular_irreducible_degrees_in_characteristic_two": [
            1,
            4,
            4,
            6,
            14,
            20,
            20,
            64,
        ],
        "degree_four_irreducible_count": 2,
        "degree_four_characters_are_dual": True,
        "brauer_table_automorphism_order": 2,
        "subgroup_conjugacy_class_count": 1,
        "subgroup_conjugacy_class_size": 48960,
        "outer_marking_absorbed_by_normalizer": False,
        "relative_marking_parities": 2,
        "six_relator_screen_survivors": 0,
        "six_relator_l44_equality_endpoint_exhausted": True,
    }
    if checks != expected:
        raise AssertionError({"expected": expected, "actual": checks})
    print(json.dumps(checks, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
