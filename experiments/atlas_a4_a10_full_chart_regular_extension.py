#!/usr/bin/env python3
"""Exact multiplicity certificate for adjoining both full A8 charts to A10."""

import json


A10 = 1_814_400
A8 = 20_160
F = 18
K = 6


def main():
    a8_copies = A10 // A8
    first_from_a10 = A10 // F
    first_from_a8 = a8_copies * (A8 // F)
    second_from_a10 = A10 // K
    second_from_a8 = a8_copies * (A8 // K)
    assert a8_copies == 90
    assert first_from_a10 == first_from_a8 == 100_800
    assert second_from_a10 == second_from_a8 == 302_400
    print(json.dumps({
        "ambient_permutation_degree": A10,
        "a8_regular_copies_per_chart": a8_copies,
        "F_order": F,
        "K_order": K,
        "Reg_A10_restricted_F_copies": first_from_a10,
        "90_Reg_A8_restricted_F_copies": first_from_a8,
        "Reg_A10_restricted_K_copies": second_from_a10,
        "90_Reg_A8_restricted_K_copies": second_from_a8,
        "underlying_vertex_graph": "A8_0--F--A10--K--A8_1",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
