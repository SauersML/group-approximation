#!/usr/bin/env python3
"""Exact normal-closure audit for collision 19243 in the A4 atlas subgroup ladder."""
import json, os
import numpy as np
from atlas_a4_rank_three_core import packet_edge, components
from atlas_a4_packet_component_audit import subgroup
from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word
from atlas_two_chart_search import I4, factor_generators, gf2_inv, gf2_mul, matrix_key


def conjugate(g, x):
    return gf2_mul(gf2_mul(g, x), gf2_inv(g))


def conjugacy_orbit(generators, seed):
    seen = {matrix_key(seed): seed}
    todo = [seed]
    while todo:
        x = todo.pop()
        for g in generators:
            y = conjugate(g, x)
            k = matrix_key(y)
            if k not in seen:
                seen[k] = y
                todo.append(y)
    return seen


def normal_closure(generators, seed):
    orbit = conjugacy_orbit(generators, seed)
    chosen = []
    N = subgroup([])
    for x in orbit.values():
        if matrix_key(x) not in N:
            chosen.append(x)
            N = subgroup(chosen)
    return N, len(orbit), len(chosen)


def is_translation(x):
    # Standard AGL_3(2) model inside GL_4(2): [I_3 v; 0 1].
    return (
        np.array_equal(x[:3, :3], np.eye(3, dtype=np.uint8))
        and tuple(int(t) for t in x[3, :]) == (0, 0, 0, 1)
    )


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())

    # Reconstruct the 14-word core exactly as in atlas_a4_rank_three_core.py.
    from atlas_a4_rank_three_core import H18_LABEL_HEX, matrix
    from atlas_a4_packet_component_audit import center
    h18 = subgroup([matrix(value) for value in H18_LABEL_HEX])
    central_order_three = {
        matrix_key(value) for value in center(h18)
        if matrix_key(value) != matrix_key(I4)
    }
    core = []
    for index, word in packet:
        factor, b0, a = packet_edge(word)
        if matrix_key(a) not in central_order_three:
            core.append((index, factor, b0, a))
    comps, matrices = components(core)
    component_groups = [subgroup([matrices[key] for key in comp]) for comp in comps]
    H = subgroup(list(component_groups[0].values()) + list(component_groups[1].values()))
    assert len(H) == 168

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as handle:
        q = decode_word(json.load(handle)[0]["word"])
    first_chart = [x for factor, x in q if factor == 1]
    assert len({matrix_key(x) for x in first_chart}) == 1
    b = first_chart[0]
    assert is_translation(b) and matrix_key(b) != matrix_key(I4)

    P = subgroup(list(H.values()) + [b])
    assert len(P) == 1344
    V = {k: x for k, x in P.items() if is_translation(x)}
    assert len(V) == 8

    h_orbit = {matrix_key(conjugate(h, b)) for h in H.values()}
    assert len(h_orbit) == 7
    assert h_orbit == set(V) - {matrix_key(I4)}

    # Any finite generating set is enough for normal-closure iteration.
    h_gens = []
    for comp in comps:
        h_gens.extend(matrices[key] for key in comp)
    Np, p_orbit_size, p_chosen = normal_closure(h_gens + [b], b)
    assert set(Np) == set(V)

    a8_gens = [word[0][1] for _, word in factor_generators()[:6]]
    Na8, a8_orbit_size, a8_chosen = normal_closure(a8_gens, b)
    assert len(Na8) == 20160

    print(json.dumps({
        "H_order": len(H),
        "P_order": len(P),
        "translation_radical_order": len(V),
        "H_conjugacy_orbit_of_b": len(h_orbit),
        "normal_closure_b_in_P": len(Np),
        "P_conjugacy_orbit_of_b": p_orbit_size,
        "P_normal_generators_needed_by_greedy_audit": p_chosen,
        "P_mod_normal_closure_order": len(P) // len(Np),
        "normal_closure_b_in_A8": len(Na8),
        "A8_conjugacy_orbit_of_b": a8_orbit_size,
        "A8_normal_generators_needed_by_greedy_audit": a8_chosen,
    }, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
