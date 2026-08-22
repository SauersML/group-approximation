#!/usr/bin/env python3
"""Fast implicit regular-A8 probe of one canonical collision-theta lift.

This is a numerical slice, not a feasibility certificate.  Matrices of size
20160 are never materialized: left regular permutations, one permutation
conjugator, and the repeated six-dimensional S3 line rotation are applied to
probe vectors.
"""

import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_a4_reference_alignment import pair_graph_components
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word
from atlas_two_chart_search import gf2_inv, gf2_mul, matrix_key
from atlas_19243_s3_relative import (
    ALIGNMENT_HEX,
    FIRST_INVOLUTION_HEX,
    SECOND_HEX,
    gf2_matrix,
)


REFERENCE_HEX = "00000001000100000100000000000100"


def perm_apply(permutation, vector):
    out = np.empty_like(vector)
    out[permutation] = vector
    return out


def subgroup(generators, identity):
    seen = {matrix_key(identity): identity}
    todo = [identity]
    moves = generators + [gf2_inv(g) for g in generators]
    while todo:
        old = todo.pop()
        for generator in moves:
            new = gf2_mul(generator, old)
            key = matrix_key(new)
            if key not in seen:
                seen[key] = new
                todo.append(new)
    return list(seen.values())


def alternating_pair_conjugator(b0, c0):
    """Return q with q c0 = b0 q, choosing an incident-edge cycle gauge."""
    n = len(b0)
    q = np.full(n, -1, dtype=np.int64)
    used_target_edges = set()
    for start in range(n):
        if q[start] >= 0:
            continue
        # Try the C0 edge at start against the B0 edge incident at start.
        target = start
        target_edge = tuple(sorted((target, int(b0[target]))))
        if target_edge in used_target_edges:
            # The other B0 edge incident to this alternating component is free.
            target = int(c0[start])
            target_edge = tuple(sorted((target, int(b0[target]))))
        if target_edge in used_target_edges:
            # Deterministic fallback only for a non-generic cycle encounter.
            target = next(
                x for x in range(n)
                if tuple(sorted((x, int(b0[x])))) not in used_target_edges
            )
            target_edge = tuple(sorted((target, int(b0[target]))))
        mate = int(c0[start])
        q[start] = target
        q[mate] = int(b0[target])
        used_target_edges.add(target_edge)
    assert sorted(q.tolist()) == list(range(n))
    assert np.array_equal(q[c0], b0[q])
    return q


def main():
    rng = np.random.default_rng(19243)
    elements = list(enumerate_gl4())
    identity = np.eye(4, dtype=np.uint8)
    index = {matrix_key(g): i for i, g in enumerate(elements)}
    n = len(elements)

    def left_perm(g):
        return np.asarray([index[matrix_key(gf2_mul(g, h))] for h in elements])

    def right_perm(g):
        return np.asarray([index[matrix_key(gf2_mul(h, g))] for h in elements])

    reference = np.frombuffer(bytes.fromhex(REFERENCE_HEX), dtype=np.uint8).reshape(4, 4)
    p_reference = left_perm(reference)
    b = np.asarray(gf2_matrix(FIRST_INVOLUTION_HEX), dtype=np.uint8)
    p_b = left_perm(b)

    alignment = np.asarray(gf2_matrix(ALIGNMENT_HEX), dtype=np.uint8)
    alignment_inv = gf2_inv(alignment)
    p_alignment = left_perm(alignment)
    p_alignment_inv = np.argsort(p_alignment)
    aligned = [
        gf2_mul(gf2_mul(alignment, np.asarray(gf2_matrix(value), dtype=np.uint8)), alignment_inv)
        for value in SECOND_HEX
    ]
    r, s = aligned[:2]
    k_group = subgroup([r, s], identity)
    sign = {}
    # sign is +1 on rotations and -1 on reflections.
    rotations = {matrix_key(identity), matrix_key(r), matrix_key(gf2_mul(r, r))}
    for value in k_group:
        sign[matrix_key(value)] = 1.0 if matrix_key(value) in rotations else -1.0

    p_c0 = right_perm(s)
    # The raw second chart includes the fixed collision alignment A.  Choose
    # the line-sector conjugator near R A^(-1), so its raw product is near R.
    p_base = p_reference[p_alignment_inv]
    p_base_inv = np.argsort(p_base)
    p_cr = p_base_inv[p_b[p_base]]
    q = alternating_pair_conjugator(p_cr, p_c0)
    # U0=(R A^(-1)) Q, so U0^* B U0=C0.  The raw chart unitary is
    # U_theta=U0 T_theta A.
    p_u0 = p_base[q]
    assert np.array_equal(q[p_c0], p_cr[q])
    assert np.array_equal(np.argsort(q)[p_cr[q]], p_c0)
    conjugated = np.argsort(p_u0)[p_b[p_u0]]
    if not np.array_equal(conjugated, p_c0):
        raise AssertionError((int(np.count_nonzero(conjugated != p_c0)),
                              conjugated[:12].tolist(), p_c0[:12].tolist()))

    # Left K-cosets and their normalized trivial/sign line vectors.
    unseen = set(range(n))
    blocks = []
    while unseen:
        h_index = min(unseen)
        h = elements[h_index]
        block = np.asarray([index[matrix_key(gf2_mul(k, h))] for k in k_group])
        if len(set(block.tolist())) != 6:
            raise AssertionError("K orbit is not regular")
        unseen.difference_update(block.tolist())
        signs = np.asarray([sign[matrix_key(k)] for k in k_group])
        blocks.append((block, signs))
    assert len(blocks) == 3360
    block_indices = np.stack([block for block, _signs in blocks])
    block_signs = np.stack([signs for _block, signs in blocks])

    def apply_t(vector, theta, adjoint=False):
        cosine = np.cos(theta)
        sine = np.sin(theta) * (-1.0 if adjoint else 1.0)
        out = vector.copy()
        values = vector[block_indices]
        alpha = values.mean(axis=1)
        beta = (block_signs * values).mean(axis=1)
        correction = (
            ((cosine - 1.0) * alpha - sine * beta)[:, None]
            + block_signs * (sine * alpha + (cosine - 1.0) * beta)[:, None]
        )
        out[block_indices] += correction
        return out

    p_u0_inv = np.argsort(p_u0)

    def apply_u(vector, theta, adjoint=False):
        if adjoint:
            out = perm_apply(p_u0_inv, vector)
            out = apply_t(out, theta, True)
            return perm_apply(p_alignment_inv, out)
        out = perm_apply(p_alignment, vector)
        out = apply_t(out, theta, False)
        return perm_apply(p_u0, out)

    states, _ = enumerate_ball(5)
    spanning, _, _ = spanning_tree_kernel_words(states)
    packet = [word for _index, word in select_packet(spanning, x_lengths())]
    with open(os.path.join(os.path.dirname(__file__), "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])
    words = packet + [collision]
    distinct = {}
    for word in words:
        for _factor, g in word:
            distinct.setdefault(matrix_key(g), left_perm(g))

    probes = rng.choice((-1.0, 1.0), size=(12, n)).astype(np.complex128)

    def apply_word(vector, word, theta):
        out = vector
        for factor, g in reversed(word):
            if factor == 1:
                out = perm_apply(distinct[matrix_key(g)], out)
            else:
                out = apply_u(out, theta, True)
                out = perm_apply(distinct[matrix_key(g)], out)
                out = apply_u(out, theta, False)
        return out

    for theta in (0.0, 0.1, 0.4, np.pi / 4):
        traces = []
        for word in words:
            estimates = [np.vdot(v, apply_word(v, word, theta)).real / n for v in probes]
            traces.append(float(np.mean(estimates)))
        defects2 = np.maximum(0.0, 2.0 - 2.0 * np.asarray(traces))
        packet2 = defects2[:-1]
        print(json.dumps({
            "theta": theta,
            "packet_rms_estimate": float(np.sqrt(packet2.mean())),
            "packet_max_estimate": float(np.sqrt(packet2.max())),
            "q_defect_estimate": float(np.sqrt(defects2[-1])),
            "canonical_lift_distance2": float((2.0 / 3.0) * (1.0 - np.cos(theta))),
            "probes": len(probes),
        }, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
