#!/usr/bin/env python3
"""Exhaust all K-central permutation completions of the fixed 56-point packet.

The packet is the existing natural head action of degree 7 times the
degree-8 tail action on cosets of a subgroup of order 21 in GL_3(2).
This is an exact integer search of one permutation packet, not all unitary
representations. Run on MSI, not on the local workstation.
"""

import itertools
import json
import math
import time


def apply(a, v):
    return (a[0] if v & 1 else 0) ^ (a[1] if v & 2 else 0) ^ (a[2] if v & 4 else 0)


def mul(a, b):
    return tuple(apply(a, v) for v in b)


def power(a, n):
    out = (1, 2, 4)
    for _ in range(n):
        out = mul(out, a)
    return out


def closure(gens):
    seen = {(1, 2, 4)}
    todo = [(1, 2, 4)]
    while todo:
        a = todo.pop()
        for g in gens:
            v = mul(g, a)
            if v not in seen:
                seen.add(v)
                todo.append(v)
    return seen


def tail_action():
    group = sorted(a for a in itertools.product(range(8), repeat=3)
                   if len({apply(a, v) for v in range(8)}) == 8)
    assert len(group) == 168
    one = (1, 2, 4)
    singer = next(a for a in group if a != one and power(a, 7) == one)
    normalizer = next(a for a in group if a != one and power(a, 3) == one
                      and mul(a, singer) == mul(power(singer, 2), a))
    subgroup = closure((singer, normalizer))
    assert len(subgroup) == 21
    representatives = []
    coset_of = {}
    for g in group:
        if g not in coset_of:
            index = len(representatives)
            representatives.append(g)
            for a in subgroup:
                coset_of[mul(g, a)] = index
    assert len(representatives) == 8
    action = {g: tuple(coset_of[mul(g, r)] for r in representatives) for g in group}
    for g in group:
        for h in group:
            assert action[mul(g, h)] == tuple(action[g][action[h][i]] for i in range(8))
    return action, singer, normalizer, representatives


def tail_braid_matchings(d):
    """All fixed-point-free h with h^2=(hd)^3=1, for a fixed free d.

    In the alternating union of the d- and h-matchings, a component has
    either one d-edge (h=d there), or three d-edges forming a hexagon.
    Partition d-edges into singletons and triples, choosing each of the
    eight hexagon matchings on every triple.
    """
    n = len(d)
    assert all(d[i] != i and d[d[i]] == i for i in range(n))
    edges = tuple((i, d[i]) for i in range(n) if i < d[i])
    h = list(range(n))

    def pair(a, b):
        h[a] = b
        h[b] = a

    def rec(remaining):
        if not remaining:
            yield tuple(h)
            return
        a, *rest = remaining
        pair(*a)
        yield from rec(tuple(rest))
        for j, k in itertools.combinations(range(len(rest)), 2):
            b, c = rest[j], rest[k]
            after = tuple(e for i, e in enumerate(rest) if i not in (j, k))
            for x, y, z in itertools.product(range(2), repeat=3):
                pair(a[x], b[y])
                pair(b[1-y], c[z])
                pair(c[1-z], a[1-x])
                yield from rec(after)

    yield from rec(edges)


def run():
    started = time.monotonic()
    tail, singer, normalizer, representatives = tail_action()
    b, d = (1, 4, 2), (4, 2, 1)
    tb, td = tail[b], tail[d]
    plane = (1, 4, 5)
    points = [(2, t) for t in range(8)]
    points += [(v ^ (2*c), t) for c in range(2) for t in range(8) for v in plane]
    index = {point: i for i, point in enumerate(points)}
    bp = tuple(index[(apply(b, v), tb[t])] for v, t in points)
    dp = tuple(index[(v, td[t])] for v, t in points)
    q = (1, 2, 5)
    qp = tuple(index[(apply(q, v), t)] for v, t in points)
    kp = tuple(index[(apply(d, v), t)] for v, t in points)
    h0s = list(tail_braid_matchings(td))
    d1 = tuple(8*c+td[t] for c in range(2) for t in range(8))
    h1s = list(tail_braid_matchings(d1))
    assert len(h0s) == len(set(h0s)) == 33
    assert len(h1s) == len(set(h1s)) == 18369
    solutions = []
    checked = 0
    best_satisfied_points = 0
    best_odd_residual_cycle = None
    best_h = None
    candidates_with_no_even_residual_cycle = 0
    for h1 in h1s:
        h = [0] * 8 + [8+3*h1[i]+j for i in range(16) for j in range(3)]
        # Verify every generated h1 already satisfies the exact tail braid.
        assert all(h1[h1[i]] == i and h1[d1[h1[d1[h1[d1[i]]]]]] == i for i in range(16))
        for h0 in h0s:
            h[:8] = h0
            checked += 1
            satisfied = 0
            for i in range(56):
                if h[bp[h[bp[h[bp[i]]]]]] != i:
                    break
                satisfied += 1
            best_satisfied_points = max(best_satisfied_points, satisfied)
            # A nontrivial permutation has defect at least sqrt(3). If every
            # residual cycle is odd, its exact defect is
            # 2*cos(pi/(2*max_cycle)); any even cycle gives defect exactly 2.
            seen = [False] * 56
            largest_odd = 1
            even = False
            for i in range(56):
                if seen[i]:
                    continue
                j, length = i, 0
                while not seen[j]:
                    seen[j] = True
                    length += 1
                    j = h[bp[j]]
                residual_length = length // math.gcd(length, 3)
                if residual_length % 2 == 0:
                    even = True
                    break
                largest_odd = max(largest_odd, residual_length)
            if not even:
                candidates_with_no_even_residual_cycle += 1
                if best_odd_residual_cycle is None or largest_odd < best_odd_residual_cycle:
                    best_odd_residual_cycle = largest_odd
                    best_h = h[:]
            if satisfied == 56:
                assert all(h[h[i]] == i for i in range(56))
                assert all(h[dp[h[dp[h[dp[i]]]]]] == i for i in range(56))
                assert all(h[qp[i]] == qp[h[i]] and h[kp[i]] == kp[h[i]] for i in range(56))
                solutions.append(h[:])
    best_product_cycles = []
    if best_h is not None:
        assert all(best_h[best_h[i]] == i for i in range(56))
        assert all(best_h[dp[best_h[dp[best_h[dp[i]]]]]] == i for i in range(56))
        assert all(best_h[qp[i]] == qp[best_h[i]] and best_h[kp[i]] == kp[best_h[i]] for i in range(56))
        seen = set()
        for i in range(56):
            if i in seen:
                continue
            j, cycle = i, []
            while j not in seen:
                seen.add(j)
                cycle.append(j)
                j = best_h[bp[j]]
            best_product_cycles.append(cycle)
        assert any(len(c) == 9 for c in best_product_cycles)
        assert all(len(c) in (1, 3, 9) for c in best_product_cycles)
    return {
        "format": "jacobson-56-point-permutation-completions-v1",
        "scope": "All K-central permutation involutions on this fixed 56-point packet only",
        "arithmetic": "Exact integers and permutations; no floating point in checks",
        "tail_group_products_verified": 168**2,
        "tail_singer_columns": singer,
        "tail_normalizer_columns": normalizer,
        "tail_coset_representative_columns": representatives,
        "tail_b": tb,
        "tail_d": td,
        "h0_candidates": len(h0s),
        "h1_candidates": len(h1s),
        "exact_tail_candidates_checked": checked,
        "joint_completions": len(solutions),
        "completion_permutations": solutions,
        "largest_initial_segment_satisfying_first_braid": best_satisfied_points,
        "candidates_with_first_defect_below_two": candidates_with_no_even_residual_cycle,
        "least_largest_odd_residual_cycle": best_odd_residual_cycle,
        "best_completion_permutation": best_h,
        "best_HB_cycles": best_product_cycles,
        "marked_negative_rank": sum(qp[i] != i for i in range(56))//2,
        "elapsed_seconds": round(time.monotonic()-started, 3),
        "positive_all_dimensions_gap_proved": False,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
