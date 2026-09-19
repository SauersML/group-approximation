#!/usr/bin/env python3
"""Lower bounds on ||lambda(1_K)||^2/|K| for critical T_3 clusters, by pruned power iteration.

This is a companion to tree_cluster_kesten_ratio.py. Instead of compressing to a
fixed ball, it runs power iteration for A^T A with A = lambda(1_K) on l2(Gamma),
where Gamma = Z/2*Z/2*Z/2. After each step the vector keeps only its M largest
entries.

For every vector xi the Rayleigh quotient ||A xi|| / ||xi|| is a rigorous lower
bound on ||A||, whatever pruning produced xi, because A xi is computed exactly.
The script prints the best such bound.

Usage: python3 tree_cluster_power_lower_bound.py [seed] [M] [iters]
"""
import sys
import random
import heapq
import math
from tree_cluster_kesten_ratio import mul, inv, sample_cluster, centre


def apply_A(K, xi):
    out = {}
    for y, v in xi.items():
        for k in K:
            x = mul(k, y)
            out[x] = out.get(x, 0.0) + v
    return out


def apply_AT(Kinv, eta):
    # (A^T eta)(y) = sum_k eta(k y) = sum_{k} (lambda(1_{K^{-1}}) eta)(y)
    return apply_A(Kinv, eta)


def norm(d):
    return math.sqrt(sum(v * v for v in d.values()))


def prune(d, M):
    if len(d) <= M:
        return d
    top = heapq.nlargest(M, d.items(), key=lambda kv: abs(kv[1]))
    return dict(top)


def lower_bound(K, M, iters):
    Kinv = [inv(k) for k in K]
    # start from the uniform vector on K^{-1}, which is well matched to 1_K
    xi = {k: 1.0 for k in Kinv}
    best = 0.0
    for _ in range(iters):
        nx = norm(xi)
        Ax = apply_A(K, xi)
        best = max(best, norm(Ax) / nx)
        xi = prune(apply_AT(Kinv, Ax), M)
        s = norm(xi)
        xi = {w: v / s for w, v in xi.items()}
    return best


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    iters = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    rng = random.Random(seed)
    bins = [(8, 16), (16, 32), (32, 64), (64, 128), (128, 256)]
    per_bin = 5
    got = {b: [] for b in bins}
    while any(len(v) < per_bin for v in got.values()):
        K = sample_cluster(0.5, 255, rng)
        if K is None:
            continue
        for b in bins:
            if b[0] <= len(K) < b[1] and len(got[b]) < per_bin:
                got[b].append(K)
    print(f"# pruned power iteration, M={M}, iters={iters}; value = (lower bound)^2 / n")
    for b in bins:
        vals, ns = [], []
        for K in got[b]:
            Kc, _ = centre(K)
            L = lower_bound(Kc, M, iters)
            vals.append(L * L / len(Kc))
            ns.append(len(Kc))
        print(f"{b[0]:4d}-{b[1]:<4d} mean n={sum(ns)/len(ns):6.1f}  mean {sum(vals)/len(vals):6.2f}  max {max(vals):6.2f}", flush=True)
    # calibration: a path inside the dihedral subgroup <a,b> has true value n
    for L in [16, 32, 64]:
        seg, w = [()], ()
        for t in range(L - 1):
            w = mul(w, (t % 2,))
            seg.append(w)
        seg, _ = centre(seg)
        lb = lower_bound(seg, M, iters)
        print(f"calibration ab-segment n={L}: {lb*lb/L:6.2f} (true value {L})")


if __name__ == "__main__":
    main()
