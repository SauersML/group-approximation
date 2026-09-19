#!/usr/bin/env python3
"""Killing test for fpbs-critical-profile-kesten-ratio-integrable, run on the tree case.

Group: Gamma = Z/2 * Z/2 * Z/2, whose Cayley graph on {a,b,c} is the 3-regular
tree T_3. Take N trivial, so Q = Gamma and the cluster profile is a = 1_K.
Critical bond percolation has p_c = 1/2, and the cluster of o is a
Galton-Watson tree.

The Gram criterion asks whether E_{p_c}[ ||lambda(1_K)||^2 / |K| ] is finite.
Since P(|K| >= n) ~ c n^(-1/2), the criterion fails as soon as
||lambda(1_K)||^2 / |K| grows like |K|^beta with beta >= 1/2 on typical large
clusters.

The script computes a rigorous LOWER bound on ||lambda(1_K)||: the top singular
value of the compression P_R lambda(1_K) P_R to the ball B_R. It centres K first,
which is harmless because left and right translation preserve the norm. A lower
bound that grows too fast would kill the criterion on T_3. A bounded or
polylogarithmic lower bound is only evidence that the criterion survives.

Usage: python3 tree_cluster_kesten_ratio.py [seed]
"""
import sys
import random
import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import svds


def mul(u, v):
    """Multiply reduced words over the involutions {0, 1, 2}."""
    u = list(u)
    for s in v:
        if u and u[-1] == s:
            u.pop()
        else:
            u.append(s)
    return tuple(u)


def inv(u):
    return tuple(reversed(u))


def sample_cluster(p, cap, rng):
    """Cluster of the identity under bond percolation on T_3.
    Returns None if the cluster exceeds cap vertices."""
    root = ()
    K = [root]
    frontier = [root]
    while frontier:
        new = []
        for w in frontier:
            for s in range(3):
                if w and w[-1] == s:
                    continue  # this edge leads back to the parent
                if rng.random() < p:
                    x = w + (s,)
                    K.append(x)
                    new.append(x)
                    if len(K) > cap:
                        return None
        frontier = new
    return K


def centre(K):
    """Return c^{-1} K, where c is a vertex of K of minimal eccentricity.
    The eccentricity is approximated by the maximal distance from c."""
    best, bestecc = None, None
    for c in K:
        ci = inv(c)
        ecc = max(len(mul(ci, k)) for k in K)
        if bestecc is None or ecc < bestecc:
            best, bestecc = c, ecc
    ci = inv(best)
    return [mul(ci, k) for k in K], bestecc


def ball(R):
    B = [()]
    layer = [()]
    for _ in range(R):
        nl = []
        for w in layer:
            for s in range(3):
                if w and w[-1] == s:
                    continue
                nl.append(w + (s,))
        B.extend(nl)
        layer = nl
    return B


def compressed_norm(K, B, idx):
    rows, cols = [], []
    for j, y in enumerate(B):
        for k in K:
            x = mul(k, y)
            i = idx.get(x)
            if i is not None:
                rows.append(i)
                cols.append(j)
    M = sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(B), len(B)))
    s = svds(M, k=1, return_singular_vectors=False)
    return float(s[0])


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    Rs = [7, 9, 11]
    balls = {R: ball(R) for R in Rs}
    idxs = {R: {w: i for i, w in enumerate(balls[R])} for R in Rs}
    bins = [(8, 16), (16, 32), (32, 64), (64, 128), (128, 256), (256, 512)]
    per_bin = 12
    got = {b: [] for b in bins}
    tries = 0
    while any(len(v) < per_bin for v in got.values()) and tries < 2_000_000:
        tries += 1
        K = sample_cluster(0.5, 511, rng)
        if K is None:
            continue
        n = len(K)
        for b in bins:
            if b[0] <= n < b[1] and len(got[b]) < per_bin:
                got[b].append(K)
    print("# critical T_3 clusters; lower bound L_R = ||P_R lambda(1_K) P_R||")
    print("# columns: n-bin, mean n, mean ecc, and for each R: mean L_R^2/n and max L_R^2/n")
    for b in bins:
        Ks = got[b]
        if not Ks:
            continue
        ns = [len(K) for K in Ks]
        cs = [centre(K) for K in Ks]
        line = f"{b[0]:4d}-{b[1]:<4d} n={np.mean(ns):7.1f} ecc={np.mean([c[1] for c in cs]):5.1f}"
        for R in Rs:
            vals = [compressed_norm(c[0], balls[R], idxs[R]) ** 2 / len(c[0]) for c in cs]
            line += f" | R={R}: {np.mean(vals):6.2f} (max {np.max(vals):6.2f})"
        print(line, flush=True)
    # Calibration: balls and geodesic segments of comparable size.
    print("# calibration sets (same statistic)")
    for r in [2, 3, 4, 5]:
        Kb = ball(r)
        vals = [compressed_norm(Kb, balls[R], idxs[R]) ** 2 / len(Kb) for R in Rs]
        print(f"ball r={r} n={len(Kb)}: " + " ".join(f"R={R}:{v:.2f}" for R, v in zip(Rs, vals)))
    for L in [8, 16, 32]:
        # an alternating a,b segment is a path inside the dihedral subgroup <a,b>
        seg = [()]
        w = ()
        for t in range(L - 1):
            w = mul(w, (t % 2,))
            seg.append(w)
        seg, _ = centre(seg)
        vals = [compressed_norm(seg, balls[R], idxs[R]) ** 2 / len(seg) for R in Rs]
        print(f"ab-segment n={L}: " + " ".join(f"R={R}:{v:.2f}" for R, v in zip(Rs, vals)))


if __name__ == "__main__":
    main()
