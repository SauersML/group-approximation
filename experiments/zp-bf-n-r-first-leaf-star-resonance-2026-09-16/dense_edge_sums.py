#!/usr/bin/env python3
"""Dense-edge weight sums of the braid characters Phi_k of bF_{n,r} (evidence only).

For a zero-sum character of P_k, viewed on M_{0,k+1}, the dense edges of the braid arrangement correspond to
subsets S of [k] with 2 <= |S| <= k-1 (a subset containing infinity gives the same weight as its complement).
The weight is w(S) = sum_{i<j in S} Phi_k(A_ij). Nonresonance vanishing theorems for Aomoto complexes ask for
w(S) != 0 on every dense edge. This script records, for random points of W_0 and for the named examples of
os_resonance_bf.py, how many subsets S have w(S) = 0, and which S have w(S) = 0 at every sampled random point
(a heuristic for "the functional w(S) vanishes identically on W_0").

Usage: timeout 600 python3 dense_edge_sums.py   (writes dense_edge_sums.json next to this file)
"""
import itertools, json, os, random, sys
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from os_resonance_bf import Phi, random_W0, first_leaf, tau  # noqa: E402


def zero_subsets(a, k):
    out = []
    for size in range(2, k):
        for S in itertools.combinations(range(1, k + 1), size):
            if sum(a[(i, j)] for i, j in itertools.combinations(S, 2)) == 0:
                out.append(S)
    return out


def main():
    rng = random.Random(916)
    res = {"cases": []}
    for n, rs, K in ((3, (1, 2), 12), (4, (1, 2, 3), 12)):
        d = n - 1
        for r in rs:
            points = [random_W0(n, r, rng, scale=50) for _ in range(4)]
            for k in range(3, K + 1):
                if (k - r) % d:
                    continue
                zs = []
                for data in points:
                    assert tau(data, n, r, k) == 0
                    zs.append(set(zero_subsets(Phi(data, n, r, k), k)))
                common = sorted(set.intersection(*zs))
                rec = {"n": n, "r": r, "k": k, "random_points": len(points),
                       "zero_subsets_per_point": [len(z) for z in zs],
                       "zero_at_every_point": [list(S) for S in common][:20],
                       "count_zero_at_every_point": len(common)}
                res["cases"].append(rec)
                print(n, r, k, rec["zero_subsets_per_point"], len(common), common[:6], flush=True)
    # first-leaf examples: every S inside {2..k} has w(S) = 0
    for n, c in ((3, [1, 0]), (4, [1, 0, 0])):
        r = 1
        k = 7
        a = Phi(first_leaf(c, n, r), n, r, k)
        z = zero_subsets(a, k)
        res.setdefault("first_leaf", []).append({"n": n, "c": c, "r": r, "k": k, "zero_subsets": len(z),
                                                 "subsets_total": 2 ** k - k - 2})
        print("first-leaf", n, c, k, len(z), 2 ** k - k - 2, flush=True)
    with open(os.path.join(HERE, "dense_edge_sums.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    print("DONE", flush=True)


if __name__ == "__main__":
    main()
