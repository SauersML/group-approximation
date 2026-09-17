#!/usr/bin/env python3
"""Tensor-amplified seeds: U (x) V of best low-dimensional witnesses, then CG + basin hopping."""
import sys, json, numpy as np, ratio_search as R
k = int(sys.argv[1]); rounds = int(sys.argv[2])
rng = np.random.default_rng(11)
E = R.edges("cycle", k)
def load(d):
    z = np.load(f"best_cycle{k}_d{d}.npz"); return [z["arr_%d" % i] for i in range(k)]
for a, b in [(3, 3), (3, 4), (4, 4)]:
    g = [np.kron(x, y) for x, y in zip(load(a), load(b))]
    J0, _, (e00, er0) = R.objective(g, E)
    g1, J1, info1, _, _ = R.cg(g, E, 5000)
    bg, br, log = R.hop(g1, E, rounds, rng, eps_list=(0.1, 0.3, 0.6))
    J, _, (e0, er) = R.objective(bg, E)
    print(json.dumps(dict(k=k, seed=f"{a}x{b}", d=a * b, seed_ratio=float(np.exp(-J0)), seed_e0=float(e00),
                          cg_ratio=float(np.exp(-J1)), hop_ratio=br, e0=float(e0), er=[float(x) for x in er])), flush=True)
    np.savez_compressed(f"tensor_cycle{k}_{a}x{b}.npz", *bg)
