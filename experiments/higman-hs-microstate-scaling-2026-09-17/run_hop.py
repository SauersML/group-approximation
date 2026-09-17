#!/usr/bin/env python3
"""Basin hopping seeded by the best low-dimensional witnesses (padded / direct sums)."""
import sys, json, numpy as np, ratio_search as R
k = int(sys.argv[1]); rounds = int(sys.argv[2]); seed = int(sys.argv[3])
rng = np.random.default_rng(seed)
E = R.edges("cycle", k)
def load(d):
    z = np.load(f"best_cycle{k}_d{d}.npz"); return [z["arr_%d" % i] for i in range(k)]
seeds = {"pad4to5": R.pad(load(4), 5), "pad4to6": R.pad(load(4), 6),
         "sum4+4": R.dsum(load(4), load(4)), "sum3+4": R.dsum(load(3), load(4)),
         "pad6to8": R.pad(load(6), 8)}
for name, g in seeds.items():
    J, _, _ = R.objective(g, E)
    bg, br, log = R.hop(g, E, rounds, rng)
    J, _, (e0, er) = R.objective(bg, E)
    print(json.dumps(dict(k=k, seed=name, d=g[0].shape[0], start=float(np.exp(-J)) if False else None,
                          ratio=br, e0=float(e0), er=[float(x) for x in er], improvements=log[-5:])), flush=True)
    np.savez_compressed(f"hop_cycle{k}_{name}.npz", *bg)
