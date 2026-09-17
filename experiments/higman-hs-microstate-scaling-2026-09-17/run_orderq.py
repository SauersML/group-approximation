#!/usr/bin/env python3
"""Ratio search with odd generators constrained to exact order q (spectrum = all q-th roots
of unity, padded by eigenvalue 1 up to dimension d); even generators free."""
import sys, json, time, numpy as np, ratio_search as R
k, q, d, restarts, seed = map(int, sys.argv[1:6])
rng = np.random.default_rng(seed)
E = R.edges("cycle", k)
iso = set(range(1, k, 2))
mult = int(sys.argv[6]) if len(sys.argv) > 6 else 1
lam = np.concatenate([np.tile(np.exp(2j * np.pi * np.arange(q) / q), mult), np.ones(d - q * mult)])
best = None
t0 = time.time()
for r in range(restarts):
    g = []
    for i in range(k):
        W = R.haar(d, rng)
        g.append((W * lam) @ W.conj().T if i in iso else W)
    g, J, (e0, er), its = R.cg_iso(g, E, 4000, iso)
    rat = float(np.exp(-J))
    if best is None or rat > best[0]:
        best = (rat, float(e0), [float(x) for x in er], g)
print(json.dumps(dict(k=k, q=q, d=d, mult=mult, restarts=restarts, ratio=best[0], e0=best[1], er=best[2],
                      secs=round(time.time() - t0, 1))), flush=True)
np.savez_compressed(f"orderq_k{k}_q{q}_d{d}_m{mult}.npz", *best[3])
