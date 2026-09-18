#!/usr/bin/env python3
"""Random + hill-climbing search over unweighted generator sets D of F_2^k for
(a) the largest gap SDP - EXACT (basic SDP = Delsarte LP versus exact 1 - Phi(delta)),
(b) the largest gap EIG - EXACT (pure spectral certificate),
(c) power-of-two sizes where no subgroup attains the exact optimum.
Usage: search_gaps.py k d_min d_max samples seed [s_list]
"""
import json, random, sys, time
from sse_cayley import exact_c, sdp_cert, eig_cert, best_subspace, sdp_cert

def rank2(vs, k):
    basis = []
    for v in vs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)

def evaluate(k, D, sizes):
    w = {a: 1 for a in D}
    out = []
    for s in sizes:
        sub = best_subspace(k, w, s)
        ex, S, _ = exact_c(k, w, s, lower=sub or 0.0, timeout=600)
        out.append(dict(s=s, EXACT=ex, SUB=sub, SDP=sdp_cert(k, w, s), EIG=eig_cert(k, w, s), witness=S))
    return out

def main():
    k, dmin, dmax, samples, seed = map(int, sys.argv[1:6])
    sizes = list(map(int, sys.argv[6].split(","))) if len(sys.argv) > 6 else [2, 4, 8]
    rng = random.Random(seed)
    N = 1 << k
    best = {"sdp_gap": (0, None), "eig_gap": (0, None), "nonsub": []}
    t0 = time.time()
    for it in range(samples):
        d = rng.randint(dmin, dmax)
        while True:
            D = rng.sample(range(1, N), d)
            if rank2(D, k) == k:
                break
        rows = evaluate(k, D, sizes)
        for r in rows:
            g = r["SDP"] - r["EXACT"]
            if g > best["sdp_gap"][0] + 1e-9:
                best["sdp_gap"] = (g, dict(D=sorted(D), **r))
                print("SDP gap", round(g, 5), sorted(D), {x: r[x] for x in r if x != "witness"}, r["witness"], flush=True)
            e = r["EIG"] - r["EXACT"]
            if e > best["eig_gap"][0] + 1e-9:
                best["eig_gap"] = (e, dict(D=sorted(D), **r))
            if r["SUB"] is not None and r["EXACT"] > r["SUB"] + 1e-9:
                best["nonsub"].append(dict(D=sorted(D), **r))
                print("NON-SUBGROUP OPTIMUM", sorted(D), {x: r[x] for x in r if x != "witness"}, r["witness"], flush=True)
    print("done", samples, "samples in", round(time.time() - t0, 1), "s")
    print(json.dumps({"sdp_gap": best["sdp_gap"], "eig_gap": best["eig_gap"], "nonsub_count": len(best["nonsub"])}, default=str))

if __name__ == "__main__":
    main()
