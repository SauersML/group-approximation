"""Independent check of a lower-bound certificate for R*(k).

Input: integer per-edge weights W[o] for each edge orbit o (from hadk_colgen.py output).
Checks, in exact integer arithmetic:
  1. completeness: every coordinate direction j carries total weight W(E)/K, so every
     dictator violates exactly the fraction 1/K (c = 1/K);
  2. soundness: s >= sum_q Pr[q] mincut_W(rep_q) / W(E), the unfolded min cut being a
     lower bound for the folded one; the orbit reduction is checked by re-solving the min
     cut at `samples` random patterns per orbit and comparing with the representative;
  3. the gadget is invariant under every generator (so orbits are genuine).
Prints K * LB as an exact fraction.

usage: python3 verify_certificate.py k W0,W1,... [samples]
"""
import sys
from fractions import Fraction
import numpy as np
from hadk_setup import setup, coord_perms, act_masks
from hadk_mincut import unfolded_price

k = int(sys.argv[1])
W = np.array([int(t) for t in sys.argv[2].split(",")], dtype=np.int64)
samples = int(sys.argv[3]) if len(sys.argv) > 3 else 2
S = setup(k)
K, E, full, eid = S["K"], S["E"], S["full"], S["eid"]
assert len(W) == S["norb"]
cap = W[S["orb"]]
tot = int(cap.sum())
# 1. completeness
dirw = np.array([int(cap[S["ej"] == j].sum()) for j in range(K)])
assert np.all(dirw * K == tot), dirw
print("completeness: each direction carries W(E)/K; dictator uval = 1/K")
# 3. invariance under generators and negation
ex, ej = S["ex"], S["ej"]
for g in coord_perms(k):
    gx = act_masks(g, ex, K); gj = np.asarray(g)[ej]
    gy = gx ^ (np.int64(1) << gj)
    base = np.where(((gx >> gj) & 1) == 0, gx, gy)
    assert np.array_equal(cap[eid(base, gj)], cap)
nx = (ex ^ full) ^ (np.int64(1) << ej)
assert np.array_equal(cap[eid(nx, ej)], cap)
print("gadget invariant under all generators and negation")
# 2. soundness
rng = np.random.default_rng(1)
num = Fraction(0)
for q, xi in enumerate(S["reps"]):
    v, _, _ = unfolded_price(S, cap, xi)
    members = np.flatnonzero(S["porb"] == q)
    for p in rng.choice(members, size=min(samples, len(members)), replace=False):
        v2, _, _ = unfolded_price(S, cap, int(p))
        assert v2 == v, (q, int(p), v, v2)
    num += Fraction(int(S["psize"][q]), int(S["npat"])) * v
    print(f"orbit {q}: size {S['psize'][q]}, mincut {v}, samples agree", flush=True)
LB = K * num / tot
print(f"certified: R*({k}) >= K * s / 1 = {LB} ~ {float(LB):.6f}")
