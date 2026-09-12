---
rg: 2
id: normalizing-subgroups-separate-double-cosets
kind: claim
title: A subgroup normalizing a disjoint subgroup injects into its double-coset set
artifacts:
  - research/artifacts/boone-higman-lean-preflight-2026-09-08.md
---

Let H and K be subgroups of a group G. Assume H intersect K = {1}
and k H k^-1 = H for every k in K. Then the map

    K -> H \\ G / H,   x |-> H x H

is injective. Thus an infinite such K forces H to have infinite bi-index.
Centralization is sufficient but is not necessary for this conclusion.

The fixed Lean statement in `experiments/bh_gpu_pilot.py`, probe
`normalizer_extension`, expresses the injectivity implication by
y=a*x*b with a,b in H and x,y in K. An assistant-authored tactic proof
passed Lean 4.32.0 with only propext and Quot.sound in the axiom audit.
This is an elementary construction filter, not a solution of Boone–Higman.

Dropping normalization as well as centralization makes the assertion
false: H=C2 and K=C3 in S3 give the recorded exact counterexample.
