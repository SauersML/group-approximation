---
rg: 2
id: virtually-finite-cd-stable-bnsr-via-finite-index-detection
kind: route
title: "Stabilize on the finite-cd subgroup, then pull the equality back up through restriction"
target: virtually-finite-cd-f-infinity-groups-have-stable-bnsr
requires:
  - bnsr-invariants-are-detected-on-finite-index-subgroups
  - bnsr-invariants-stabilize-at-cohomological-dimension
---

Let `G` be of type `F_∞`, let `H ≤ G` have finite index with `cd H = d < ∞`,
and put `e = max(d,2)`.

1. By `bnsr-invariants-are-detected-on-finite-index-subgroups` (item 1), `H`
   is of type `F_∞`.
2. `H` is of type `F_∞` with `cd H = d`. So
   `bnsr-invariants-stabilize-at-cohomological-dimension` gives
   `Σ^m(H) = Σ^e(H)` for all `m ≥ e`.
3. By the second consequence of
   `bnsr-invariants-are-detected-on-finite-index-subgroups` (stabilization
   passes up, applied with `k = e`), `Σ^m(G) = Σ^e(G)` for all `m ≥ e`. ∎

Step 3 needs no case split: if `S(G)` is empty, both sides are empty.
