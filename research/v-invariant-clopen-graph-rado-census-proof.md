---
rg: 2
id: v-invariant-clopen-graph-rado-census-proof
kind: route
title: Classify invariant graphs by the five pair classes, reduce extension to atom colourings, and check one certificate per graph
target: v-invariant-clopen-graphs-are-never-the-rado-graph
requires: []
artifacts:
  - research/artifacts/hl-bh-fraisse-thompson-2026-09-14.md
  - experiments/bh-fraisse-rado/fraisse-rado-search.py
  - experiments/bh-fraisse-rado/fraisse-rado-certs.py
  - experiments/bh-fraisse-rado/fraisse-rado-verify.py
  - experiments/bh-fraisse-rado/k2.txt
  - experiments/bh-fraisse-rado/k3.txt
  - experiments/bh-fraisse-rado/certs.jsonl
  - experiments/bh-fraisse-rado/verify.txt
---

Notation as in the claim.

**Step 1 (pair classes).**
- For `U != W` in `X` put `π(U,W) = (U∩W ≠ ∅, U\W ≠ ∅, W\U ≠ ∅, C\(U∪W) ≠ ∅)`.
- Since `U, W` are nonempty and proper and `U != W`, exactly six ordered patterns occur. They
  form five unordered classes:
  - complementary `(0,1,1,0)`;
  - disjoint `(0,1,1,1)`;
  - nested `(1,0,1,1)`, `(1,1,0,1)`;
  - covering overlap `(1,1,1,0)`;
  - generic overlap `(1,1,1,1)`.
- Homeomorphisms preserve `π`. `V` is transitive on each ordered pattern:
  1. write each nonempty atom of both pairs as a finite union of dyadic cones;
  2. split cones until corresponding atoms have equal counts;
  3. match cones atom by atom. The resulting prefix replacement lies in `V`.

  This is the tuple classification of `full-cantor-boolean-atom-orbits-and-embedding-proof`,
  specialized to pairs.
- So for `V <= D <= Homeo(C)` the `D`-invariant graphs on `X` are exactly the 32 unions of
  classes.

**Step 2 (colouring lemma).**
- Let `F = {U_1, ..., U_K} ⊆ X` be distinct, with nonempty Boolean atoms `A_1, ..., A_r`.
- For `z ∈ X` colour `A_j` by `E` if `A_j ∩ z = ∅`, by `F` if `A_j ⊆ z`, and by `M` otherwise.
- Each coordinate of `π(U_i, z)` is a disjunction over atoms. For example `U_i ∩ z ≠ ∅` iff
  some `A_j ⊆ U_i` has colour `F` or `M`, and `C \ (U_i ∪ z) ≠ ∅` iff some `A_j ⊄ U_i` has
  colour `E` or `M`. So the adjacency vector of `z` to `F` depends only on the colouring.
- Conversely every colouring except constant `E` and constant `F` is realized by some `z ∈ X`:
  split each `M` atom into two nonempty clopen pieces and take one of them.
- `z ∈ F` only when no atom is coloured `M` and the `F`-atoms form some `U_i`.

**Step 3 (finite check).**
- By Step 2 the extension property of an invariant graph over `F` depends only on the
  configuration `Q ⊆ {0,1}^K` of nonempty atoms. It is decided by enumerating at most `3^r`
  colourings.
- `fraisse-rado-search.py` does this for every configuration with `K = 2, 3`, and with
  `K = 4` restricted to at most 8 atoms, over all 30 nonempty proper unions (MSI job 793013).
- `k2.txt`: 6 configurations, 8 surviving graphs. `k3.txt`: 174 configurations, 0 surviving.
  `k4a8.txt`: 36,355 configurations, 0 surviving.

**Step 4 (independent verification, MSI job 795198).**
- `fraisse-rado-certs.py` emits one certificate per graph: a family configuration and a
  missing vector `v`.
- `fraisse-rado-verify.py` shares no code with the search:
  - it rebuilds each family as unions of the 8 dyadic cones of depth 3;
  - it classifies pairs by a separate hand rule;
  - it enumerates every `z ∈ X` built from depth-4 cones (65,534 sets).
- Completeness: every family atom contains at least two depth-4 cones, so depth 4 realizes
  every colouring of Step 2.
- `verify.txt`:
  - 30 of 30 certificates VERIFIED;
  - positive control PASS: the 8 two-point survivors satisfy the two-point property over every
    pair of distinct depth-2 clopens, and those pairs realize every two-set configuration;
  - negative control PASS: a corrupted certificate is rejected.

**Step 5 (conclusion).**
- The empty and complete graphs fail the one-point property. Every other invariant graph has
  a verified certificate at `K <= 3`.
- The Rado graph is the unique countable graph in which, for all finite disjoint vertex sets
  `A, B`, some vertex outside `A ∪ B` is adjacent to all of `A` and none of `B` (source in the
  artifact). Taking `A = {U_i : v_i = 1}` and `B = {U_i : v_i = 0}` contradicts this for every
  invariant graph.
