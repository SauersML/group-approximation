---
rg: 2
id: surface-generalized-bs-groups-satisfy-boone-higman-proof
kind: route
title: Feed the quaternion-lattice witness into Bux–Llosa Isenrich–Wu Theorem 11.1
target: surface-generalized-bs-groups-satisfy-boone-higman
requires:
  - surface-groups-have-faithful-generalized-bs-witnesses
  - virtually-free-extensions-lie-in-generalized-bs-classes
  - bliw-locally-finite-tree-actions-embed-in-fp-simple-groups
artifacts:
  - research/artifacts/gq-bh-bh-free-extensions-bliw-section-11-12.md
---

1. **Type F_∞.** `G = π_1(Σ)` is the fundamental group of a closed aspherical surface, so it is of
   type `F_∞`, and in particular of type `F_n` for every `n ≥ 2`.
2. **Witness.** By `surface-groups-have-faithful-generalized-bs-witnesses`, some
   nontrivial `H ∈ BS_G` acts faithfully on its Bass–Serre tree.
3. **BLIW Theorem 11.1**, read in §11 of arXiv:2408.05673v2 and recorded in the artifact: for `G` of
   type `F_n` with `n ≥ 2` and such an `H`, every `K ∈ BS_G` embeds in a simple group of type
   `F_n`. With `n = 2` this already gives a finitely presented simple group, which is the
   Boone–Higman conclusion. For type `F_∞`: the group `L ⊇ K` built in the proof of Theorem 11.1
   does not depend on `n`, and neither does the simple envelope in Theorem 10.5 (the twisted
   Brin–Thompson group of the rigid permutation group). So that one envelope is of type `F_n` for
   every `n`. This is exactly how BLIW state their Theorems 12.2–12.5 with type `F_∞`.
   (`bliw-locally-finite-tree-actions-embed-in-fp-simple-groups` imports the paper's introductory
   form of Theorem C [11.1] with the finitely presented conclusion. The `F_n` form used here is §11's.)
4. **Item 1** is `virtually-free-extensions-lie-in-generalized-bs-classes`
   with `N = π_1(Σ)`, which is finitely generated and infinite.
5. **Items 2–3** are finite graphs of groups of the defining kind. Subgroups of finite index in
   surface groups are again (virtually) surface groups, so they are commensurable with `G` (step 4 of
   the witness proof).

**Trust surface:** BLIW Theorems 10.5 and 11.1 (their proofs not re-checked), plus the textbook
inputs listed in the witness proof.
