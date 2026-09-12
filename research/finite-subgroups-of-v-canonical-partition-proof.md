---
rg: 2
id: finite-subgroups-of-v-canonical-partition-proof
kind: route
title: Maximal cylinders on which the whole finite group acts by prefix replacements
target: finite-subgroups-of-thompson-v-permute-a-canonical-partition
requires: []
artifacts:
  - research/artifacts/laminar-cycle-overfilled-stars-2026-09-12.md
---

Proof: Section 3 of the artifact (Proposition 3.1, Corollary 3.2).

1. **`C_H` is invariant.** On `h(c)`, `g` is `gh` on `c` composed with the inverse replacement, and both
   are prefix replacements.
2. **Maximal elements.** Each point lies in a cylinder inside a piece of every domain partition `D_h`, and
   the cylinders above a cylinder form a finite chain. Distinct maximal cylinders are disjoint, and by
   compactness they give a finite partition.
3. **The action.** If `h(c)` were strictly inside a maximal `c'`, then `h^(-1)(c')` would be a cylinder of
   `C_H` strictly containing `c`.
4. **Intersections.** An element permuting both partitions maps `p n q` onto `g(p) n g(q)` by the prefix
   replacement of `p`.
