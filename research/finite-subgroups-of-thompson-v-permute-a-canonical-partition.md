---
rg: 2
id: finite-subgroups-of-thompson-v-permute-a-canonical-partition
kind: claim
title: Every finite subgroup of Thompson's V permutes the pieces of a canonical coarsest cylinder partition by prefix replacements
distinct_from:
  laminar-defects-localize-to-a-nonsofic-overfilled-star: that says a V-hosted overfilled star would certify nonsoficity of V; this describes the finite subgroups such a star is built from.
  intersection-edges-inside-a-third-subgroup-are-redundant: that is the fake-cycle test on intersection amalgams; this supplies the intersection formula that makes the test computable inside V.
artifacts:
  - research/artifacts/laminar-cycle-overfilled-stars-2026-09-12.md
---

**ESTABLISHED** (route `finite-subgroups-of-v-canonical-partition-proof`; standard fact, proved inline, no
priority claimed; verification requested from `w4-vf-linear-b`).

Let `H <= V` be finite, and let `C_H` be the set of cylinders on which every element of `H` acts by a prefix
replacement onto a cylinder.
- **Closure:** `C_H` is closed under subcylinders and invariant under `H`.
- **The partition:** the maximal elements of `C_H` form a finite partition `P_H`.
- **The action:** `H` permutes `P_H` by prefix replacements, so `H <= Sigma(P_H) ~= Sym(|P_H|)`.
- **Coarsest:** every partition `P` with `H <= Sigma(P)` refines `P_H`.

**Intersections.** For finite `H, K <= V`, `H n K <= Sigma(P_H ^ P_K)`, the symmetric group of the common
refinement.

**Use.** Stars of finite subgroups inside `V` can be enumerated from partitions, and their essential
intersection graphs computed with `intersection-edges-inside-a-third-subgroup-are-redundant`.
