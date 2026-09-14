---
rg: 2
id: rigid-defect-witness-from-canonical-normalization-failure
kind: route
title: A non-normalized Kun--Thom commutant in a Connes-embeddable target generates a hyperlinear group with a rigid defect
target: hyperlinear-group-carries-nontrivial-rigid-defect
requires: [kt-canonical-hs-normalization-fails, rigid-compression-defect-normalization-dichotomy]
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

1. The first prerequisite gives `sigma : G -> U(M)` for the Theorem E pair,
   with `M` Connes embeddable, together with a unitary
   `z in sigma(Gamma)' cap M` and `g in G` such that `sigma(g) z sigma(g)^-1`
   does not commute with some `sigma(gamma)`.
   - A non-normalized von Neumann algebra has a non-normalized unitary,
     because unitaries span it.
2. Embed `M` trace-preservingly into `R^U`. Commutation does not depend on
   the ambient algebra, so the same `z`, `g` and `gamma` still witness
   non-normalization.
3. The group `<sigma(G), z> <= U(R^U)` is countable, hence hyperlinear.
   - Use the inclusion `(+) 1` and tensor amplification.
4. It contains the rigid pair `sigma(Gamma) <= sigma(G)`: quotients of
   Kazhdan groups are Kazhdan, and images of compressors generate.
5. `[sigma(g) z sigma(g)^-1, sigma(gamma)] != 1` with `z` centralizing
   `sigma(Gamma)`, so the rigid defect is nontrivial.

This is the `not NORM => not DD` half of
`rigid-compression-defect-normalization-dichotomy`. Combined with
`hyperlinear-nonsofic-via-hyperlinear-rigid-defect`, it reaches
`hyperlinear-nonsofic-group` without intermediate coset wreaths, relative
embeddability, or the trace-free stabilizer criterion used by
`hyperlinear-nonsofic-from-canonical-hs-normalization-failure`. The group
produced is not a coset wreath, but it is nonsofic by the Hamming defect
criterion.
