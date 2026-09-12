---
rg: 2
id: compressed-coset-shifts-carry-strict-embeddings-proof
kind: route
title: Pull configurations back along the compressor surjection of the coset space
target: compressed-coset-shifts-carry-strict-equivariant-embeddings
requires: [binary-leavitt-unit-group-is-simple, leavitt-gl-equals-el-and-perfect-unit-group, rank-twelve-leavitt-simple-non-mf, leavitt-cylinder-swaps-generate-thompson-in-el]
artifacts:
  - research/artifacts/simple-kazhdan-hosts-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Section 3.3 of the artifact.

**General theorem.**
- `g h u^-1 H = g u^-1 (u h u^-1) H` makes `psi` well defined.
- Any `k in u^-1 H u` outside `H` has `psi(kH) = psi(H)`.
- `y -> y o psi` is injective because `psi` is onto, and not surjective
  because its image is constant on the fibres of `psi`.

**Instance.**
- `binary-leavitt-unit-group-is-simple`: `R^x` is infinite and simple.
- `leavitt-gl-equals-el-and-perfect-unit-group` and
  `rank-twelve-leavitt-simple-non-mf`: `R^x ~= EL_12(R)` is Kazhdan.
- `leavitt-cylinder-swaps-generate-thompson-in-el`: `R^x` contains the copies
  `V_l`.
- The prefix bijection `u` maps `[1]` onto `[11]`, so `u V_1 u^-1 = V_11`. This
  is a proper subgroup of `V_1`, which moves points of `[10]`.
- An infinite simple group has no proper subgroup of finite index, so
  `[R^x : V_1]` is infinite.

**Kazhdan-side properties.** Property (T) gives strong ergodicity and spectral
gap for the ergodic Bernoulli measure (Schmidt; Connes--Weiss) and closedness of
ergodic measures (Glasner--Weiss).

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 18 of the
verification artifact). `psi(kuH) = kH` gives ontoness, and the fibres have size
`[u^-1 H u : H] >= 2`.
