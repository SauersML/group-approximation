---
rg: 2
id: nv-fibration-stabilizer-kazhdan-finite-proof
kind: route
title: The base map to |I|V has finite Kazhdan image, and the finite-index kernel lies in a finite product of copies of |J|V whose Kazhdan subgroups are finite by induction
target: kazhdan-subgroups-of-nv-fibration-stabilizers-are-finite
requires:
  - thompson-v-has-haagerup-property
artifacts:
  - research/artifacts/kazhdan-nv-displacement-gap-2026-09-17.md
---

Complete proof: artifact Section D. Imports: countable Kazhdan groups are finitely
generated; quotients and finite-index subgroups of Kazhdan groups are Kazhdan.

Induction on `n`, with `n = 1` from `thompson-v-has-haagerup-property`.

1. `g -> v` is a homomorphism `Stab_I -> |I|V` (on each piece of a brick partition of `g`,
   `v` is the prefix replacement of the `I`-words). The image of Kazhdan `K` is Kazhdan
   in `|I|V`, finite by induction; the kernel `K_1` has finite index and is Kazhdan.
2. A kernel element has the identity on `I`-words on each piece, so its fibre maps
   `φ_a ∈ |J|V` are constant on bricks of shape `D_g·1` in `C^I`. A finite generating set
   of `K_1` gives one brick partition `P` of `C^I`, and `K_1 <= Π_{B∈P} |J|V`.
3. Each factor image is a Kazhdan subgroup of `|J|V`, finite by induction, so `K_1` and
   `K` are finite. Conjugation preserves both (T) and finiteness.
