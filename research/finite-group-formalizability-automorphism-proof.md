---
rg: 2
id: finite-group-formalizability-automorphism-proof
kind: route
title: Ax–Grothendieck turns a formal left inverse on finitely many variables into a two-sided inverse
target: finite-group-formalizability-equals-equivariant-automorphism
requires: []
artifacts:
  - research/artifacts/formalizability-finite-levels-and-z3-rigidity-2026-09-12.md
---

Artifact, Section 1, Theorem 1.
1. **Forward.**
   - A formal identity `S o T = id` on `A^(n|G|)` makes `T` injective on `F̄_2`-points.
   - Ax–Grothendieck makes `T` bijective, so `S = T^-1` on points.
   - Then `T o S = id` holds on an infinite field, hence formally, and `T` is an equivariant
     automorphism.
2. **Backward.**
   - An equivariant automorphism `T` satisfies `T(x)_g = T(g^-1.x)_1`, so it is the automaton with
     memory `G` and rule `T(.)_1`. Its inverse is also equivariant.
   - `tau` is bijective on the finite configuration set, so `sigma = tau^-1` is the shadow of
     `T^-1`.
   - The identity `T^-1 o T = id` is formal.
