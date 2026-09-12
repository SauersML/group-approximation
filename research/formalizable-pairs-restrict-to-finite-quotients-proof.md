---
rg: 2
id: formalizable-pairs-restrict-to-finite-quotients-proof
kind: route
title: Substitute coset variables into the formal identity
target: formalizable-pairs-restrict-to-finite-quotients
requires: []
artifacts:
  - research/artifacts/formalizability-finite-levels-and-z3-rigidity-2026-09-12.md
---

Artifact, Section 1, Theorem 2.
1. **Invariant configurations.** `tau` and `sigma` commute with translations, so they preserve the
   `K`-invariant configurations. Those are the functions constant on cosets of the normal subgroup
   `K`.
2. **Substitution.** `X_(h,i) -> X_(hK,i)` is a ring homomorphism. It sends each rule to the rule of
   the induced automaton on `(F_2^n)^(G/K)`, and the formal identity to its image.
3. **Stable case.** Apply the same argument to `tau x id`.
