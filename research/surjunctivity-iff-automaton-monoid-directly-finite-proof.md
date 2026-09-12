---
rg: 2
id: surjunctivity-iff-automaton-monoid-directly-finite-proof
kind: route
title: Extend the continuous inverse on the image to a cellular left inverse
target: surjunctivity-iff-automaton-monoid-directly-finite
requires: []
artifacts:
  - research/artifacts/simple-host-direct-attack-2026-09-12.md
---

Proposition 3.1 of the artifact.

- **Surjunctive implies directly finite:** if `sigma o tau = id`, then `tau` is injective, hence
  bijective, and `sigma = tau^-1`.
- **Directly finite implies surjunctive:**
  1. For injective `tau`, the inverse `tau^-1` on the image `X` is continuous and equivariant.
  2. So it has a finite window `N` and a rule `nu` on the patterns of `X`.
  3. Extending `nu` to all of `A^N` gives an automaton `sigma` with `sigma o tau = id`.
  4. Direct finiteness gives `tau o sigma = id`, so `tau` is onto.
- **Iterates:** if `tau^(n+1)(A^G) = tau^n(A^G)`, then applying `sigma^n` gives
  `tau(A^G) = A^G`.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 13 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
