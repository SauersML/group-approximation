---
rg: 2
id: injective-measure-preserving-ca-is-surjective-proof
kind: route
title: Full support turns a measure-one closed image into the whole shift
target: injective-measure-preserving-ca-is-surjective
requires: []
artifacts:
  - research/artifacts/gottschalk-kazhdan-direct-attack-2026-09-12.md
  - research/artifacts/gk-vf-positive-verification-2026-09-12.md
---

## Direct proof

Let `G` be countable, `A` finite, `mu_A` the uniform Bernoulli measure on `A^G`.
`mu_A` has full support: every nonempty basic open cylinder has positive measure,
so every nonempty open set does.

Let `tau: A^G -> A^G` be an injective cellular automaton with `tau_* mu_A = mu_A`.

1. `A^G` is compact and `tau` is continuous, so `Y = tau(A^G)` is compact, hence
   closed.
2. `tau^{-1}(Y) = A^G`, so `mu_A(Y) = tau_* mu_A(Y) = mu_A(A^G) = 1`.
3. `A^G \ Y` is open with `mu_A(A^G \ Y) = 0`. Full support forces every
   `mu_A`-null open set to be empty, so `A^G \ Y = emptyset` and `Y = A^G`.

Hence `tau` is surjective. Injectivity is not used in the argument beyond making
the statement about an automaton; the content is that a measure-preserving
continuous self-map of `A^G` for a full-support measure has dense, hence full,
image. QED

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 1.2 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`).
