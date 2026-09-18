---
rg: 2
id: nv-periodic-groups-via-schreier-subshift-factors
kind: route
title: If an element of nV factors on a clopen invariant set onto an infinite minimal subshift whose full group contains an infinite periodic group, that group lies in nV
target: brin-thompson-groups-contain-infinite-periodic-groups
requires:
  - aperiodic-full-groups-lift-along-factor-maps
  - brin-thompson-groups-contain-full-groups-of-their-elements
---

**Route (conditional; the condition is OPEN).** Lane proof, bh-free-01, elementary.

**Hypothesis (F).** There are `n ≥ 2`, `g ∈ nV`, a clopen `U ⊆ C^n` with `g(U) = U`, an infinite minimal
subshift `(X, T)` and a continuous surjection `π : U -> X` with `π ∘ g = T ∘ π`, such that the
topological full group `[[T]]` contains an infinite finitely generated periodic group `P`.

**Conclusion.** `P` embeds in `nV`.

**Proof.**
- `X` is infinite and minimal, so `T` has no periodic points. By `aperiodic-full-groups-lift-along-factor-maps`
  (applied to `S = g|_U`), `f -> f~` is an injective homomorphism `[[T]] -> [[g|_U]]`.
- By `brin-thompson-groups-contain-full-groups-of-their-elements`, `[[g|_U]]`, extended by the identity
  off `U`, is a subgroup of `nV`.
- So `P ≅ P~ ≤ nV`. Periodicity is preserved because `f -> f~` is an injective homomorphism.

**Candidate `(X, T)`.** A Grigorchuk subshift: Matte Bon, arXiv:1408.0762 (abstract read 2026-09-18),
embeds every Grigorchuk group `G_ω` in `[[T]]` for a minimal subshift. The ternary variant is in Attempt 1
of the target. The whole difficulty is the factor map `π`, see there.
