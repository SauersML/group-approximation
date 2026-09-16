---
rg: 2
id: berend-some-dual-circle-has-finite-rokhlin-dimension
kind: claim
title: Some closed one-dimensional subgroup of the dual torus acts on the Berend algebra with finite commuting-tower Rokhlin dimension
refuted_by:
  - berend-dual-circles-have-infinite-rokhlin-dimension
distinct_from:
  berend-dual-circles-have-infinite-rokhlin-dimension: that proves infinite Rokhlin dimension for every infinite closed subgroup; this is the opposite hypothesis, which a Rokhlin-dimension transfer to the root would need.
  stw99-lxxxvi-berend-groups-decomposition-rank: that is the decomposition-rank assertion; this is a dynamical hypothesis about the dual action which would imply it.
  ghs-z2-commuting-rokhlin-dimension-one-dual-sai: that concerns Z_2-actions and the Rokhlin property; this concerns one-dimensional closed subgroups of T^2 acting by the dual action on one group algebra.
---

Let `A = C*(L ⋊ Σ) = C(T^3) ⋊ Σ` be the Berend algebra of
`berend-torus-actions-give-strongly-qd-polycyclic-groups`, and let `\hat α`
be the dual action of `\hat Σ ≅ T^2`. **Hypothesis:** there is a closed
subgroup `S ≤ \hat Σ` with `dim S = 1` such that
`dim^c_Rok(\hat α|_S) < ∞`, in the sense of Gardella--Hirshberg--Santiago,
arXiv:1709.00222, Definition 1.3.

This hypothesis is recorded because it is exactly what the transfer
`berend-case-from-finite-dual-rokhlin-dimension` needs. It is false:
`berend-dual-circles-have-infinite-rokhlin-dimension` shows that every
infinite closed `S` has infinite Rokhlin dimension, even without commuting
towers.

## Attempts

* **Refutation (2026-09-16).**
  1. *The dual action is inner on finite-orbit quotients.* On
     `C(Y) ⋊ Σ` with `Y` a finite orbit, every character in `Stab(Y)^⊥` acts
     by `Ad` of a unitary in `C(Y)`. Hence it fixes the central sequence
     algebra of the quotient. Pushing forward Rokhlin towers along the unital
     comparison map `F(A,A) → (C(Y) ⋊ Σ)_∞ ∩ (C(Y) ⋊ Σ)'` then gives
     `1 = 0`.
  2. *Some such character lies in `S`.* A certified `2`-adic logarithm
     computation gives infinitely many finite orbits with `Stab(Y) ⊆ Σ^2`. A
     one-dimensional `S` meets `(Σ^2)^⊥ ≅ (Z/2)^2` nontrivially, because
     `S^⊥ ≅ Z`.
  3. *Scope.* The argument does not use commuting towers, and it applies on
     every nonzero invariant ideal.
