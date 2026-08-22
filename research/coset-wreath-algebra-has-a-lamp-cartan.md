---
rg: 2
id: coset-wreath-algebra-has-a-lamp-cartan
kind: claim
title: The summit coset wreath algebra is a II1 factor with the lamp algebra as a Cartan masa
artifacts:
  - research/artifacts/coset-wreath-cartan-entropy-2026-08-22.md
distinct_from:
  invariant-cartan-group-basis-needs-hyperfinite-envelope: that is an envelope-lane statement about group bases of invariant Cartans in algebraic-action crossed products; this identifies a concrete Cartan masa inside L(W_3) itself, as input to the free-entropy bound, with no envelope or group-basis content.
  coset-bernoulli-action-is-essentially-free: that is the dynamical freeness statement; this is its operator-algebraic conversion - factoriality, maximal abelianness and regularity of the lamp masa - the package Voiculescu-Jung-Hayes machinery consumes.
---

Let `W_3 = (direct_sum_{Gamma/Lambda} C_2) rtimes Gamma` with
`Gamma = SL_3(Z[1/3])`, `Lambda = SL_3(Z)` (the summit wreath of
`nonhyperlinear-coset-wreath-from-p3-collapse`), and let
`X = {-1,1}^{Gamma/Lambda}` with Bernoulli(1/2) measure `mu`.  Claim:

1. the generalized Bernoulli action `Gamma acts (X, mu)` is ergodic;
2. `L(W_3) = L^infinity(X) rtimes Gamma` (canonical trace = Bernoulli
   trace) is a II_1 factor;
3. `A = L^infinity(X)` — the von Neumann algebra of the lamp group — is
   a CARTAN subalgebra of `L(W_3)`: diffuse, hyperfinite, maximal
   abelian, regular.

Mechanism: ergodicity by the Fourier–Walsh orbit computation (every
nonempty finite subset of `Gamma/Lambda` has an infinite orbit because
point stabilizers have infinite index); maximal abelianness from
essential freeness (`coset-bernoulli-action-is-essentially-free`);
regularity is visible; factoriality from free + ergodic + p.m.p.
Details in the artifact (Theorem 2).

Wanted for: activating Jung–Hayes strong 1-boundedness on `L(W_3)`
(`coset-wreath-hyperlinearity-forces-strong-one-boundedness`).  Scope
note: for the `SL_2(Z[1/2])` wreath the same holds after quotienting
the central `{+-1}` (both direct summands of `L(W)` acquire lamp
Cartans); the p = 3 instance is stated because its center is trivial
and it is the lane's summit group.

Deliberately recorded alongside `coordinate-action-not-sofic`: the
existence of a Cartan in the limit algebra does NOT contradict the
Kun–Thom refutation of Cartan-compatible (permutation) approximations;
microstates of `W_3`, if any, cannot respect this Cartan, yet
(`coset-wreath-hyperlinearity-forces-strong-one-boundedness`) they are
still entropy-starved because the Cartan exists at the limit.
