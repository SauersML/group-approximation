---
rg: 2
id: iwahori-finite-image-vertex-congruence-capture
kind: claim
title: An almost compatible Iwahori pair whose first vertex has finite image has that vertex close to congruence
distinct_from:
  iwahori-one-vertex-congruence-capture: that allows any first vertex; this assumes the first vertex has finite image, so the whole difficulty is non-congruence finite quotients of SL_2(Z).
  iwahori-vertex-finite-image-capture: that is the complementary infinite-image half.
  iwahori-congruence-capture-transfers-across-one-edge: that treats a congruence first vertex, the case in which this claim holds trivially; this asks about finite-image first vertices that are not congruence.
  codense-tau-coset-soficity-forces-permutation-instability: that turns positive vertex-action models into permutation instability; this is a unitary capture statement for finite-image first vertices, with no permutation structure assumed.
---

**OPEN.** Notation as in `iwahori-congruence-capture-transfers-across-one-edge`.

> **(NC)** For every sequence of exact pairs `pi_n` with `def(pi_n) -> 0`
> **such that each `pi_(n,+)` has finite image**, we have `A_+(pi_n) -> 0`.

**Role.** This is the *non-congruence half* of
`iwahori-one-vertex-congruence-capture`. By the route
`iwahori-capture-from-finite-image-and-finite-image-congruence`, capture is
equivalent to `iwahori-vertex-finite-image-capture` together with (NC). The
second vertex `pi_(n,-)` is unrestricted.

**What is already known.**
* **Congruence first vertex.** If `pi_(n,+)` is congruence then
  `A_+(pi_n) = 0`. The Exact case of the transfer theorem then puts `pi_-`
  within `C sqrt(def)` of congruence.
* **Bounded-degree non-congruence quotients are excluded.** By
  `iwahori-bounded-dimensional-vertex-constituents-are-congruence`, a
  countersequence has, apart from mass `o(1)`, its non-congruence
  constituents in dimensions tending to infinity. So each `pi_(n,+)` factors
  through a finite quotient `C/K_n`, with `K_n` not congruence, whose
  relevant irreducibles have unbounded degree.
* **Permutation subcase.** If both vertices are permutation representations,
  (NC) follows from flexible permutation stability of `SL_2(Z[1/2])`. A
  stabilized action factors through a finite quotient, which is odd
  congruence by the congruence subgroup property. For permutation matrices
  `||P - Q||_2^2` is twice the normalized Hamming distance, so Hamming
  capture gives `d_2` capture. That stability is itself open; see the
  Attempts of `dyadic-bruhat-tits-vertex-action-is-not-sofic`.

## Attempts

- **2026-09-19 (swarm-0917, operator-algebras).** Uniform `(tau)` induction
  as in the transfer proof. Dead as a direct transfer. The transfer proof
  induces from a congruence vertex and uses Selberg's uniform gap for
  `Gamma(N)`. For a non-congruence kernel `K_n` no uniform spectral gap over
  all finite-index `K_n` is available, since `C` is virtually free and its
  finite quotients include non-expanding families. So the induction step
  has no dimension-free constant.
