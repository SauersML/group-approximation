---
rg: 2
id: random-complex-bounded-removal-detected-by-quotient
kind: claim
title: A mid-range random complex has a bounded set of triangles whose removal lets a finite quotient detect one removed perimeter
distinct_from:
  random-complex-missing-triangle-detected-by-quotient: that asks a uniformly random missing triangle added to the complex to be detected by a finite quotient; this lets a bounded set of the complex's own triangles be chosen after sampling, which is weaker, and that claim implies this one with t = 1 through bounded-removal-detection-from-random-triangle-detection
  random-complex-group-no-large-finite-quotients: that forbids large finite quotients of the random group itself; this concerns quotients of the group of the complex minus t triangles, which need not factor through the random group
  non-residually-finite-hyperbolic-group: that asks for some non-residually-finite hyperbolic group; this is a bounded-removal detection statement about specific random complexes and says nothing about other hyperbolic groups
---

**OPEN.** For every `0 < η < 1/2` there is a fixed integer `t` such that, with
`p = n^(-1+η)` and `Y ~ Y(n,p)`, a.a.s. some `T ⊂ Y(2)` with `|T| <= t` satisfies:

1. `Y \ T` is pure and connected, with the same 1-skeleton as `Y`;
2. `Y \ T` is a `1/4`-local spectral expander;
3. for some `Δ in T`, the perimeter of `Δ` survives in a finite quotient of
   `π_1(Y \ T)`.

By `bounded-removal-finite-quotient-caps-cocycle-cheeger` this refutes
`random-complex-cocycle-cheeger-beats-triangle-count` at every exponent `η`
(route `random-complex-cheeger-capped-via-bounded-removal`).

## Where it sits

* **Weaker than random-triangle detection.** `T` is chosen after sampling, and
  only one of its perimeters must be detected. Route
  `bounded-removal-detection-from-random-triangle-detection` derives the claim
  with `t = 1` from `random-complex-missing-triangle-detected-by-quotient`, taking
  `T` to be the added triangle of a Chapman--Peled pair.
* **Meshulam's exclusion.** Quotients of `π_1(Y \ T)` that detect a removed
  perimeter do not factor through `π_1(Y)`. When `T` is one uniformly random
  triangle of the sample, `Y \ T` is close to `Y(n,p)` in total variation, so
  `meshulam-random-complex-no-polynomial-quotients` applies to `π_1(Y \ T)`: for
  every fixed `c`, a.a.s. every detecting quotient has order larger than `n^c`. Whether
  the exclusion holds for all `n^(O(t))` choices of `T` at once is not checked.
* **Conditions 1–2.** In that route they come from
  `random-complex-mid-range-pair-properties` and a first-moment purity count. For
  adversarially chosen `T` no perturbation lemma is landed.
* **Kazhdan caution.** As in `random-complex-missing-triangle-detected-by-quotient`,
  `π_1(Y)` has property (T) and is not cubulated, so virtual specialness is
  unavailable.
