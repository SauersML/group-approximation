---
rg: 2
id: closed-extreme-trace-sets-give-r-fibre-w-star-bundles
kind: claim
title: Every closed set of extreme traces spans a Bauer face whose tracial completion is a W*-bundle over that set
distinct_from:
  bauer-uniform-gamma-iff-trivial-tracial-bundle: that needs the whole trace simplex to be Bauer and the algebra simple; this needs only a closed set of extreme traces, in any unital separable algebra, including algebras with Poulsen simplices.
  nontrivial-w-star-bundle-with-r-fibres-exists: that is the open existence question; this widens the admissible sources of witnesses to closed faces of arbitrary trace simplices.
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-2026-09-12.md
---

Let `A` be a unital separable C*-algebra and `K ⊆ ∂_e T(A)` a nonempty closed set.
Then:
1. `F = conv‾(K)` is a closed face of `T(A)` with `∂_e F = K`, so `F` is a Bauer
   simplex;
2. the completion `M_K` of `A` in `‖a‖_{2,F} = sup_{τ∈F} τ(a*a)^{1/2}` is a strictly
   separable continuous W*-bundle over `K`, with `E(x)(λ) = λ(x)` and fibre
   `π_λ(A)''` at `λ`;
3. if `A` is nuclear and has no finite-dimensional representation, every fibre is `R`.

**Dictionary.** Suppose all fibres are `R`. If `M_K` is trivial, then for every `N`
and `ε > 0` there is a c.p.c. order zero `φ: M_N → A` with `λ(φ(1)) > 1 − ε` for all
`λ ∈ K`. So a divisibility gap of the unit relative to `K`, at a single `N`, certifies
a nontrivial bundle and answers BBSTWW Question 3.14.

**Consequence for the witness hunt.** Question 3.14 does not need an algebra with a
Bauer trace simplex. A closed set of extreme traces of any separable nuclear algebra
suffices, simple or not, including towers whose trace simplex is Poulsen
(`toms-doubling-ah-trace-simplex-is-poulsen`).

Proof and sources: Section 1 of the artifact (Lemma 1, Proposition 2, Lemma 3).
