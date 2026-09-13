---
rg: 2
id: nowhere-scattered-af-crossed-products-dichotomy-proof
kind: route
title: Tarski gives an invariant trace or a paradoxical multiple, and the minimal-action coinvariant lemma upgrades the multiple to proper infiniteness
target: nowhere-scattered-af-crossed-products-dichotomy
requires: [rainone-type-semigroup-crossed-product-dichotomy, coinvariant-tarski-lemma-minimal-nowhere-scattered, af-k0-order-divisible-iff-no-elementary-subquotient]
---

**Hypotheses.**
* A unital separable AF algebra `D` is exact.  It has real rank zero, so its
  projections are total and it has property (SP).  It is stably finite and
  has cancellation.
* `K_0(D)` is a dimension group, so (R) and (P) of
  `coinvariant-tarski-lemma-minimal-nowhere-scattered` hold.
* Every closed ideal of `D` contains a nonzero projection.  So by Rainone,
  Theorem 3.7, minimality of `alpha` is equivalent to the absence of
  nontrivial `Gamma`-invariant order ideals in `K_0(D)`.
* Condition 3 of `af-k0-order-divisible-iff-no-elementary-subquotient` gives
  (ND).

So the lemma applies to `Sigma = S(D, Gamma, alpha)`.  The crossed product is
simple because `alpha` is minimal and properly outer: Olesen--Pedersen,
Theorem 7.2, as invoked in Rainone's proof of Theorem 4.16.

**Case A: `Sigma` has a nontrivial state.**  Take `nu` with
`0 < nu([x]) < infinity`.

* As in Rainone's proof of Theorem 4.21 (`(4) => (5)`) and Proposition 4.12,
  minimality makes `nu` finite on `Sigma`.
* Composing with `K_0(D)^+ -> Sigma` and extending gives a `Gamma`-invariant
  positive homomorphism `beta: K_0(D) -> R`.  It is nonzero, so
  `beta([1]) > 0`, because every positive class lies below a multiple of `[1]`.
* It is faithful.  For `x != 0`, `K_0`-minimality gives
  `sum_j alpha_(t_j)(x) >= [1]`, hence `n beta(x) >= beta([1])`.
* Normalizing gives a faithful `Gamma`-invariant state on
  `(K_0(D), K_0(D)^+, [1])`.  By Rainone's Theorem 4.13 (`(5) => (1) => (2) => (3)`;
  `D` exact with total projections), `D` has an invariant faithful tracial
  state, and the crossed product has a faithful tracial state and is stably
  finite.

**Case B: `Sigma` has no nontrivial state.**  By the consequences part of
`coinvariant-tarski-lemma-minimal-nowhere-scattered` (Tarski plus the lemma),
`Sigma` is purely infinite.  That is condition (1) of Rainone's Theorem 4.21,
whose hypotheses hold here: unital, separable, exact, total projections,
cancellation, Riesz refinement, minimal and properly outer.  The unconditional
implications `(1) => (2) => (3)` make the crossed product purely infinite.
They go through Proposition 4.17 and Theorem 4.16, which use (SP).

**Exclusivity and the trace criterion.**
* Let `tau` be a `Gamma`-invariant tracial state.  Its null set
  `{a : tau(a^* a) = 0}` is a closed `Gamma`-invariant two-sided ideal, proper
  since `tau(1) = 1`.  So it is `0` by minimality, and `tau` is faithful.
* By Theorem 4.13 (`(1) => (3)`), the crossed product is then stably finite.
  A purely infinite algebra is not stably finite, so Case B is excluded.
* Conversely Case A produces an invariant tracial state.  In Case B the crossed
  product is traceless, so no invariant tracial state exists (`tau o E` would
  be a trace).
