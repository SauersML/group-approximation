---
rg: 2
id: rr0-sr1-coefficient-crossed-products-dichotomy-proof
kind: route
title: Real rank zero and stable rank one put K_0 in Rainone's framework, unperforation makes it a dimension group, and the integer-layer-free condition supplies the divisibility axiom
target: rr0-sr1-coefficient-crossed-products-dichotomy
requires: [rainone-type-semigroup-crossed-product-dichotomy, coinvariant-tarski-lemma-minimal-nowhere-scattered, dimension-group-divisible-iff-no-integer-subquotient]
---

**Hypotheses.**
* Real rank zero and stable rank one give (SP), total projections,
  cancellation of projections, and Riesz refinement of `K_0(A)^+` (Zhang).
* Stable rank one makes `A` stably finite, so `K_0(A)^+` is conical.
* `A` is separable, so `K_0(A)` is countable.  It is directed, has Riesz
  interpolation, and is unperforated by assumption.  So it is a countable
  dimension group.
* By `dimension-group-divisible-iff-no-integer-subquotient`, it satisfies (ND).
* Every closed ideal of a real-rank-zero algebra contains a nonzero
  projection.  So by Rainone, Theorem 3.7, minimality of `alpha` is equivalent
  to the absence of nontrivial `Gamma`-invariant order ideals in `K_0(A)`.

So `coinvariant-tarski-lemma-minimal-nowhere-scattered` applies to
`Sigma = S(A, Gamma, alpha)`.  The crossed product is simple (Olesen--Pedersen,
Theorem 7.2, as invoked in Rainone's proof of Theorem 4.16).

The rest follows `nowhere-scattered-af-crossed-products-dichotomy-proof`
word for word, since that argument used only these hypotheses of Rainone's
Theorems 4.13 and 4.21: unital, separable, exact, total projections,
cancellation, Riesz refinement, minimal and properly outer.

* **Case A** (a nontrivial state on `Sigma`).  Minimality gives a faithful
  invariant state on `(K_0(A), [1])`.  Theorem 4.13 (`(5) => (1) => (3)`),
  using exactness and total projections, gives an invariant faithful tracial
  state and stable finiteness.
* **Case B** (no nontrivial state).  Tarski and the lemma make `Sigma` purely
  infinite, and Theorem 4.21 (`(1) => (3)`, through Theorem 4.16 and (SP))
  makes the crossed product purely infinite.
* **Exclusivity.**  An invariant tracial state is faithful by minimality, since
  its null set is a proper invariant ideal, and it forces stable finiteness.

**Examples.**  For `C(X) tensor A_theta`:
* it has real rank zero and stable rank one, being an inductive limit of
  finite direct sums of copies of `A_theta`, which has both (Elliott--Evans;
  Putnam);
* `K_0` is `C(X, Z + theta Z)` with pointwise positivity, which is unperforated;
* its order-subquotients are `C(V, Z + theta Z)` for locally closed `V`, never
  `(Z, N)`.
