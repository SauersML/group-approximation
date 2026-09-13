---
rg: 2
id: o6-plus-forces-tracial-equivalence-of-equal-trace-projections
kind: claim
title: If the Cuntz semigroup satisfies Thiel's (O6+), equal-trace projections are equivalent in the uniform tracial ultrapower, with no comparison hypothesis
distinct_from:
  strict-comparison-compares-ultrapower-projections: that derives ultrapower comparison of projections from strict comparison; this derives equivalence of equal-trace projections of the algebra from (O6+), with no comparison hypothesis.
  toms-schubert-algebra-fails-o6-plus: that is the instance in Toms's no-Gamma algebra, with a quantitative support gap; this is the general implication whose contrapositive the instance realizes.
  trivial-r-fibre-bundles-compare-equal-trace-projections: that compares equal-trace projections inside a trivial W*-bundle; this compares projections of a C*-algebra whose Cuntz semigroup has (O6+).
artifacts:
  - research/artifacts/toms-schubert-o6-plus-failure-2026-09-12.md
---

Let `A` be a unital, simple, separable, exact, stably finite C*-algebra whose
Cuntz semigroup satisfies Thiel's axiom (O6+) (arXiv:1711.04721, Definition 6.1).
By Thiel's Theorem 6.4 and Remark 6.5, this holds whenever `A tensor K` has almost
stable rank one, in particular when `A` has stable rank one.

**Theorem.** Let `p, q in M_k(A)` be projections with `tau(p) = tau(q)` for every
`tau in T(A)`. For every `eps > 0` there is a contraction `b in q M_k(A) p` with

```text
||p - b*b||_(2,u) < eps,        ||q - bb*||_(2,u) < eps.
```

Hence `p` and `q` are Murray–von Neumann equivalent in `M_k(A^omega)`, the uniform
tracial ultrapower.

**Contrapositive.** Two equal-trace projections of `A` that are not approximately
equivalent in uniform 2-norm certify that (O6+) fails and that `A tensor K` is not
of almost stable rank one. Toms's twisted pair `(p_m, q̂_m)` is such a certificate.

**Model tests.**
- *Hypothesis model.* Simple stable-rank-one algebras satisfy the hypothesis. For
  first-type Villadsen algebras the conclusion is consistent with Vaccaro's uniform
  property Gamma.
- *Nontriviality.* In `C(S^2)` the trivial line and the Hopf line have equal traces
  at every point. Point traces would force a pointwise near-isometry between them,
  which the Chern class forbids. So the conclusion fails there, and indeed Thiel's
  Example 6.7 shows (O6+) fails for `C(S^2)`. That algebra is not simple, so it only
  illustrates what the conclusion demands.
- *A real simple object where the conclusion fails.* Toms's algebra `B`.

The Theorem does not compare projections of unequal trace, and it says nothing
about uniform property Gamma beyond this consequence.
