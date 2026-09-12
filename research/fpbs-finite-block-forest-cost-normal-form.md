---
rg: 2
id: fpbs-finite-block-forest-cost-normal-form
kind: claim
title: Prescribed finite block trees can be included at the cost infimum on both sides of a free factor
distinct_from:
  fpbs-small-marker-induction-input: that imports the complete-section induction formula; this applies it to prescribed finite block forests simultaneously across a free factor and records the exact scaling of a possible cost gap
  fpbs-relative-traffic-descent-over-hyperfinite-spine: that uses an aperiodic hyperfinite spine and conditional traffic budgets; this uses finite blocks, their transversal, and countable connector graphings on the restricted relations
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

Let R be an aperiodic countable p.m.p. relation of finite cost, E a
finite-class subrelation, F a prescribed measurable tree on every
E-class, and A an E-transversal of measure q. Then

    C(R)=inf_{J generates R|A} c(F union J)=1-q+q C(R|A),

where the restriction cost uses the normalized measure on A. Thus
graphings containing F approximate C(R) arbitrarily well.

For a free factor pi:Y->X with both action costs finite, impose F
and its orbitwise lift simultaneously. With B=pi^{-1}(A), the cost
gap D of the two full actions satisfies D=q D_A, where D_A is the
gap of the two normalized restricted relations. Small q alone does
not bound D. No finite-generation, ergodicity, bounded-degree, or
finite group-label assertion is included.

Section 5 supplies a deduction from the classical induction formula,
not a novel cost theorem or a proof of the universal comparison.
