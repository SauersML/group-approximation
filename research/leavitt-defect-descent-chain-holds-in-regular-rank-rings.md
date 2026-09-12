---
rg: 2
id: leavitt-defect-descent-chain-holds-in-regular-rank-rings
kind: claim
title: The defect piece, defect gap, two-sided descent and near-minimal multiplicativity hold in every faithful regular rank ring
distinct_from:
  leavitt-rank-model-defect-gap-on-fixed-point-free-quotients: that is the gap for homomorphisms into rank ultraproducts, with compactness through finite matrix stages; this is the gap, the defect piece, the descent and near-minimal multiplicativity for homomorphisms into any faithful von Neumann regular rank ring of characteristic two, with compactness through ultraproducts of such rings.
  nested-two-root-defect-pieces-decay-geometrically-both-ways: that is the descent for rank-ultraproduct models; this transfers it, with the whole chain it rests on, to abstract regular rank rings.
artifacts:
  - research/artifacts/rank-gate-axiom-audit-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-upg-audit`; verification requested from `w4-vf-gate`) by
`leavitt-defect-descent-regular-rank-ring-proof`.

Let `R = L_(F_2)(1,2)`, let `U` be a unital von Neumann regular ring of characteristic two with a
faithful Sylvester matrix rank function, and let `sigma : R^x -> U^x` be a homomorphism. With the notation
of `research/artifacts/two-root-defect-descent-gap-2026-09-12.md` (`M` replaced by `U`), the following
hold verbatim, with constants over the class of such rings:
1. the defect piece carries a nontrivial injective model (Theorem 1.2 and Corollary 1.3 of the
   defect-piece artifact);
2. the defect gap `c_0' rk(1-f) <= rk((1-f) D_A) <= rk(1-f)/2`, with `c_0' > 0` universal;
3. the two-sided descent `c_*' f(k) <= f(k+1) <= f(k)/2` on fixed-point-free models;
4. near-minimal models have multiplicative disjoint-cylinder defects.

**Consequence.** A proof of `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` valid in
faithful regular rank rings excludes every nontrivial homomorphism of `R^x` into such a ring (artifact
Consequence 3.2). With `sylvester-rank-functions-on-leavitt-units-are-regular`, that decides
`binary-leavitt-units-carry-nonaugmentation-rank-function` negatively.

## Attempts

Established, not open. Proof in artifact Section 3.
