---
rg: 2
id: stw95-transfinite-ash-layered-factor-proof
kind: route
title: Discharge every filtration cell by Seth--Vilalta and run the transfinite-filtration theorem
target: stw95-transfinite-ash-layered-factor-preserves-purity
requires:
  - stw95-nuclear-successor-filtrations-need-no-exact-factor
---

Put `L_alpha=J_(alpha+1)/J_alpha` at a successor stage.  Seth--Vilalta,
*Continuous functions over a pure C*-algebra*, Theorem B (Theorem 6.7,
together with Remark 6.10 for the residually stably finite alternative),
states that

```text
A tensor_min L_alpha
```

is pure when `A` is pure and is either simple or has every quotient stably
finite, and `L_alpha` is a unital separable ASH algebra.  By symmetry of the
minimal tensor product, `L_alpha tensor_min A` is therefore pure for every
successor stage.

Every `L_alpha` is nuclear because it is ASH.  Now apply
`stw95-nuclear-successor-filtrations-need-no-exact-factor` with filtered
algebra `B` and tensor factor `A`.  Nuclearity gives a Choi--Effros cpc split
at each successor stage, so the successor extension remains exact after
tensoring by the arbitrary algebra `A`; the local purity hypothesis was just
verified by Seth--Vilalta.  That theorem's transfinite induction uses
extension permanence at successors, Cu continuity at countable-cofinality
limits, and separable stabilization at uncountable-cofinality limits.  It
gives purity of `A tensor_min B`.

If `B` is pure, both tensor factors are pure, so the same conclusion is
exactly the asserted Problem XCV positive class.  We do not suppress the
words “unital separable” from the ASH-layer hypothesis: those are the
hypotheses in Seth--Vilalta's stated tensor theorem, and no nonunital
unitization argument is needed or claimed here.
