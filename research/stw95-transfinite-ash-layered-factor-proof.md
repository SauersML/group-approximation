---
rg: 2
id: stw95-transfinite-ash-layered-factor-proof
kind: route
title: Discharge every filtration cell by Seth--Vilalta and run the transfinite-filtration theorem
target: stw95-transfinite-ash-layered-factor-preserves-purity
requires:
  - stw95-nuclear-successor-filtrations-need-no-exact-factor
  - stw95-nonunital-ash-factor-preserves-purity
---

Put `L_alpha=J_(alpha+1)/J_alpha` at a successor stage.  The
unitization-and-ideal theorem
`stw95-nonunital-ash-factor-preserves-purity`, based on Seth--Vilalta,
*Continuous functions over a pure C*-algebra*, Theorem B (Theorem 6.7,
together with Remark 6.10 for the residually stably finite alternative),
gives

```text
A tensor_min L_alpha
```

is pure when `A` is pure and is either simple or has every quotient stably
finite, and `L_alpha` is any separable ASH algebra.  No unit is needed:
apply Seth--Vilalta to `A tensor_min (L_alpha)_tilde` and pass purity to its
ideal `A tensor_min L_alpha`.  By symmetry of the minimal tensor product,
`L_alpha tensor_min A` is therefore pure for every successor stage.

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
exactly the asserted Problem XCV positive class.  The word “separable” on
the ASH layers is retained from Seth--Vilalta's theorem; the word “unital”
has been removed by the explicit unitization-and-ideal argument above.
