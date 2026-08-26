---
rg: 2
id: unnamed-fixed-space-promotion-is-goal-equivalent
kind: claim
title: Bare unnamed fixed-space promotion is exactly finitely presented nonhyperlinearity
distinct_from:
  unnamed-fixed-space-wandering-promotion: that asks for one concrete positive-density moving carrier; this audits its unrestricted existential content and shows that, without a nonvacuity condition on finite models, it is exactly the root goal.
  localized-square-return-promotion-is-goal-equivalent: that keeps a named finite-support group-algebra carrier; this is the still weaker model-dependent projection formulation.
---

**ESTABLISHED.**  The following existence statements are equivalent.

1. There is a nonhyperlinear group.
2. There are a finitely presented group `Gamma`, an infinite-order word `w`,
   and `alpha>0` such that every full canonical-trace matrix microstate
   sequence admits projections `P_U` with

   ```text
   tr(P_U)>=alpha-o(1),
   ||(w(U)^2-1)P_U||_2=o(1).                           (UGE1)
   ```

The implication `2 => 1` is
`unnamed-positive-density-fixed-space-is-terminal`, applied to `u=w^2` and a
fixed Fejer order larger than `1/alpha`.

For `1 => 2`, use
`nonhyperlinearity-has-a-finite-presentation-witness` to choose a finitely
presented nonhyperlinear group `K`, and let

```text
Gamma=K times Z,              w=z,              alpha=1/2.
```

The subgroup `K<=Gamma` prevents `Gamma` from being hyperlinear.  By
`nonhyperlinear-group-has-finite-canonical-microstate-witness`, one finite
canonical window already has a positive all-dimensions defect.  Hence
`Gamma` has no full canonical-trace matrix microstate sequence, so `(UGE1)`
holds over the empty collection of sequences.  The word `z` has infinite
order.

Again, this reverse implication is intentionally vacuous.  It does not
produce a geometric carrier, an extensive rank defect, or a heterogeneous
row.  Thus the bare existential target does not reduce the root problem.  A
productive promotion theorem must exhibit the presentation without assuming
a nonhyperlinear seed or impose nonvacuity of the finite model family on
which the positive-density fixed space is forced.
