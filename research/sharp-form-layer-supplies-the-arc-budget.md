---
rg: 2
id: sharp-form-layer-supplies-the-arc-budget
kind: claim
title: The lambda-parameterized sharp form of Greendlinger's conclusion exists and reduces to two sharp residuals, and the half form provably cannot replace it
distinct_from:
  cascade-landing-from-deep-arc-and-beta: that is the half form of the descent, whose conclusion is the 1/6-pinned arc bound; this is its lambda-parameterized twin, strictly stronger below 1/6, and it is what the torsion descent spends.
  deep-two-factor-regime-is-empty: that emptiness result is shared by both forms; this claim is about the arc BOUND the two forms conclude, not about the regimes they quantify over.
artifacts:
  - GroupApproximation/Sofic/GreendlingerSharpTwins.lean
  - GroupApproximation/Sofic/GreendlingerFreeGate.lean
  - GroupApproximation/Sofic/TorsionDescent.lean
---

The sharp conclusion is the arc bound

```text
(1 - 3*lam) * |r|  <  |u|
```

for a `C'(lam)` family with `lam <= 1/6`, in place of the half form `|r| < 2|u|`
that the `1/6`-pinned lane concludes.  At `lam = 1/6` the two agree; below
`1/6` the sharp form is strictly stronger.

`SharpGreendlingerGate` is the gate `Prop`, and the layer's end state is

```text
DeepArcSourceSharp (at the family's own lam)
  and LandingProductionBetaSharp (likewise)
        ==>  SharpGreendlingerGate alpha,
```

which is `sharpGreendlingerGate_of_deepArcSharp_of_betaSharp` --- **two
hypotheses, no side condition**, because the metric hypothesis is now inside
the quantified families.

## Why the half form is not enough, proved rather than asserted

The router's own relator family is `C'(1/8)`, and there the half form yields
only `n > (3/8)|r|`, which does not empty the torsion residual.  The layer
contains the arithmetic witness for this:

```text
(1 - 3*(1/8)) * 25 < 25 - (25/8 + 25/8)   and   not ((1 - 3*(1/8)) * 25 < 13),
```

`two_pieces_beat_the_half_form_witness`, a closed `norm_num` fact with no
binders at all.  So the sharp form is not a stylistic preference; the half form
is demonstrably too weak at the constant the router actually achieves, and
`TorsionDescent.isPowerTorsionFree_of_sharp` is the consumer that needs the
difference.

The constant `1 - 3*lam` is the three-piece budget, and it is tight:
`three_pieces_budget` and `three_pieces_budget_is_tight`.

## The cost of the layer

Everything structural was re-proved at the `lambda` parameter rather than
transported: `GreendlingerAtSharp`, `LandsInSharp`, `CascadeLandingSharp`,
`DeepArcSourceSharp`, `LandingProductionSharp`, `LandingProductionBetaSharp`,
`DeepOverrunArcSharp`.  The one piece that did **not** need twinning is
`LocatedSplit`, the positional core, which is parameter-free --- that is the
seam along which the duplication was avoided, and it is why the sharp lane
shares `not_deep_confined` with the half lane instead of reproving it.
