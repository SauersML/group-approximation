---
rg: 2
id: quasi-retracts-have-smaller-dehn-functions
kind: claim
title: A finitely presented quasi-retract of a finitely presented group has smaller Dehn function
distinct_from:
  subgroup-dehn-function-is-the-hyperlinearity-modulus: that identifies the Dehn function of a subgroup inside an ambient presentation with a hyperlinearity modulus; this is the coarse monotonicity of intrinsic Dehn functions under quasi-retractions, with no approximation content.
---

**ESTABLISHED (literature import).** Let `G` and `Q` be finitely generated groups
with word metrics from finite generating sets, and let `Q` be a quasi-retract of
`G`: there are coarse Lipschitz maps `r: G -> Q` and `i: Q -> G` with
`d(r(i(y)), y) <= E` for all `y`. Then:

1. if `G` is of type `F_n`, so is `Q`; in particular a quasi-retract of a
   finitely presented group is finitely presented;
2. if `G` and `Q` are finitely presented, `delta_Q ≼ delta_G`, and more generally
   `delta_Q^(k) ≼ delta_G^(k)` for `1 <= k <= n` when both are of type `F_(n+1)`.

Here `f ≼ g` means `f(n) <= K g(Kn) + Kn + K` (LISW) or `f(n) <= K g(Kn) + Kn`
(Zaremsky). For Dehn functions, which vanish at `0`, the two relations agree.

Since quasi-isometries are quasi-retractions in both directions, this contains the
quasi-isometry invariance of Dehn functions.

DERIVATION
quasi-retracts-have-smaller-dehn-functions-citation
