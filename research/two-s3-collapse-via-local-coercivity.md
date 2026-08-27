---
rg: 2
id: two-s3-collapse-via-local-coercivity
kind: route
title: Localization at the fold plus the dimension-free tangent constant gives the covariance collapse
target: atlas-two-s3-covariance-collapse
requires:
  - atlas-boundary-tangent-covariance-coercivity
  - atlas-fold-localization-with-uniform-remainder
artifacts:
  - research/artifacts/atlas-asc-tangent-exact-2026-08-19.md
---

Assume both prerequisites and let `(U_n, k_n)` satisfy
`max_(s in bar_S) ||pi_(U_n)(s)-1||_2 -> 0`.  Fix `eps_n -> 0` bounding that
maximum over the finite packet `S_0` of
`atlas-fold-localization-with-uniform-remainder` -- legitimate because every
member of `S_0` lies in the normal closure of `bar_S`, so its defect is
bounded by a fixed multiple of the packet maximum
(`atlas-19243-centrality-is-bar-s-consequence` supplies exactly this for the
interior word).

Localization gives gauge elements putting `U_n` at normalized distance
`delta_n = delta(eps_n) -> 0` from the identity, and both `a_n, b_n` and the
boundary defects are gauge invariant, since the gauge lies in the commutant
of the first chart and the two raw letters lie in the first chart's image.
Write `U_n = exp(A_n)` with `||A_n||_2 = O(delta_n)`.

The uniform remainder bound makes the quadratic forms govern:

```text
a_n^2 + b_n^2 = Ncov(A_n) + O(delta_n^3),
sum_(s in boundary) ||pi_(U_n)(s)-1||_2^2 = D(A_n) + O(delta_n^3).
```

`atlas-boundary-tangent-covariance-coercivity` gives `Ncov <= D/14` with a
constant independent of `k_n`, and the left side of the second display is
`O(eps_n^2)`.  Hence `a_n^2 + b_n^2 = O(eps_n^2) + O(delta_n^3) -> 0`, which
is `(ASC)`.

Against `raw-swap-forces-two-s3-covariance-energy` this contradicts
hyperlinearity of `Q` along the route
`nonhyperlinear-from-two-s3-covariance-collapse`.

**Against the other route to the same target.**
`nonhyperlinear-from-linear-energy-domination` reaches the goal from the same
coercivity claim through a single energy inequality rather than a metric
localization.  That one is sharper and is the one to attack; this route is
retained because localization is the geometric reading of the same gap.

**Where the difficulty now sits.**  Entirely in the localization hole.  The
coercivity half is finished and dimension-free; the exact characteristic-two
countermodel of the boundary packet shows the localization cannot be proved
from the boundary relations alone, so any proof of the remaining hole must
consume the interior separator -- which is the discipline item 5 of the
target node already imposes.
