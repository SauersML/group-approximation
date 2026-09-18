---
rg: 2
id: toms-overlap-window-cubes-force-linear-depth
kind: claim
title: A box of N ancestor-twisted swap nodes whose windows have overlapping leaf maxima forces every target of the upper band to drop by a fixed fraction of N at one point
distinct_from:
  toms-ancestor-twisted-cubes-force-depth-k-over-2: that forces depth N from cube data with one line per facet and room one per node; this asks for depth cN from the data a pushforward actually offers, namely overlap windows with two lines per facet and room three per node, which by toms-transit-windows-fill-unless-their-ranks-overlap is the smallest forcing pattern.
  toms-transit-windows-fill-unless-their-ranks-overlap: that proves the one-node case and shows windows without overlap fill; this is the many-node statement, where the drops must coincide.
  toms-sibling-cube-swap-drops-add-to-depth-n: that is the untwisted-ancestor cube theorem with room one; the room-three facets here are not in its band space.
---

**OPEN.** Work in the setting of `toms-transit-windows-fill-unless-their-ranks-overlap`,
with `D = d_n c` an integer. Take all `N = K/2` bottom sibling nodes `nu` of `X_M` over one
stage-`n` swap path, with windows `I_nu` of overlap excess `kappa(I_nu) >= 1`. Let
`S = prod_nu I_nu`, let `Y = prod_v CP^(j_v)` be the vertex slices, and let `Z` be the
product of the ancestors' projective factors. The lines are
`L_(nu,±) = gamma_(v,1/2) ⊗ Gamma_nu`, as in `toms-ancestor-twisted-cubes-force-depth-k-over-2`.
Let `U = N D`, the integer upper band on the box. Let
`Q in M_infinity(C(S x Y x Z))_+` satisfy

```text
psi_(n,M)(a_n)|_(S x Y x Z)  <~  Q,        rank Q <= U everywhere.
```

Then there is an absolute constant `c > 0` such that `rank Q <= U - c N` at some point.
For non-integer `D`, the same statement with `U = floor(N D)` is part of the conjecture.

**Why it is the right statement.**
- `Q = a_M` restricted to the box satisfies the hypotheses: `psi(a_n) <~ a_M`, and the
  upper band gives `rank a_M <= U`. The conclusion then gives
  `d_M eps_M >= c N`, that is `eps_M >= c / (2 d_n)`, for every `M > n`. This is the reduction
  `toms-leaf-average-rank-via-overlap-window-cubes`.
- Here `rank P - U = sum_nu kappa_nu >= N`, where `P` is the projection of all leaf maxima.
  So the conjecture says that a positive fraction of the total overlap is lost at a single
  point.
- The hypothesis `kappa >= 1` cannot be dropped: if `kappa <= 0` at every node, the constant
  filling of Part 2 of `toms-transit-windows-fill-unless-their-ranks-overlap` has no drop.
- Room-one data cannot replace it: by Part 1 of the same claim, that premise is equivalent to the
  conclusion.

**Model test.**
- *`N = 1`.* This is Part 3 of `toms-transit-windows-fill-unless-their-ranks-overlap`:
  coprime Chern divisibility on the vertex slice `CP^(j_v)` forces a drop, with `c = 1`.
- *Product model.* The block product of depth-one transports over forcing windows
  (`toms-chern-swap-count-allows-depth-one-drops`) drops by one at some point `s_nu` of each
  window. The box is a product, so the product drops by `N` at the point `(s_nu)`. This is
  consistent with `c = 1`.
- *Untwisted ancestors.* Without the ancestor factors, room-one cubes fill without a common
  drop once `N >= 2j - 1` (`toms-wide-sibling-cubes-fill-without-common-drop`). So the
  conjecture must use the classes `A_nu`, exactly as the room-one theorem does.

**The gap.** The known cube theorem needs the target to lie in the band
`[g + 1, g + N]`, with one line entering per facet. An overlap window has room three. Its
facets carry `2 L_-` and `2 L_+`, and its middle chamber carries `L_+ ⊕ L_-`. The boundary
data of `Q` therefore do not lie in the band space of `toms-sibling-cube-depth-n-proof`.

The natural reduction restricts to the middle chambers `C_nu` between the two walls. There
the pushforward is the constant `P_mid`, of rank `U - N`. Theorem 1 over `C = prod C_nu` would
need `Q` to carry an extra `L_-`-type line near wall 1 and an extra `L_+`-type line near
wall 2. Only the pushforward is known to lie below `Q`, and it supplies these lines on the
outer chambers, not on `C`. So `e <~ Q` on `∂C` is not available.

The `N = 1` obstruction is a non-linear divisibility statement (two coprime factors of
total degree `> r`). It is not the non-vanishing of a single top-column class, so the
Mayer-Vietoris summation of the cube proof does not apply to it directly.

**First step.** Prove the case `N = 2` with ideal two-wall windows. There, a Chern
computation on `C_1 x C_2`, with the four slices and one ancestor factor, decides whether the
two drops must share a point.
