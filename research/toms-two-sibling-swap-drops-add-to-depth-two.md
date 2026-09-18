---
rg: 2
id: toms-two-sibling-swap-drops-add-to-depth-two
kind: claim
title: On the square family of two sibling twisted swap nodes, a Cuntz target that contains a common bundle plus one transported line of each node on the boundary, and has rank at most two above the common part, drops to the common rank at some interior point, so two nodes cannot stagger their depth-one drops
artifacts:
  - experiments/toms-sibling-depth-2026-09-17/square_invariant.py
  - experiments/toms-sibling-depth-2026-09-17/results.json
distinct_from:
  toms-chern-swap-count-allows-depth-one-drops: that builds depth-one drops on one swap family; this shows that two such families over sibling nodes cannot be coordinated so that at most one of them drops at a time.
  toms-swap-drop-locus-has-codimension-at-most-2m-plus-1: that bounds the dimension of the drop set on one family by Chern classes of the support bundle on the constant-rank part; this uses a degree-7 class of the space of matrices with rank in a band of width two, which sees both nodes at once and bounds the depth of the drop.
  toms-constant-rank-twisted-transport-costs-double-rank: that is the constant-rank count on one node; this is a two-node count that allows drops of depth one and forbids depth-one drops only.
  untwisted-doubling-tower-has-a-nonconstant-continuous-rank: that realizes the rotation with trivial twists; there the invariant here vanishes identically.
---

**Setting.** Let `j >= 2` and `Y = CP^j x CP^j`, with hyperplane classes `u_1, u_2`. For
`nu = 1, 2` let `L_1^(nu), L_2^(nu)` be line bundles pulled back from the `nu`-th factor,
with `c_1(L_1^(nu)) = alpha u_nu` and `c_1(L_2^(nu)) = beta u_nu`. Let `S = [0,1]^2`.
Name the sides of `S` bottom, right, top, left, and attach to them the lines

```text
L_b = L_2^(2),   L_r = L_1^(1),   L_t = L_1^(2),   L_l = L_2^(1).
```

Let `G` be a bundle of rank `g` on `Y`. Let `P_G, P_b, P_r, P_t, P_l` be mutually orthogonal
projections in some `M_k(C(Y))` with these ranges. Let
`e in M_k(C(∂S x Y))_+` be of the form `e = P_G + sum_a w_a(s) P_a`, where the weights `w_a >= 0`
are continuous on `∂S`, `w_a = 1` on side `a`, and `w_a` vanishes outside side `a` and small
neighbourhoods of its two endpoints. At a corner the two adjacent lines are both present.

**Theorem (square obstruction).** Let `Q in M_n(C(S x Y))_+` with
- `e <~ Q|(∂S x Y)`, and
- `rank Q <= g + 2` on `S x Y`.

If `alpha != beta` and `alpha + beta != 0`, then `rank Q(w) <= g` for some `w in S x Y`.
Since `rank Q >= g + 1` on the boundary, `w` is interior.

The obstruction is the class `delta(c_1(W) y^2) in H^7` of the space `X_g` of positive
matrices of rank `g + 1` or `g + 2`. Here `W` is the span of the top `g + 1` eigenvectors,
`y = c_1(range/W)`, and `delta` is the Mayer–Vietoris map. On the boundary loop of `Q` it
evaluates to

```text
(alpha - beta)^2 (alpha + beta) (u_1 u_2^2 - u_1^2 u_2)   in  H^1(S^1) ⊗ H^6(Y),
```

which is non-zero, whereas it vanishes for anything defined on the whole square.

**Consequence (the staggered model is dead).** Put the depth-one transport of
`toms-chern-swap-count-allows-depth-one-drops` on two sibling doubling nodes, with
arbitrary coordination. Take windows `W_i` of node 1 and `W_(i')` of node 2, widen each
to `W^+ = [c - 2 eta, c + 2 eta]` (still disjoint from the other windows), and let `S` be
the box `W_i^+ x W_(i')^+` in the cube family `[0,1]^2 x CP^j x CP^j`. In the box every
other pair of both nodes carries one slot with a positive coefficient, and these slots
give `G`, constant on the box. On the side where `s_1` is minimal, pair `i` of node 1
carries its `L_2^(1)` slot, on the side where `s_1` is maximal its `L_1^(1)` slot, and likewise
for node 2. At a corner both lines are present. So `e <= C P` for a suitable `e` and a
constant `C`, and `e <~ P <~ Q` on `∂S x Y`. If `rank Q <= m = g + 2` on the box, as the upper band requires, `Q` drops by
`2` at an interior point. Every box of windows has such a point. No transport of this
form spreads its drops so that the two nodes drop one at a time. Toms's twists
(`alpha = -2`, `beta = -1`, or `O(1), O(2)`) have `alpha + beta != 0`, and `j = 2 d^2 >= 2`.

**Model test.**
- *Untwisted.* `alpha = beta = 0` gives the invariant `0`. This is consistent with the
  constant-rank rotations of `untwisted-doubling-tower-has-a-nonconstant-continuous-rank`.
- *Product model.* The block-diagonal product of two depth-one models drops by `2` at
  `(c_i, c_(i')) x Z_(sigma_1) x Z_(sigma_2)`, as the theorem requires.
- *Sharp band.* With `rank Q <= g + 3` allowed, `Q = e`-type diagonal matrices on the
  square with all four lines have rank `>= g + 1` everywhere. So the band width two is
  load-bearing.
- *Open sign case.* For `alpha = -beta`, for example `O(1), O(-1)`, the invariant
  vanishes, and the theorem says nothing. That case is not Toms's.
- *Script.* The artifact checks the value above symbolically, checks that classes
  pulled back from either open set give `0` (so the value is well defined), and
  evaluates it for five twist pairs and `j = 1, 2, 3`. It vanishes for `j = 1`.

**What it does not do.**
- A depth-two drop is `2 / r_M` on a point trace. The firewall needs about `K/2` blocks
  at once. The `N`-node version is open. It would need a class in the band of width `N`
  that is non-zero on the boundary sphere `S^(N-1)` of the window box.
- The hypothesis is in window form. A general deep approximant need not have windows.
  The single-node drop sets of
  `toms-swap-drop-locus-has-codimension-at-most-2m-plus-1` are not yet shown to organise
  into boxes.

Proof: `toms-two-sibling-depth-two-proof`. Internal derivation, unreviewed.
