---
rg: 2
id: toms-swap-drop-locus-has-codimension-at-most-2m-plus-1
kind: claim
title: A containment target on a twisted swap family that transports less than double rank must drop rank on a set of real dimension at least 2j - 2m, so deep approximants of a leaf-average realizer in Toms's limit A drop rank on a nearly full-dimensional set
distinct_from:
  toms-constant-rank-twisted-transport-costs-double-rank: that assumes constant rank on the whole family; this allows a drop set D and shows the same Chern count survives whenever dim D <= 2j - 2m - 1, recovering that theorem at D empty. It turns "the rank is not constant" into "the rank drops on a set of codimension at most 2m + 1".
  toms-line-subalgebra-has-no-nonconstant-continuous-rank: that forces a trace-visible rank jump for block-diagonal realizers through Poincare–Miranda; this bounds the geometry of the drop locus for all realizers, without any trace jump.
  toms-chern-swap-count-allows-depth-one-drops: that proves the drop set cannot be forced to be deeper than one, or bigger than a hyperplane per transported coordinate; this is the lower bound on its dimension.
  toms-twisted-swap-pairs-are-totally-degeneracy-forcing: that bounds contractions carrying one twisted half to the other uniformly; this bounds where any Cuntz target must lose rank.
---

**Setting.** Let `j >= 1` and let `L_1, L_2` be line bundles on `CP^j` with
`c_1(L_1) = alpha u`, `c_1(L_2) = beta u`, `beta != 0`, `alpha != beta`. Let `Z` be a
space homeomorphic to `[0,1]`, with endpoints `z_0, z_1`, and `K = Z x CP^j`. Let
`Q in M_k(C(K))_+`, `m = max_K rank Q`, and let

```text
D = { w in K : rank Q(w) < m },
```

a compact set, by lower semicontinuity of rank. `dim` is covering dimension, and
`dim ∅ = -1`. For `i = 0, 1` let `e_i` be a projection with `e_i <~ Q|({z_i} x CP^j)`
whose range is `L_1^(p_i) ⊕ L_2^(q_i) ⊕ θ^(π_i)`, where `θ` is the trivial line.
Put `s_i = m - p_i - q_i - π_i`.

**Theorem (drop-locus transport bound).** If `dim D <= 2j - 2m - 1`, then
`s_0, s_1 >= 0` and

```text
q_0 - q_1  in  [ -s_0, s_1 ].
```

If `alpha != 0`, then also `p_0 - p_1 in [-s_0, s_1]`.

At `D = ∅` this is `toms-constant-rank-twisted-transport-costs-double-rank`.

**Swap corollary.** Suppose
`B_x tensor gamma_1 + B_y tensor gamma_2 + Π <~ Q|({z_0} x CP^j)` and
`B_y tensor gamma_1 + B_x tensor gamma_2 + Π <~ Q|({z_1} x CP^j)`. Here `B_x, B_y, Π` are constant positive
matrices of ranks `R_x, R_y, π`, and the three summands are orthogonal. If
`m < 2 max(R_x, R_y) + π`, then

```text
dim D  >=  2j - 2m.
```

So the drop set has codimension at most `2m + 1` in the `(2j+1)`-dimensional family.

**Consequence in `A`.** Take the notation and hypotheses of the "Consequence for
leaf averages" of `toms-constant-rank-twisted-transport-costs-double-rank`. Let
`h` equal `s` along an embedded arc `c(s)` in `X_1`, `j = j_(M-1) = 2 r_(M-1)^2`, and
`Z = {(x(s), x(1-s))}`. For every stage `M` supplied there, the drop set `D` of the
approximant `a_(n+1)` on `Z x CP^j` satisfies

```text
dim D  >=  2j - 2 r_(M-1)  =  2j (1 - 1/r_(M-1)).
```

Every deep approximant loses rank on a set of real codimension at most
`2 r_(M-1) + 1` in the `(4 r_(M-1)^2 + 1)`-dimensional swap family.

**Model test.**
- *Sharp at m = 1.* `toms-chern-swap-count-allows-depth-one-drops` gives
  `Q >= P` with `R_x = 1`, `R_y = 0`, `m = 1`, whose drop set is one point times a
  hyperplane, of dimension `2j - 2 = 2j - 2m`.
- *Untwisted calibration.* With `alpha = beta = 0` no root is counted, and the
  theorem is empty. This matches the constant-rank realizer of
  `untwisted-doubling-tower-has-a-nonconstant-continuous-rank`.
- *Pushforwards.* `Q = phi(a')` along the swap family has rank
  `rank a'(x(s)) + rank a'(x(1-s))`, which drops on sets `S x CP^j` of dimension
  `>= 2j`, consistent with the bound.

**What it does not do.** A drop of depth one at a point of `X_M` changes a point
trace by `1/r_M`. So a large drop set is not by itself a trace-visible jump, and
the bound does not combine with the Poincare–Miranda firewall into a contradiction.
`toms-chern-swap-count-allows-depth-one-drops` shows that this gap is real.

Proof: `toms-swap-drop-locus-codimension-proof`. Internal derivation, unreviewed.
