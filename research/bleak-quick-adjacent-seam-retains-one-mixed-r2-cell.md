---
rg: 2
id: bleak-quick-adjacent-seam-retains-one-mixed-r2-cell
kind: claim
title: An adjacent Bleak--Quick seam retains one cross-chart R2 triangle
distinct_from:
  bleak-quick-adjacent-seam-retains-finite-selector-packet: that asks directly for one joint S6 map and three common selector commutators; this permits two private fixed S6 charts and asks only that one R2 triangle use an arm from each chart.
  depth-three-bq-arm-expansion-is-equivariant-under-label-flip: that proves the two canonical within-chart R2 triangles move equivariantly under the label flip; this requires a genuinely mixed triangle, not either of those private triangles.
  shared-s5-selector-face-has-multiplicity-rotation-gauge: that preserves every chart-separable relation over the common S5 face; the mixed triangle here contains one private generator from each S6 extension and is exactly the relation which that gauge violates.
---

Fix an adjacent pair of contextual Carmichael charts and one shared label in
a `delta`-model of the Bleak--Quick R1--R5 presentation.  In the original
matrix dimension, construct two fixed-six-letter maps

```text
Phi_a:S_6->U(d),             a=0,1,
```

with all-pairs multiplicative defect at most `C delta`, together with
contextual Carmichael matrices `C_a`, arms `X_a`, transported arms `Y_a`,
and one common pivot `R`, such that

```text
||X_a-Phi_a((i p))||_2+||Y_a-Phi_a((i q))||_2 <= C delta,
||Phi_0(h)-Phi_1(h)||_2 <= C delta             (h in S_5),       (BMR1)
||C_a-X_a R^* X_a R||_2 <= C delta,
```

and the **mixed** R2 triangle obeys

```text
||Y_1^* X_0 Y_1-R||_2 <= C delta.                              (BMR2)
```

Every comparison in `(BMR1)--(BMR2)` must use a bounded number of literal
conjugates of R1--R5, independent of addresses and matrix dimension.

The point of `(BMR2)` is that the ordinary private chart-one triangle gives
`Y_1^* X_1 Y_1=R+O(delta)`.  Hence
`mixed-r2-cell-couples-shared-s5-extension-multiplicities` yields

```text
||X_0-X_1||_2 <= C' delta.                                     (BMR3)
```

This is strictly less data than a jointly named selector packet.  The
literal depth-three relation is already known: with
`s=(010 000)`, `t=(010 001)`, `r=(000 001)`, the word `t s t r` is one
conjugate of R2.  The open occurrence question is whether `s` can be retained
from the first contextual name and `t` from the second contextual name in a
bounded R1--R5 diagram.  Taking both from either private chart merely
reproduces the equivariant construction already refuted by
`depth-three-bq-arm-expansion-is-equivariant-under-label-flip`.

## Attempts

The first attempt substitutes the canonical depth-three R2 triangles
`t_0s_0t_0=r` and `t_1s_1t_1=r`.  It fails because each triangle is internal
to one chart: the S5 multiplicity rotation conjugates `s_1,t_1` together and
preserves it exactly.  The useful word is instead `t_1s_0t_1r`, containing
one private occurrence from each chart.  Although its exact Thompson value
is trivial when the occurrences are coherent, it is not literally a single
conjugate of the displayed R2 relator when their private conjugator words
differ.  The next attack must cancel those two conjugator boundaries inside
one bounded diagram; separately transporting either endpoint pays the known
unbounded centralizer-area cost.

The boundary calculation is now exact.  If `t_0,t_1` are the two transported
arms and `d=t_1t_0^(-1)`, then
`mixed-r2-boundary-is-one-finite-mark-centralizer-commutator` rewrites the
mixed triangle, modulo one private R2 cell, as the commutator of `d` with the
first input arm.  After conjugating that arm to a fixed prefix
transposition, finite-mark Schreier properness rules out every construction
whose relative corrections escape.  This invalidates
`escaping-separate-endpoint-transport-closes-mixed-r2`.

The same calculation leaves the genuinely interacting local route alive.
When the entire adjacent seam is one conjugate of a fixed depth-three
diagram, the normalized correction is fixed rather than escaping, so the
properness lower bound is only a constant.  The remaining task is therefore
exactly a fixed local word audit: find the null mixed boundary before the
private gauges are separated, or prove that the normalized finite correction
itself is nontrivial.

For the obvious normalized splice, it is nontrivial.
`mixed-r2-boundary-is-one-finite-mark-centralizer-commutator` computes

```text
(011 001)(010 000)(011 001)(000 001)
 =(010 000)(000 001),
```

a three-cycle.  This invalidates
`canonical-depth-three-private-triangles-close-mixed-r2`.  The still-live
fixed local audit must therefore retain a different second-chart endpoint;
the canonical label-flipped `t_j` cannot be the transported arm in `(BMR2)`.
