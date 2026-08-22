---
rg: 2
id: sparse-face-row-square-survives-intrinsic-green-step
kind: claim
title: Sparse face and equality layers remain in the row-square basin under the intrinsic Green step
distinct_from:
  dense-complete-pair-remainders-are-cb-quadratic: that controls the normalized all-pairs remainder; this must control bounded local templates hit by unequal coordinate conjugators.
  one-anchor-grading-makes-parity-damage-quadratic: that gives a quadratic formula for one common anchor grading; this concerns coordinate-dependent finite-Green gauges.
  averaged-pinching-channels-are-row-square-lipschitz: that transfers one averaged CP channel; this preserves sparse group-word residuals during iteration.
---

OPEN.  For the intrinsic finite-Green conjugators `(k_i)` on the retained
low-square block, prove that every bounded parity face and equality edge has
first-order damage controlled by the existing balanced residual row square,
and that after local correction

```text
 b_new<=rho b_old+O(b_old^(3/2))+O(epsilon_inv),         (SFR1)
```

with `rho<1` independent of code length and dimension.

## Attempts

Telescoping a face word gives terms `k_i-k_j` with only boundedly many
indices, but a coordinatewise operator-norm bound loses sparse outliers.
The estimate must average these differences through the bounded occurrence
and equality expanders before taking operator norm, as in the averaged
pinching theorem.  The unresolved input is an operator Jensen/SOS
factorization for this bounded-template incidence map, or a local
exactification whose correction row square is Loewner-dominated by the raw
face residual square.

