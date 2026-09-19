---
rg: 2
id: murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness
kind: claim
title: A conditional Murray-von Neumann arrow has an explicit Steinberg conjugacy witness
distinct_from:
  matrix-corona-projection-monoid-is-rank-germs: That lifts an already decoded partial isometry in a matrix corona; this constructs a fixed algebraic conjugator before any matrix representation is chosen.
  hs-finite-adaptive-ring-tree-decoder: That must place all decoded corners on one physical carrier; this proves only that each named source and range have exactly conjugate stabilized root data.
  mixed-steinberg-loops-admit-morita-rectangular-model: That shows typed multiplication triangles tolerate unequal object reservoirs; this is the exact same-object conjugacy supplied by one genuine partial-isometry arrow.
---

**ESTABLISHED.**  Let `R` be a unital ring with idempotents `a,d` and
elements `s,sbar` satisfying

```text
sbar s=a,       s sbar=d,
s a=s=d s,      a sbar=sbar=sbar d.                    (MSC1)
```

Then

```text
W=[[1-a, sbar],
   [s,   1-d]] in M_2(R)                               (MSC2)
```

is an involution and

```text
W diag(a,0) W=diag(0,d).                               (MSC3)
```

After one harmless stabilization, `diag(W,W^(-1))` lies in the elementary
group and is a fixed word in elementary generators with coefficients
`a,d,s,sbar`.  Consequently it conjugates every root word attached to the
stabilized source corner to the corresponding range-corner root word.

In particular, in every unitary representation of the rank-five Steinberg
wordization, source and range root words have unitarily conjugate spectral
measures, fixed-space projections, and normalized-HS displacement.  No
coefficient-module decoder or rank cut is needed for this equality.

This does not prove additivity for `q+d`.  A Morita-rectangular
representation may realize each conjugacy while placing different object
identities on different reservoirs.  The still-missing assertion is that
the decoded `q`, `d`, and their sum refer to one physical matrix corner.
