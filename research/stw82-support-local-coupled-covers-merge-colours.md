---
rg: 2
id: stw82-support-local-coupled-covers-merge-colours
kind: claim
title: Support-local coupled covers merge outgoing order-zero colours
artifacts:
  - research/artifacts/stw82-order-zero-spectral-subdivision-audit-2026-08-30.md
distinct_from:
  stw82-coupled-operator-partitions-merge-colours: that requires every original colour to partition the whole multiplier unit; this only covers the order-zero support and can therefore reduce colours in a tracial target.
  stw82-traces-block-unit-coupled-colour-reduction: that proves full-unit coupled partitions cannot reduce tracial colours; this supplies the support-relative replacement construction.
---

Fix finite-dimensional C*-algebras `F_v` indexed by a finite set `V`, a
positive integer `d`, and `epsilon>0`.  There is `delta>0` with the following
property.

Let `phi_v:F_v->B` be cpc order-zero maps, put
`h_v=phi_v(1_(F_v))`, and let `c_(v,1),...,c_(v,d)` be positive contractions
in `M(B)`.  Write `s_v=sum_k c_(v,k)`.  Suppose

```text
norm((1_(M(B))-s_v)h_v)<delta,                         (L1)
```

and, for every contraction `x in F_v`,

```text
max_k max(
  norm([c_(v,k),phi_v(x)]),
  norm([c_(v,k)^(1/2),phi_v(x)])
)<delta.                                               (L2)
```

Assume pieces with the same new label are coupled by

```text
c_(v,k)c_(w,k)=0                     (v!=w, k<=d).     (L3)
```

Then there are cpc order-zero maps

```text
psi_(v,k):F_v->closure(c_(v,k)^(1/2) B c_(v,k)^(1/2))
```

such that

```text
norm(phi_v-sum_k psi_(v,k))<epsilon                  (v in V),
```

and, for each fixed `k`, the direct-sum map

```text
directSum_(v in V) F_v -> B,
(x_v)_v |-> sum_v psi_(v,k)(x_v),
```

is cpc order zero.

Unlike a partition of the multiplier unit, (L1) allows every colour's
cutters to vanish away from the support of that colour.  It is therefore
the support-sensitive coupled subdivision needed after the tracial
full-unit obstruction.
