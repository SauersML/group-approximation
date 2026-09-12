---
rg: 2
id: titz-witzel-macroscopic-noncommutation-proof
kind: route
title: Telescope the involution sandwich against the eighth power
target: titz-witzel-two-generator-gate-forces-macroscopic-noncommutation
requires:
  - titz-witzel-sofic-gate-two-generators-four-approximate-relators
artifacts:
  - research/artifacts/elementary-group-closures-2026-08-30.md
  - research/artifacts/titz-witzel-involution-sandwich-check.py
---

Use the words from `(TW2G1)` and abbreviate

```text
h=ueu^(-1),       a=ehe,       c=u^2 a u^2,
kappa=d(h,e),     delta=d(c^2,1).
```

Because `e^2=1` and the metric is bi-invariant,

```text
d(a,e)=d(ehe,e)=d(h,e)=kappa.                         (1)
```

Successive conjugates telescope:

```text
d(u^m e u^(-m),e) <= m kappa                         (2)
```

for every positive `m`.  Cancelling the common outer `u^2` factors and
using `(1)--(2)` gives

```text
d(c^2,u^8)
 =d(a u^4 a,u^4)
 <=2d(a,e)+d(eu^4e,u^4)
 <=6 kappa.
```

The triangle inequality therefore proves
`d(u^8,1)<=delta+6kappa`.

There is also a support-sharp estimate.  The word `a=ehe` is a conjugate of
`h`, which is a conjugate of `e`, so `d(a,1)=d(e,1)`.  Hence

```text
d(c,u^4)=d(a,1)=d(e,1),
d(c^2,u^8)<=2d(c,u^4)=2d(e,1).
```

Finally `kappa=d([u,e],1)`.  Applied pointwise to normalized Hamming metrics,
the two inequalities and `delta_n->0` imply, after taking limsups,

```text
limsup d_H([u_n,e_n],1) >= (limsup d_H(u_n^8,1))/6,
limsup d_H(e_n,1)       >= (limsup d_H(u_n^8,1))/2.
```

This is exactly the claimed macroscopic noncommutation and nontriviality
screen for every separated solution of the two-generator gate.
