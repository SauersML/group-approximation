---
rg: 2
id: stw74-defect-tower-proper-infiniteness-proof
kind: route
title: Replicate a full defect down an isometry tower
target: stw74-simple-infinite-projections-are-properly-infinite
requires: []
---

Work in the simple unital corner `pAp`.  Since `p` is infinite, choose an
isometry `v` in this corner with

```text
v* v=p,                 vv*<p,
```

and put `r=p-vv*`.  The nonzero projection `r` is full in `pAp`.  Hence for
some `n` one has

```text
p Cuntz-below r directSum ... directSum r       (n copies).
```

For `i=0,...,n-1`, set `r_i=v^i r (v*)^i`.  These projections are pairwise
orthogonal, each is Murray--von Neumann equivalent to `r`, and the telescoping
identity gives

```text
r_0+...+r_(n-1)=p-v^n(v*)^n.
```

Thus `p` is Murray--von Neumann subequivalent to the left-hand projection,
while `v^n(v*)^n` is equivalent to `p`.  The two projections are orthogonal
and lie below `p`.  Hence `p` contains two orthogonal copies of itself and is
properly infinite.
