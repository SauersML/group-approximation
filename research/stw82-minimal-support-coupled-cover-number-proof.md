---
rg: 2
id: stw82-minimal-support-coupled-cover-number-proof
kind: route
title: Read a proper colouring from the scalar compression of each minimal support
target: stw82-minimal-support-coupled-cover-number
requires:
  - stw82-spectral-support-hall-capacity
---

Assume (C2)--(C4).  Minimality and (C3) give numbers
`alpha_(v,k) in [0,1]` such that

```text
c_(v,k)p_v=p_v c_(v,k)=alpha_(v,k)p_v.               (R1)
```

Compressing (C2) by `p_v` gives

```text
sum_k alpha_(v,k)=1.                                 (R2)
```

Thus every vertex has at least one label with positive `alpha_(v,k)`.
If `p_v p_w!=0`, then (C4) and (R1) imply

```text
0=p_v c_(v,k)c_(w,k)p_w
  =alpha_(v,k)alpha_(w,k)p_vp_w.                     (R3)
```

No label can therefore occur with positive coefficient at both ends of an
edge.  Choose, for each `v`, any label with `alpha_(v,k)>0`.  Equation (R3)
makes this a proper `d`-colouring of `G_p`, proving `d>=chi(G_p)`.

Conversely, from a proper `d`-colouring `f` set

```text
c_(v,k)=p_v     if k=f(v),
c_(v,k)=0       otherwise.
```

Equations (C2) and (C3) are immediate.  Two vertices of the same colour
are nonadjacent, hence their projections are orthogonal, which proves
(C4).  This establishes (C5).

For fixed `M`, `(p_v)`, and `d`, the space of all tuples of positive
contractions is compact.  If no positive lower bound on the maximum defect
in (C2)--(C4) existed, a convergent sequence with all defects tending to
zero would give an exact cover, contrary to (C5).  This proves robustness.

For the displayed three projections, all pairs have nonzero inner product,
so `G_p=K_3`.  A singleton in (C6) gives `1/2<=1`; any subset of at least
two projections spans `C^2`, so its join is one and its left side is at
most `3/2<=2`.  Thus every inequality (C6) holds although the exact cover
number is three.

