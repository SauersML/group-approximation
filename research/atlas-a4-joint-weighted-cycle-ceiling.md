---
rg: 2
id: atlas-a4-joint-weighted-cycle-ceiling
kind: claim
title: Jointly weighting the S3 detector and t21 synthesis beats the collision floor
distinct_from:
  atlas-a4-optimized-weighted-four-cycle-ceiling: that fixes equal weight on the two raw S3 covariance defects before optimizing the t21 word; this target also optimizes the relative price of the synthesized t21 detector against the direct t12 detector.
---

For the normalized exact-regular A4 context-network sequence put

```text
D_ij(n)=1-Re tau_n(V_n(tij)).
```

Prove that there exist `p,q>0` and positive `c_01,c_23,c_30` such that

```text
4/c_01+4/c_23+16/c_30 <= 1,                            (W1)

lambda=p+q-sqrt(p^2-pq+q^2),                           (W2)
```

and

```text
limsup_n [
  p(c_01 D_01(n)+c_23 D_23(n)+c_30 D_30(n))
  + q D_12(n)
] < lambda/256.                                        (A4-JOINT-W)
```

This is the exact scalar budget obtained by optimizing both independent finite
spectral comparisons available downstream: the sharp diagonal envelope for the
`t21` word and the sharp weighted Cayley gap of the two-generator `S3`
detector.  The target is homogeneous in `(p,q)`.

The previous optimized-weight target is the specialization `p=q=1`, for which
`lambda=1`.  Allowing `p/q` to vary is useful when the packet/collision system
controls the directly observed `t12` direction at a very different cost from
the three directions used only to synthesize `t21`.

## Attempts

- **Normalize q=1 and search one scalar r=p/q.** Then
  `lambda(r,1)=r+1-sqrt(r^2-r+1)`.  The outer optimization is one-dimensional;
  the t21 reciprocal weights can be parameterized independently by a simplex.
- **Spend cheap t12 control aggressively.** As `r->0`, the effective price of
  the three synthesized directions decreases while the normalized price of
  `D_12` increases.  This is favorable if collision 19243 already pins the
  direct detector direction much more tightly than the transverse cycle.
- **Spend cheap transverse control in the opposite regime.** Large `r` lowers
  the normalized price of `D_12` but raises the synthesized-direction price.
  The optimum should therefore be chosen by the actual finite SOS/dual escape
  mode rather than fixed in advance.
- **Return a dual obstruction.** If the finite scalar optimization cannot cross
  the threshold, retain the maximizing multiplicity/holonomy state and use it
  to identify which packet relation must be added or reweighted.