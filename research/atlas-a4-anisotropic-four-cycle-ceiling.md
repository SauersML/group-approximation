---
rg: 2
id: atlas-a4-anisotropic-four-cycle-ceiling
kind: claim
title: A weighted four-cycle trace ceiling already beats the raw S3 covariance floor
distinct_from:
  atlas-a4-four-cycle-dirichlet-ceiling: that symmetric target charges the t12 direction by the same worst-case factor as the three generators needed to synthesize t21; this target keeps the exact anisotropy of the raw detector.
  atlas-a4-holonomy-coherence-gap: that target bounds the two raw S3 covariance directions directly; this target remains a four-cycle scalar condition and delegates the exact finite word transfer.
---

Put

```text
D_ij(n)=1-Re tau_n(V_n(tij)).
```

For the normalized exact-regular A4 context-network sequence, prove only

```text
limsup_n
  (24(D_01(n)+D_23(n)+D_30(n)) + D_12(n))
 < 1/256.                                               (A4-ANISO)
```

This is enough because the exact four-cycle-to-raw-S3 transfer uses
`h_b=t12` directly, while only `h_a=t21` needs the eight-letter word containing
`t01,t23,t30`.  Consequently

```text
a_n^2+b_n^2
 <=48(D_01+D_23+D_30)+2D_12
 =2(24(D_01+D_23+D_30)+D_12).
```

Thus `(A4-ANISO)` gives the strict `1/128` holonomy ceiling.

The target is strictly weaker than the symmetric `E_n<1/6144` ceiling in the
`t12` direction: it permits a `t12` trace deficit up to almost `1/256` when the
other three directions are already aligned, instead of forcing every direction
below the worst-case `1/6144` budget.

## Attempts

- **Solve the weighted problem actually used downstream.**  In a finite SOS or
  SDP search, put coefficient `1` on the `t12` trace deficit and coefficient
  `24` only on `t01,t23,t30`.  Do not spend the eight-letter synthesis loss on
  the detector direction that is already a cycle generator.
- **Search better path certificates.**  The coefficient `24` is the squared
  Euclidean norm of the count vector `(2,2,4)` in the exact t21 word.  Multiple
  paths or a finite-group Laplacian comparison can only improve this weighted
  objective and therefore relax the target further.
- **Use collision asymmetrically.**  Collision `19243` repeats `t23`; it may
  control the `t23` contribution more cheaply than the two transverse cycle
  directions.  Keep separate weights during optimization instead of enforcing
  an artificial symmetric four-generator bound.
