---
rg: 2
id: canonical-moments-admit-divergent-edge-leakage
kind: claim
title: Canonical moments allow divergent edge leakage with vanishing covariance defect
distinct_from:
  kt-infinite-index-returns-force-divergent-edge-leakage: That proves divergent aggregate leakage is necessary for a Kun--Thom relative model; this gives an explicit amenable-group matrix sequence realizing exactly that analytic scaling, but does not satisfy the strict-compressor relations.
  kt-kazhdan-edge-grams-are-conditioned-only-at-fixed-radius: That calibrates degeneration of a moving word Gram in exact residually finite representations; this keeps an exactly orthonormal diagonal word basis and makes the number of small principal-angle leaks diverge instead.
  one-compressor-covariance-has-free-hs-telescope: That uses a boundary telescope for a genuine injective endomorphism; this uses small rotations for the identity action solely to test the sharpness of the aggregate principal-angle inequality.
---

There is no purely finite-matrix or canonical-character contradiction in

```text
pointwise covariance defect -> 0,
aggregate edge leakage -> infinity.                         (CEL1)
```

Explicitly, let

```text
A=direct_sum_(j>=1) C_2,             H=A times Z.
```

There are unitary maps

```text
phi_r:H->U(D_r),
```

with pointwise normalized-Hilbert--Schmidt multiplicative defect tending to
zero and canonical limiting character, such that, for

```text
B_r=C*(phi_r(A)),       T_r=phi_r(0,1),
```

one has

```text
max_(a in F)||T_r phi_r(a)T_r^*-phi_r(a)||_2->0          (CEL2)
```

for every fixed finite `F subset A`, while

```text
||(1-E_(B_r))Ad(T_r)E_(B_r)||_HS^2->infinity.            (CEL3)
```

The word basis of `B_r` can be chosen exactly orthonormal, so `(CEL3)` is
not caused by Gram ill-conditioning.  With `d_r=2^r` and
`theta_r=d_r^(-1/4)`, the exact values are

```text
pointwise covariance defect <=2 theta_r,
aggregate leakage=(d_r/2) sin^2(2 theta_r)
                    asymptotic to 2 sqrt(d_r).           (CEL4)
```

Thus the divergent capacity required by
`kt-infinite-index-returns-force-divergent-edge-leakage` is sharp at the
level of matrix geometry and canonical group moments.  What remains special
to Certificate C is **group compatibility**: the Kun--Thom stable letter
implements a strict infinite-index compression and sits inside the full
Kazhdan actor, whereas the calibration uses an approximately central stable
letter in the amenable group `A times Z`.

DERIVATION
small-rotation-canonical-edge-leakage-proof
