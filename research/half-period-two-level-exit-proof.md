---
rg: 2
id: half-period-two-level-exit-proof
kind: route
title: Resolve the top two dyadic conductor layers by Fourier projections
target: half-period-sector-sits-inside-two-level-exit
requires: []
---

On a `d`-th root eigenvalue `zeta^r`,

```text
(zeta^r)^m=(-1)^r.                                     (HCP1)
```

Thus `(I+T^m)/2` selects the even exponents, equivalently the characters
whose order divides `d/2`. Also

```text
(1/4)sum_(j=0)^3 (zeta^r)^(j d/4)
 =1 if r=0 mod 4, and 0 otherwise.                     (HCP2)
```

This is the projection onto characters whose order divides `d/4`. Equations
`(HCE2)--(HCE3)` follow pointwise on the spectrum.

Write

```text
I-F_<=N-2=(I-F_<=N-1)+(F_<=N-1-F_<=N-2).              (HCP3)
```

The two projections on the right are orthogonal. Their left products with
`X` are therefore orthogonal in `L_2(M,tau)`, so Pythagoras proves `(HCE5)`.

For `(HCE6)`, an exact-order-`d/2` scalar belongs to `F_<=N-1` and is
orthogonal to `F_<=N-2`. The tensor calibration is immediate because all
spectral cuts and transitions act on the first tensor factor, whereas the
six coordinate PVMs act on independent tensor factors. Normalized product
trace gives overlap `(1/42)(1/42)=1/42^2` between atoms from distinct
charts.
