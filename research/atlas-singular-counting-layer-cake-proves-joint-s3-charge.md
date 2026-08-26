---
rg: 2
id: atlas-singular-counting-layer-cake-proves-joint-s3-charge
kind: route
title: Integrate the six-row singular-rank incidence to charge the nontrivial collision channel
target: atlas-finite-six-row-charges-nontrivial-s3-mass
requires:
  - atlas-six-row-singular-counting-dominates-nontrivial-s3
---

The singular-counting claim implies `(JSC3)` with no dimension loss.  Indeed,
normalized layer cake gives, for every matrix `T` with `||T||<=2`,

```text
||T||_2^2 = integral_0^2 2t N_T(t) dt.                (SCL1)
```

Both `A=U-E_K(U)` and every word residual in `(SCI1)` have operator norm at
most `2`.  Integrating `(SCI3)` and changing variables `s=kappa t` yields

```text
m_nt(U)
 = integral_0^2 2t N_A(t) dt
 <= C_rank sum_r integral_0^2 2t N_(R_r)(kappa t) dt
 = C_rank kappa^(-2)
       sum_r integral_0^(2kappa) 2s N_(R_r)(s) ds
 <= C_rank kappa^(-2) D_6(U).                         (SCL2)
```

Thus

```text
C_S3=C_rank kappa^(-2)                               (SCL3)
```

is valid in `(JSC3)`.  This reduction is deliberately one-way: a quadratic
Hilbert--Schmidt charge need not control the singular counting function at
each scale.  The new claim is a strictly stronger but finite and directly
checkable rank-incidence gate, not a reformulation of the original scalar
floor.


