---
rg: 2
id: atlas-repeated-collision-fiber-procrustes-proof
kind: route
title: Average diagonal blocks and take two polar factors
target: atlas-repeated-collision-fiber-is-two-block-procrustes
requires:
  - atlas-19243-has-continuous-regular-s3-line-holonomy
  - atlas-mixed-c3-gram-has-local-zero-interval
---

Because `U_0^*rho(b_0)U_0=B_0` and `C` commutes with `B_0`, direct
substitution in `(RCP2)` gives `(RCP4)`.  The established relative `S3`
normal form then proves exact collision for every `C`.

Unitary invariance of normalized Hilbert--Schmidt norm and
`U_0=RA^(-1)q` give

```text
||U_(theta,C)-R||_2
 =||(I tensor C)-q^(-1)T_theta^*||_2.                 (RCP7)
```

For any operator `W` on `directSum_j C^6`, only its diagonal blocks
contribute against a repeated block:

```text
tau((I tensor C)^*W)=(1/6)Tr(C^* [(1/3360)sum_j W_(j,j)]). (RCP8)
```

Apply `(RCP8)` to `W=W_theta`.  Since both terms in `(RCP7)` are unitaries,
the squared distance is two minus twice the real part of `(RCP8)`.

Finally `[C,b]=0` means

```text
C=Q_+ C_+ Q_+^* + Q_- C_- Q_-^*,
C_+,C_- in U(3).
```

The two blocks optimize independently.  The elementary polar-decomposition
identity

```text
max_(V in U(3)) Re Tr(V^*D)=||D||_*
```

gives `(RCP6)` and the asserted minimizers.  No numerical step enters the
reduction; the script merely evaluates its two `3 x 3` matrices and separately
estimates the packet defects of the resulting lift.
