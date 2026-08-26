---
rg: 2
id: atlas-joint-s3-charge-gives-six-relator-floor
kind: route
title: Convert joint nontrivial S3 channel charging into the scalar six-relator floor
target: atlas-six-relator-regular-face-defect-floor
requires:
  - atlas-finite-six-row-charges-nontrivial-s3-mass
  - atlas-19243-centrality-forces-s3-distance
---

Let `E_K` be the diagonal-`K` Reynolds projection.  Orthogonality of the
three central isotypic pieces gives

```text
m_nt(U)=||U-E_K(U)||_2^2.                              (JCF1)
```

Polar rounding inside the finite-dimensional commutant supplies a unitary
`V in rho(K)'` with

```text
dist_2(U,U(rho(K)'))^2<=||U-V||_2^2<=2m_nt(U).        (JCF2)
```

Write `e_c=||pi_U(c_19243)-1||_2`.  The collision-distance theorem is
equivalently

```text
sqrt(2)<=e_c+16 dist_2(U,U(rho(K)')).                 (JCF3)
```

Assuming the joint charge `(JSC3)`, equations `(JCF2)--(JCF3)` and
`e_c<=sqrt(D_6(U))` give

```text
sqrt(2)
 <=sqrt(D_6(U))+16 sqrt(2m_nt(U))
 <=(1+16 sqrt(2C_S3)) sqrt(D_6(U)).                   (JCF4)
```

Squaring proves

```text
D_6(U)>=2/(1+16 sqrt(2C_S3))^2,                       (JCF5)
```

uniformly in the external multiplicity.

For completeness, the reduction loses no qualitative information.  If the
target scalar floor holds with `eta_6`, then `m_nt(U)<=||U||_2^2=1` and
`D_6(U)>=eta_6`, so

```text
m_nt(U)<=eta_6^(-1)D_6(U).
```

Thus the joint charge and the scalar floor are quantitatively equivalent.
