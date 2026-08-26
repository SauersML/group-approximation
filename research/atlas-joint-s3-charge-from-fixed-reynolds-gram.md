---
rg: 2
id: atlas-joint-s3-charge-from-fixed-reynolds-gram
kind: route
title: Charge the nontrivial S3 channels by a fixed Reynolds-Gram certificate
target: atlas-finite-six-row-charges-nontrivial-s3-mass
requires:
  - atlas-radius-nine-packet-gram-sos-is-tracial
  - atlas-six-relator-factor-retains-half-nontrivial-s3-mass
---

**INVALIDATED.**  The tempting proof is to use the fixed diagonal collision
Reynolds operator

```text
E_K(T)=|K|^(-1) sum_(k in K) rho(k)T rho(k)^*,
```

write

```text
m_nt(U)=||U-E_K(U)||_2^2,
```

and seek a fixed positive operator-valued Gram or Schur-complement estimate

```text
||U-E_K(U)||_2^2
 <=C [sum_j ||pi_U(s_j)-1||_2^2
              +||pi_U(c_19243)-1||_2^2].             (FRG1)
```

Allowing a fixed finite matrix amplification, central sign/standard
idempotents, positive combinations, regularized Schur complements, and sums
of Hermitian squares does not help.  These are exactly the operations of
`atlas-radius-nine-packet-gram-sos-is-tracial`, and they remain valid in every
finite tracial von Neumann algebra carrying the same exact finite packet
representations.

Substitute the internal relative chart unitary in the exact Leavitt group
factor.  All six residuals on the right of `(FRG1)` vanish, while
`atlas-six-relator-factor-retains-half-nontrivial-s3-mass` gives

```text
||U-E_K(U)||_2^2=m_nt(U)>=1/2.
```

Thus no certificate in the fixed Reynolds--Gram calculus can prove the joint
charge.  In particular splitting the central idempotent into sign and
standard blocks, then applying fixed blockwise Gram positivity, is still
inside the refuted calculus.  A viable proof must make a finite-coordinate
selection whose definition or rank complexity depends on the ambient matrix
dimension; fixed channel diagonalization is only an upstream localization.
