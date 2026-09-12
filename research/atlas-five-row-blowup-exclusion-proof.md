---
rg: 2
id: atlas-five-row-blowup-exclusion-proof
kind: route
title: Polar-round five-row small vectors into the collision commutant
target: atlas-five-row-blowup-branch-is-impossible
requires:
  - atlas-five-row-lift-failure-dichotomy
  - regular-atlas-linearized-h-coercivity
  - atlas-19243-centrality-forces-s3-distance
---

Let `H=diag(GL_3(2),1)` and let `E_H` be Hilbert--Schmidt conditional
expectation onto `N=rho(H)'`.  The four fixed transvections generate the
finite group `H`, so their Cayley Laplacian has a positive gap `kappa_H` on
`N^perp`, independent of external multiplicity.  Combining that Poincare
inequality with the cited five-row coercivity gives

```text
||U-E_H(U)||_2^2 <= (C_lin/kappa_H) A(U).              (ABE1)
```

Put `X=E_H(U)`.  It is a contraction in `N`.  Extend the polar partial
isometry of `X` to a unitary `V in N`.  Orthogonality of the expectation and
`(1-s)^2<=1-s^2` for `0<=s<=1` imply

```text
||U-V||_2^2
 = ||U-X||_2^2 + ||X-V||_2^2
 <= 2 ||U-X||_2^2
 <= (2C_lin/kappa_H) A(U).                             (ABE2)
```

The collision subgroup `K_19243~=S3` lies in `H`, hence `V` commutes with
it.  The cited exact collision calculation gives
`||pi_V(c_19243)-1||_2=sqrt(2)` on this commutant, and the collision word is
`16`-Lipschitz in the relative unitary.  Therefore

```text
sqrt(2)
 <= e_int(U) + 16 ||U-V||_2
 <= e_int(U) + 16 sqrt(2C_lin/kappa_H) sqrt(A(U)).     (ABE3)
```

This is `(FBI2)`.  A normalized blow-up sequence would have both terms on
the right tend to zero, contradicting `(ABE3)`.  The failure dichotomy then
leaves only a macroscopic exact ultraproduct escape, proving the final
equivalence in the claim as well.
