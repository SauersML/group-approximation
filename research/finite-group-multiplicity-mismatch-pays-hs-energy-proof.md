---
rg: 2
id: finite-group-multiplicity-mismatch-pays-hs-energy-proof
kind: route
title: Bound the compatible isotypic mass of a unitary and apply the finite-group Laplacian gap
target: finite-group-multiplicity-mismatch-pays-hs-energy
requires:
  - finite-group-intertwiner-laplacian-gap
---

Let `P_lambda` and `Q_lambda` be the isotypic projections of `rho` and
`sigma`.  Orthogonal projection in the Hilbert space of matrices onto the
exact intertwiner space keeps, inside each compatible isotypic rectangle, only
the `I_(S_lambda)` tensor multiplicity-map component.  Hence it keeps no more
Hilbert--Schmidt mass than the whole rectangle `P_lambda U Q_lambda`.

For a unitary `U`,

```text
||P_lambda U Q_lambda||_HS^2
 <= min(rank P_lambda, rank Q_lambda)
 = d_lambda min(m_lambda,n_lambda).                    (1)
```

Indeed `P_lambda U Q_lambda` is a contraction both as a map out of the
`Q_lambda` space and into the `P_lambda` space, so the sum of its squared
singular values is bounded by the smaller rank.  Summing `(1)` over `lambda`
shows that the squared unnormalized distance from `U` to `Hom_H(sigma,rho)`
is at least

```text
d - sum_lambda d_lambda min(m_lambda,n_lambda).         (2)
```

Since the two total representation dimensions are both `d`,

```text
sum_lambda d_lambda(m_lambda-n_lambda)=0.
```

Positive and negative weighted multiplicity excess therefore have the same
mass, and `(2)` is exactly

```text
(1/2) sum_lambda d_lambda |m_lambda-n_lambda| = L/2.    (3)
```

After division by `d`, the normalized squared distance is at least `L/(2d)`.
Apply `(FIL2)` of `finite-group-intertwiner-laplacian-gap` to the component of
`U` orthogonal to the exact intertwiner kernel.  This gives

```text
sum_(s in S) ||rho(s)U-U sigma(s)||_(2,d)^2
 >= kappa(H,S) dist_(2,d)(U,Hom_H(sigma,rho))^2
 >= (kappa(H,S)/2)(L/d),
```

which is `(FGMP1)`.
