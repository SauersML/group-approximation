---
rg: 2
id: disjoint-tag-covariance-controls-cross-gram
kind: claim
title: Exclusive disjoint finite tag types pay both exit leakage and cross-Gram overlap
distinct_from:
  finite-group-intertwiner-laplacian-gap: that gives the fixed spectral gap for one arbitrary operator; this applies it to branch cross-Gram operators and sums the covariance errors.
  partial-isometry-gram-is-range-overlap: that identifies cross-Gram norm with range overlap but supplies no upper bound; this bounds that overlap from finite tag covariance.
  global-v4-exit-capacity-is-cross-gram-curvature: that says cross-Gram overlap must be paid; this gives a sufficient representation-theoretic condition for paying it by defining covariance relators.
---

Let `H` be a fixed finite group with inverse-closed generating set `S`.  Let
`rho:H->U(K)` and `pi_i:H->U(V_i)`, `1<=i<=N`, be exact finite-dimensional
representations.  Let `P` be a projection commuting with `rho(H)`, and assume

```text
Hom_H(V_j,V_i)=0                 whenever i!=j,
Hom_H(V_i,(1-P)K)=0              for every i.            (DTC1)
```

For contractions `T_i:V_i->K`, put

```text
D_(i,s)=rho(s)T_i-T_i pi_i(s),
E_i=sum_(s in S)||D_(i,s)||_2^2.                        (DTC2)
```

Then, with `kappa=kappa(H,S)` from the finite-group intertwiner gap,

```text
sum_i ||(1-P)T_i||_2^2
 <= (1/kappa) sum_i E_i,                               (DTC3)

sum_(i!=j)||T_i^*T_j||_2^2
 <= (4(N-1)/kappa) sum_i E_i.                          (DTC4)
```

The Hilbert--Schmidt norms may all be divided by one common ambient
dimension; the same formula holds.  If the `T_i` are partial isometries with
range projections `R_i=T_iT_i^*`, then

```text
sum_(i!=j)tau(R_iR_j)
 <= (4(N-1)/kappa) sum_i E_i.                          (DTC5)
```

Thus both error terms in a finite branch-capacity ledger are automatically
controlled once the branch ranges carry pairwise disjoint types of one fixed
tag group, those types occur only inside the parent `P`, and the tag
covariances are defining relators.  In the notation of
`global-v4-exit-capacity-is-cross-gram-curvature`,

```text
l+o <= ((4N-3)/kappa) sum_i E_i.                       (DTC6)
```

No multiplicity classicalization or dimension-dependent constant appears.

For the global V4 programme, `(DTC6)` closes the analytic inequality `(VGC5)`
conditional on constructing exclusive tag types.  It does not construct the
tags from the shared contextual tuple, and it does not prove that their
allowed extensions preserve the exact non-CE tracial model.
