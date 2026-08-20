---
rg: 2
id: property-t-laplacian-sos-certificate
kind: claim
title: Property T is witnessed by a finite Laplacian sum-of-squares certificate
---

Let `Gamma` be finitely generated and let `mu` be a finitely supported
symmetric generating probability measure.  Write `Delta_mu` for its real
group-algebra Laplacian.  If `Gamma` has property `(T)`, then there are
`kappa>0` and finitely many `xi_1,...,xi_r in R[Gamma]` such that

```text
Delta_mu^2 - kappa Delta_mu = sum_j xi_j* xi_j.
```

Conversely, existence of such a certificate implies property `(T)`.

This is Ozawa's algebraic characterization.  The finiteness of the supports is
important here: a single fixed microstate window can contain every coefficient
and product appearing in the certificate.
