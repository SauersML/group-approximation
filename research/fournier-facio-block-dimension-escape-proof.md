---
rg: 2
id: fournier-facio-block-dimension-escape-proof
kind: route
title: Restrict any positive finite-size stratum to the bounded-block no-go
target: fournier-facio-block-dimension-escapes-every-charge-cutoff
requires:
  - fournier-facio-bounded-block-near-witness-impossible
  - fournier-facio-charge-null-monomial-perturbations-impossible
---

Use the null-ideal argument first to replace the proposed actors by their
block-monomial comparison family `B_g` without changing invariance, near
multiplicativity, or essential freeness in the charged sense.  Let

```text
Y_(<=m)={y in Y:d(y)<=m},
X_(<=m)=disjoint_union_(y in Y_(<=m)) X_y.             (FDEP1)
```

Every `B_g` maps a block unitarily onto another block, so it preserves block
dimension and hence preserves `X_(<=m)`.  If

```text
c_m=mu(X_(<=m))=nu(Y_(<=m))>0,                         (FDEP2)
```

define the normalized restricted charge

```text
mu_m(A)=mu(A cap X_(<=m))/c_m.                          (FDEP3)
```

All exceptional sets for the multiplication and essential-freeness tests
had zero `mu`-charge, so they still have zero `mu_m`-charge.  Invariance
also restricts because `X_(<=m)` is `B_g`-invariant.  Therefore

```text
(ell^2(X_(<=m)),mu_m,B|_(X_(<=m)))                     (FDEP4)
```

is an essentially free amenable near representation with block dimensions
at most `m`.  This contradicts
`fournier-facio-bounded-block-near-witness-impossible` (with zero comparison
error).  Hence `c_m=0` for every `m`.  Finite additivity and normalization
give `nu({d>m})=1`, proving `(FDE2)`.
