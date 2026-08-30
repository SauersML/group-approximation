---
rg: 2
id: diagonal-regular-isotypic-center-stays-plancherel
kind: claim
title: The intrinsic isotypic center of a diagonal regular tensor power stays Plancherel
distinct_from:
  diagonal-tensor-powers-do-not-amplify-regular-lamp-center: that incorrectly excludes reducing tensor-leg center projections; this states only the true intrinsic-center consequence of Fell absorption.
  tensor-leg-centers-give-independent-plancherel-samples: that constructs a finer reducing PVM in the multiplicity commutant, not in the intrinsic center of the diagonal image algebra.
---

**ESTABLISHED.**  For every finite group `Q` and `t>=1`, put

```text
Lambda_t(g)=lambda_Q(g)^(tensor t).
```

Then `Lambda_t` is unitarily equivalent to `|Q|^(t-1)` copies of the left
regular representation.  Consequently the minimal central isotypic
projections of `Lambda_t(CQ)''` have the same normalized ranks

```text
dim(rho)^2/|Q|
```

as one regular packet.  For `Q=K^F` their intrinsic spectrum is
`Irr(K)^F` with product Plancherel law, and the intrinsic fiber mass faithful
on `K^Z` is `(1-1/|K|)^|Z|`.

This statement concerns only the intrinsic center of the diagonal image
algebra.  It does not say that the representation has no finer equivariant
reducing PVM in its multiplicity commutant.
