---
rg: 2
id: tensor-leg-centers-give-independent-plancherel-samples
kind: claim
title: Tensor-leg centers give independent Plancherel samples in the diagonal multiplicity commutant
distinct_from:
  diagonal-regular-isotypic-center-stays-plancherel: that computes the coarser intrinsic center of the diagonal image algebra; this uses the canonical center of every known tensor leg as a reducing PVM.
---

**ESTABLISHED COUNTEREXAMPLE.**  Let `P_rho` be the central isotypic
projections of `lambda_Q`.  In `lambda_Q^(tensor t)`, the products

```text
E_(rho_1,...,rho_t)=P_(rho_1) tensor ... tensor P_(rho_t)
```

form an orthogonal PVM commuting with the diagonal `Q`-action.  Their
normalized ranks are

```text
product_j dim(rho_j)^2/|Q|,
```

so this PVM records `t` independent Plancherel samples.  A diagonal
automorphism implementer permutes the labels coordinatewise.  These
projections generally lie in the multiplicity commutant rather than in the
intrinsic center of the diagonal image algebra.

For `Q=K^F` with `K` finite centerless nonabelian simple, the representation
on a tensor-leg fiber is faithful on `K^Z` exactly when at each coordinate at
least one of the `t` labels is nontrivial.  Its good mass is therefore

```text
(1-|K|^(-t))^|Z|.
```

For `K=A5`, the one-site Plancherel collision probability is

```text
(1^4+3^4+3^4+4^4+5^4)/60^2=29/100.
```

Thus a transposition mismatch is detected by the product PVM with exact mass
`1-(29/100)^t`; any distinct coordinate permutation has at least this mass.
This directly refutes the claim that diagonal tensor powers provide no
independent center samples or leave both chart costs unchanged.
