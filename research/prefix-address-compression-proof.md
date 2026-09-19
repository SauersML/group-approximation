---
rg: 2
id: prefix-address-compression-proof
kind: route
title: Store the decaying Amitsur left inverses in prefix-free Fock corners
target: prefix-address-compresses-one-sided-amitsur-oracle
requires:
  - one-sided-amitsur-oracle-has-bounded-fock-model
  - two-generator-amitsur-levitzki-dimension-oracle
---

Use the prefix-free binary addresses `0^n1`.  Their left-creation ranges are
pairwise orthogonal, so the operators

```text
V_n (I tensor q_n) V_n^*
```

occupy orthogonal reducing blocks.  Since the established Fock inverse has
norm `1/sqrt((2n)!)`, their strong sum is one bounded operator `Q` and
compression to the `n`th address recovers exactly `q_n`.  This proves all
relations `(PAC2)` in one representation of the five-generator star algebra.

In an arbitrary `d`-dimensional evaluation, the `d`th standard polynomial is
zero before the address decoder is used.  Its defining residual is therefore
`-I_d`, giving the exact normalized-HS floor one.

The address operators are deliberately unconstrained in the presentation.
Their proper-isometry and orthogonality properties belong only to the chosen
infinite representation; imposing them as relations would manufacture a
separate, trivial finite-dimensional obstruction and would not survive a
tracial group-algebra decoder.

