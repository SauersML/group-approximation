---
rg: 2
id: counterexample-times-z-lacks-contractible-product-rips-proof
kind: route
title: Crossing with Z makes G x Z of type F, while the product formula keeps the Rips complex of G as a homotopy factor
target: counterexample-times-z-lacks-contractible-product-rips
requires:
  - g-times-z-type-f-iff-g-f-infinity-with-finite-cd
  - contractible-rips-groups-closed-under-direct-products
  - contractible-rips-complex-gives-finite-classifying-space
---

**1. `G × Z` is of type F.** `G` is of type `F_∞` with `cd G < ∞`, so the
backward direction of `g-times-z-type-f-iff-g-f-infinity-with-finite-cd` makes
`G × Z` of type F. There the product of a finite projective resolution of `G`
with `0 → Z[Z] → Z[Z] → Z → 0` has Euler class `j_*σ(G) − j_*σ(G) = 0`.

**2. No contractible product Rips complex.** By
`contractible-rips-groups-closed-under-direct-products`,
`|R_r(G×Z, S⊠T)| ≃ |R_r(G,S)| × |R_r(Z,T)|`. If this is contractible, then
`|R_r(G,S)|` is a retract of a contractible space (include it at a point of the
other factor, then project), so all its homotopy groups vanish. It is a CW
complex, so by Whitehead's theorem it is contractible. `G` has finite cd, so it
is torsion-free, and `contractible-rips-complex-gives-finite-classifying-space`
makes `G` of type F, a contradiction.

**3. General form.** If `R_r(H,T)` is contractible, then
`|R_r(G×H, S⊠T)| ≃ |R_r(G,S)| × |R_r(H,T)| ≃ |R_r(G,S)|`. If `R_r(G,S)` is
contractible, so is the product. Conversely, a contractible product forces
`R_r(G,S)` to be contractible, by the retract argument of part 2.
