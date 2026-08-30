---
rg: 2
id: unseparated-finite-table-gap-is-impossible-proof
kind: route
title: Collapse every table symbol to the identity
target: unseparated-finite-table-gap-is-impossible
requires: []
---

Let `T` have label set `F` and tested products `P subseteq F x F x F`.
For any `d >= 1`, put `U_g = I_d` for every `g in F`. For each
`(g,h,k) in P`,

```text
U_g U_h = I_d I_d = I_d = U_k.
```

Thus every normalized Hilbert--Schmidt multiplication error is zero. Likewise,
for any nonempty finite set `X`, put `sigma_g = id_X` for every `g in F`.
Then `sigma_g sigma_h = id_X = sigma_k` for each tested product, so every
normalized Hamming multiplication error is zero. Nonnegative defects with a
zero-defect model have infimum zero. This proves the claim.
