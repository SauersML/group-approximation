---
rg: 2
id: whitehead-finitely-generated-support-proof
kind: route
title: A matrix and its inverse mention finitely many group elements
target: whitehead-class-supported-on-finitely-generated-subgroup
requires: []
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

## Why sufficient

Let `x` in `Wh(G)` be represented by `A` in `GL_m(ZG)` and put `B = A^-1`.
Finitely many elements of `G` occur in the coefficients of the entries of `A`
and of `B` together; let `H` be the subgroup they generate.  `H` is finitely
generated, and torsion-free whenever `G` is, being a subgroup.  Both matrices
lie in `M_m(ZH)`, and the identities `AB = BA = I_m` are identities between
elements of `M_m(ZH)`, so they already hold there.  Hence `A` is invertible
over `ZH` and defines a class in `Wh(H)`; functoriality of `Wh` along
`H -> G` sends it to `x`.

Taking `B` into the support is the whole point: the support of `A` alone
would generate a subgroup over which `A` need not be invertible, and a `K_1`
representative must be genuinely invertible, not merely one-sided.
