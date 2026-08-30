---
rg: 2
id: regular-dominating-amenable-subgroup-proof
kind: route
title: Restrict the regular kernel and use amenability
target: regular-dominating-quotients-preserve-amenable-subgroup-algebras
requires: []
artifacts:
  - research/artifacts/elementary-group-closures-2026-08-30.md
---

First identify `C^*(H)` with its canonical subalgebra of `C^*(G)`.  Indeed,
for every unitary representation `sigma` of `H`, the restriction to `H` of
`Ind_H^G(sigma)` contains `sigma` on the subspace supported on the identity
coset.  Thus the universal `H`-norm is detected inside the universal
`G`-norm, proving injectivity of `C^*(H)->C^*(G)`.

Weak containment `lambda_G prec pi` reverses kernel inclusion, so

```text
J_pi=ker(C^*(G)->C^*_pi(G))
   <= ker(C^*(G)->C^*_r(G)).                            (1)
```

After restriction to `H`, the left regular representation of `G` is a
direct sum of copies of `lambda_H`, one for each right `H`-coset.  Therefore

```text
ker(lambda_G) cap C^*(H)
 =ker(C^*(H)->C^*_r(H)).                               (2)
```

If `H` is amenable, the full-to-reduced map in `(2)` is injective.  Equations
`(1)--(2)` give `J_pi cap C^*(H)=0`, which is exactly injectivity of the
restriction of `q_pi`.  Finite subgroups are amenable, so every one of their
nonzero central isotypic projections survives as claimed.
