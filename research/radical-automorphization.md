---
rg: 2
id: radical-automorphization
kind: claim
title: A radical-kernel surjective endomorphism forces its stable kernel
artifacts:
  - research/artifacts/radical-renormalization-2026-08-23.md
  - GroupApproximation/Sofic/UniversalFactorization.lean
---

Let `R:G->G` be a surjective endomorphism of a countable group.  If

```text
ker R <= Rad_MF(G),
```

then every homomorphism from `G` to an MF group, and every norm-matrix-corona
representation, factors through `R^n` for every `n`.  Consequently

```text
K_infty(R) := union_{n>=1} ker(R^n) <= Rad_MF(G).
```

The induced endomorphism on `G/K_infty(R)` is an automorphism.  Among quotients
through which `R` descends, this is the maximal one on which the descended map
is injective (hence invertible).  If `G/K_infty(R)` is MF, then

```text
Rad_MF(G) = K_infty(R).
```

More generally the identical proof works for any residual defined as the
intersection of kernels of homomorphisms into a chosen class of target groups.
