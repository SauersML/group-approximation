---
rg: 2
id: leavitt-gl-equals-el-via-purely-infinite-k1
kind: route
title: An external route through pure infiniteness and vanishing K_1
target: leavitt-gl-equals-el-and-perfect-unit-group
requires:
  - agp-purely-infinite-simple-k1-is-unit-abelianization
  - ge-ring-with-perfect-units-has-gl-equals-el
artifacts:
  - research/artifacts/rank-one-headline-review-2026-09-07.md
---

## Why sufficient

A second complete route to the target, recorded for reuse.  The printed route
is internal and machine-checked and remains the preferred one here; this one
is stated because its two inputs are general ring theory and apply beyond the
Leavitt case.

`R = L_k(1,2)` is purely infinite simple by Ara--Goodearl--Pardo Theorem 4.2,
so `K_1(R) = (R^x)^ab` by their Theorem 2.4, and a purely infinite simple ring
is a GE-ring.

`K_1(R) = 0`.  In the Leavitt `K`-theory sequence the relevant map is
multiplication by `1 - 2 = -1`, an isomorphism of `Z`, so it has zero kernel
and cokernel; over `F_2` this is immediate anyway, since `K_1(F_2) = 0` and
the `K_0` map is injective.  So `(R^x)^ab = 0` and `R^x` is perfect.

Then `ge-ring-with-perfect-units-has-gl-equals-el` gives
`GL_n(R) = EL_n(R)` for every `n >= 2`.

**Trust boundary.**  Ara--Brustenga--Cortinas, arXiv:0903.0056, Corollary 7.7
is cited in the source dossier for the `K_1` vanishing; only its abstract was
read here, and the `F_2` computation above is what this route relies on.
