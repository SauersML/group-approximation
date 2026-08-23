---
rg: 2
id: inverse-finite-algebraic-actions-are-ce
kind: claim
title: Inverse limits of finite algebraic actions have Connes-embeddable crossed products
distinct_from:
  stacked-finite-haar-modules-are-residually-finite: that assumes the compact group is a direct product of finite invariant factors and proves residual finiteness using coordinate projections; this allows arbitrary nonsplit bonding maps and proves only the exactly sufficient conclusion of soficity.
  dense-homoclinic-algebraic-actions-are-ce: that applies to general profinite compact groups under a dense-homoclinic hypothesis; an inverse limit of finite actions can have trivial homoclinic group, and this proof instead uses locality of soficity on the discrete dual.
  finite-profinite-lamp-packets-cannot-carry-manzoor-trace: that excludes inverse limits at the level of stabilizer characters; this proves Connes embeddability of the entire Haar crossed product.
---

Let `H` be a countable sofic group and let

```text
K = inverse_limit_i K_i
```

be an inverse limit of finite abelian `H`-groups with continuous
`H`-equivariant bonding maps.  No bonding map is assumed to split.  Then

```text
L^infinity(K,Haar) rtimes H
```

is Connes embeddable.  Equivalently, if `A=K-hat`, then `A rtimes H` is
sofic.

Thus nonsplit relations between finite invariant layers do not evade the
finite-layer obstruction.  In particular, any proposed `SL_3(Z)` module
obtained as a filtered colimit of finite invariant modules, or dually any
Haar action obtained as an inverse limit of finite `SL_3(Z)`-actions, is
barren for the algebraic-envelope route.  A surviving construction must
already have a finitely generated dual submodule which is not contained in
the image of any finite invariant module; failure of coordinatewise
splitting alone is insufficient.
