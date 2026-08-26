---
rg: 2
id: transitive-product-socle-intermediate-proof
kind: route
title: Project to each socle coordinate and then recover the supported simple factors
target: transitive-product-socle-intermediate-is-an-endpoint
requires: []
---

For `1<=i<=k`, let `pi_i:T^k->T` be the coordinate projection and put

```text
E_i=pi_i(E).
```

The inclusion `K^k<=E` gives `K<=E_i`.  For `u in U`, conjugate `E` by the
element of `U^k` which is `u` in coordinate `i` and the identity elsewhere.
The assumed `U^k`-invariance shows that `E_i` is `U`-invariant.  Maximality
of `K` among proper `U`-invariant subgroups therefore gives

```text
E_i=K    or    E_i=T.                                  (1)
```

Coordinate permutations in `A` carry `E_i` to `E_(a i)`.  Since `A` is
transitive, the same alternative in `(1)` occurs at every coordinate.

If every `E_i=K`, then `E<=K^k`; together with `K^k<=E` this gives `E=K^k`.

Suppose instead that every `E_i=T`.  Define

```text
N_i={t in T : (1,...,1,t,1,...,1) belongs to E},        (2)
```

with `t` in coordinate `i`.  This is a subgroup of `T`.  It is normal in
`E_i=T`: if `t=pi_i(e)` for `e in E` and `n in N_i`, conjugating the
coordinate-supported element corresponding to `n` by `e` gives the
coordinate-supported element corresponding to `t n t^(-1)`.  Moreover
`K<=N_i`, because `K^k<=E`.  Hence `N_i` is nontrivial.  Simplicity of `T`
forces

```text
N_i=T.                                                  (3)
```

Thus `E` contains the full copy of `T` supported in each individual
coordinate.  Those coordinate copies generate `T^k`, so `T^k<=E`.  The
reverse inclusion is part of `(PSI1)`, and therefore `E=T^k`.

For the boundary statements, omit transitivity and take a product with
some coordinates equal to `K` and the rest equal to `T`.  If a proper
`U`-invariant subgroup `H` satisfies `K<H<T`, then `H^k` violates the
conclusion.  Finally, the supported-factor argument uses `K!=1` to ensure
`N_i!=1` and simplicity to turn that nonzero normal subgroup into all of
`T`; without those inputs the usual diagonal or fiber-product subgroups are
not excluded.
