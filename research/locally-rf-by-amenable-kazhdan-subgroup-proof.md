---
rg: 2
id: locally-rf-by-amenable-kazhdan-subgroup-proof
kind: route
title: Make the amenable image finite and use finite-extension permanence of residual finiteness
target: locally-rf-by-amenable-cannot-supply-exact-kazhdan-kernel
requires: []
---

Let `q:H->A` denote the quotient map.  The image `q(K)` is both amenable and
Kazhdan, because amenability and property `(T)` pass to subgroups and
quotients in the required directions.  Hence `q(K)` is finite.  Therefore

```text
K_0=K cap L=ker(q|K)
```

is a finite-index normal subgroup of `K`.

Property `(T)` makes `K`, and hence `K_0`, finitely generated.  Since `L` is
locally residually finite, the finitely generated subgroup `K_0<=L` is
residually finite.  A finitely generated residually finite group has, inside
each of its finite-index subgroups, a finite-index characteristic subgroup:
intersect the finitely many subgroups of the relevant bounded index.  It
follows that a finite extension of a finitely generated residually finite
group is residually finite.  Applying this to `K_0 normal K` proves that `K`
is residually finite.

If `K` has no nontrivial finite quotient and were nontrivial, residual
finiteness would separate one of its nonidentity elements in a finite group.
This contradiction proves `(LRA1)`.

Cornulier constructs an exact sequence with locally residually finite kernel
and abelian quotient and proves the resulting group finitely presented and
sofic.  Thus the theorem applies directly:

```text
Y. Cornulier, A sofic group away from amenable groups,
arXiv:0906.3374v2, Theorem 2, Corollary 3 and Proposition 4.
https://arxiv.org/abs/0906.3374
```

