---
rg: 2
id: arithmetic-star-packet-is-sofic-proof
kind: route
title: Embed the twisted Bass-Serre packet kernel into a finite-fiber graph wreath product
target: arithmetic-star-packet-is-sofic
requires:
  - arithmetic-star-packet-carrier
  - arithmetic-star-packet-fiber-clique-action-sofic
  - sofic-halo-products-preserve-hyperlinearity
artifacts:
  - research/artifacts/sofic-halo-permanence-falsification-audit-2026-08-20.md
---

Projection of the packet host `A=K rtimes_(Ad theta) P` onto `P`, together
with the identity of `E`, gives a retraction `pi:W->E`.  The standard kernel
theorem for an amalgam retraction gives

```text
N=ker(pi) ~= *_(x in E/P) K_x,
W ~= N rtimes E.
```

The action is twisted: the stabilizer `P` of the base factor acts on `K` by
`Ad(theta(p))`.

Put `L=ker(theta)`, `Q=P/L`, and `Y=E/L`.  Make every fiber of `Y->E/P` a
clique.  The graph product `B` of copies of `K` over this graph is

```text
B ~= *_(x in E/P) K^Q.
```

At the base fiber define the diagonal-conjugacy embedding

```text
delta:K -> K^Q,       delta(k)_q=theta(q)^(-1) k theta(q).
```

It is injective because its identity coordinate is `k`.  Under left
translation by `p in P`, pure coordinate permutation sends `delta(k)` to
`delta(theta(p) k theta(p)^(-1))`.  Thus `delta` exactly converts the inner
stabilizer action on `K` into the site-permutation action on the clique
fiber.  Induce this map over `E/P`.  Free-product normal form shows that the
resulting `E`-equivariant map `N->B` is injective, hence

```text
W=N rtimes E  ->  B rtimes E
```

is injective.

The right side is a graph wreath product.  The actor `E` is sofic by Cairn's
finite-index ascending-HNN theorem, its action on the graph is sofic by
`arithmetic-star-packet-fiber-clique-action-sofic`, and `K` is finite.
Alekseev--Bradford, arXiv:2601.18742, Theorem 6.11 (equivalently the graph-
halo specialization already imported by
`sofic-halo-products-preserve-hyperlinearity`) makes `B rtimes E` sofic.
Soficity passes to the embedded subgroup `W`.

