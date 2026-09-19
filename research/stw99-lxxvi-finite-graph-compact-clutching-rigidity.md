---
rg: 2
id: stw99-lxxvi-finite-graph-compact-clutching-rigidity
kind: claim
title: Finite graph formation preserves the compact Cuntz wing of a simple Cu-regular fiber
artifacts:
  - research/artifacts/stw99-lxxvi-finite-graph-compact-audit-2026-08-30.md
---

Let `X` be a connected finite graph and let `D` be a simple separable
stably finite C-star-algebra.  Put `E=D tensor_min Z`, and suppose that
`D` and `E` have stable rank one and that the actual first-factor map

```text
Cu(D) -> Cu(E)
```

is an isomorphism.  Then the first-factor map for `C(X,D)` is an
isomorphism on compact elements:

```text
Cu(C(X,D))_c  ->  Cu(C(X,E))_c .
```

Equivalently, it induces an isomorphism of projection monoids

```text
V(C(X,D)) -> V(C(X,E)).
```

Naturally, if `X` has first Betti number `b`, then

```text
V(C(X,D))
  ~= {0} disjointUnion
     (V(D) minus {0}) times H^1(X;K_1(D))
  ~= {0} disjointUnion
     (V(D) minus {0}) times K_1(D)^b .
```

The first coordinate is the fiber projection class and the second is the
clutching class around the independent cycles.

In particular the hypotheses hold when `D` is simple, separable, stably
finite, and pure.  Thus every compact class survives tensoring with `Z`
over every finite graph, even when `K_1(D)` is nonzero.  Any failure of
Cuntz-semigroup regularity for such a graph field must be noncompact and
supportwise; global projection clutching cannot witness it.
