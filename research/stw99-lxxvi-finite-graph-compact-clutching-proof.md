---
rg: 2
id: stw99-lxxvi-finite-graph-compact-clutching-proof
kind: route
title: Classify graph projection bundles by their fiber and cycle clutching
target: stw99-lxxvi-finite-graph-compact-clutching-rigidity
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-finite-graph-compact-audit-2026-08-30.md
---

Write `B=D tensor K`.  If `D` is stably projectionless, then
`V(D)={0}`; the assumed coefficient Cu-isomorphism gives `V(E)={0}`
as well, and both graph projection monoids are zero.  Thus suppose that a
nonzero projection occurs.

Let `p` be a nonzero projection in `C(X,B)`.  Its norm is zero or one
at each point, so connectedness makes every fiber `p(x)` nonzero.
The class `[p(x)] in V(D)` is constant along paths.  Since `D` is
simple, every nonzero fiber projection is full.

Choose a spanning tree `T` of `X` and a base vertex.  A projective
module bundle is trivial over `T`; fix a fiber projection `q` there.
Each edge outside `T` then closes one independent cycle.  Its gluing
automorphism is a unitary in the full corner `qBq`.  Stable rank one
identifies

```text
U(qBq)/U_0(qBq) ~= K_1(qBq) ~= K_1(D).
```

Changing the tree trivialization changes the edge labels by a coboundary.
Consequently the bundle has a well-defined clutching class in

```text
H^1(X;K_1(D)) ~= K_1(D)^b,
```

where `b=rank H_1(X;Z)`.  Conversely, choose unitary representatives in
`qBq` for a set of cycle labels and glue the constant module over the
tree.  This realizes every pair.  Two bundles are isomorphic exactly when
their fiber and cohomology classes agree.  Hence

```text
V(C(X,D))
  ~= {0} disjointUnion
     (V(D) minus {0}) times H^1(X;K_1(D)).                 (1)
```

This description is additive.  It also proves cancellation: stable rank one
cancels the fiber projections, and the cycle coordinates cancel in the
abelian group `H^1(X;K_1(D))`.  The full-corner inclusions used when taking
direct sums induce the usual Morita isomorphisms on `K_1`.

Let `iota:D->E=D tensor Z` be the first-factor map.  Its Cu-isomorphism
restricts to an isomorphism `V(D)->V(E)`.  Moreover the unital inclusion
`C->Z` is a KK-equivalence, so exterior product with `D` shows that
`K_1(iota)` is an isomorphism without a nuclearity, exactness, or UCT
assumption on `D`.  Under (1), `V(C(X,iota))` is exactly

```text
(v,kappa) |-> (V(iota)(v), H^1(X;K_1(iota))(kappa)),
```

and is therefore an isomorphism.

Finally, stable finiteness passes to continuous graph fields.  Brown--Ciuperca
identify compact Cuntz classes of a stably finite algebra with its projection
monoid.  Thus the projection-monoid isomorphism is precisely the asserted
isomorphism on compact Cu elements.
