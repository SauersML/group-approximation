---
rg: 2
id: stw99-lxxvi-cactus-enriched-cu-classification
kind: claim
title: Articulation gluing reduces graph Cu to its blocks and computes every finite cactus
artifacts:
  - research/artifacts/stw99-lxxvi-cactus-enriched-cu-audit-2026-08-31.md
distinct_from:
  stw99-lxxvi-unicyclic-enriched-cu-classification: that retains one cyclic block; this permits arbitrarily many circle blocks separated by articulation vertices.
  stw99-lxxvi-stably-projectionless-finite-graph-cu-regularity: that permits arbitrary finite graphs by excluding compact fiber classes; this permits projections but requires every multi-cycle interaction to split at cut vertices.
  stw99-lxxvi-finite-graph-compact-clutching-rigidity: that computes only compact elements for every finite graph; this computes the full Cu semigroup for cactus graphs.
---

Let `D` be a simple separable stable-rank-one C*-algebra.

If finite graphs `Y` and `Z` meet at one point, restriction is a natural
isomorphism

```text
Cu(C(Y wedge Z,D))
 ~= Cu(C(Y,D)) pullback_{Cu(D)} Cu(C(Z,D)).
```

Consequently, for every connected finite graph `X`, restriction gives the
exact block-cut reduction

```text
Cu(C(X,D))
 ~= { (xi_B)_B :
      xi_B in Cu(C(B,D)),
      ev_v(xi_B)=ev_v(xi_B') at every articulation vertex }.
```

This reduces the problem to the actual Cu semigroups of the 2-connected
blocks; it does not compute a block containing several independent cycles.

If `X` is a finite cactus and `S=Cu(D)`, its blocks are bridge edges and
embedded circles, so the reduction becomes the explicit enriched formula

```text
Cu(C(X,D))
 ~= (product_{C in Cycles(X)} Cu(C(C,D)))
      pullback_{product_C Lsc(C,S)}
    Lsc(X,S).
```

Point evaluation is surjective. Its fiber over `F` is naturally
`K_1(D)^{m_X(F)}`, where `m_X(F)` counts the cyclic blocks on which `F` is a
nonzero constant compact class. The labels are independent at articulation
vertices.

Thus a forest always has the pointwise formula. If a finite cactus contains
a cycle, point evaluation is an isomorphism exactly when `K_1(D)=0` or `D`
is stably projectionless.

Finally, if `D` is simple, separable, stable rank one, and Cu-regular for the
actual first-factor map, then `C(X,D)` is Cu-regular for every finite cactus
`X`. In particular every simple separable stably finite pure fiber gives a
pure Cu-regular cactus field, with arbitrary projections and arbitrary
`K_1(D)`.

No computation is asserted for a 2-connected block of first Betti number at
least two.

ROUTES

stw99-lxxvi-cactus-block-tree-pullback-proof
