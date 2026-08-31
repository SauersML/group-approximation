---
rg: 2
id: stw99-lxxvi-unicyclic-enriched-cu-classification
kind: claim
title: A unicyclic graph carries exactly one supportwise circle clutching sector
artifacts:
  - research/artifacts/stw99-lxxvi-unicyclic-enriched-cu-audit-2026-08-31.md
distinct_from:
  stw99-lxxvi-finite-tree-formation-preserves-cu-regularity: trees have no cyclic core and need no enriched coordinate.
  stw99-lxxvi-stably-projectionless-finite-graph-cu-regularity: that permits arbitrarily many cycles by excluding compact fiber classes; this permits projections but at most one cycle per connected component.
  stw99-lxxvi-one-dimensional-formation-preserves-cu-regularity: that uses a pointwise formula under idealwise K1-vanishing; this records nonzero K1 clutching exactly.
---

Let `X` be a connected finite graph with first Betti number one, let
`Gamma` be its unique embedded circle, and let `D` be a simple separable
stable-rank-one C*-algebra. Put `S=Cu(D)`. There is a natural isomorphism

```text
Cu(C(X,D))
 ~= Cu(C(Gamma,D))
      pullback_{Lsc(Gamma,S)}
    Lsc(X,S).
```

The compatibility maps are circle point evaluation and restriction to
`Gamma`. Thus the full class consists of its actual circle class together
with its global pointwise Cu function. This retains compact circle clutching
even when the global element is noncompact.

Point evaluation onto `Lsc(X,S)` is surjective. Its fiber over `F` is a
singleton unless `F|Gamma` is a nonzero constant compact class; in that
case the fiber is naturally indexed by `K_1(D)`. Hence point evaluation is
an isomorphism exactly when `K_1(D)=0` or `D` is stably projectionless.

Consequently, if `D` is simple, separable, stable rank one, and Cu-regular
for the actual first-factor map, then `C(X,D)` is Cu-regular for every finite
pseudoforest `X`. In particular this applies to every simple separable stably
finite pure `D`, and then `C(X,D)` is also pure. Projections and `K_1(D)` are
arbitrary. The assertion is componentwise: tree components use the pointwise
formula and unicyclic components use the enriched formula above.

No classification is asserted for a component containing two or more
independent cycles.

ROUTES

stw99-lxxvi-unicyclic-leaf-pullback-proof
