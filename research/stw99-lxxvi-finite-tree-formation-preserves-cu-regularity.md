---
rg: 2
id: stw99-lxxvi-finite-tree-formation-preserves-cu-regularity
kind: claim
title: Finite trees erase every supportwise K1 clutching obstruction
artifacts:
  - research/artifacts/stw99-lxxvi-finite-tree-noncompact-audit-2026-08-30.md
distinct_from:
  stw99-lxxvi-one-dimensional-formation-preserves-cu-regularity: that permits every one-dimensional base but assumes idealwise K1-vanishing; this permits arbitrary K1 but uses the acyclicity of a finite tree.
  stw99-lxxvi-finite-graph-compact-clutching-rigidity: that controls only compact Cu classes over arbitrary finite graphs; this computes the full Cu semigroup on finite trees.
---

Let `T` be a finite tree and let `D` be a simple separable C*-algebra of
stable rank one.  Then point evaluation is a natural isomorphism

```text
Cu(C(T,D)) -> Lsc(T,Cu(D)).
```

In particular, let `E` be another simple separable stable-rank-one
C*-algebra and let `phi:D->E` induce an isomorphism
`Cu(D)->Cu(E)`.  Then

```text
Cu(C(T,phi)):Cu(C(T,D)) -> Cu(C(T,E))
```

is an isomorphism.  No restriction on `K_1(D)` or `K_1(E)` is required.

Consequently, if `D` is simple, separable, stably finite and pure, then
`C(T,D)` is pure and Cuntz semigroup regular for every finite tree `T`.
This includes fibers with nonzero `K_1`.

The acyclicity hypothesis is substantive.  On a graph with a cycle, a
noncompact global element may restrict to a projection bundle around that
cycle and retain a supportwise `K_1`-clutching class, as in Phillips's
circle-with-a-tail example.

ROUTES

stw99-lxxvi-finite-tree-leaf-induction-proof
