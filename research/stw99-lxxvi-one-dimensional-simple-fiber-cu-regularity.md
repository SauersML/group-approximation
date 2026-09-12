---
rg: 2
id: stw99-lxxvi-one-dimensional-simple-fiber-cu-regularity
kind: claim
title: Every second-countable one-dimensional base preserves simple-fiber concrete Cu regularity without K1 vanishing
artifacts:
  - research/artifacts/stw99-lxxvi-one-dimensional-simple-fiber-audit-2026-09-05.md
distinct_from:
  stw99-lxxvi-one-dimensional-formation-preserves-cu-regularity: that uses idealwise K1 vanishing and a pointwise formula; this allows arbitrary K1 for simple fibers and retains actual Cu through graph approximation.
  stw99-lxxvi-finite-graph-compact-core-cu-regularity: that gives a finite-graph classification by compact cycle cores; this extends concrete first-factor regularity to arbitrary second-countable locally compact one-dimensional bases, without asserting a finite-core formula there.
---

Let `X` be a second-countable locally compact Hausdorff space of covering
dimension at most one. Let `D` be a simple separable stably finite
C*-algebra such that `D` and `D tensor Z` have stable rank one and the
actual coefficient first-factor Cu map is an isomorphism. Then

```text
Cu(C_0(X,D)) -> Cu(C_0(X,D) tensor Z)
```

induced by the actual first-factor map is an isomorphism. There is no
vanishing-K1 hypothesis and no restriction on projections.

In particular, every simple separable stably finite pure coefficient
`D` yields a pure Cu-regular `C_0(X,D)` for every such `X`.

The compact case follows by expressing `X` as an inverse limit of finite
graphs, applying the finite-graph compact-core theorem at every stage,
and passing the natural first-factor maps through the Cu inductive
limit. The locally compact case follows from the one-point compactification
and ideal permanence.

The conclusion is concrete Cu regularity. It is not an unrestricted
pointwise identification with `Lsc(X,Cu(D))`: compact circle clutching
already disproves that formula when projections and nonzero K1 coexist.
The general STW LXXVI problem remains open.

ROUTES

stw99-lxxvi-one-dimensional-graph-limit-proof
