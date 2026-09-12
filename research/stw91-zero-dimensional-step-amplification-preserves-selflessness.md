---
rg: 2
id: stw91-zero-dimensional-step-amplification-preserves-selflessness
kind: claim
title: Zero-dimensional step-function amplification preserves exact selflessness
distinct_from:
  stw90-cantor-locally-constant-php-groups-are-selfless: that theorem assumes the stronger group-theoretic PHP property and proves additional geometry for the Cantor example; this permanence theorem starts from any exact selfless reduced group algebra and works over every compact metrizable zero-dimensional space.
  stw91-countable-free-direct-sum-is-selfless: that is one restricted-direct-sum example with coordinate-extension bonding maps; this theorem treats locally constant function groups through arbitrary finite clopen-partition refinements.
  complete-selflessness-tensor-permanence: that is a two-factor C*-probability-space theorem; this result iterates its exact ordinary-selfless clause and then identifies a directed limit of reduced group algebras.
artifacts:
  - research/artifacts/stw91-selfless-group-frontier-2026-08-30.md
---

Let `P` be a nontrivial countable discrete group such that `C*_r(P)` is exact
and selfless.  Let `X` be a nonempty compact metrizable zero-dimensional
space, give `P` the discrete topology, and put

```text
LC(X,P)={f:X->P : f is locally constant}
```

with pointwise multiplication.  Then `LC(X,P)` is countable and
`C*_r(LC(X,P))` is exact and selfless.  In particular, the step-function
group is C\*-simple, and its reduced algebra has stable rank one, strict
comparison by the canonical trace, and a unique normalized `2`-quasitrace.

This is an unconditional permanence theorem for XCI: it requires
selflessness only of the base reduced algebra, not PHP, linearity, or an
acylindrical action for the amplified group.
