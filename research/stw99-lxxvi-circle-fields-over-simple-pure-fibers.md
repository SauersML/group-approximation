---
rg: 2
id: stw99-lxxvi-circle-fields-over-simple-pure-fibers
kind: claim
title: Circle fields over simple stably finite pure fibers are Cu-regular
distinct_from:
  stw99-lxxvi-interval-fields-over-simple-pure-fibers: the interval has no compact monodromy term and is computed pointwise; the circle has a V(C(T,D)) clutching summand whose cancellation is the new content.
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Let `D` be a simple separable stably finite pure C*-algebra.  Then

```text
A=C(T,D)
```

is Cuntz semigroup regular.  That is, the actual first-factor embedding
induces an isomorphism

```text
Cu(C(T,D)) -> Cu(C(T,D) tensor_min Z).
```

The conclusion does not assume that `D` is nuclear or Z-stable.  It extends
the interval-field theorem
`stw99-lxxvi-interval-fields-over-simple-pure-fibers` across the compact
monodromy term: stable rank one prevents that term from collapsing after
tensoring with `Z`.
