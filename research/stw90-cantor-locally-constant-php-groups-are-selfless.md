---
rg: 2
id: stw90-cantor-locally-constant-php-groups-are-selfless
kind: claim
title: Cantor step-function groups over PHP groups are selfless and strictly comparing
distinct_from:
  stw91-countable-free-direct-sum-is-selfless: that group is the union of finite products under coordinate extension by the identity; the Cantor step group uses diagonal coordinate refinement and contains full-support constant functions.
  stw90-stable-special-linear-group-is-selfless: that is a nested stable matrix group assembled from Vigdorovich's linear stages; this class is assembled from finite PHP powers and is nonlinear for a disjoint-support reason.
  ozawa-php-groups-completely-selfless: Ozawa treats groups which themselves have PHP; the Cantor step group is obtained by directed-union permanence, without asserting that PHP survives the infinite diagonal-refinement union.
artifacts:
  - research/artifacts/stw90-strict-comparison-group-frontier-2026-08-30.md
---

Let `P` be a nontrivial countable group with Ozawa's PHP property, let `X` be
the Cantor set, and give `P` the discrete topology.  The pointwise group

```text
LC(X,P)={f:X->P : f is locally constant}
```

is countable, and its reduced C\*-algebra is selfless.  Consequently
`LC(X,P)` is C\*-simple and its reduced algebra has stable rank one, strict
comparison by the canonical trace, and that trace is its unique normalized
`2`-quasitrace.

The group `LC(X,P)` is nonlinear over every field and is not
acylindrically hyperbolic.  If `P` is exact, then `LC(X,P)` is exact.  Taking
`P=F_2` therefore gives an explicit exact positive instance of STW Problem XC
outside both the linear and acylindrically hyperbolic classes, built from
coherent Cantor refinements rather than a restricted direct sum.
