---
rg: 2
id: stw99-lxxvi-finite-graph-fields-over-k1-trivial-pure-fibers
kind: claim
title: Finite-graph fields over K1-trivial simple pure fibers are Cu-regular
distinct_from:
  stw99-lxxvi-circle-fields-over-simple-pure-fibers: the circle theorem permits arbitrary K1 by retaining a compact clutching summand; this theorem permits arbitrary finite branching and cycle rank because K1-triviality makes the whole Cu computation pointwise.
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Let `X` be a finite graph and let `D` be a simple separable stably finite pure
C*-algebra such that

```text
K_1(D)=0.
```

Then `C(X,D)` is pure and Cuntz semigroup regular.  More precisely, evaluation
gives natural order isomorphisms

```text
Cu(C(X,D))                  ~= Lsc(X,Cu(D)),
Cu(C(X,D tensor_min Z))     ~= Lsc(X,Cu(D tensor_min Z)),       (1)
```

under which the actual first-factor map is pointwise application of
`Cu(D)->Cu(D tensor_min Z)`.  Consequently,

```text
Cu(C(X,D)) -> Cu(C(X,D) tensor_min Z)
```

is an isomorphism.

The graph may be disconnected and may have vertices of arbitrary finite
valence and any finite number of independent cycles.  Thus this includes
finite trees, bouquets of circles, and theta graphs, not only intervals and
single circles.  The hypothesis `K_1(D)=0` is essential to the pointwise-formula
argument used here; no formula for arbitrary stable-rank-one fibers over a
general graph is asserted.
