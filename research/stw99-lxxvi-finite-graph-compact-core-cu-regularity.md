---
rg: 2
id: stw99-lxxvi-finite-graph-compact-core-cu-regularity
kind: claim
title: Compact cycle cores prove concrete Cu regularity over every finite graph
artifacts:
  - research/artifacts/stw99-lxxvi-finite-graph-compact-core-audit-2026-09-05.md
distinct_from:
  stw99-lxxvi-cactus-enriched-cu-classification: that separates cycles at articulation vertices; this retains whole compact multicycle cores and handles arbitrary 2-connected blocks.
  stw99-lxxvi-stably-projectionless-finite-graph-cu-regularity: that excludes all nonzero compact fiber classes; this permits arbitrary projections and arbitrary K1.
  stw99-lxxvi-finite-graph-compact-clutching-rigidity: that controls only global compact classes; this proves the full Cu isomorphism, including globally noncompact classes compact on cyclic subgraphs.
---

Let `D,E` be simple separable stably finite stable-rank-one C*-algebras.
If a *-homomorphism `phi:D -> E` induces isomorphisms on both `Cu` and
`K_1`, then for every finite graph `X` it induces an isomorphism

```text
Cu(C(X,phi)):Cu(C(X,D)) -> Cu(C(X,E)).
```

In particular, every simple separable stably finite pure fiber `D` gives
a pure Cu-regular algebra `C(X,D)` for every finite graph. The result
includes theta graphs and 2-connected blocks with arbitrarily many cycles.

For a lower-semicontinuous function `F:X -> Cu(D)`, define its compact
cycle core `K(F)` as the union of embedded circles on which `F` is a
nonzero constant compact value. The core has finitely many connected
components `K_j`. Point evaluation is surjective, and two classes with
the same pointwise function `F` agree exactly when their compact
restrictions to every `K_j` agree. Thus, after choosing the usual
projection-clutching coordinates, the fiber of point evaluation is

```text
product_j H^1(K_j;K_1(D)).
```

This imposes the cycle relations inside a multicycle core: a theta core
has two independent coordinates, although it has three embedded circles.
The theorem does not replace actual core projection classes by unrelated
independent circle labels.

The proof first establishes equivalence-data realization and set
bijectivity. It then uses `(O5)` to split compact-left comparisons in the
target, lifts the remainder, and uses injectivity to reflect those
comparisons. A finite soft-spectrum cutting argument reduces general
comparison to these compact core comparisons and interval comparisons.
No reverse-order implication is inferred merely from a bijective Cu map.

The classification argument is finite-graph specific. The separate
`stw99-lxxvi-one-dimensional-simple-fiber-cu-regularity` passes its
first-factor conclusion through graph approximation to arbitrary
second-countable one-dimensional bases. Neither theorem solves STW
LXXVI for arbitrary pure algebras. Compact-level-set projection methods
already occur in Tikuisis's Theorem 1.1 for Z-stable ASH coefficients;
the extension here permits arbitrary simple stably finite stable-rank-one
coefficients and proves rigidity of the specified map.

ROUTES

stw99-lxxvi-finite-graph-compact-core-proof
