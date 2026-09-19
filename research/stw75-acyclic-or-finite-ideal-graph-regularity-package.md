---
rg: 2
id: stw75-acyclic-or-finite-ideal-graph-regularity-package
kind: claim
title: Pure row-finite graph algebras are Z-stable in the acyclic and finite-ideal cases
distinct_from:
  stw99-problem-lxxv-nonsimple-toms-winter: that asks for every separable nuclear nowhere-scattered algebra; this settles the countable row-finite graph subclass when the graph is acyclic or its graph algebra has finitely many ideals.
  stw99-problem-lxxvi-pure-implies-cu-regular: that asks whether every pure C-star algebra has a Cu-regular first-factor map; this establishes that conclusion on the same graph subclass by proving actual Z-stability.
---

Let `E` be a countable row-finite graph. Assume either

1. `E` has no cycles, or
2. `C*(E)` has finitely many ideals.

Then the following are equivalent.

1. `E` has distinct detours.
2. `C*(E)` has no elementary subquotients.
3. `C*(E)` is pure.
4. `C*(E)` is Z-stable.

Whenever these conditions hold,

```text
dim_nuc(C*(E)) <= 2
```

(and it is zero in the acyclic case), while the first-factor map induces an
isomorphism

```text
Cu(C*(E)) -> Cu(C*(E) tensor Z).
```

Thus the generalized nonsimple Toms--Winter regularity package and the
Problem LXXVI Cu-regularity conclusion hold on this graph-algebra subclass.

**ESTABLISHED 2026-08-30** by
[[stw75-faurot-graph-regularity-import]].
