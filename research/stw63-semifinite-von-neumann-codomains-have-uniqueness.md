---
rg: 2
id: stw63-semifinite-von-neumann-codomains-have-uniqueness
kind: claim
title: Every separably acting semifinite von Neumann codomain has unique Jiang--Su embeddings
distinct_from:
  stw63-uniqueness-is-closed-under-products: that assembles coordinatewise positive codomains; this proves the factorwise input and its central integral assembly using center-valued traces and support ranks.
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Let `M` be a semifinite von Neumann algebra acting on a separable Hilbert
space.  Then every two unital embeddings

```text
phi,psi:Z->M
```

are approximately unitarily equivalent in the C-star norm.

This includes arbitrary finite von Neumann algebras with separable predual,
type-I-infinity and type-II-infinity factors, and semifinite algebras with
nontrivial center and mixed finite/properly-infinite central summands.

On the finite summand, uniqueness of the trace of `Z` forces equality after
the center-valued trace.  On the summand with no finite central part, every
nonzero image element has support Murray--von Neumann equivalent to the unit;
hence the two maps have identical von Neumann rank element by element.

