---
rg: 2
id: stw63-semifinite-von-neumann-codomains-have-uniqueness
kind: claim
title: Finite and separably acting semifinite von Neumann codomains have unique Jiang--Su embeddings
distinct_from:
  stw63-uniqueness-is-closed-under-products: that assembles coordinatewise positive codomains; this proves the factorwise input and its central integral assembly using center-valued traces and support ranks.
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

Let `M` be either an arbitrary finite von Neumann algebra or a semifinite
von Neumann algebra acting on a separable Hilbert space.  Then every two
unital embeddings

```text
phi,psi:Z->M
```

are approximately unitarily equivalent in the C-star norm.

This includes all finite von Neumann algebras without any countability
assumption, type-I-infinity and type-II-infinity factors on separable Hilbert
space, and separably acting semifinite algebras with nontrivial center and
mixed finite/properly-infinite central summands.

On the finite summand, uniqueness of the trace of `Z` forces equality after
the center-valued trace.  On the summand with no finite central part, every
nonzero image element has support Murray--von Neumann equivalent to the unit;
hence the two maps have identical von Neumann rank element by element.
