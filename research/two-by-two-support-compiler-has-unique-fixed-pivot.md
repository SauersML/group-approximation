---
rg: 2
id: two-by-two-support-compiler-has-unique-fixed-pivot
kind: claim
title: A two-by-two exact support-violation compiler can name at most one fixed Pauli pivot
artifacts:
  - experiments/minimal_rank_one_support_compiler.py
  - research/artifacts/relative-rank-one-fanizza-synthesis-2026-08-20.md
distinct_from:
  support-failure-has-fixed-pivot-rank-one-compiler: that constructs one sparsest fixed pivot; this proves a second assignment-independent pivot is impossible at the same matrix size and exact predicate profile.
  finite-selector-gadget-induction-barrier: that prohibits deleting selector characters by a finite-group extension; this is a finite affine-matrix rigidity theorem about naming the relative spin coordinate.
---

Let `M(e,f)` be a two-by-two matrix of affine `F_2` forms with

```text
rank M(e,f)=1+(1+e)f.                                  (UFP1)
```

Call a pair of nonzero constant vectors `(r,c) in F_2^2 x F_2^2` a **fixed
Pauli pivot** if

```text
r^T M(e,f)c = 1
```

as an affine form, identically on the Boolean square.  Then `M` has at most
one fixed Pauli pivot.

Thus the extra relative `M_2` coordinate in an exact two-by-two compiler
cannot be bracketed by two fixed rank-one subgroup embeddings.  Any return
construction at this size must use conditional expectations/multiplicity, a
named carrier, or a larger nonlinear holonomy object; it cannot simply
conjugate between two fixed Pauli pivots.

The MSI verifier independently exhausts all 4096 affine matrices: among the
252 with profile `(UFP1)`, 216 have one fixed pivot and 36 have none.
