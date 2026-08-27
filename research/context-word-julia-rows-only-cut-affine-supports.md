---
rg: 2
id: context-word-julia-rows-only-cut-affine-supports
kind: claim
title: Context-word Julia rows can cut only affine assignment supports
distinct_from:
  universal-central-selector-word-is-affine-for-any-actor: that classifies a universally central selector word even after adjoining an arbitrary actor; this treats a finite family of state-dependent return rows on one free Julia Gram carrier.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that classifies universally scalar words in a finite marked role packet; this treats arbitrary context words acting on one nonzero Julia Gram source and needs no finite role group.
  algebraic-selector-mixing-frame-collapses-forbidden-sector: that rules out a universal operator frame plus exact mixing rows; this is the local character calculation for the simpler proposal using only context-word returns.
---

**ESTABLISHED NO-GO.**  Let `x_1,...,x_k` be commuting involutions and let
`G` be a nonzero Gram operator carried by the free Julia grading of
`free-julia-grading-carries-one-gram-at-canonical-quarter-mass`.  Consider any
finite family of predicate rows whose positive-side operators are ordinary
context words, with optional fixed signs:

```text
h_l=s_l product_i x_i^(a_(l,i)),
s_l in {+1,-1}.                                        (CJW1)
```

Imposing the corresponding Julia return rows makes `h_lG=G` for every `l`.
On the joint character with assignment `v in F_2^k`, the source of `G` can
have support only if

```text
sum_i a_(l,i)v_i=b_l          for every l,             (CJW2)
```

where `s_l=(-1)^(b_l)`.  Hence the assignment support retained by any such
finite row family is an affine subspace of `F_2^k`.

In particular, these rows cannot retain every point of a nonaffine predicate
while deleting its forbidden assignments.  For the one-ghost predicate
`R_*`, any row family retaining all seven honest assignments also retains
the ghost, because the ghost lies in their affine hull.

The free Julia carrier therefore solves the common positive-mass Gram
problem but cannot itself solve nonlinear predicate authentication.  A
successful ordinary-group compiler must add a genuinely non-character
predicate actuator whose soundness is matrix-only or canonical-trace-only;
adding more context-word commutators cannot close the gap.

