---
rg: 2
id: support-failure-has-fixed-pivot-rank-one-compiler
kind: claim
title: Child-without-parent has a two-by-two affine compiler with one fixed Pauli pivot
artifacts:
  - experiments/minimal_rank_one_support_compiler.py
  - research/artifacts/relative-rank-one-fanizza-synthesis-2026-08-20.md
distinct_from:
  nested-support-failure-is-one-clifford-rank-jump: that reads the forbidden atom from the raw Steinberg pairing, whose baseline rank is not constant; this changes coordinates to keep one fixed pivot on every Boolean assignment.
  boolean-predicate-is-one-rank-jump: that gives a general algebraic-branching-program compiler; this is the minimal-size explicit matrix for the support-containment predicate.
---

For Boolean bits `e,f`, put

```text
M_sub(e,f) = [[1, 1+e],
              [f,   0]].                              (SFP1)
```

Then

```text
rank_F2 M_sub(e,f) = 1 + (1+e)f.                      (SFP2)
```

The upper-left `1` is an assignment-independent invertible leading block.
Consequently the Schur--Clifford inclusion associated to `(SFP1)` has one
fixed baseline Pauli simple on all four selector sectors, and exactly the
forbidden support atom `e=0, f=1` adds one relative `M_2` coordinate.

The exhaustive verifier enumerates all `8^4=4096` two-by-two matrices whose
entries are affine forms in `e,f`.  There are 252 with rank profile
`(1,2,1,1)` on `(00,01,10,11)`, 24 with upper-left entry identically one, and
four sparsest fixed-pivot compilers at complexity three nonzero entries and
four affine monomials.  `(SFP1)` is one of those four.  The enumeration is a
minimality certificate for this finite search space; equation `(SFP2)` itself
has the direct proof below and does not depend on computation.
