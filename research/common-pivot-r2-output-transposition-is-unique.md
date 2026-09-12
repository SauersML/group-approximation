---
rg: 2
id: common-pivot-r2-output-transposition-is-unique
kind: claim
title: A fixed input arm and pivot uniquely determine the transposition output of an R2 cell
invalidates:
  - different-private-r2-endpoint-closes-fixed-mixed-cell
distinct_from:
  mixed-r2-boundary-is-one-finite-mark-centralizer-commutator: that rewrites a general mixed boundary as a finite-mark commutator and rules out escaping relative gauges; this is the finite six-letter classification of every possible transposition output before any gauge is introduced.
  depth-three-bq-arm-expansion-is-equivariant-under-label-flip: that computes the canonical Bleak--Quick words and their label-flip symmetry; this proves that no different private transposition in the second chart can replace the canonical output while retaining the same input and pivot.
---

Let `i,j,p,q` be distinct letters and put

```text
s=(i p),                 r=(p q),                 f=(i j).
```

If `t` is a transposition and

```text
t s t = r,                                                     (URO1)
```

then necessarily

```text
t=(i q).                                                       (URO2)
```

Indeed, conjugation by `t` sends the support `{i,p}` of `s` to the support
`{p,q}` of `r`.  A transposition moves at most two letters.  It cannot move
`p`: if `t(p)=q`, then the other endpoint `i` is fixed and the image support
is `{i,q}`; if `t(p)=i`, the support is unchanged.  Hence `t(p)=p`, and
`t(i)=q`, which is exactly `(URO2)`.

In the normalized depth-three adjacent Bleak--Quick seam, the first private
R2 output is

```text
t_i=(i q),
```

whereas every occurrence obtained from that output by the chart label flip
has

```text
t_i^f=(j q).
```

The latter is disjoint from `s`, so it cannot satisfy `(URO1)`.  More
generally, no other private transposition in the second chart's star at its
missing letter `j` satisfies `(URO1)`: uniqueness already forces the missing
letter to be `i`.

Consequently the fixed-local repair which merely chooses a different
second-chart **private R2 transposition** is impossible.  A surviving proof
of the mixed occurrence claim must do strictly more: a bounded interacting
diagram must retain or manufacture the first-chart word `(i q)` inside the
second contextual occurrence before the two gauges split.  The statement
does not rule out such a multi-cell diagram and does not claim that every
bounded R1--R5 mixed occurrence is impossible.

