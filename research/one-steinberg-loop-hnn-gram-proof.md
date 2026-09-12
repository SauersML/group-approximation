---
rg: 2
id: one-steinberg-loop-hnn-gram-proof
kind: route
title: Equal actor words give the same coset permutation and the same lamp atom
target: one-steinberg-loop-is-hnn-gram-neutral
requires:
  - free-hnn-outlier-has-dyadic-a2-pvm-tower
---

Let `u=x_23(1)`, `v=x_31(-1)`, and `w=x_21(-1)`.  Equation `(SNG1)` says
`uvu^(-1)v^(-1)=w` in the actor.  Covariance `(DPT3)` therefore gives

```text
q_(r,j)^([u,v]x)=q_(r,j)^(wx)                           (SNP1)
```

as equality of projections, not merely equality of traces.  Pair either
side with an arbitrary atom `q_(s,l)^y`.  If the endpoint coset equals `y`,
same-coset PVM calculus gives the corresponding nested-atom intersection.
If it differs from `y`, equation `(DPT4)` gives `2^(-r-s)`.  Thus the two
paths have identical pairings against every atom for the formal reason that
they are the same actor element.  No new Gram direction is produced.
