---
rg: 2
id: root-transported-outliers-have-positive-ucp-gap
kind: claim
title: Root-transported arithmetic actor outliers have a positive lattice UCP gap
refuted_by: balanced-denominator-transport-is-ucp-neutral
distinct_from:
  sl3-large-prime-hnn-matrix-range-capture: that asks for an upper bound tending to zero on packets satisfying the full arithmetic HNN presentation; this false intermediate assertion asks for a positive lower bound from actor noncorrectability plus balanced root transport.
---

**REFUTED INTERMEDIATE BRIDGE.**  A tempting use of the one-Britton
noncorrectability theorem is to regard a uniform arithmetic actor outlier as
a latent Choi obstruction, and then use the native relation

```text
h e_12(1) h^(-1)=e_12(p)
```

to expose it as a positive distance from the lattice UCP matrix range.

`balanced-denominator-transport-is-ucp-neutral` proves this false.  Its
finite packet has exact root transport, exact lattice centrality, zero
one-Britton commutator trace, and the uniform actor-outlier lower bound, but
its lattice tuple is the image of an honest representation and hence has
matrix-range distance zero.  The same packet satisfies every arithmetic
relation of total denominator exponent zero.

This refutation does not decide whether the full unbalanced arithmetic
closure can force matrix-range **capture**.  It says precisely that actor
noncorrectability cannot first be converted into a positive UCP defect, even
after adding all balanced denominator-conjugacy relations.
