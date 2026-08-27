---
rg: 2
id: isomorphic-extraspecial-packet-complex-folds
kind: claim
title: A complex of isomorphic extraspecial packets folds to finite holonomy
distinct_from:
  finite-sign-safe-base-has-bounded-pauli-capacity: that is the sign-matrix rank ceiling for one finite coset base; this gives an explicit fixed-dimensional folding model for a whole graph of identical packets.
  commuting-schur-replicas-force-exponential-dimension: that requires genuinely commuting independent replicas; this shows full-packet transport identifications do not create such independence.
---

Let `K` be a finite extraspecial `2`-group with characteristic central
involution `J`.  Consider any graph of groups whose vertex groups are copies
of `K` and whose edge maps identify the **whole** packet by automorphisms of
`K`.  Its fundamental group has a quotient

```text
K semidirect Aut(K)                                             (IEP1)
```

which is finite and in which every vertex copy of `J` has the same nontrivial
image.

Therefore arbitrarily many transported copies of one finite packet admit a
fixed-dimensional exact unitary model with `J=-1`.  Full-packet holonomy,
even around an unbounded small-cancellation skeleton, cannot be the source of
an unbounded Pauli dimension witness.

A surviving complex-of-groups construction must use proper/rank-growing
edge attachments which prevent this finite holonomy folding, while still
retaining one exact infinite representation and a uniform HS decoder.
