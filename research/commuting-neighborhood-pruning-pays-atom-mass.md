---
rg: 2
id: commuting-neighborhood-pruning-pays-atom-mass
kind: claim
title: A commuting neighborhood with no joint extension pays the whole central atom mass
distinct_from:
  one-gram-vector-decodes-a-finite-bcs-strategy: that sums all game rows against one Gram matrix; this is a local projection union bound requiring only mutual commutation of the neighboring PVM algebras and no common Gram operator.
  pairwise-cross-grams-do-not-supply-one-game-state: that warns separate edge Gram states need not glue; this gives a sufficient gluing condition, namely a joint PVM for the whole neighboring family.
---

ESTABLISHED.
Let `P` be a projection in a finite tracial matrix algebra and, for
`i=1,...,k`, let `(Q_(i,b))_b` be PVMs whose generated algebras commute for
different `i`.  Declare some pairs `(i,b)` bad.  If every joint tuple
`boldb=(b_1,...,b_k)` contains at least one bad coordinate, then

```text
tau(P)<=sum_i sum_(b:(i,b) bad)||P Q_(i,b)||_2^2.              (CNP1)
```

In particular, if every bad overlap vanishes, then `P=0`.  This contains the
usual pairwise pruning rule: an atom with no compatible atom in one neighbor
PVM vanishes.

No commutation between `P` and the neighbor PVMs is assumed.  Mutual
commutation among the neighbor algebras is load-bearing; without it there is
no joint refinement and pairwise compatible atoms need not define one joint
extension.
