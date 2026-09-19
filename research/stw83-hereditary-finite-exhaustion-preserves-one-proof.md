---
rg: 2
id: stw83-hereditary-finite-exhaustion-preserves-one-proof
kind: route
title: Apply gauge-invariant uniqueness to hereditary graph inclusions and then inductive-limit permanence
target: stw83-hereditary-finite-exhaustion-preserves-one
requires: []
---

Fix `n`.  Heredity says that every edge emitted by a vertex of `H_n` remains in
`H_n`.  Row-finiteness therefore makes the Cuntz--Krieger equality at each
regular vertex of `E_n` identical to its equality in `E`.  The canonical vertex
projections in `C*(E)` are nonzero, and the generator assignment intertwines the
gauge actions.  The gauge-invariant uniqueness theorem consequently gives an
injective *-homomorphism

```text
C*(E_n) -> C*(E).
```

The same argument gives the connecting inclusion from `E_n` to `E_(n+1)`.
Every edge belongs to some `E_n`, because its source and range eventually lie in
one `H_n`, and every vertex does as well.  Thus the increasing union of the
images contains all canonical generators of `C*(E)` and is dense.

Finally, Winter--Zacharias, Proposition 2.3, gives

```text
dim_nuc(C*(E)) <= liminf_n dim_nuc(C*(E_n)) <= 1.
```

No extension estimate is used, so there is no additional color.
