---
rg: 2
id: shrunk-matrix-space-unitary-distance
kind: claim
title: A linear-size shrunk subspace gives a normalized-HS distance floor from every unitary
---

Let `K` be a complex linear subspace of `M_d(C)`.  Suppose there is a subspace
`X <= C^d` such that, writing

```text
K(X) = span { T x : T in K, x in X },
```

one has the linear-size shrinkage

```text
dim X - dim K(X) >= gamma d                            (SMS1)
```

for some `gamma>0`.  Then every unitary `U in U(d)` satisfies

```text
inf_(T in K) ||U-T||_2^2 >= gamma,                     (SMS2)
```

where `||.||_2` is normalized Hilbert--Schmidt norm.

Thus a large shrunk subspace is not merely an algebraic noncommutative-rank
certificate.  It is a quantitative obstruction to approximating a unitary,
with a dimension-free loss equal to the fractional dimension deficit.

This is the operator-space analogue of weighted Hall deficiency.  When `K` is
the block-support matrix space of a bipartite graph, coordinate subspaces `X`
recover the usual Hall cuts.  For atlas finite-multiplicity work, however, `K`
may be selected from **low-energy singular directions inside blocks**, allowing
operator scaling / shrunk-subspace methods to see rank structure that a
zero-one block support graph discards.