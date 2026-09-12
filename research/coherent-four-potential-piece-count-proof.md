---
rg: 2
id: coherent-four-potential-piece-count-proof
kind: route
title: Sum the four forced piece inequalities in one coherent pairing contour
target: coherent-four-potential-pairings-cannot-be-long-c-sixth
requires: []
---

In a symmetrized presentation, a reduced word appearing at two genuinely
different relator positions is a piece.  Recurrence therefore makes each of
the four displayed potential blocks `H_i` a piece.  The `C'(1/6)` condition
gives `6|H_i|<|r|`; summing over the four occurrences gives

```text
6L<4|r|=4(L+b),
```

so `L<2b` and `|r|<3b`.  In the commuting free-phase construction all packet
coefficients collect into one peripheral word, hence `b<=1` in the relative
alphabet, whereas four nonempty potential blocks give `L>=4`; this proves
the relative impossibility.  Bounded `b` also proves that increasing the
potential lengths cannot produce long ordinary `C'(1/6)` contours.

The expansion `WYW^*` labels every nonzero `(i,j)` coefficient by
`h_i h_j^(-1)`.  Hence any potential used by two paired coefficients supplies
the recurrence required above.  Occurrence-specific replacements no longer
have this form; restoring it is precisely the already identified cocycle
system.  This proves all clauses of the target claim.
