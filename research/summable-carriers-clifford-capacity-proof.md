---
rg: 2
id: summable-carriers-clifford-capacity-proof
kind: route
title: Intersect the central carriers and apply finite Clifford divisibility at every rank
target: summable-reducing-carriers-force-infinite-clifford-capacity
requires: []
---

For finite projections `P,Q`,

```text
codim(Ran(P) intersect Ran(Q)) <= codim Ran(P)+codim Ran(Q).
```

Induction gives, for `C^(m)=meet_(N<=m) C_N`,

```text
tau(C^(m)) >= 1-sum_(N<=m) tau(1-C_N).
```

The decreasing sequence of subspaces `C^(m)H` stabilizes because `H` is
finite dimensional.  Its stable value is `CH`, and `(SRC1)` gives `(SRC3)`.

Every `C_N` is central in `A`, hence so is their meet `C`.  Since `C<=C_N`,
the relations `(SRC2)` restrict to `CH`.  The universal complex algebra of
`N` commuting Pauli pairs is the tensor product of `N` copies of `M_2(C)`,
hence `M_(2^N)(C)`.  Every nonzero finite-dimensional unital module over that
full matrix algebra has dimension divisible by `2^N`.  Thus `(SRC4)` holds
for all `N`.  Choosing `N>log_2 rank(C)` is impossible.

No compactness, approximation, or trace-class interchange is used; this is
ordinary finite-dimensional linear algebra.  `requires: []` is a proof
commitment.
