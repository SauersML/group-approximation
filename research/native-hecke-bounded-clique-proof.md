---
rg: 2
id: native-hecke-bounded-clique-proof
kind: route
title: Count the two finite Hecke shells and bound simultaneous lamp atoms
target: native-hecke-edge-rank-integrality-is-bounded
requires:
  - native-sl3-group-is-hecke-graph-wreath-product
  - commuting-conjugate-involution-is-balanced-overlap
---

An edge incident to `C` is an `A`-translate of the unordered prototype edge.
If its first endpoint is `C`, the translating element lies in `C`, producing
the shell `ChC/C`.  If its second endpoint is `C`, reversing the prototype
produces `Ch^-1C/C`.  Their cardinalities are the two commensurability
indices in `(BRI1)`.  This proves the degree and clique bounds.

On a clique, functional calculus gives commuting self-adjoint involutions.
The projection onto a joint sign `epsilon in {+1,-1}^k` is

```text
E_epsilon=2^-k product_j (1+epsilon_j c_j).
```

If canonical trace separation kills every nonempty product of distinct
vertex lamps, expanding the product gives

```text
tr(E_epsilon)=2^-k+o(1)
```

uniformly over the fixed clique.  Thus the only direct integrality demand is
the fixed packet of `2^k` approximately equal atom ranks.  Since `k` is
uniformly bounded, tensoring by spectators removes any dimension obstruction.
