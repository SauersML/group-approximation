---
rg: 2
id: stw99-xciv-two-norm-centrality-does-not-control-norm-centrality
kind: claim
title: Tracial centrality in R can hide maximal norm noncentrality
distinct_from:
  stw99-hyperfinite-factor-property-si: property (SI) is a comparison statement in a relative ultrapower; this claim only proves that tracial-ultrapower representatives carry no automatic operator-norm centrality information.
---

There are a selfadjoint contraction `x in R` and unitaries `u_n in R` such
that

```text
||u_n-1||_2 -> 0,
||[u_n,y]||_2 -> 0                 for every y in R,
||[u_n,x]|| = 2                    for every n.
```

Thus `(u_n)` and the constant sequence `(1)` define the same element of the
tracial sequence algebra, even though one representative is maximally
noncentral in operator norm relative to the fixed singleton `{x}`.  In
particular, McDuffness or a property-(SI) construction performed only modulo
the trace-kernel ideal cannot be promoted to the norm-relative commutant
needed for separable `Z`-stability without an additional norm-control or
representative-selection argument.

This is an obstruction to that proof method, not a negative answer to Problem
XCIV and not a failure of property (SI).

