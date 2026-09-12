---
rg: 2
id: dimension-matched-kleene-microstate-diagonal-proof
kind: route
title: Make the fixed-point search print the dimension of its own bad witness
target: dimension-matched-kleene-microstate-diagonal
requires: []
---

Choose computable rationals

```text
0<delta_0<delta,                 alpha<gamma<sqrt(2).
```

By Kleene's recursion theorem, construct a machine `M_*` which obtains its
own index, computes `(G_(M_*),w_(M_*))`, and searches a computable dense family
of finite-dimensional unitary tuples for a witness

```text
Def_(R_(M_*))(U)<delta_0,        ||w_(M_*)(U)-I||_2>gamma.         (DMK3)
```

The inequalities are strict, so the search is semidecidable.  When it finds a
witness in dimension `D`, the machine halts and outputs that same integer `D`.

If `M_*` halted, its witness would have dimension `D`, defect below `delta`,
and marked distance above `gamma>alpha`, contradicting the dimension-matched
soundness `(DMK2)`.  Hence it does not halt, and `(DMK1)` gives
`w_(M_*)!=1`.

If `G_(M_*)` were hyperlinear, the canonical trace would supply matrix
microstates with relator defect tending to zero and marked distance tending to
`sqrt(2)`.  Eventually a strict witness `(DMK3)` would exist; density makes the
search find one, contradicting nonhalting.  Thus `G_(M_*)` is nonhyperlinear.

