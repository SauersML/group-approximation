---
rg: 2
id: instance-modulated-kleene-microstate-diagonal-proof
kind: route
title: Let the fixed-point search read its own compiled thresholds before searching
target: instance-modulated-kleene-microstate-diagonal
requires: []
---

By Kleene's recursion theorem, construct a machine `M_*` which obtains its
own index and computes

```text
(G_(M_*), w_(M_*), delta_(M_*), alpha_(M_*)).
```

It then chooses computable rationals

```text
0<delta_0<delta_(M_*),
alpha_(M_*)<gamma<sqrt(2),
```

and searches a computable dense family of finite-dimensional unitary tuples
for a strict witness

```text
Def_(R_(M_*))(U)<delta_0,
||w_(M_*)(U)-I||_2>gamma.                                        (IMK3)
```

Strict inequalities make the search semidecidable.  Upon finding a witness
in dimension `D`, the machine halts and outputs that same positive integer.

If `M_*` halted, `(IMK3)` would contradict the dimension-matched soundness
`(IMK2)` for its output `D`.  Hence it does not halt, and `(IMK1)` gives
`w_(M_*)!=1`.

If `G_(M_*)` were hyperlinear, its canonical trace would supply matrix
microstates with relator defect tending to zero and marked distance tending
to `sqrt(2)`.  Since `delta_(M_*)` is one fixed positive number and
`alpha_(M_*)<sqrt(2)`, eventually a strict witness `(IMK3)` would exist.
Density makes the search find it, contradicting nonhalting.  Therefore
`G_(M_*)` is nonhyperlinear.
