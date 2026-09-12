---
rg: 2
id: trace-functorial-bcs-signal-groupification-impossible-proof
kind: route
title: Apply the hypothetical decoder to the regular trace
target: trace-functorial-bcs-signal-groupification-impossible
requires:
  - self-referential-bcs-nonzero-signal-collapse
---

Let `tau_reg` be the canonical trace of the left regular representation of
`Gamma`. Since `w!=1`,

```text
tau_reg((w-1)^*(w-1))=2.
```

The hypothetical decoder produces a perfect strategy `S_(tau_reg)`. Apply
`(SBS2)` at `epsilon=0` to get

```text
phi_(S_(tau_reg))(D)=0.
```

But `(TFG)` gives `phi_(S_(tau_reg))(D)>=2c>0`, a contradiction.

The obstruction is not that the regular representation is finite
dimensional; it is precisely that any algebraic trace-functorial decoder also
acts on this infinite-dimensional tracial representation. A viable compiler
must separate finite matrix algebras from the regular finite von Neumann
algebra by a non-functorial quantitative mechanism.
