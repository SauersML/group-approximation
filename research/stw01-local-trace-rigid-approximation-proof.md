---
rg: 2
id: stw01-local-trace-rigid-approximation-proof
kind: route
title: Approximate each self-adjoint pair in one trace-rigid subalgebra
target: stw01-local-trace-rigid-models-force-linearity
requires: []
artifacts:
  - research/artifacts/stw01-quasitrace-status-and-local-permanence-audit-2026-08-30.md
---

Let `tau` be a bounded 2-quasitrace on `A`.  Its restriction to any unital
C*-subalgebra is again a bounded 2-quasitrace.  Fix self-adjoint `x,y in A`
and `epsilon>0`.  Apply `(QL1)` to `{x,y}` and replace the approximants by
their self-adjoint parts to obtain self-adjoint `b,c in B` with

```text
||x-b||<epsilon,             ||y-c||<epsilon.          (QL2)
```

The restriction `tau|B` is a trace, so

```text
tau(b+c)=tau(b)+tau(c).                                (QL3)
```

For self-adjoint `r,s` with `||r-s||<=delta`, order gives

```text
s-delta 1 <= r <= s+delta 1.
```

A quasitrace is monotone on self-adjoint elements, and it is additive on
commuting self-adjoint elements.  Since `s` commutes with `1`,

```text
|tau(r)-tau(s)| <= delta tau(1).                       (QL4)
```

Apply `(QL4)` to `(x,b)`, `(y,c)`, and `(x+y,b+c)`, then use `(QL3)`.
It follows that

```text
|tau(x+y)-tau(x)-tau(y)| <= 4 epsilon tau(1).
```

Letting `epsilon` tend to zero proves additivity on all self-adjoint pairs.
The complexification axiom for a 2-quasitrace then makes `tau` linear on
`A`; the quasitrace identity `tau(z*z)=tau(zz*)` says precisely that this
positive linear functional is tracial.
