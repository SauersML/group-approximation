---
rg: 2
id: full-packet-cyclic-aggregate-gram-proof
kind: route
title: Bound the Whitehead Gram on the two odd cyclic orbit joins
target: full-packet-cyclic-aggregates-retain-positive-endpoint-gram
requires:
  - endpoint-order-five-actor-has-half-gram
---

For any finite family of projections, the trace of their join is at most
the sum of their traces.  Every conjugate in `(FCA2)` has trace `tau(p)`,
which proves `(FCA3)`.  Cyclically permuting the family proves that `E_U`
is `U`-invariant.

Let `Q_U=W E_U W`.  The established projection

```text
p*=p(WpW)
```

is below both `E_U` and `Q_U`, proving `(FCA4)`.  For projections `E,Q` and
any projection `f<=E,Q`, positivity and cyclicity of trace give

```text
||EWE||_2^2
 =tau(EWEWE)
 =tau(E(W E W))
 =tau(EQ)
 >=tau(f).                                              (1)
```

Apply `(1)` with `E=E_U`, `Q=Q_U`, and `f=p*`.  By the signed-sheet theorem,

```text
tau(p*) >= (1/3)tau(p).                                (2)
```

Combining `(2)` with `tau(E_U)<=ord(U)tau(p)` yields

```text
||E_U W E_U||_2^2 >= tau(E_U)/(3 ord(U)).              (3)
```

The orders five and seven give `(FCA5)`.  The meet projection itself is a
valid positive common corner, but neither `(1)` nor the join construction
makes it `U`-invariant.  This is exactly why `(3)` supplies a cross Gram but
does not by itself let the odd cyclic relator act on its polar corner.
