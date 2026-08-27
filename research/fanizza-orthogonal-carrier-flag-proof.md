---
rg: 2
id: fanizza-orthogonal-carrier-flag-proof
kind: route
title: Expand the projection sum and pass to reflection involutions
target: fanizza-doubling-carriers-form-orthogonal-flag
requires:
  - fanizza-bcs-polynomial-doubling-tape
---

If `A,B` and `A+B` are projections, expansion of `(A+B)^2=A+B` gives

```text
AB+BA=0.
```

Multiplying on the left and right by `A` gives `2ABA=0`; positivity of
`ABA=(BA)^*(BA)` gives `BA=0`, hence also `AB=0`.  Apply this with
`A=P_n` and `B=R_n` to obtain `(FOF2)`.  Induction in `(FOF1)` gives
`(FOF3)`.  Since `R_n` is orthogonal to `P_n`, it is orthogonal to every
earlier `P_0,R_0,...,R_(n-1)` contained in `P_n`.  This proves the pairwise
orthogonal flag.

For orthogonal projections `A,B`, their reflections commute and

```text
(1-2A)(1-2B)=1-2(A+B).
```

Substitution of `A=P_n`, `B=R_n` proves `(FOF4)`.

For the converse audit, commuting involutions give commuting projections
`A,B`, and direct expansion gives

```text
C=(1-(1-2A)(1-2B))/2=A+B-2AB.
```

Hence `A+B-C=2AB`.  Since `AB` is itself a projection,
`||2AB||_2^2=4tau(AB)`, proving `(FOF5)`.
