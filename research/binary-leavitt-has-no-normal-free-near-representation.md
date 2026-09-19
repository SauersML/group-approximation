---
rg: 2
id: binary-leavitt-has-no-normal-free-near-representation
kind: claim
title: The binary Leavitt unit group has no essentially free near representation with a normal invariant state
distinct_from:
  binary-leavitt-unit-group-fails-factorization-property: that excludes the abstract factorization property; this translates that exclusion into the exact state-form near-representation language relevant to the unresolved hyperlinearity fork.
  binary-leavitt-unit-group-hyperlinear: that asks whether any hyperlinear witness exists; this rules out only the entire normal-state sector and leaves genuinely non-normal states open.
---

Write

```text
Q=L_(F_2)(1,2)^x.
```

There do not exist a Hilbert space `H`, a **normal** state `phi` on `B(H)`, and
a `phi`-near representation `pi:Q -> U(H)` such that

```text
phi(pi(g))=0                         for every g != 1.   (BLN1)
```

Indeed `normal-state-free-near-representation-forces-factorization` would
turn such a triple into Kirchberg's factorization property for `Q`, whereas
`binary-leavitt-unit-group-fails-factorization-property` proves that `Q`
does not have that property.

Thus any state-form Kahl--Schneider witness of hyperlinearity for the first
nonsofic group must be genuinely non-normal.  In particular it cannot be
represented by a trace-class density operator, by a finite convex combination
of vector states, or by any countably additive atomic diagonal state with
`ell^1` weights.
