---
rg: 2
id: full-overlap-rationalization-proof
kind: route
title: Evaluate every overlap atom and rationalize the resulting polytope
target: tracial-bcs-rationalizes-full-overlap-distributions
requires: []
---

For a tracial state `tau`, let `P_(c,a)` be the context atom and set
`mu_(c,a)=tau(P_(c,a))`.  For `S=U_c intersect U_d`, the common overlap atom

```text
Q_sigma=product_(x in S) (1+sigma_x X_x)/2              (RFO2)
```

is well defined because all variables of `S` commute.  Expanding `(RFO2)` in
either context gives

```text
Q_sigma=sum_(a:a|_S=sigma)P_(c,a)
       =sum_(b:b|_S=sigma)P_(d,b).
```

Applying `tau` proves `(RFO1)` for a real feasible point.  The finite system
consisting of nonnegativity, context normalization, and all equations
`(RFO1)` has rational coefficients.  Every nonempty rational polytope contains
a rational point, as in `rational-balanced-hyperoctahedral-atlas-proof`.
Clearing denominators gives equal cardinalities in each overlap-pattern
fiber, and arbitrary fiberwise bijections intertwine all signs in `S`.
