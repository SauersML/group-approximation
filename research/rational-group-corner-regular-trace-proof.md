---
rg: 2
id: rational-group-corner-regular-trace-proof
kind: route
title: Read every pulled-back moment as an identity coefficient
target: rational-group-corner-map-forces-rational-regular-trace
requires: []
---

For `x=sum_g c_g g in Q[Gamma]`, the canonical group trace is
`tau_Gamma(x)=c_1` after equal group elements have been collected.  Hence it
is rational on `Q[Gamma]`.  Faithfulness of the canonical trace on
`L(Gamma)` and `q!=0` give

```text
0<tau_Gamma(q)=c_(q,1) in Q.
```

The canonical trace is positive and tracial.  Its restriction to the corner,
divided by `tau_Gamma(q)`, is therefore a normalized positive trace.  Pulling
it back through the star homomorphism gives `(RRT2)--(RRT3)`.  Rationality is
preserved because both numerator and denominator are rational.

Multiplicatively expanding a rational word in the finite sums `(RRT4)` and
then applying the canonical trace retains exactly the tuples of support words
whose product is the identity.  This is `(RRT5)` and proves the stated
weighted word-problem formula.

