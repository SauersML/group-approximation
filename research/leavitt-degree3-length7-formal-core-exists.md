---
rg: 2
id: leavitt-degree3-length7-formal-core-exists
kind: claim
title: A degree-three length-seven cyclic word realizes a formal long-corner two-core
artifacts:
  - research/artifacts/search-degree3-formal-long-corner-core.py
distinct_from:
  leavitt-degree3-formal-corner-cycle-is-absent: that excludes the sharp cycle for seven distinct packet letters and four identities at length eleven; this permits repeated occurrences of one formal coefficient.
---

Over the one-letter formal coefficient alphabet `{1,x,x^(-1)}`, lengths three
and five have no degree-three cyclic topology in which two unary corners both
recur in distinct corners of a non-unary orbit.  The first example has length
seven:

```text
signs = (-,+,+,+,+,-,+),
slots = (1,x,x,x,1,x^(-1),x^(-1)).
```

Equivalently, the cyclic equation word is

```text
t^(-1) x t x t x t^2 x^(-1) t^(-1) x^(-1) t.
```

In the degree-three cover, exact free-product reduction gives unary corners
`H=x_2` and `Y=x_0`.  The remaining orbit has signed corners

```text
(-,H), (+,x_0 x_1), (+,Y^(-1)), (-,H^(-1)), (+,1).
```

Thus `H` and `Y` both have incidence degree at least two after adjoining the
second-unary relation `YH^(-1)`: the long-corner peeling core is nonempty.
This is an incidence realization only.  It does not kill `[c,d]`; a marked
`D`-corner still has to be coupled into this core.
