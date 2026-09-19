---
rg: 2
id: stw95-purity-inductive-limit-proof
kind: route
title: Lift compactly contained inequalities to one pure Cu stage
target: stw95-purity-passes-to-sequential-inductive-limits
requires: []
---

Write `S_n=Cu(A_n)` and `S=lim S_n=Cu(lim A_n)`.  We use the concrete
description of sequential colimits in `Cu`: every element of `S` is the
supremum of a rapidly increasing sequence of stage images; a compactly
contained piece of such a supremum is dominated at one stage; and an
inequality whose left side is compactly contained lifts, after moving far
enough forward, to an inequality at one common stage.

First prove almost unperforation.  Suppose

```text
(r+1)x <= r y                                           (U1)
```

in `S`, and fix `x'<<x`.  Choose two elements `a'<<a` at one stage whose
images satisfy

```text
x' <= image(a') << image(a) << x                       (U2)
```

for two elements `a'<<a` at one stage.  Addition preserves compact
containment, so `(r+1)image(a)` is compactly contained in `(r+1)x` and hence
is dominated by `r` times one stage approximant of `y`.  Move all elements
to one common later stage.  The colimit lifting property, applied to
`(r+1)a'<<(r+1)a`, then gives a stage element `b` such that

```text
(r+1)a' <= r b.                                        (U3)
```

Almost unperforation of that stage gives `a'<=b`.  Returning to the limit
yields `x'<=y`.  Since this holds for every `x'<<x`, the Cu axioms give
`x<=y`.

Now prove almost divisibility.  Fix `x'<<x` in `S` and a positive integer
`r`.  The colimit description supplies stage elements `a'<<a` with

```text
x' <= image(a'),             image(a)<=x.             (D1)
```

Almost divisibility of that stage supplies `z` such that

```text
r z <= a,                   a' <= (r+1)z.              (D2)
```

Its image in `S` satisfies

```text
r image(z)<=x,              x'<=(r+1)image(z),
```

which is almost divisibility of `S`.  Thus `S` has both purity axioms, so
the C*-inductive limit is pure.
