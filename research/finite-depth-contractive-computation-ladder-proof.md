---
rg: 2
id: finite-depth-contractive-computation-ladder-proof
kind: route
title: Retain the terminal term and absorb it below half the marked floor
target: finite-depth-contractive-computation-ladder
requires: []
---

Iterating `(FDL1)` exactly `m` times gives

```text
a_0 <= lambda^m a_m
       +C sqrt(E) sum_(n=0)^(m-1) lambda^n p(n)
    <= lambda^m A+C S_m sqrt(E),
```

which is `(FDL3)`.  Combine this with `(FDL2)`:

```text
a_*-lambda^m A <= (K_0+C S_m)sqrt(E).
```

If `lambda^m A<=a_*/2`, the left side is at least `a_*/2`.  Squaring and
rearranging proves `(FDL4)`.  Since `lambda^m A` tends to zero and all of
`lambda,A,a_*` are fixed construction constants, such an `m` is finite and
independent of matrix dimension.

The argument deliberately makes no numerical claim until the compiler
constants `C,K_0,A,a_*` are known.  In particular, the existence of a
positive floor is unconditional under `(FDL1)--(FDL2)`, while any advertised
decimal floor must be recomputed from the actual packet comparison bounds.
