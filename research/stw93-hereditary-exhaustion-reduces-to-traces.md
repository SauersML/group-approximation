---
rg: 2
id: stw93-hereditary-exhaustion-reduces-to-traces
kind: claim
title: A trace-rigid hereditary exhaustion reduces the residual XCIII leaf exactly to bounded traces
distinct_from:
  stw93-residual-trace-kernel-is-quasitrace-null: that is the still-open unconditional annihilation assertion; this theorem identifies exactly what remains after a specified hereditary quasitrace-linearity hypothesis is verified.
  stw93-singular-trace-kernel-witness-for-any-negative-answer: that theorem localizes an arbitrary negative quasitrace at one positive trace-kernel element; this theorem makes every such quasitrace linear under a hereditary exhaustion and identifies a bounded residual trace as the exact obstruction.
  stw93-all-z-central-slices-generate-quasitrace-null-ideal: that theorem enlarges the removable Jiang--Su-generated ideal; this theorem works after that quotient and does not assert that the slice-generated ideal exhausts the trace kernel.
  stw01-extensions-preserve-qt-linearity: that is the abstract three-space theorem used here; the present result supplies the residual hereditary local-to-global step and converts XCIII invisibility into residual bounded-trace-freeness.
artifacts:
  - research/artifacts/stw93-hereditary-exhaustion-audit-2026-08-30.md
---

Use the notation

```text
bar(D)=D/K_Z^sat,             R=I/K_Z^sat triangleleft bar(D)
```

from `stw93-all-z-central-slices-generate-quasitrace-null-ideal`.  Suppose
that `R` has a family of sigma-unital hereditary C*-subalgebras `(H_lambda)`
such that

1. every finite subset of `R` is contained in some `H_lambda`; and
2. every bounded `2`-quasitrace on every `H_lambda` is a trace.

Then every bounded `2`-quasitrace on `R` is a trace, and the following are
equivalent:

```text
(a) every normalized 2-quasitrace on bar(D) annihilates R;
(b) R carries no nonzero bounded trace;
(c) bar(D) has a unique normalized trace;
(d) bar(D) has a unique normalized 2-quasitrace.
```

Consequently such a hereditary exhaustion closes the residual XCIII leaf
exactly when one also proves bounded-trace-freeness of `R`.  Exhaustion by
sigma-unital, even finite-dimensional, quasitrace-rigid pieces alone cannot
force annihilation.

The exhaustion hypothesis is implied by the formally stronger statement
that every sigma-unital hereditary subalgebra of `R` has quasitrace
linearity.
