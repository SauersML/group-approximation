---
rg: 2
id: computable-bcv-halt-bound-diagonal-proof
kind: route
title: Dovetail the bounded-factor upper hierarchy with quantum lower bounds
target: computable-bcv-halt-bound-diagonalizes-to-finite-readable-gap
requires:
  - bounded-readable-factor-zirs-value-has-computable-upper-hierarchy
---

For each machine `M`, compute its BCV tailored game `G_M` and the integer
`B(M)` from the hypothesis.  The prerequisite gives computable decreasing
upper bounds

```text
alpha_t -> omega_ZIRS^(B(M))(G_M).
```

In parallel, exhaustive finite-dimensional search gives computable increasing
lower bounds

```text
beta_t -> omega*(G_M).
```

Suppose, for contradiction, that every nonhalting `M` has

```text
omega_ZIRS^(B(M))(G_M) < 1.                              (CDP1)
```

The following dovetailing algorithm would decide whether `M` halts:

```text
accept if beta_t > 1/2,
reject if alpha_t < 1.
```

If `M` halts, BCV perfect completeness together with `(CBD1)` makes the
bounded-factor value and the quantum value both equal to one.  Thus rejection
never occurs and acceptance eventually occurs.  If `M` does not halt, BCV
soundness gives `omega*(G_M)<=1/2`, so acceptance never occurs, while
`(CDP1)` makes rejection eventually occur.  This contradicts
undecidability of the halting problem.

Therefore a nonhalting `M_0` violates `(CDP1)`.  Its bounded-factor value
is one, BCV soundness gives the second equality in `(CBD2)`, and compact
attainment in the prerequisite supplies an actual maximizing ZPC-IRS law,
not merely a sequence of bounded factors.  Its readable translate algebra
has at most `B(M_0)` atoms by definition.  This proves every assertion.
