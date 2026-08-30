---
rg: 2
id: directed-unions-preserve-trace-approximations
kind: claim
title: Directed unions detect amenability and quasidiagonality of traces
distinct_from:
  stw99-problem-x1-amenable-traces-quasidiagonal: this is a locality theorem for each approximation property separately, not the implication between them.
  directed-unions-preserve-tracial-strict-comparison: that concerns Cuntz comparison from dimension functions; this concerns matrix u.c.p. approximations of a fixed trace.
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Let `A` be a unital C*-algebra, `tau` a tracial state, and `(A_i)` an upward
directed family of unital C*-subalgebras with norm-dense union.  Then:

1. `tau` is amenable on `A` if and only if every restriction `tau|A_i` is
   amenable.
2. `tau` is quasidiagonal on `A` if and only if every restriction `tau|A_i`
   is quasidiagonal.

Consequently, if an amenable trace is not quasidiagonal, its restriction to
some separable unital C*-subalgebra is amenable and not quasidiagonal.
