---
rg: 2
id: qd-trace-positive-class-from-k0-separated-nonqd-trace
kind: route
title: When K_0 separates traces, a nonquasidiagonal trace is off the quasidiagonal K_0-states, so a separating singular class exists
target: qd-nuclear-algebra-with-qd-trace-positive-singular-class
requires: [qd-trace-positive-class-iff-k0-state-off-qd-traces, trace-separating-k0-nuclear-qd-algebra-with-nonqd-trace]
artifacts:
  - research/artifacts/qd-trace-positive-class-k0-state-form-2026-09-16.md
---

Artifact Section 4 (Proposition 3).

Let `A` be separable, unital, nuclear and quasidiagonal, with `K_0(A)`
separating tracial states (`r_A: tau -> tau_*` injective), and let `sigma` be
a nonquasidiagonal tracial state.  The second required claim provides such an
`A`.

- For every `tau in T_qd(A)` we have `tau != sigma`, so injectivity gives
  `r_A(tau) != r_A(sigma)`.
- Hence `r_A(sigma) notin r_A(T_qd(A))`, and condition (c) of the first
  required claim holds.
- `A` is exact, being nuclear.  By (c) => (a), `A` has a singular `x in K_0(A)`
  with `(Tr tensor tau)(x) > 0` for every quasidiagonal tracial state `tau`.

This is the target.
