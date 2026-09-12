---
rg: 2
id: qd-nuclear-algebra-with-qd-trace-positive-singular-class
kind: claim
title: Some separable unital nuclear quasidiagonal algebra has a singular K_0-class positive on its quasidiagonal traces
distinct_from:
  stw07-qd-trace-positive-class-kills-qd-extension: that is the established implication from such an algebra to a Problem VII counterexample; this is the open existence input.
  amenable-traces-on-exact-cstar-algebras-are-quasidiagonal: that is the positive statement that all amenable traces are quasidiagonal; this asks for a failure of it that is additionally separated from the quasidiagonal traces by one K_0-class.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**OPEN.**  There exist a separable, unital, nuclear, quasidiagonal `A` and
`x in K_0(A)` with `Zx cap K_0^+(A) = {0}` and `(Tr tensor tau)(x) > 0` for
every quasidiagonal tracial state `tau`.

By `stw07-qd-trace-positive-class-kills-qd-extension` this gives a negative
answer to STW Problem VII.

## Attempts

- **Algebras all of whose traces are quasidiagonal: impossible.**  By
  `stw07-singular-classes-change-sign-or-sit-on-boundary`, a singular class is
  never strictly positive on all traces.  This excludes every algebra whose
  trace-kernel quotients satisfy the UCT, in particular type I, bootstrap and
  all-quotients-UCT algebras.
- **What any witness costs.**  `stw07-trace-obstruction-forces-nonqd-trace-and-non-uct`:
  a witness has a nonquasidiagonal trace, so the exact residual of X(1) fails,
  and a nuclear quotient outside the UCT class.  So this hole sits strictly
  behind two open negative answers.  It needs a nonquasidiagonal amenable
  trace on a nuclear algebra, plus enough `K_0` to separate it from the
  quasidiagonal traces.  Enlarging `K_0` by tensoring changes the trace space,
  and no such separation construction is recorded.
