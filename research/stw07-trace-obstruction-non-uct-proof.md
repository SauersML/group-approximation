---
rg: 2
id: stw07-trace-obstruction-non-uct-proof
kind: route
title: Find the nonpositive trace, pass to its trace-kernel quotient, and apply the UCT quasidiagonality theorem
target: stw07-trace-obstruction-forces-nonqd-trace-and-non-uct
requires: [stw07-singular-classes-change-sign-or-sit-on-boundary, tww-gabe-schafhauser-af-embedding-theorem]
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

Artifact Section 5.

- The boundary claim gives a tracial state `sigma` with `x^(sigma) <= 0`;
  that value excludes quasidiagonality of `sigma`.
- `J_sigma = {a : sigma(a*a)=0}` is a closed ideal.  The induced trace on
  `A/J_sigma` is faithful and amenable, because the quotient is nuclear.
- Models of the quotient composed with the quotient map are models of `A`.
  So if the induced trace were quasidiagonal, `sigma` would be.
- A trace-extending AF embedding (the UCT theorem) makes a faithful trace
  quasidiagonal.  Hence `A/J_sigma` is not UCT.
