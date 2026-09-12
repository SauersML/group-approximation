---
rg: 2
id: stw07-trace-obstruction-forces-nonqd-trace-and-non-uct
kind: claim
title: The trace-positive K_0 obstruction needs a nonquasidiagonal trace and a non-UCT nuclear quotient
distinct_from:
  stw07-qd-trace-positive-class-kills-qd-extension: that says the obstruction produces a counterexample; this says what any algebra carrying the obstruction must already violate.
  amenable-traces-on-exact-cstar-algebras-are-quasidiagonal: that is the open exact residual of X(1); this shows the obstruction would refute it.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**ESTABLISHED (Theorem E of the artifact).**  Let `A` be separable, unital,
nuclear and quasidiagonal, and let `x in K_0(A)` be singular with `x^ > 0` on
every quasidiagonal tracial state.  Then some tracial state `sigma` of `A`
has `x^(sigma) <= 0` and is not quasidiagonal.  The quotient
`A/J_sigma` by its trace kernel is separable and nuclear, carries the
faithful amenable non-quasidiagonal trace induced by `sigma`, and does **not**
satisfy the UCT.

Hence every counterexample to STW Problem VII produced by
`stw07-qd-trace-positive-class-kills-qd-extension` simultaneously refutes the
exact residual of Problem X(1) and gives a separable nuclear algebra outside
the UCT class (STW Problem II).

Proof: `stw07-singular-classes-change-sign-or-sit-on-boundary` supplies
`sigma`.  A quasidiagonal trace on `A/J_sigma` pulls back along the quotient
map to a quasidiagonal trace on `A`.  And Tikuisis--White--Winter's theorem
(a faithful amenable trace on a separable nuclear UCT algebra is
quasidiagonal) is recorded here through
`tww-gabe-schafhauser-af-embedding-theorem`, whose trace-extending form
(Schafhauser) gives quasidiagonality of the trace.
