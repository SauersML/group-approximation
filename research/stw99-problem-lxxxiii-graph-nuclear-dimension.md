---
rg: 2
id: stw99-problem-lxxxiii-graph-nuclear-dimension
kind: claim
title: Graph C*-algebras have nuclear dimension at most one (STW Problem LXXXIII, ENSW)
root: true
distinct_from:
  stw99-problem-lxxxii-nuclear-dimension-extensions: that asks the max formula for dimnuc of general extensions; this asks the sharp global bound one for all graph algebras, and would follow from the max formula along the gauge-invariant ideal structure in the finite-lattice case.
artifacts:
  - research/artifacts/stw99-master-ledger-2026-08-30.md
---

**Problem LXXXIII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Evington--?--Sims--White in-prep, Question C).  Is the nuclear
dimension of every graph C\*-algebra at most one?

## Attempts

* Known anchors: AF pieces have dimension zero; simple purely
  infinite graph algebras are UCT Kirchberg algebras of nuclear
  dimension one; stably finite simple ones are AF.  So every SIMPLE
  graph algebra has `dimnuc ≤ 1`, and the problem is pure extension
  bookkeeping: gauge-invariant ideal filtrations have AF/Kirchberg
  subquotients, and a positive Problem LXXXII (max formula) closes
  every FINITE ideal lattice case immediately; infinite lattices need
  the known order-zero tower arguments to be run uniformly.  A
  counterexample would need dimension created purely by an infinite
  ideal lattice of dimension-≤1 subquotients — no such phenomenon is
  known for any class; recorded as expected-positive with LXXXII as
  the load-bearing half.
