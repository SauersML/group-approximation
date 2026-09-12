---
rg: 2
id: fanizza-c18-residual-factors-through-three-tiny-rank-gates-proof
kind: route
title: Greedily match the target child and substitute the affine phase bit before compiling
target: fanizza-c18-residual-factors-through-three-tiny-rank-gates
requires:
  - c18-child-oriented-gates-follow-the-two-source-words
  - ordered-bdd-compresses-predicate-rank-gate
artifacts:
  - experiments/fanizza_factored_c18_exit_compiler.py
---

The unmatched `p` child is `p(1-r)`.  The unmatched `q` child is
`q(1-r)+pqr`; the two terms are disjoint because their target bits differ.
Multiplication by the phase carrier gives `(FCR1)`, which the verifier checks
against `e_1+e_2` on all 64 assignments.

The best OBDD compilers for the two three-bit conjunctions have baseline rank
4; the four-bit conjunction has baseline rank 5.  Substitution of the affine
form `(FCR2)` preserves affinity of every entry and the rank truth table.

The exhaustive dual-word search then checks the 8, 8, and 4 lifted atoms.
Every search succeeds at word weight at most two.  The verifier asserts the
unique kernel code `52789443047427`, unique hard form
`(0,1,0,0,0,0)`, and one left/right word pair within each compressed gate.
The complete run takes under one second and 14 MB on one low-priority MSI
core.
