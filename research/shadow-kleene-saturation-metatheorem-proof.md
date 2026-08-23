---
rg: 2
id: shadow-kleene-saturation-metatheorem-proof
kind: route
title: Diagonalize by proof enumeration, then invoke the one-word saturation compiler
target: shadow-kleene-saturation-metatheorem
requires:
  - single-shadow-word-saturation-compiler
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
---

Kleene's recursion theorem gives a machine which computes its own compiled
presentation and halts exactly when proof enumeration finds `w=1`.  Halting
would contradict the HALT-survival clause.  Therefore it does not halt.  If
`w` were trivial, one finite derivation would eventually appear, so the same
nonhalting proves `w!=1`.  The NONHALT clause puts this nontrivial word in the
shadow residual.  Apply `single-shadow-word-saturation-compiler`.
