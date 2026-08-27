---
rg: 2
id: nonhyperlinear-from-hs-pcp-boone
kind: route
title: Let the HS-PCP Boone presentation search for microstates of itself
target: non-hyperlinear-group
requires:
  - hs-pcp-boone-compiler
  - kleene-self-destroying-microstate-lemma
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
---

Apply `kleene-self-destroying-microstate-lemma` to the compiler and constants
of `hs-pcp-boone-compiler`.  The recursion-theorem machine computes its own
finite presentation and marked word and searches for a finite-dimensional
microstate in the strict attack window.  A successful search contradicts the
halting soundness clause, so the machine does not halt; the nonhalting clause
makes its marked word nontrivial.  Hyperlinearity would force the search to
succeed.  Therefore the one fixed-point presentation output by the compiler is
an explicit finitely presented nonhyperlinear group.

