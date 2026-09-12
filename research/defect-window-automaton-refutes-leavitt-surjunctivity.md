---
rg: 2
id: defect-window-automaton-refutes-leavitt-surjunctivity
kind: route
title: An injective automaton with a Garden of Eden on the defect window is strict
target: leavitt-unit-group-nonsurjunctive
requires: [defect-window-automaton-over-leavitt-units]
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

A Garden-of-Eden pattern is a pattern no configuration in the image contains, so
`tau` is not surjective, and the left inverse makes it injective. That is the
target.

This is a narrowing, not a rename. The prerequisite fixes both the window, a
commutator of the compression configuration, and the certification, a left
inverse automaton. The target allows any injective non-surjective automaton with
any window.
