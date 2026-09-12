---
rg: 2
id: reversible-xor-has-linear-observable-rank
kind: claim
title: A reversible two-track automaton has observable rank exactly 2n plus 3
distinct_from:
  finite-pattern-orbit-closure-forces-surjunctivity: that gives a sufficient criterion and notes unbounded growth; this computes the exact unsaturated Hilbert rank and refutes a universal sublinear upper bound.
  split-ca-defects-force-linear-observable-rank: that gives a necessary positive-rank tower for a strict encoder; this has zero defect and nonetheless has exactly linear total observable rank.
artifacts:
  - research/artifacts/gottschalk-observable-growth-2026-09-07.md
---

Over Z with alphabet F_2^2, the reversible rule

    tau(a,b)_j=(a_j XOR b_j,b_(j+1))

and its unique decoder

    sigma(a,b)_j=(a_j XOR b_(j-1),b_(j-1))

have d_n=2n+3 for every n>=0, with the unsaturated observable dimensions
defined in split-ca-defects-force-linear-observable-rank. Their reverse
defect has delta=0. The same exact count holds for the saturated Walsh
pattern-orbit module.

Thus a universal sublinear observable-rank bound on injective automata
is false, even allowing a choice of local decoder. Linear growth alone
does not detect a strict full-shift embedding. This does not refute
Gottschalk's conjecture: the displayed automaton is bijective.
