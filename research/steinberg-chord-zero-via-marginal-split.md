---
rg: 2
id: steinberg-chord-zero-via-marginal-split
kind: route
title: Split the Steinberg chord recurrence into marginal vanishing and local propagation
target: steinberg-chord-fox-recurrence-has-zero-solutions
requires:
  - steinberg-tree-cuts-are-five-marginals
  - steinberg-fox-recurrence-forces-zero-marginals
  - steinberg-zero-marginal-fox-recurrence-is-zero
---

The first open claim kills `P,H`, hence `A,C,T`.  The established marginal
formula then kills every exceptional tree-cut term.  The second open claim
kills the remaining local solution `f`, proving the target.
