---
rg: 2
id: non-hyperlinear-from-computable-hs-dehn-modulus
kind: route
title: Decide an undecidable word problem with microstates unless the group is nonhyperlinear
target: non-hyperlinear-group
requires:
  - unsolvable-word-problem-group-with-computable-hs-dehn-modulus
  - hyperlinear-computable-hs-dehn-modulus-solvable-word-problem
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Take the group of `unsolvable-word-problem-group-with-computable-hs-dehn-modulus`.
If it were hyperlinear,
`hyperlinear-computable-hs-dehn-modulus-solvable-word-problem`
would decide its word problem by racing relator enumeration against a
rational Cayley microstate search.  Hence it is an explicit finitely
presented nonhyperlinear group.

This is the self-reference-free form of `nonhyperlinear-from-hs-pcp-boone`:
the recursion-theorem machine is replaced by the undecidability of one
fixed word problem, and the machine-indexed compiler by one uniform
length-control estimate.
