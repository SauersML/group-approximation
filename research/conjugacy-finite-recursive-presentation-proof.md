---
rg: 2
id: conjugacy-finite-recursive-presentation-proof
kind: route
title: Enumerate the conjugacy classes against the word problem
target: conjugacy-finite-recursive-presentation-solvable-wp
requires: []
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Complete direct proof, written out in the target node.  No Lean counterpart
exists; the statement is a standard complementary-enumeration argument and
would formalize against a computability development the repository does not
have.

The one step that is easy to get wrong is uniformity: the class
representatives are not produced by any algorithm from the presentation, and
the argument does not claim they are.  Decidability of a fixed group's word
problem is an existence statement about an algorithm, so a non-uniform choice
of finitely many representatives is legitimate.  Nothing downstream asks for
a uniform version, and a uniform version is false for the obvious reason that
`k` is not computable from a presentation.
