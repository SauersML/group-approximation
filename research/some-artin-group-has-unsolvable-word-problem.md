---
rg: 2
id: some-artin-group-has-unsolvable-word-problem
kind: claim
title: Some Artin group has unsolvable word problem
distinct_from:
  novikov-boone-fp-group-undecidable-word-problem: that exhibits a finitely presented group with unsolvable word problem; this asks for one among Artin groups, whose relators are length-balanced braid relations between pairs of generators, and no Artin group is known to qualify.
  every-artin-group-has-solvable-word-problem: that is the affirmative answer to Charney's Problem 10; this is its negation.
---

**OPEN.** There is a finite Coxeter graph `Γ` such that the Artin group `A_Γ` has
unsolvable word problem.

It is equivalent to the no answer to Zaremsky Problem 3.8. See
`some-artin-twisted-brin-thompson-group-embeds-in-no-fp-group` and the route
`artin-unsolvable-wp-from-twisted-bt-without-fp-host`.

## Attempts

- **Exclusions.** A witness has rank at least 4, contains a spherical triangle, is not
  of type FC, and is not euclidean (artifact
  `research/artifacts/zp-z3-08-twisted-bt-artin-2026-09-13.md` §5).
- **Mechanism.** None known. Classical undecidability constructions (Novikov–Boone)
  encode machines in relators, while an Artin group has one braid relation per edge,
  both sides of the same length and in two letters. No encoding into such relations is
  known.
