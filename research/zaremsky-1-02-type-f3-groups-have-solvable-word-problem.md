---
rg: 2
id: zaremsky-1-02-type-f3-groups-have-solvable-word-problem
kind: claim
title: "Zaremsky Problem 1.2 resolved: does every group of type F_3 have solvable word problem?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 2,
verbatim: "Does every group of type `F_3` have solvable word problem? [The
answer is no – Xiaolei Wu pointed out a result of Collins and Miller producing
a group of type F with unsolvable word problem.]"

This claim is the question. It is established only through an answer route:

- **No**: `zaremsky-1-02-by-no` requires
  `some-type-f-group-has-unsolvable-word-problem`.
- **Yes** would say that every group of type `F_3` has solvable word problem.
  The no answer refutes it, so no yes-route is written.

Never write a `requires: []` route into this claim.

**Reading.** A group has type `F_n` when it has a `K(G,1)` with finite
`n`-skeleton, and type `F` when it has a finite `K(G,1)`. Type `F` implies
type `F_n` for every `n`. Groups of type `F_2` are the finitely presented
groups, and the word problem is posed for a finite presentation.

**Status.** Answered negatively in the list's own note, from a remark of
Xiaolei Wu citing Collins and Miller (1999).
