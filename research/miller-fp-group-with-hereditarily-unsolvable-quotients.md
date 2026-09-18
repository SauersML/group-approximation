---
rg: 2
id: miller-fp-group-with-hereditarily-unsolvable-quotients
kind: claim
title: Some finitely presented group has unsolvable word problem in every nontrivial quotient
distinct_from:
  novikov-boone-fp-group-undecidable-word-problem: that gives one finitely presented group with unsolvable word problem, and its abelianization or other quotients may be decidable; this asks the same of every nontrivial quotient, so the group has no decidable nontrivial image at all.
  some-type-f-group-has-unsolvable-word-problem: that improves the finiteness type of a group with unsolvable word problem; this is about how undecidability passes to quotients, and says nothing about finiteness type.
  universal-fp-group-hosts-have-unsolvable-word-problem: that pushes undecidability UP to overgroups of a universal finitely presented group; this pushes it DOWN to every nontrivial quotient of one finitely presented group.
artifacts:
  - experiments/ck-miller-poison-2026-09-17/kmss-miller-quote.txt
---

There is a finitely presented group `M` such that every nontrivial quotient
`M/N` (with `N != M`) has unsolvable word problem. In particular `M != 1`,
because `M` itself is such a quotient.

This is imported (C. F. Miller III) through the route
`miller-fp-group-with-hereditarily-unsolvable-quotients-citation`. Miller's
construction uses two disjoint recursively enumerable sets that are not
recursively separable, together with the Adian--Rabin construction.

**How it is used.** In a finitely generated group `P`, a solvable word problem
passes to every finitely generated subgroup. So whenever a quotient of `P`
contains a nontrivial image of `M`, that quotient has unsolvable word problem.
By Kuznetsov (`simple-envelope-forces-solvable-word-problem`), such a quotient
therefore cannot be a finitely presented simple group.
