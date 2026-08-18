---
rg: 2
id: simple-envelope-forces-solvable-word-problem
kind: claim
title: A finitely generated subgroup of a finitely presented simple group has solvable word problem
distinct_from:
  boone-final-group-finitely-presented: that establishes finite presentability of the Boone tower's final group; this deduces decidability of the word problem from membership in a finitely presented SIMPLE group, and its content is the two-enumeration argument rather than any presentation.
  finitely-presented-nonsofic-group-exists: that combines finite presentation with failure of soficity in an existence statement; this is a decidability consequence of simplicity together with finite presentation, and has no approximation content.
  boone-higman-conjecture: that is the open converse -- every finitely generated group with solvable word problem has such an envelope; this is the direction that is a theorem, and it is the reason the conjecture is stated as an equivalence at all.
  literal-word-problem-solvable: that decides the word problem of one specific group constructed in this repository, by a normal form for that group; this is a general theorem whose whole content is that simplicity semi-decides nontriviality inside any finitely presented simple group.
  novikov-boone-fp-group-undecidable-word-problem: that exhibits a finitely presented group with undecidable word problem; taken together with this claim it says such a group embeds in no finitely presented simple group, but the two statements share no argument.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Let `H` be a finitely presented simple group and `G <= H` finitely generated.
Then `G` has solvable word problem.

This is the easy direction of the Boone--Higman equivalence, classically due
to Kuznetsov.  It is what makes `boone-higman-conjecture` a characterization
attempt rather than a one-way embedding question.

## The two enumerations

Simplicity is not decoration here.  It supplies the semi-decision procedure
for **non**triviality of a word: kill the word and wait for the whole finite
generating set to collapse.  Finite presentation supplies the other half, by
making consequences of the relators recursively enumerable.  Drop either
hypothesis and the argument stops:

* finitely presented but not simple — killing `w` need not collapse anything,
  and no bound says when to give up;
* simple but not finitely presented — the consequence relation need not be
  enumerable, so neither search is a procedure.

That is also why the conjecture's open direction is hard.  The statement
being aimed at is not "embed in something simple" (Schupp,
`countable-group-embeds-in-two-generator-simple-group`) nor "embed in
something finitely presented" (Higman); it is the conjunction, and each
classical theorem destroys the other's property.
