---
rg: 2
id: boone-higman-via-hypothesis-free-shift-compiler
kind: route
title: Dead -- make the shift-similar envelope finitely presented from a finite presentation alone
target: boone-higman-conjecture
requires: []
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

**Dead.**  Invalidated by
`compilers-cannot-drop-the-decidability-hypothesis`.

The route recorded here is the tempting simplification of
`boone-higman-via-shift-higman-compiler`: prove finite presentability of the
Mallery--Zaremsky envelope `E_nu(P)` for **every** finitely presented `P`
and a suitable `nu`, with no decidability hypothesis, and then run
Proposition 5.3 and Corollary B as before.  It is written with an empty
prerequisite list because there is nothing left to prove once the
simplification is granted -- the whole conjecture would follow, and rather
more besides.

Rather more besides is exactly the refutation.  Corollary B would then give
every subgroup of every such envelope a solvable word problem, so every
finitely presented group would have one, contradicting
`novikov-boone-fp-group-undecidable-word-problem`.  The kill is therefore not
a difficulty in the construction; the statement is false.

Recorded because the simplification is what one writes down first: the
decidability hypothesis looks like an artifact of starting from Clapham, and
it is not.  It also localizes where a real proof must put the algorithm --
in the choice of `nu`, which is the only free parameter the construction has.
