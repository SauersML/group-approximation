---
rg: 2
id: unsolvable-word-problem-does-not-obstruct-type-f-infinity-proof
kind: route
title: "A type-F group with unsolvable word problem (Collins-Miller) plus Higman embedding kill the word-problem obstruction"
target: unsolvable-word-problem-does-not-obstruct-type-f-infinity
requires: []
---

Direct proof, by citation of two classical facts.

1. (Collins--Miller.) There exists a group of type `F` -- a group with a
   finite `K(pi,1)`, hence of type `F_infinity` -- whose word problem is
   unsolvable. This is the result Xiaolei Wu pointed to in refuting Zaremsky's
   Problem 1.2 ("Does every group of type `F_3` have solvable word problem?"),
   recorded there as answered negatively. It shows directly that type
   `F_infinity` does not imply solvable word problem, so no word-problem
   quantity of `G` can be bounded merely by the existence of a type-`F_{n+1}`
   overgroup.

2. (Higman embedding theorem, Higman 1961.) Every finitely generated
   recursively presented group embeds in a finitely presented group. So a
   recursively enumerable (even undecidable) word problem is not an
   obstruction to embedding into a type-`F_2` group.

The claim asserts exactly that word-problem complexity cannot obstruct such an
embedding; (1) supplies the F_infinity witness and (2) supplies the embedding
theorem. This route imports both statements from their sources and does not
reprove them.
