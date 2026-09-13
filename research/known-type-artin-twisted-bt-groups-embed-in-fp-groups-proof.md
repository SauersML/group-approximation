---
rg: 2
id: known-type-artin-twisted-bt-groups-embed-in-fp-groups-proof
kind: route
title: Solvable word problem gives a finitely presented host for AV_A
target: known-type-artin-twisted-bt-groups-embed-in-fp-groups
requires:
  - known-artin-classes-have-solvable-word-problem
  - self-twisted-bt-group-fp-embedding-iff-solvable-wp
---

- For `A` in the listed classes, `known-artin-classes-have-solvable-word-problem`
  gives a solvable word problem.
- Direction (4)⇒(3)⇒(2)⇒(1) of `self-twisted-bt-group-fp-embedding-iff-solvable-wp`
  then gives a finitely presented host for `AV_A`.
  - (4)⇒(3) is the brick algorithm of the artifact §3.
  - (3)⇒(2) holds because a solvable word problem is a computable presentation.
  - (2)⇒(1) is Higman's embedding theorem.
- The envelope can keep a solvable word problem by Clapham's theorem
  (`clapham-fp-embedding-preserves-word-problem`, applied to `AV_A`). ∎
