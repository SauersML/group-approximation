---
rg: 2
id: artin-twisted-bt-fp-hosts-from-solvable-word-problem
kind: route
title: If every Artin group has solvable word problem then every AV_A embeds in a finitely presented group
target: every-artin-twisted-brin-thompson-group-embeds-in-fp-group
requires:
  - every-artin-group-has-solvable-word-problem
  - self-twisted-bt-group-fp-embedding-iff-solvable-wp
---

Every Artin group `A` on a finite generating set is finitely generated. If `A` has
solvable word problem, then (4)⇒(1) of
`self-twisted-bt-group-fp-embedding-iff-solvable-wp` gives a finitely presented host
for `AV_A`. The host comes from Higman's embedding theorem applied to the computably
presented group `AV_A`. By Clapham's theorem
(`clapham-fp-embedding-preserves-word-problem`, applied to `AV_A`, which has solvable
word problem), the host can even keep a solvable word problem.

With `artin-solvable-word-problem-from-twisted-bt-fp-hosts`, this route records an
equivalence.
