---
rg: 2
id: bh-unbounded-wp-complexity-proof
kind: route
title: Embed an arbitrarily hard finitely presented group in a simple one and transfer the bound
target: bh-forces-unbounded-fp-simple-wp-complexity
requires: [boone-higman-conjecture, kms-arbitrarily-hard-fp-rf-groups]
artifacts:
  - research/artifacts/boone-higman-complexity-wall-2026-09-11.md
---

Fix a recursive non-decreasing `g` and let `F(g)` be as in `(UWB1)`.

Step 1 of `uniform-wp-bound-excludes-bh-targets-proof` supplies a recursive
problem `X` outside `F(g)`, by clocked diagonalization. Step 2 applies
`kms-arbitrarily-hard-fp-rf-groups` to `X` and yields a finitely presented
residually finite group `G`, solvable of class three, with decidable word
problem not in `F(g)`.

`G` is finitely generated with solvable word problem, so
`boone-higman-conjecture` applies: there are a finitely presented simple group
`K` and an embedding `G <= K`.

Suppose the word problem of `K`, over some finite generating set `Y`, were in
`F(g)`. Step 3 of the same route — rewriting each generator of `G` as a word
over `Y` gives a length-linear, linear-time reduction, valid because `G` is a
subgroup of `K` — would put the word problem of `G` in `F(g)` as well,
contradicting the previous paragraph.

So `K` is a finitely presented simple group whose word problem is not in
`F(g)`. Since a change of finite generating set is itself a length-linear
substitution and `F(g)` is closed under those, the conclusion does not depend
on which finite generating set of `K` is used. `∎`

The three imported ingredients are the conjecture, the
Kharlampovich--Myasnikov--Sapir realization theorem, and nothing else; the
diagonalization and the transfer are written out in the companion route rather
than repeated here.
