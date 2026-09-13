---
rg: 2
id: artin-unsolvable-wp-from-twisted-bt-without-fp-host
kind: route
title: An Artin group whose AV_A has no finitely presented host has unsolvable word problem
target: some-artin-group-has-unsolvable-word-problem
requires:
  - some-artin-twisted-brin-thompson-group-embeds-in-no-fp-group
  - self-twisted-bt-group-fp-embedding-iff-solvable-wp
---

Let `A` be an Artin group such that `AV_A` embeds in no finitely presented group. If
`A` had solvable word problem, then (4)⇒(1) of
`self-twisted-bt-group-fp-embedding-iff-solvable-wp`, through Higman's embedding
theorem, would give a finitely presented host. So `A` has unsolvable word problem.

**Cycle note.** Together with `artin-twisted-bt-without-fp-host-from-unsolvable-wp`,
this route makes a dependency cycle, which `cairn check` warns about. It records an
equivalence, and neither claim establishes itself through it. Do not delete either
route.
