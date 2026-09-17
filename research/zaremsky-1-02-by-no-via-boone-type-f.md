---
rg: 2
id: zaremsky-1-02-by-no-via-boone-type-f
kind: route
title: Zaremsky Problem 1.2 answered no by the type F Aanderaa--Cohen--Boone group of a machine with non-computable halting set
target: zaremsky-1-02-type-f3-groups-have-solvable-word-problem
requires:
  - boone-final-group-is-of-type-f
  - boone-final-group-finitely-presented
  - boone-commutator-criterion-for-halting
  - modular-machine-with-noncomputable-halting
---

## Why sufficient

Fix a modular machine `M` whose halting set `H_M subseteq N x N` is not computable
([[modular-machine-with-noncomputable-halting]]), and let `G_M` be its final group.

* `G_M` is finitely presented ([[boone-final-group-finitely-presented]]), on the
  generators `t, x, y, r_1, ..., r_n, k`, so its word problem is posed for a
  finite presentation.
* `G_M` is of type `F` ([[boone-final-group-is-of-type-f]]), hence has a finite
  `K(G_M,1)`, whose 3-skeleton is finite: `G_M` is of type `F_3`.
* For `(a,b) in N x N`, `k^{-1} t(a,b) k = t(a,b)` in `G_M` iff `(a,b) in H_M`
  ([[boone-commutator-criterion-for-halting]], `conj_k_finalTw_eq_iff`). The
  word `W(a,b) = k^{-1} u^{-1} t u k u^{-1} t^{-1} u` with `u = x^a y^b` (so that
  `t(a,b) = u^{-1} t u` by `sh_conj_tw`, up to the order convention, which is
  computable either way) is a computable function of `(a,b)`, and `W(a,b) = 1`
  iff `(a,b)` halts.

An algorithm for the word problem of `G_M` would therefore decide membership in
`H_M`, which is not computable. So `G_M` is a group of type `F_3` (indeed `F`)
with unsolvable word problem, and the answer to Problem 1.2 is **no**.

## What this adds over the citation route

The existing route rests on an unread chapter body. This route's undecidability
input is Mathlib's halting problem through the machine-checked chain, and its
topological input is the textbook Scott--Wall theorem; the one new group-theoretic
fact is that the associated subgroup `<t, r_1, ..., r_n>` of the last stable
letter is free on those generators
([[boone-halting-lift-is-free-on-t-and-stable-letters]]).
