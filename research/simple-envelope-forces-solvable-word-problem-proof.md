---
rg: 2
id: simple-envelope-forces-solvable-word-problem-proof
kind: route
title: Two parallel enumerations, one of which must halt
target: simple-envelope-forces-solvable-word-problem
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Fix a finite presentation `H = <X | R>` with `H` simple.  If `H = 1` every
subgroup is trivial and there is nothing to prove, so assume `H != 1`.

Given `w in F(X)`, run two enumerations in parallel.

**A.**  Enumerate finite products of conjugates of elements of `R^{±1}`,
i.e. the normal closure of `R` in `F(X)`.  Halt if `w` appears.  A halts iff
`w = 1` in `H`.

**B.**  Enumerate consequences of `R ∪ {w}`.  Halt once a proof of `x = 1`
has been found for **every** `x in X`.  This is a terminating condition
because `X` is finite.

Exactly one halts.  If `w = 1` in `H`, A halts.  If `w != 1`, then `<<w>>` is
a nontrivial normal subgroup of a simple group, hence all of `H`, so
`<X | R, w>` presents the trivial group and every generator is a consequence
of `R ∪ {w}`; B halts.

So `H` has decidable word problem.  For `G = <g_1,…,g_k> <= H` fix words
`u_i(X)` representing the images of the `g_i`.  Injectivity of the inclusion
gives, for every word `v` in the `g_i^{±1}`,

    v = 1 in G   <==>   v(u_1,…,u_k) = 1 in H ,

and the right-hand side is decidable.

## Where the finiteness of X is used

Twice, and both uses are essential.  B's halting condition is a *finite*
conjunction, so it is a single recursively enumerable event rather than an
infinite schedule; and the substitution step needs only finitely many words
`u_i` fixed in advance.  Neither survives if `H` is merely computably
presented on infinitely many generators, which is exactly the gap between
`boone-higman-thompson-simple-envelope` and `boone-higman-conjecture`.
