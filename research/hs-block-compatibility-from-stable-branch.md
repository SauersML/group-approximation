---
rg: 2
id: hs-block-compatibility-from-stable-branch
kind: route
title: On the stable branch the rank-one algebra synchronizes any two one-level decompositions
target: leavitt-hs-block-compatibility
requires: [leavitt-steinberg-hs-stable, stable-branch-trivializes-hs-block-programme]
---

`stable-branch-trivializes-hs-block-programme`, item 3, is exactly this
implication.  Replace both one-level decompositions by one rank-one basis
algebra.  It is nested, carried to itself by `u` and `v` with total squared
transport error at most `4 eta(delta)^2`, adds boundary at most
`4 eta(delta)^2`, and keeps every surviving gap vacuously.

**Cycle, deliberately.**  Granting `hs-one-level-expander-block-decomposition`,
two routes compose into the converse:

* `hs-expander-block-decomposition-from-one-level-and-compatibility`, and
* `hs-blocks-select-stable-branch-through-masa-transport`.

So this claim is a reformulation of `leavitt-steinberg-hs-stable` modulo the
universal one-level theorem.  Keep both directions; `cairn check` warns about
the cycle, and the least fixpoint never fires on it.
