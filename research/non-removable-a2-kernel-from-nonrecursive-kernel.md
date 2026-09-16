---
rg: 2
id: non-removable-a2-kernel-from-nonrecursive-kernel
kind: route
title: A type [A_2] action with non-recursive kernel gives a pair whose kernel cannot be removed
target: a2-pair-with-non-removable-kernel-exists
requires:
  - some-a2-action-has-a-nonrecursive-kernel
  - a2-kernel-removal-forces-recursive-kernel
---

Let `G ↷ S` be of type `[A_2]` with non-recursive kernel `K`, as given by
`some-a2-action-has-a-nonrecursive-kernel`.

Suppose `(G, K)` sharply embeds in a pair `(G', K')`, where `G' ↷ S'` is of type
`[A_2]` with kernel `K'` and `K'` is finitely normally generated in `G'`. Then
`a2-kernel-removal-forces-recursive-kernel` (b) makes `K` recursive, a contradiction.

So `(G, K)` sharply embeds in no such pair, which is the target. ∎
