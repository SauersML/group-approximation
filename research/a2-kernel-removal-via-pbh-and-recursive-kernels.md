---
rg: 2
id: a2-kernel-removal-via-pbh-and-recursive-kernels
kind: route
title: Decide the action image, place it in a faithful type (A_2) actor by the permutational conjecture, and multiply
target: a2-pairs-embed-in-a2-pairs-with-fng-kernels
requires:
  - a2-kernel-removal-iff-image-satisfies-pbh
  - permutational-boone-higman-conjecture
  - a2-action-kernels-are-recursive
---

Let `G ↷ S` be of type [A_2] with kernel `K`.

1. `G/K` is finitely generated, as a quotient of the finitely presented group
   `G`.
2. By `a2-action-kernels-are-recursive`, `G/K` has solvable word problem.
3. By `permutational-boone-higman-conjecture`, `G/K` embeds in a finitely
   presented group with a type (A) action: faithful, finitely generated point
   stabilizers, finitely many orbits of pairs. This is type (A_2) in the
   notation of Fournier-Facio--Wu--Zaremsky.
4. By `a2-kernel-removal-iff-image-satisfies-pbh`, (2) ⇒ (1), the action is
   removable. Concretely, `(G, K)` embeds in `(G x Λ, G x {1})` with `G x Λ`
   acting through `Λ`.

**Cycle.** With `pbh-via-bh-and-a2-kernel-removal`, which derives the
permutational conjecture from Boone--Higman and this target, this route closes
an intended cycle. It records a conditional equivalence and does not fire while
`permutational-boone-higman-conjecture` is open.
