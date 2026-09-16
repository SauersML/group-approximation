---
rg: 2
id: nonrecursive-a2-kernel-from-unsolvable-hnn-realization
kind: route
title: An HNN realization of a type (A) actor whose permutation image has unsolvable word problem is a type [A_2] action with non-recursive kernel
target: some-a2-action-has-a-nonrecursive-kernel
requires:
  - type-a-hnn-realization-with-unsolvable-word-problem
  - permutation-hnn-realization-of-type-a-actor-is-a2
---

Take the data promised by `type-a-hnn-realization-with-unsolvable-word-problem`:
- a type (A) action `Γ ↷ X`;
- finitely generated `D_1, D_2 <= Γ`, with `D_1` having finitely many orbits;
- an isomorphism `ψ : D_1 -> D_2`;
- a permutation `π` with `π d π^-1 = ψ(d)` as permutations for every `d in D_1`;

such that `<Γ, π>` has unsolvable word problem.

These are exactly the hypotheses of `permutation-hnn-realization-of-type-a-actor-is-a2`.
By its part (a):
- `L = Γ*_ψ` acting on `X` through `t -> π` is of type `[A_2]`;
- its image is `<Γ, π>`;
- its kernel `K` is recursive iff `<Γ, π>` has solvable word problem.

So `K` is not recursive, which is the target. ∎
