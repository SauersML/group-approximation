---
rg: 2
id: self-similar-hosts-rf-proof
kind: route
title: Level stabilizers separate points, and infinite simple groups have no finite quotients
target: self-similar-hosts-contain-only-residually-finite-groups
requires:
  - thompson-v-finitely-presented-infinite-simple
  - simple-envelope-forces-solvable-word-problem
---

1. **Faithful tree actions are residually finite.** Let `H <= Aut(T_d)`. The
   level-`n` stabilizer `St_H(n)` is the kernel of the action on the finitely
   many vertices of level `n`, so it is a normal subgroup of finite index. An
   element in every `St_H(n)` fixes every vertex, so it is the identity. Hence
   the intersection of the `St_H(n)` is trivial and `H` is residually finite.
   Self-similarity is not used.
2. **Heredity.** If `K <= H`, the subgroups `K ∩ St_H(n)` are normal of finite
   index in `K` with trivial intersection, so `K` is residually finite.
3. **Simple inputs.** An infinite residually finite group has a proper
   nontrivial normal subgroup of finite index, so it is not simple. Hence no
   infinite simple group is a subgroup of a self-similar group.
4. **Witness.** `thompson-v-finitely-presented-infinite-simple` gives V
   finitely presented, infinite and simple. V is a finitely generated subgroup
   of the finitely presented simple group V, so
   `simple-envelope-forces-solvable-word-problem` gives V a solvable word
   problem. By step 3, V embeds in no self-similar group. `∎`
