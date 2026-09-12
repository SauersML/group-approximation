---
rg: 2
id: baumslag-gersten-base-is-elliptic-in-every-tree-action
kind: claim
title: In every action of a Baumslag--Gersten group on a tree its Baumslag--Solitar base fixes a vertex, so no tree host with BS(1,n)-free vertex stabilizers contains it
distinct_from:
  fa-subgroups-of-graph-towers-lie-in-base-pieces: that places subgroups with property FA inside base pieces of towers; this places the non-FA subgroup BS(1,n) of a Baumslag--Gersten group inside a vertex stabilizer of every tree action, using only that its generators are conjugate to their own powers.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports the Bux--Llosa Isenrich--Wu embeddings through generalized Baumslag--Solitar hosts; this shows that none of their host families over free, abelian or nilpotent vertex groups contains a Baumslag--Gersten group.
  bh-embeddability-survives-magnus-subgroup-hnn: that is the open permanence for Magnus-subgroup HNN extensions; this is an obstruction to one method of attacking its Baumslag--Gersten instance, and refutes nothing.
artifacts:
  - research/artifacts/one-relator-boone-higman-2026-09-12.md
---

For `n >= 2` let

    BG_n = < a, t | (t a t^-1) a (t a t^-1)^-1 = a^n >,

so `BG_2` is the Baumslag--Gersten group. Put `b = t a t^-1`. Then
`B = <a, b>` satisfies `b a b^-1 = a^n`, and it is a copy of `BS(1,n)`: by the
Magnus rewriting, `BG_n` is the HNN extension of
`BS(1,n) = <a_0, a_1 | a_1 a_0 a_1^-1 = a_0^n>` along `a_0 -> a_1`.

**ESTABLISHED.**

1. **Ellipticity.** In every action of `BG_n` on a tree without inversions,
   `B` fixes a vertex.
2. **No Baumslag--Solitar-free host.** Let `Γ` act on a tree, and suppose no
   vertex stabilizer of `Γ` contains a subgroup isomorphic to `BS(1,m)` for any
   `m >= 2`. Then `BG_n` does not embed in `Γ`.
3. **Consequence for the Bux--Llosa Isenrich--Wu hosts.** `BG_n` lies in no group
   of `BS_G` when `G` is virtually free, virtually abelian or virtually
   nilpotent, because there the vertex stabilizers of the Bass--Serre tree are
   commensurable with `G`. So their Theorems 12.2, 12.3, 12.5 and the nilpotent
   case of 12.1 cannot certify `BG_n`. A generalized Baumslag--Solitar host for
   `BG_n` needs vertex groups that contain `BS(1,n)`.

The proof is `baumslag-gersten-base-elliptic-proof`.

## Why this matters for the one-relator problem

`BG_2` is the smallest one-relator test case outside every class reached so
far (see `one-relator-groups-satisfy-boone-higman`):
- it is not residually finite;
- it contains `BS(1,2)`, so it is not hyperbolic;
- its Magnus step has the non-free base `BS(1,2)`.

Item 3 rules out the explicit tree hosts. The Theorem 11.1 route would need a
group in `BS_G`, with `G` commensurable to a group containing `BS(1,2)`, that
acts faithfully on its Bass--Serre tree and contains `BG_2`. Whether one exists
is open.
