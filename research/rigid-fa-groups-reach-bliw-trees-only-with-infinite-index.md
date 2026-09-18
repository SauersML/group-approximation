---
rg: 2
id: rigid-fa-groups-reach-bliw-trees-only-with-infinite-index
kind: claim
title: A commensurator-rigid group with property FA lies in a Bux--Llosa Isenrich--Wu tree host only with infinite index in a vertex stabilizer
requires:
  - commensurator-rigid-groups-have-no-faithful-bs-members
distinct_from:
  commensurator-rigid-groups-have-no-faithful-bs-members: that rules out faithful members of BS_G, that is, tree hosts in which G is commensurable with a vertex group; this handles every faithful cocompact locally finite tree host of Theorem B, using property FA to force a fixed vertex.
  bliw-locally-finite-tree-actions-embed-in-fp-simple-groups: that imports Theorems B and C as embedding theorems; this constrains how a commensurator-rigid FA group could sit inside a group they apply to.
---

**ESTABLISHED** (lane proof, elementary given its inputs; not reviewed; no priority
claimed).

**Statement.** Let `G` be an infinite group with property FA (every action on a tree
has a fixed vertex), such that `G -> Comm(G)` is injective with image of finite index.
Let `Γ` act faithfully and cocompactly on a locally finite tree `X`, as in
Bux--Llosa Isenrich--Wu Theorem B, and let `G <= Γ`. Then `G` fixes a vertex `v`,
and `[G_v : G] = ∞`. Moreover the commensurability class of `G_v` is not
commensurator-rigid in the same sense.

**Proof.**
- By FA, `G` fixes a vertex `v`, so `G <= G_v`.
- `X` is locally finite and `Γ\X` is finite. So every edge stabilizer has finite
  index in both adjacent vertex stabilizers, and `Γ` is the fundamental group of a
  finite graph of groups whose vertex and edge groups are pairwise commensurable,
  with finite-index edge inclusions. That is, `Γ ∈ BS_(G_v)`, and it acts
  faithfully on its Bass--Serre tree `X`.
- If `[G_v : G] < ∞`, then `G_v` is commensurable with `G`, so `BS_(G_v) = BS_G`, and
  `commensurator-rigid-groups-have-no-faithful-bs-members` forbids a faithful
  member. So `[G_v : G] = ∞`.
- The same node, applied to `G_v`, shows that `G_v -> Comm(G_v)` is not both
  injective and of finite-index image.

**Instances** (FA and rigidity are cited, not read at source this session):
- `Out(F_n)`, `n >= 4`: property FA (Culler--Vogtmann; Bogopolski) and Farb--Handel.
- `Mod(S_g)`, closed, `g >= 3`: property FA (Culler--Vogtmann) and Ivanov.

So the tree machinery of Bux--Llosa Isenrich--Wu, in both of its forms, can reach
BBMZ Problems 5.3(3) and the closed part of 5.3(2) only through a finitely presented
vertex group `P` containing `Out(F_n)` or `Mod(S_g)` with infinite index, whose
commensurator is not virtually `P`. Arithmetic lattices have such commensurators,
but a copy of `Mod(S_g)` inside one would make `Mod(S_g)` linear, which is open.
This gives a precise target for the lanes working on those problems.
