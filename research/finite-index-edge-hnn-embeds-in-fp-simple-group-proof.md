---
rg: 2
id: finite-index-edge-hnn-embeds-in-fp-simple-group-proof
kind: route
title: Read the HNN extension as a one-vertex graph of groups and apply Theorem 10.5 of Bux--Llosa Isenrich--Wu
target: finite-index-edge-hnn-embeds-in-fp-simple-group
requires: [bliw-locally-finite-tree-actions-embed-in-fp-simple-groups]
---

**The tree.** `K = A*_phi` is the fundamental group of the graph of groups with
one vertex carrying `A` and one loop carrying `C_1`, attached by the inclusion
`C_1 -> A` and by `phi : C_1 -> A` (Serre, *Trees*, §I.5.1). Its Bass--Serre
tree `T` has vertex set `K/A` and edge set `K/C_2`, with the edge `gC_2`
joining `gA` to `gtA`. By Britton's lemma `A ∩ tAt^-1 = C_2`, so this is well
defined and the edge stabilizers are the conjugates of `C_2`.

**Hypotheses of Theorem 10.5, with n = 2.**

* The vertex group `A` is finitely presented, that is, of type `F_2`.
* The edge group has finite index in the vertex group at both ends, because
  `[A : C_1]` and `[A : C_2]` are finite. The edges leaving the vertex `A` are
  the cosets `aC_2`, and the edges arriving there are
  `a t^-1 C_2 = a C_1 t^-1`, indexed by `A/C_1`. So `T` is locally finite, of
  valence `[A : C_1] + [A : C_2]`.
* The kernel of `K` on `T` fixes every vertex `gA`, so it is the intersection of
  all conjugates of `A`, which is the largest normal subgroup of `K` contained
  in `A`. It is trivial by hypothesis, so `K` acts faithfully.

Theorem 10.5 of `bliw-locally-finite-tree-actions-embed-in-fp-simple-groups`
embeds `K` in a simple group of type `F_2`, that is, a finitely presented simple
group.

## The limits

*(L1).* Suppose `K` acts faithfully. `A` fixes the vertex `A` and permutes each
finite ball of radius `r` about it. The kernel of that finite permutation action
is a normal subgroup of finite index in `A`. The intersection of these kernels
over all `r` fixes `T` pointwise, so it is trivial. So `A` is residually finite.

*(L2).* A proper finite-index subgroup of an infinite group has a normal core of
finite index, which is proper and nontrivial. So an infinite simple `A` forces
`C_1 = C_2 = A` and `phi in Aut(A)`. Then `A <| K`, the valence is `2`, and
`A` lies in every conjugate of `A`, hence in the kernel.

*(L3).*
* **Index bound.** `A` fixes the vertex `B` of the tree of `B*_psi`. It permutes
  the `[B : D_2]` edges `bD_2` leaving that vertex, and the orbit of `D_2` has
  `[A : A ∩ D_2]` elements. The `[B : D_1]` arriving edges `b D_1 s^-1` bound
  `[A : A ∩ D_1]` the same way.
* **Containment.** By Britton's lemma in `B*_psi`,
  `f(C_2) = s f(C_1) s^-1 <= B ∩ sBs^-1 = D_2`. Symmetrically `f(C_1) <= D_1`.
* **The example.** `u = b^-1 s` centralizes `F(a,b)`, so
  `F(a,b)*_psi = F(a,b) x <u>`. The projection to `F(a,b)` sends `a -> a` and
  `s = bu -> b`, which form a free basis. So `<a, s>` is free on `a, s`, and `f`
  is injective. `F(a,b)` is normal, because `D_1 = D_2 = F(a,b)`, so it lies in
  every vertex stabilizer and hence in the kernel of the tree action.

*(L4).* A group with a residually finite subgroup of finite index is residually
finite (intersect the finitely many conjugates of a finite-index subgroup that
misses a given element). With the passage to subgroups, this makes residual
finiteness a commensurability invariant. The vertex groups of the faithful
graph of groups used in Theorem 11.1 are residually finite by (L1), so every
vertex group commensurable with them is too.
