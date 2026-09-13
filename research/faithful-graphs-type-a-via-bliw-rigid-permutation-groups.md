---
rg: 2
id: faithful-graphs-type-a-via-bliw-rigid-permutation-groups
kind: route
title: The rigid permutation group of the augmented Bass--Serre tree is a finitely presented type (A) actor
target: faithful-finite-index-graphs-of-groups-have-type-a-overgroups
requires: []
---

Source: K.-U. Bux, C. Llosa Isenrich, X. Wu, *On the Boone--Higman Conjecture
for groups acting on locally finite trees*, arXiv:2408.05673v2, extracted text on
MSI (`/scratch.global/sauer354/orbh-lit/2408.05673.txt`), read 2026-09-13.
Hats are transliterated: `Ĝ` for the augmented graph of groups and `T̂` for its
Bass--Serre tree. The calligraphic gate system is written `𝒢`.

## Verbatim pins

- **Definition 1.2.** "We call the action strongly faithful if no non-trivial
  element of G acts as identity on a piece of G."
- **Definition 1.3.** "The rigid permutation group RPG(G) (of the G-action on G)
  is the group of rigid permutations of V(G)." Also: "Given a finite set
  B ⊂ V(G), we denote by RPG(G,B) the subgroup of RPG(G) that fixes B
  pointwise."
- **Remark 1.4(2).** "Any group element of G acts on G as a rigid permutation.
  In particular, when the action is faithful, we have an embedding of G into
  RPG(G)."
- **Section 3, standing assumption.** "We will also assume that T is an infinite
  tree without leaves."
- **Definition 8.1.** "An action of a group H on a set S is called oligomorphic
  if for every k ∈ N there are only finitely many H-orbits of k-tuples."
- **Lemma 8.3.** "Let Γ be a graph equipped with a faithful G-action. Then G is a
  subgroup of RPG(Γ) and the RPG(Γ)-action on V(Γ) is oligomorphic."
- **Proposition 9.2.** "Let G be a group that acts strongly faithfully and
  without inversions on a tree T. Assume that all edge stabilisers are of type Fn
  and that there is a system of gates G and an admissible tree T0 ⊂ T such that
  (RPG(T), G, T0) has the viral expansion property. Then for every finite subset
  B ⊂ T the rigid permutation group RPG(T,B) is of type Fn."
- **Section 10, augmentation.** "Ĝv := Gv × Z/3Z, Ĝe := Ge, Ĝe = Ge ↪ Gv × {1}
  ≤ Ĝv for v = ι(e), τ(e)". Also: "the embeddings Ge ↪ Ĝe and Gv ↪ Ĝv induce a
  canonical embedding G ↪ Ĝ together with a G-equivariant embedding T ↪ T̂."
- **Lemma 10.2.** "If G acts faithfully on T, then Ĝ acts strongly faithfully on
  T̂."
- **Lemma 10.3.** "𝒢 defines an admissible system of gates on T̂."
- **Lemma 10.4.** "For every finite subset B ⊂ T̂ there is an admissible subtree
  T0 such that the triple (RPĜ(T̂,B), 𝒢, T0) has the viral expansion property."
- **Proof of Theorem 10.5.** "This is an immediate consequence of Theorem 9.1,
  Lemma 10.2, Lemma 10.4 and the fact that the edge stabilisers of the Ĝ-action
  on T̂ are isomorphic to the edge stabilisers of the G-action on T, thus Fn."

## Item 1

- **No edges.** If the graph of groups has no edge, the Bass--Serre tree is one
  vertex, so faithfulness forces `G = 1`, which lies in `B_A`. Assume there is an
  edge.
- **`T̂` has no leaves.** A vertex of `T̂` over `v` has degree
  `Σ [Ĝ_v : Ĝ_e]` over the edge ends at `v`, and each index is
  `3 [G_v : G_e] >= 3`. So `T̂` is infinite, locally finite and without leaves,
  as Section 3 assumes.
- **Finiteness input.** Edge groups have finite index in finitely presented
  vertex groups, so they are finitely presented, i.e. of type `F_2`. By Lemma
  10.2 the action of `Ĝ` on `T̂` is strongly faithful. It is without inversions
  (Bass--Serre tree), and its edge stabilizers are conjugates of the `G_e`. By
  Lemmas 10.3 and 10.4 with `B = ∅` there is an admissible triple
  `(RPĜ(T̂), 𝒢, T0)` with the viral expansion property.
- **Proposition 9.2 with `n = 2`.** Put `H = RPĜ(T̂)`. Then `RPĜ(T̂,B)` is of
  type `F_2`, hence finitely presented, for every finite `B ⊂ V(T̂)`:
  - with `B = ∅`, `H` itself;
  - with `B = {w}`, the stabilizer `Stab_H(w)` (Definition 1.3).
- **Type (A).** `H` is a group of permutations of `V(T̂)`, so its action is
  faithful. Strongly faithful implies faithful, because an element acting
  trivially on `T̂` acts trivially on every piece. So Lemma 8.3 applies to `Ĝ` and says the action of
  `H` is oligomorphic. In particular there are finitely many `H`-orbits of
  2-tuples, hence of 2-element subsets. So `H ↷ V(T̂)` satisfies all four
  clauses of type (A): faithful, `H` finitely presented, point stabilizers
  finitely generated, finitely many orbits of 2-element subsets.
- **Embedding.** `G ↪ Ĝ` (canonical embedding), and `Ĝ ↪ H` by Remark 1.4(2)
  since `Ĝ` acts faithfully on `T̂`. So `G ∈ B_A`.

## Item 2

Let `T` be the tree and `T'` its barycentric subdivision, on which `G` acts
without inversions and still faithfully. If `T` is a single vertex then `G = 1`.
Otherwise:
- **Finite quotient.** `G` has finitely many vertex orbits on `T`. Every edge has
  an endpoint in one of finitely many orbit representatives, each of finite
  degree, so the edge orbits are finite too, and `G \ T'` is a finite graph.
- **Stabilizers.** The stabilizer `G_e` of both endpoints of an edge `e` has
  index at most 2 in the setwise stabilizer of `e`, and index at most `deg(v)`
  in `G_v` for an endpoint `v`. So whichever of the two edge stabilizers is
  finitely presented, all of `G_e`, the setwise stabilizers and the `G_v` are
  finitely presented, as finite-index subgroups or overgroups of finitely
  presented groups.
- **Reduction.** By the structure theorem (Serre, *Trees*, §I.5.4; not re-read),
  `G` is the fundamental group of a finite graph of groups over `G \ T'` with
  these stabilizers as vertex and edge groups, edge inclusions of finite index,
  and Bass--Serre tree `G`-isomorphic to `T'`. The action on it is faithful, so
  item 1 applies. `∎`
