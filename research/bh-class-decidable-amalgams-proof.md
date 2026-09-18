---
rg: 2
id: bh-class-decidable-amalgams-proof
kind: route
title: Realize the amalgam inside the HNN extension of A * B along C, and induct over a maximal tree
target: bh-class-decidable-amalgams-from-free-products-and-hnn
requires:
  - bh-class-free-products-iff-joint-embedding-and-free-z
  - bh-embeddability-survives-decidable-edge-hnn
---

Standard inputs, not re-read at source: normal forms in free products, Britton's
lemma, and the normal form theorem for fundamental groups of graphs of groups
(Serre, *Trees*, I.5).

**Item 1.** Put `P = A * B`, finitely generated and in `𝓑` by (FP). Put
`C_1 = i_A(C)`, `C_2 = i_B(C)`, `φ = i_B ∘ i_A^{-1}: C_1 -> C_2`, given on generators.
- *Decidability in `P`.* `A` and `B` have solvable word problem, being finitely
  generated members of `𝓑`, so reduced forms in `P` are computable. An element lies
  in `C_1` iff its reduced form is empty or a single letter from `A` lying in `C_1`,
  which is decidable in `A`. The same holds for `C_2`.
- By (HNN), `P*_φ = <P, t | t c t^{-1} = φ(c), c ∈ C_1>` lies in `𝓑`.
- *The amalgam inside.* Define `θ(a) = a` and `θ(b) = t^{-1} b t`. Then
  `θ(i_B(c)) = t^{-1} i_B(c) t = i_A(c) = θ(i_A(c))`, so `θ` is defined on
  `A *_C B`. A reduced alternating word `a_1 b_1 a_2 b_2 ...` (`a_i ∈ A ∖ C_1`,
  `b_i ∈ B ∖ C_2`) maps to `a_1 t^{-1} b_1 t a_2 t^{-1} b_2 t ...`. It has no pinch:
  `t^{-1} b t` is a pinch only if `b ∈ C_2`, and `t a t^{-1}` only if `a ∈ C_1`. By
  Britton's lemma it is nontrivial, so `θ` is injective and `A *_C B ∈ 𝓑`.

**Item 2.** Choose a maximal tree `Y` of the graph.
- *Along `Y`.* Amalgamate the vertex groups one edge at a time. At each step the new
  edge group sits in one vertex group `A_v` of the current tree product `G_k`.
  Membership of `A_v` in `G_k` is decidable: reduced forms are computable (vertex
  word problems plus decidable edge membership), and an element lies in `A_v` iff
  some reduced form of it has length `0` at `v` (by the normal form theorem, a
  reduced word of positive length times an element of `A_v` stays reduced of
  positive length, hence is nontrivial). So the edge group is decidable in `G_k`,
  and Item 1 applies. Each `G_k` is finitely generated.
- *Off `Y`.* Each remaining edge adds an HNN letter whose associated subgroups lie in
  vertex groups. They are decidable in the current group by the same normal-form
  argument, so (HNN) applies.
- After finitely many steps this gives `π_1(𝔾) ∈ 𝓑`. ∎
