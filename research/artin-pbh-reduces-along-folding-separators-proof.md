---
rg: 2
id: artin-pbh-reduces-along-folding-separators-proof
kind: route
title: Identify A_Γ with the amalgam over the folded parabolic, apply common-retract closure, and induct over the block-cut tree
target: artin-pbh-reduces-along-folding-separators
requires:
  - artin-ordinary-foldings-are-retractions
  - pbh-class-closed-under-common-retract-amalgams
  - boone-higman-type-a-class-closed-under-finite-extensions
  - spherical-artin-groups-satisfy-permutational-boone-higman
---

**1. The amalgam.** The defining relators of `A_Γ` are indexed by edges, and every edge lies in `Γ[V_1]` or in `Γ[V_2]`, since none joins `V_1 \ Λ` to `V_2 \ Λ`; an edge inside `Λ` lies in both, and its relator is a relator of `A_Λ`. So `A_Γ` is the pushout of `A_(V_1) ← A_Λ → A_(V_2)`, the maps induced by the inclusions. By `artin-ordinary-foldings-are-retractions`, each map `A_Λ → A_(V_i)` has a left inverse `ρ_i`, so it is injective. A pushout of two injections is the amalgamated free product, so `A_Γ = A_(V_1) *_(A_Λ) A_(V_2)`, and each factor embeds in `A_Γ` (normal form theorem).

**2. Part 1.** `C = A_Λ` is a retract of `X = A_(V_1)` (via `ρ_1`) and of `Y = A_(V_2)` (via `ρ_2`). If `X, Y ∈ B_A`, then `A_Γ = X *_C Y ∈ B_A` by Part 1 of `pbh-class-closed-under-common-retract-amalgams`. Conversely `X` and `Y` embed in `A_Γ`, and `B_A` is closed under subgroups (its definition: groups embedding in a group with a type (A) action; see `boone-higman-type-a-class-closed-under-finite-extensions`).

**3. Part 2.** Induct on the number of blocks.
- *Disconnected `Γ`.* Take `V_1` a component and `V_2` the rest, `Λ = ∅`. The folding `f ≡ 1` satisfies (a) on every edge, and `A_∅ = 1`. So `A_Γ = A_(V_1) * A_(V_2)` and Part 1 applies.
- *Connected with at least two blocks.* The block-cut tree has a leaf block `B` meeting the rest of `Γ` in a single cut vertex `v`. Put `V_1 = V(B)`, `V_2 = (V \ V(B)) ∪ {v}`, `Λ = {v}`. No edge joins `V_1 \ {v}` to `V_2 \ {v}` (otherwise `v` would not separate). The constant foldings `f ≡ v` on `Γ[V_1]` and on `Γ[V_2]` satisfy (a) everywhere. So Part 1 applies; `Γ[V_2]` has one block fewer, and its blocks are blocks of `Γ`.
- *One block.* Nothing to do.
- *Converse.* Each block's Artin group is a factor in the iterated amalgam, hence a subgroup of `A_Γ`.

A block is an induced subgraph: an edge between two vertices of a 2-connected subgraph can be added to it without losing 2-connectedness, so it belongs to the block by maximality.

**4. Part 3.** Each of the three reductions takes as input any finite labelled graph and returns induced subgraphs, and each asserts an equivalence, so they compose.

**5. The example.** For `V_1 = {u,w,x}`, `Λ = {u,w}`, the folding `x ↦ w`: the edge `ux` has label 3 and maps to `(u, w)`, with `m_uw = 3` dividing 3 (case (c)); the edge `wx` maps to `(w, w)` (case (a)); the edge `uw` lies in `Λ`. The same holds for `y`. `A(A_3) ∈ B_A` by `spherical-artin-groups-satisfy-permutational-boone-higman` (or BFFHZ's type-A braid case, imported in `aut-free-groups-satisfy-permutational-boone-higman`).

**6. Bounded priority check (2026-09-18).** arXiv API search `abs:retraction AND abs:Artin AND abs:parabolic` (six hits, including arXiv:2603.15314, 2408.12291, 2407.07459, 2204.05142). None mentions Boone--Higman. The BH searches recorded in `research/artifacts/gq-bh-bh-lit-survey.md` found no Artin results beyond BFFHZ and BLIW. MathSciNet was not searched.

QED
