---
rg: 2
id: artin-hub-cones-reduce-pbh-to-coned-cliques
kind: claim
title: Adding a hub vertex whose labels divide the incident edge labels embeds an Artin group in one that splits over folded stars, reducing permutational Boone--Higman to the coned maximal cliques
distinct_from:
  artin-pbh-reduces-along-folding-separators: that splits A_Γ along separators of Γ itself, and does nothing on a 2-connected graph without foldable separators; this first embeds A_Γ as a standard parabolic subgroup of the Artin group of a cone over Γ, where every vertex star becomes a foldable separator, so it reaches 2-connected graphs such as the all-3 four-cycle.
  artin-pbh-reduces-to-odd-component-cliques: that reduces along even boundaries; with every hub label 2 this node recovers its even-label case (Corollary C there), and with odd hub labels it reaches odd graphs that reduction cannot touch.
  artin-groups-satisfy-boone-higman: that is the open named problem, Problem 5.3(13) of arXiv:2306.16356v3; this reduces its permutational form, for graphs admitting a divisible hub labelling, to finitely many complete Artin groups.
---

**ESTABLISHED** (route `artin-hub-cones-reduce-pbh-to-coned-cliques-proof`; lane proof, not independently reviewed). It inherits the status of `artin-pbh-reduces-along-folding-separators` and so of `pbh-class-closed-under-common-retract-amalgams` (lane proofs, not reviewed). `B_A` is the class of groups embedding in a group with a type (A) action; its finitely generated members embed in finitely presented simple groups. No priority is claimed; the construction was designed in lane bh-artin (2026-09-18) and a bounded check is in the route.

## Setting

Notation of `artin-ordinary-foldings-are-retractions`: `Γ` is a finite labelled graph, `m_vw ∈ {2, 3, ...}` on edges, non-edges mean `m = ∞`.

A **hub labelling** is a map `k : V(Γ) → {2, 3, 4, ...}` such that for every edge `vw`, both `k_v` and `k_w` divide `m_vw`. The **hub cone** `Γ^k` is `Γ` together with one new vertex `e` joined to every `v ∈ V(Γ)` by an edge labelled `k_v`. For a clique `Δ` of `Γ`, `Δ^k` is the (complete) labelled graph `Γ^k[Δ ∪ {e}]`.

## Statement

Let `k` be a hub labelling of `Γ`.
1. `A_Γ` is a standard parabolic subgroup of `A_(Γ^k)`; in particular `A_Γ ≤ A_(Γ^k)`.
2. `A_(Γ^k) ∈ B_A` if and only if `A_(Δ^k) ∈ B_A` for every maximal clique `Δ` of `Γ`.
3. Hence, if `A_(Δ^k) ∈ B_A` for every maximal clique `Δ` of `Γ`, then `A_Γ ∈ B_A`, so `A_Γ` embeds in a finitely presented simple group and has solvable word problem.

## Consequences

- `triangle-free-all-3-artin-groups-satisfy-pbh`: with `k ≡ 3`, every triangle-free graph with all labels 3 (the all-3 four-cycle, all longer all-3 cycles, all-3 bipartite graphs, the all-3 Petersen graph, ...), because each coned edge is the Euclidean triangle `(3,3,3)`, type Ã_2.
- **Triangle-free graphs in general.** The maximal cliques are edges and isolated vertices, so the pieces are the triangles `(m_vw, k_v, k_w)` and the dihedral groups `A(I_2(k_v))`. For example, every triangle-free graph with all labels equal to one odd `m` lies in `B_A` as soon as the triangle Artin group `(m, m, m)` does (take `k ≡ m`).
- **Even labels.** With `k ≡ 2` every `Δ^k` is `A_Δ × Z`, recovering Corollary C of `artin-pbh-reduces-to-odd-component-cliques`.

## Scope

- A hub labelling needs every vertex's incident labels to have a common divisor `≥ 2`. A vertex meeting labels 3 and 4, say, admits none.
- Cliques are atoms: a clique never contains a separation, so the complete pieces `Δ^k` must be handled by other means. With a triangle `(3,3,3)` in `Γ`, the piece is the complete graph `K_4` with all labels 3, whose status is open.
