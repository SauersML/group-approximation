---
rg: 2
id: artin-pbh-reduces-along-folding-separators
kind: claim
title: An Artin group lies in the permutational Boone--Higman class iff the two sides of any separation over a foldable parabolic do; in particular iff every block of its defining graph does
distinct_from:
  artin-pbh-reduces-to-odd-component-cliques: that splits only along separators with even boundary, and does nothing when the graph has a single odd component (its Scope S1); this splits along any separator onto which both sides fold, including every cut vertex whatever its labels, so it applies to connected graphs with all labels odd.
  pbh-class-closed-under-common-retract-amalgams: that is the abstract closure theorem; this is its application to Artin groups through the folding retractions of `artin-ordinary-foldings-are-retractions`.
  artin-groups-satisfy-boone-higman: that is the open named problem, Problem 5.3(13) of arXiv:2306.16356v3; this reduces its permutational form to 2-connected defining graphs, and more generally to pieces without foldable separators.
---

**ESTABLISHED** (route `artin-pbh-reduces-along-folding-separators-proof`; lane proof, not independently reviewed). It inherits the status of `pbh-class-closed-under-common-retract-amalgams`, which is itself a lane proof not yet reviewed. `B_A` is the class of groups embedding in a group with a type (A) action (`boone-higman-type-a-class-closed-under-finite-extensions`); its finitely generated members embed in finitely presented simple groups (`type-a-action-gives-boone-higman-for-subgroups`). No priority is claimed; the bounded check is in the route.

## Statement

Notation of `artin-ordinary-foldings-are-retractions`.

1. **Folding separations.** Let `V = V_1 ∪ V_2` with `Λ = V_1 ∩ V_2`, such that no edge joins `V_1 \ Λ` to `V_2 \ Λ`. Suppose each `Γ[V_i]` admits a folding onto `Λ` satisfying (a)--(c) of that node. Then `A_Γ = A_(V_1) *_(A_Λ) A_(V_2)`, and
   `A_Γ ∈ B_A` if and only if `A_(V_1) ∈ B_A` and `A_(V_2) ∈ B_A`.
2. **Blocks.** `A_Γ ∈ B_A` if and only if `A_B ∈ B_A` for every block `B` of `Γ` (isolated vertex, bridge, or maximal 2-connected subgraph; blocks are induced subgraphs). Cut vertices need no condition on labels.
3. **Iteration.** Part 1, Part 2 and the odd-component reduction (`artin-pbh-reduces-to-odd-component-cliques`) may be applied in any order to the pieces they produce.

## Consequences

- `forest-artin-groups-satisfy-permutational-boone-higman`: every Artin group whose defining graph is a forest lies in `B_A`.
- **Blocks of known type.** If every block of `Γ` is a complete graph of spherical type (`spherical-artin-groups-satisfy-permutational-boone-higman`), of type Ã_n, B̃_n, C̃_n or a Euclidean triangle (nodes listed in `artin-groups-satisfy-boone-higman`, "What is known"), or satisfies the hypothesis of `even-fc-artin-groups-satisfy-permutational-boone-higman`, then `A_Γ ∈ B_A`. Example: any cactus graph whose cycles carry only even labels.
- **A 2-connected example with one odd component.** Take vertices `u, w, x, y` with `m_uw = m_ux = m_uy = 3`, `m_wx = m_wy = 2`, and `x, y` not adjacent. Then `Γ[u,w,x]` and `Γ[u,w,y]` are of type `A_3`, and the foldings `x ↦ w`, `y ↦ w` retract them onto `A_(u,w) ≅ A(A_2)`. So `A_Γ = A(A_3) *_(A(A_2)) A(A_3) ∈ B_A`. It is of FC type with a single odd component that is not a clique, so neither the odd-component reduction nor its Corollary E applies, and `Γ` has no cut vertex.

## Scope

- The all-3 four-cycle has no foldable separator of its own (over `{a, c}` the free subgroup `<a, c>` is not a retract of either side). It is reached instead by embedding it as a standard parabolic subgroup of a hub cone, where vertex stars become foldable separators: `artin-hub-cones-reduce-pbh-to-coned-cliques` and `triangle-free-all-3-artin-groups-satisfy-pbh` (2026-09-18). The hyperbolic triangles remain open.
- Part 1 needs foldings on both sides; one-sided retracts are not covered (Scope of the closure theorem).
