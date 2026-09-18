---
rg: 2
id: artin-pbh-reduces-to-free-of-infinity-artin-groups
kind: claim
title: Every Artin group lies in the permutational Boone--Higman class iff every Artin group with complete defining graph (free of infinity) does, via a clone double in which each infinity splitting is over a common retract
distinct_from:
  artin-word-problem-reduces-to-free-of-infinity-graphs: that moves the word problem to the maximal free-of-infinity standard parabolic subgroups of the same graph (Godelle--Paris, Theorem C of arXiv:1105.1048), through amalgams along labels ∞ and membership algorithms; this moves membership in B_A, which is not closed under such amalgams, and so needs a larger graph in which every infinity splitting is over a common retract. The free-of-infinity pieces here are Artin groups built from Γ, not parabolic subgroups of A_Γ.
  artin-k-pi-1-reduces-to-free-of-infinity-parabolics: that is the analogous reduction of the K(π,1) conjecture; this is for the permutational Boone--Higman property.
  artin-hub-cones-reduce-pbh-to-coned-cliques: that uses one hub vertex and needs a divisibility condition on the labels at each vertex; this uses one clone per vertex, needs no condition on labels, and applies to every Artin group, at the price of larger complete pieces.
  artin-groups-satisfy-boone-higman: that is the open named problem, Problem 5.3(13) of arXiv:2306.16356v3; this reduces its permutational form, for all Artin groups at once, to the Artin groups whose defining graph has no label ∞.
---

**ESTABLISHED** (route `artin-pbh-reduces-to-free-of-infinity-artin-groups-proof`; lane proof, not independently reviewed). It inherits the status of `artin-pbh-reduces-along-folding-separators` and so of `pbh-class-closed-under-common-retract-amalgams` (lane proofs, not reviewed). `B_A` is the class of groups embedding in a group with a type (A) action; its finitely generated members embed in finitely presented simple groups and have solvable word problem. No priority is claimed; the construction was designed in lane bh-artin (2026-09-18).

## The clone double

Let `Γ` be a finite labelled graph on `V` (labels `m_ux ∈ {2, 3, ...}`, non-edges `m = ∞`). Fix integers `L, M >= 2`. The **clone double** `Γ^(L,M)` has vertex set `V ⊔ V̂`, with a clone `û` for each `u ∈ V`, and labels
- `m(u, x)` as in `Γ`, for `u, x ∈ V`;
- for `u ≠ x`: `m(u, x̂) = m(û, x) = m(û, x̂) = m_ux` if `m_ux < ∞`, and `= L` if `m_ux = ∞`;
- `m(u, û) = M`.

So `V̂` spans the complete graph `Γ^L` obtained from `Γ` by replacing every label `∞` by `L`, each `u` has the same labels as `û` to every other vertex, and the only non-edges of `Γ^(L,M)` are those of `Γ` itself.

## Statement

1. `A_Γ` is the standard parabolic subgroup of `A_(Γ^(L,M))` on `V`.
2. `A_(Γ^(L,M)) ∈ B_A` if and only if `A(Γ^(L,M)[Δ ∪ V̂]) ∈ B_A` for every maximal clique `Δ` of `Γ`. Each of these pieces has a complete defining graph.
3. **Class form.** Every Artin group lies in `B_A` if and only if every Artin group with complete defining graph (every label finite) lies in `B_A`.

## Scope

- The pieces contain `Γ^L` and commuting (for `M = 2`) twins of the vertices of `Δ`, so for a single graph they can be harder than `A_Γ` itself. For example the path `a -3- b -3- c` is a forest (`forest-artin-groups-satisfy-permutational-boone-higman`), but its pieces contain the Euclidean diagram Ã_3 on `{a, b, â, b̂}` with extra vertices attached. The value is the class-level equivalence and the mechanism, not a new single group.
- Free-of-infinity Artin groups include the open cases that no folding separation can reach, such as the all-3 complete graph `K_4` (`artin-hub-cones-reduce-pbh-to-coned-cliques`, Scope).
