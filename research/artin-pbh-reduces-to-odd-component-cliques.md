---
rg: 2
id: artin-pbh-reduces-to-odd-component-cliques
kind: claim
title: An Artin group lies in the permutational Boone--Higman class iff the Artin groups on the unions of odd components over cliques of the odd-component graph do; for even labels, iff every clique Artin group does
distinct_from:
  artin-word-problem-reduces-to-free-of-infinity-graphs: that transfers solvability of the word problem from the maximal free-of-infinity parabolic subgroups, splitting along labels ∞ and using membership algorithms; this transfers membership in B_A from the unions of odd components over cliques of Q, splitting along even boundaries and using homomorphic retractions, which do not exist across odd edges.
  artin-groups-satisfy-boone-higman: that is the open problem for all Artin groups; this is an equivalence that moves the permutational form of it from a graph to its odd-saturated clique subgraphs, and settles nothing when Q is complete.
  pbh-class-closed-under-graph-products: that is closure under graph products and centralizing retract amalgams; the even splittings of Artin groups used here are twisted, as for the labelled 4-cycle, so they need the common-retract amalgams.
  artin-k-pi-1-reduces-to-free-of-infinity-parabolics: that reduces asphericity to free-of-infinity parabolic subgroups; this reduces permutational Boone--Higman to odd-saturated clique subgraphs, a different family of parabolic subgroups, through retractions rather than cube complexes.
artifacts:
  - research/artifacts/bh-common-retract-amalgams-even-artin-2026-09-16.md
---

Proved by the route `artin-pbh-odd-component-reduction-proof`. It has not been
independently reviewed. `B_A` is as in
`boone-higman-type-a-class-closed-under-finite-extensions`.

## Setting

- `Γ` is a finite simplicial graph. Every edge `uv` carries a label
  `m_uv ∈ {2, 3, 4, ...}`, and a non-edge means `m_uv = ∞`.
- `A_Γ` is the Artin group. For `S ⊆ V(Γ)`, `A_S` is the Artin group of the induced
  labelled subgraph `Γ[S]`.
- The **odd components** are the connected components of the graph on `V(Γ)` whose
  edges are the odd-labelled edges. Isolated vertices count as components.
- `Q` is the graph whose vertices are the odd components, with two joined when some
  edge of `Γ` joins them.

## Statement

1. `A_Γ ∈ B_A` if and only if `A_S ∈ B_A` for every union `S` of the odd components
   in a clique of `Q`.
2. **Even labels.** If every label is even, then `Q = Γ`. So `A_Γ ∈ B_A` iff
   `A_Δ ∈ B_A` for every (maximal) clique `Δ` of `Γ`.
3. In both cases membership in `B_A` gives an embedding in a finitely presented simple
   group and solvable word problem (`type-a-action-gives-boone-higman-for-subgroups`).

Two tools, both proved in the route:
- **Retractions.** If every edge from `Λ` to `V \ Λ` is even, then killing the
  generators outside `Λ` is a retraction `A_Γ -> A_Λ`.
- **Splittings.** Suppose `V = V_1 ∪ V_2`, no edge joins `V_1 \ V_2` to `V_2 \ V_1`,
  and the boundary of `Λ = V_1 ∩ V_2` is even. Then
  `A_Γ = A_(V_1) *_(A_Λ) A_(V_2)`, over a common retract.

## Consequences recorded elsewhere

- `even-fc-artin-groups-satisfy-permutational-boone-higman`: every even Artin group of
  FC type, and more.
- **FC type with clustered odd components.** Suppose `A_Γ` is of FC type, every odd
  component spans a clique, and adjacent odd components are completely joined. Then
  every union over a clique of `Q` is a clique of `Γ`, which is spherical. So
  `A_Γ ∈ B_A` by `spherical-artin-groups-satisfy-permutational-boone-higman`.
  - Example: `m_ab = 3`, `m_bc = 4`, `m_ac = 2`, `m_cd = 4`, `m_de = 3`, `m_ce = 2`,
    and no other edges. This gives `A(B_3) *_(<c>) A(B_3)`.

## Scope

- **It does nothing when `Q` is complete**, for instance when `Γ` is connected with
  all labels odd.
  - Odd edges genuinely block homomorphic retractions. In `A_3`, the subgroup
    `<s, u> ≅ Z^2` is not a retract, because `A_3^ab = Z`.
- **For even graphs** it reduces the permutational form of Boone--Higman to
  irreducible even Artin groups on complete graphs. The open ones start with the
  hyperbolic triangles `(2,4,6)`, `(2,6,6)`, `(4,4,4)` and `(4,4,6)`.

**Verification (bh-verify-artin, 2026-09-18; lane check, not an external review).** PASS. The retraction lemma, the pushout splitting and the induction were re-checked. The claim rests on `pbh-class-closed-under-common-retract-amalgams`, whose Steps 0--4 were re-derived. See `research/artifacts/gq-bh-bh-verify-artin-report.md`.
