---
rg: 2
id: triangle-free-all-3-artin-groups-satisfy-pbh
kind: claim
title: Every Artin group whose defining graph is triangle-free with all edge labels 3, e.g. the all-3 four-cycle, lies in the permutational Boone--Higman class and embeds in a finitely presented simple group
distinct_from:
  forest-artin-groups-satisfy-permutational-boone-higman: that covers forests, whose blocks are edges; this covers triangle-free graphs with cycles, which are 2-connected where they are not forests and have no foldable separator of their own.
  admissibly-oriented-artin-groups-satisfy-boone-higman: that is the open 2-dimensional class reduced to decidable-edge HNN permanence; it contains, e.g., the all-3 four-cycle with its cyclic orientation, which this node settles directly without HNN permanence.
  even-fc-artin-groups-satisfy-permutational-boone-higman: that covers even labels; this covers the all-odd label 3, where even-boundary retractions do not exist.
  artin-groups-satisfy-boone-higman: that is the open named problem, Problem 5.3(13) of arXiv:2306.16356v3; this settles an infinite family of 2-dimensional large-type Artin groups that are not virtually cocompactly cubulated.
---

**ESTABLISHED** (route `triangle-free-all-3-artin-groups-satisfy-pbh-proof`; lane proof, not independently reviewed). It inherits the status of `artin-hub-cones-reduce-pbh-to-coned-cliques` and, through it, of `pbh-class-closed-under-common-retract-amalgams` (lane proofs, not reviewed). No priority is claimed; see the hub-cone route for the bounded check.

## Statement

Let `Γ` be a finite simplicial graph with no triangles, every edge labelled 3 (non-edges `∞`). Then `A_Γ ∈ B_A`. So `A_Γ` embeds in a finitely presented simple group (a twisted Brin--Thompson group), and so does every finite direct product of such groups with members of `B_A`, and every finite-index overgroup of one.

## Examples and why they were open

- **The all-3 four-cycle** `A = <a, b, c, d | aba = bab, bcb = cbc, cdc = dcd, dad = ada>`, with `a, c` and `b, d` free.
  - It is two-dimensional of large type. By Huang--Jankiewicz--Przytycki, arXiv:1510.08493v1, Theorem 1.1 (quoted in `research/artifacts/bh-common-retract-amalgams-even-artin-2026-09-16.md`, §8), it is not virtually cocompactly cubulated: its defining graph is connected, is not a vertex or an edge, and has an interior edge labelled 3. So the virtually-special route to linearity is closed.
  - Its defining graph is 2-connected with a single odd component, so neither `artin-pbh-reduces-to-odd-component-cliques` nor `artin-pbh-reduces-along-folding-separators` applies. Over its own separator `{a, c}`, `<a, c> ≅ F_2` is not a retract of `A(a -3- b -3- c)`: a retraction would send `b` to some `w ∈ <a, c>` with `a w a = w a w`, which in a free group forces `w = a`, and then `bcb = cbc` would give `aca = cac` in `F(a, c)`.
  - It lies in the admissibly oriented class (orient the cycle), which `admissibly-oriented-artin-groups-satisfy-boone-higman` reduces to the open decidable-edge HNN permanence.
- **All-3 cycles of every length ≥ 4, all-3 bipartite graphs, the all-3 Petersen graph, all-3 hypercube graphs.**

## Remark: labels 3 and 6 together

With hub labels `k_v = 3` on vertices meeting a 3-edge and `k_v = 2` elsewhere, the same argument covers triangle-free graphs with labels in `{3} ∪ 2Z` in which every vertex on a 3-edge meets only labels 3 and 6, and no 6-edge joins two such vertices. The new pieces are the triangles `(6, 3, 2)` of type G̃_2 and `(m, 2, 2)` (spherical). This needs `A(G̃_2) ∈ B_A`, which `artin-groups-satisfy-boone-higman` records from BLIW (arXiv:2408.05673, Corollary 12.8 and Remark 12.7) but no node here imports as a claim, so the remark is conditional on that import.
