---
rg: 2
id: forest-artin-groups-satisfy-permutational-boone-higman
kind: claim
title: Every Artin group whose defining graph is a forest, with arbitrary labels, lies in the permutational Boone--Higman class and embeds in a finitely presented simple group
distinct_from:
  even-fc-artin-groups-satisfy-permutational-boone-higman: that covers even labels (including even triangle-free graphs); this covers forests with any labels, odd ones included, where the even-boundary retractions of that node do not exist.
  artin-groups-satisfy-boone-higman: that is the open named problem, Problem 5.3(13) of arXiv:2306.16356v3; this settles its forest-defined part in the permutational form, from primary sources and landed nodes only.
  artin-pbh-reduces-along-folding-separators: that is the general block reduction; this is its consequence when every block is an edge or a vertex.
---

**ESTABLISHED** (route `forest-artin-groups-satisfy-permutational-boone-higman-proof`; lane proof, not independently reviewed). It inherits the status of `pbh-class-closed-under-common-retract-amalgams` (lane proof, not reviewed).

## Statement

Let `Γ` be a finite forest, each edge labelled by some `m ∈ {2, 3, 4, ...}`. Then `A_Γ ∈ B_A`. Consequently `A_Γ` embeds in a finitely presented simple group (a twisted Brin--Thompson group), and so does every finite direct product of such groups with other members of `B_A`, and every finite-index overgroup of one.

## Relation to what was known

- **Plain Boone--Higman, secondary source.** Jankiewicz, arXiv:2103.01343, introduction: forest-defined Artin groups "are the fundamental groups of graph manifolds with boundary [Bru92], [HM99], and so they are virtually special [Liu13], [PW14]". With Scott's theorem that gives an embedding in a finitely presented simple group. `artin-groups-satisfy-boone-higman` recorded this but did not import it, because Brunner and Hermiller--Meier were read only through that quotation.
- **This node** needs none of the 3-manifold theory: only dihedral Artin groups, the length retractions onto `<v>`, and common-retract amalgams. It also gives the stronger permutational form `B_A`, which is closed under direct products and finite-index overgroups. No priority is claimed.

## Examples

- Every tree with all labels 3, e.g. the path `a -3- b -3- c` (with `a, c` not adjacent), which is of FC type with a single odd component that is not a clique, so it is outside the odd-component reduction and its Corollary E.
- Trees mixing odd and even labels, and stars `K_(1,n)` with arbitrary labels.
