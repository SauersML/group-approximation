---
rg: 2
id: admissibly-oriented-artin-groups-split-over-free-groups
kind: claim
title: An Artin group whose defining graph admits an admissible partial orientation splits over finite-rank free groups
distinct_from:
  admissibly-oriented-artin-groups-satisfy-boone-higman: that is the open Boone--Higman statement for this class; this is the literature splitting theorem it is reduced through.
  baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman: that imports BLIW families, whose graphs of groups have finite-index edge inclusions; this is Jankiewicz's splitting over finite-rank free groups, where finite index is not asserted.
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

**ESTABLISHED (literature import).** Source: K. Jankiewicz, *Residual finiteness
of certain 2-dimensional Artin groups*, arXiv:2006.04717v2, text extracted on
MSI.

**Definition 4.2** (verbatim): a partial orientation ι on a labelled simple
graph Γ is *admissible* if
- "ι(e) for an edge e is defined if and only if the label of e is ≥ 3, and
- no cycle in Γ is almost misdirected."

**Theorem 4.3** (verbatim): "Suppose Γ admits an admissible partial orientation.
If Γ is a bipartite graph with all labels even, then Art Γ splits as an
HNN-extension A∗B, where A,B are finite rank free groups. Otherwise ArtΓ splits
as a free product with amalgamation A∗C B where A,B,C are finite rank free
groups. Moreover, rk A =|E(Γ)|, rkB = 1−|V (Γ)| + 2|E(Γ)|, and C is an index 2
subgroup of B, so rkC = 1− 2|V (Γ)| + 4|E(Γ)|."

**Examples** listed after Theorem 4.3:
- "All large type 3-generator Artin groups."
- "More generally, large type Artin group whose defining graph Γ admits an
  orientation where each simple cycle is directed."

**Corollary 4.13:** for `M,N,P >= 3`, `Art_MNP = A ∗_C B` with `A ≅ F_3`,
`B ≅ F_4`, `C ≅ F_7` and `[B : C] = 2`.

The paper also proves that all Artin groups satisfying Theorem 4.3 are CAT(0)
(via Brady--McCammond) and 2-dimensional.

**Scope.** Finite index of `C` in `A` is not part of the theorem. Example 4.14
states a degree-3 covering only for `Art_333`.

The route is `jankiewicz-artin-splitting-theorem-citation`.
