---
rg: 2
id: admissibly-oriented-artin-groups-satisfy-boone-higman
kind: claim
root: true
title: Every Artin group whose defining graph admits an admissible partial orientation embeds in a finitely presented simple group
distinct_from:
  admissibly-oriented-artin-groups-split-over-free-groups: that is the established splitting theorem over finite-rank free groups; this is the open Boone--Higman statement for the same class, reduced through that splitting.
  artin-groups-satisfy-boone-higman: that is the open named problem over all Artin groups; this is the 2-dimensional class covered by Jankiewicz's splitting theorem, including all large-type 3-generator Artin groups.
  bh-embeddability-survives-decidable-edge-hnn: that is the open permanence of Boone--Higman embeddability under HNN extensions over decidable finitely generated edges; this is one class of groups that permanence would settle.
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

**OPEN.** Let Γ be a labelled simple graph admitting an admissible partial
orientation in the sense of Jankiewicz, arXiv:2006.04717v2, Definition 4.2. Then
the Artin group `Art_Γ` embeds in a finitely presented simple group.

*Marked `root` because it is a natural class question in its own right.* It
contains every large-type Artin group on three generators, and it is part of
item (13) of Problem 5.3 in arXiv:2306.16356v3.

**The class.**
- It contains every large-type Artin group on three generators, and every
  large-type Artin group whose defining graph has an orientation in which each
  simple cycle is directed.
- An admissible orientation allows no label 2 on a 3-cycle (Jankiewicz, after
  Theorem 4.3). So among 3-generator Artin groups whose defining graph is a
  triangle, the class is exactly the large-type ones.
- The only one of those that the sources read already record as satisfying
  Boone--Higman is the Euclidean triangle `Art_333` (BLIW Corollary 12.8).

**Wiring.** `oriented-artin-bh-via-free-group-hnn-permanence` derives this claim
from `bh-embeddability-survives-decidable-edge-hnn`, through
`admissibly-oriented-artin-groups-split-over-free-groups`.

## Attempts

1. **BLIW generalized Baumslag--Solitar groups over F_2.** *Stops.* Theorem C of
   `bliw-locally-finite-tree-actions-embed-in-fp-simple-groups` needs finite-index
   edge inclusions. Jankiewicz's splitting `F_3 ∗_(F_7) F_4` of a large-type
   triangle group has `[F_4 : F_7] = 2`, but finite index in `F_3` is established
   only for (3,3,3) (Example 4.14). By the rank formula, finite index in `F_3`
   would force index 3.
2. **HNN permanence over finite-rank free edges.** *Reduces* this claim to
   `bh-embeddability-survives-decidable-edge-hnn` with a free base group. The
   base and the edge groups are free of finite rank, and membership in finitely
   generated subgroups of free groups is decidable (Stallings foldings). So the
   open input is exactly that permanence, specialized to free bases.
