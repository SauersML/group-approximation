---
rg: 2
id: edge-split-ore-via-synchronization-and-tree-domination
kind: route
title: Synchronization of nested unimodular cells and tree domination of descendant dissections give common edge-split refinements in every rank
target: edge-split-operad-has-common-refinements
requires:
  - unimodular-cells-synchronize-under-edge-splits
  - edge-split-descendant-dissections-are-tree-dominated
  - edge-split-ore-iff-synchronization-and-tree-domination
---

Lane bh-free-54, 2026-09-18. This route replaces the dead route
`edge-split-ore-via-atom-plane-restriction` (see
`edge-split-order-is-not-geometric-refinement`). It works for every `m`.

1. **Synchronization.** `unimodular-cells-synchronize-under-edge-splits` gives
   (Sync_m). By part 2 of `edge-split-ore-iff-synchronization-and-tree-domination`,
   this gives (Sync′). For `m = 2`, (Sync_m) is proved except at totally irrational
   rays (`rank-two-synchronization-off-totally-irrational-rays`).
2. **Tree domination.** This is `edge-split-descendant-dissections-are-tree-dominated`.
3. **Conclusion.** Part 1 of the equivalence node turns (Sync′) ∧ (TD) into common
   `≥_E`-upper bounds.
4. **A bonus from the same premises.** Part 3 of that node gives
   `π_1(𝒪_E, Δ) = 𝒯_m`, which is saturation.
