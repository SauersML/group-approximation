---
rg: 2
id: input-encoded-sft-groupoid-hosts-are-not-universal
kind: claim
title: Topological full groups of shifts of finite type, even with the graph chosen from the input, are not universal Boone--Higman hosts and contain no infinite Kazhdan group
distinct_from:
  complexity-bounded-host-classes-are-not-universal: that is the general principle for any class sharing a recursive word-problem bound; this applies it to every topological full group of a one-sided irreducible shift of finite type, over all finite graphs, and adds the Kazhdan exclusion.
  fw-subgroups-of-eventually-similar-groups-virtually-embed: that shows FW subgroups of canonical-similarity groups are finite when every vertex has out-degree at least two; this removes the out-degree hypothesis through a-T-menability and adds the complexity half, so both universal test inputs are excluded.
  self-similar-hosts-contain-only-residually-finite-groups: that excludes non-residually-finite inputs from self-similar hosts; this excludes hard inputs and Kazhdan inputs from shift-of-finite-type full groups, which are not self-similar.
artifacts:
  - research/artifacts/hl-bh-groupoid-embedding-2026-09-13.md
  - research/artifacts/ideas-boone-higman-2026-09-13.md
---

**ESTABLISHED** through `sft-groupoid-hosts-non-universality-proof` (not
independently reviewed; no novelty claimed).

## Statement

Let `K` be the class of groups that embed in the topological full group
`[[G|Y]]` of the etale groupoid `G` of some one-sided irreducible shift of finite
type without isolated points, for some clopen `Y`, over all finite graphs. This
includes Matui's finitely presented simple groups `D([[G]])` and the
Higman--Thompson groups.

1. **Complexity.** Some two-generated group with solvable word problem embeds in
   no member of `K`. The graph may depend on the input without changing this.
2. **Kazhdan inputs.** Every Kazhdan subgroup of a member of `K` is finite. So no
   infinite Kazhdan group, in particular not Deligne's non-residually-finite
   lattice, embeds in a member of `K`.

## Consequence for the idea log

Idea 1 of `research/artifacts/ideas-boone-higman-2026-09-13.md` ("input-encoded
Cuntz--Krieger full group", marked alive there) cannot give a universal
Boone--Higman host. Part 1 kills it for hard inputs, and part 2 kills it at the
universal test input of `research/artifacts/hl-bh-universal-route-map-2026-09-13.md`.

## What a groupoid host must do instead

- **Leave canonical similarities.** Its elements must not be finite tables of
  prefix replacements over one finite coding, or part 1 applies.
- **Carry non-residually-finite local structure.** For Kazhdan inputs with
  infinite center, `fw-subgroups-of-eventually-similar-groups-virtually-embed`
  and `fw-nst-inputs-virtually-embed-in-one-vertex-group` force a vertex group of
  the local groupoid to contain the input virtually, which is circular
  (`deligne-lattice-eventually-similar-hosts-are-circular`).
- **What is left:** non-expansive groupoids (unit spaces that are not shifts of
  finite type, or infinite graphs), for which no finite-presentation theorem is
  recorded on main.
