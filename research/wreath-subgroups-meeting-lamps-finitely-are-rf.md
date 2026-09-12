---
rg: 2
id: wreath-subgroups-meeting-lamps-finitely-are-rf
kind: claim
title: A subgroup of a finite-lamp permutational wreath over a residually finite base that meets the lamp kernel finitely is residually finite
distinct_from:
  kun-thom-nonsofic-wreath: that is nonsoficity of the whole Kun--Thom wreath; this shows that every subgroup meeting the lamp kernel finitely is residually finite, so nonsoficity lives only in subgroups with infinite lamp part.
  nested-rigid-defects-live-in-nonsofic-kazhdan-groups: that says a refutation of the nested-defect criterion needs a surjunctive group containing a nonsofic Kazhdan group; this excludes such subgroups of the Kun--Thom wreaths whose lamp part is finite.
artifacts:
  - research/artifacts/defect-window-automata-2026-09-12.md
---

**ESTABLISHED** by `wreath-finite-lamp-meeting-rf-proof`.

Let `A` be finite, `G` residually finite acting on a set `X`, and
`W = (⊕_X A) ⋊ G`. Every subgroup `G' <= W` with `G' ∩ ⊕_X A` finite is residually
finite. In particular it is sofic.

**Consequence.** Every nonsofic subgroup of a Kun--Thom wreath
`(Z/2) wr_(G/Gamma) G` meets the lamp kernel in an infinite elementary abelian
2-group. So does every nonsofic Kazhdan subgroup that could carry a nested rigid
defect.
