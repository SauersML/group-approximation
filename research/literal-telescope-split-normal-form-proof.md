---
rg: 2
id: literal-telescope-split-normal-form-proof
kind: route
title: Ascending HNN plus Bass-Serre computation of the literal splitting
target: literal-telescope-split-normal-form
requires: [literal-kazhdan-clifford-inputs, literal-base-presentation-complete]
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
  - non_mf_groups_exist.tex
---

## Direct proof

Sections 1-3 of the artifact.  The twenty base relators present
`B = Z^3 semidirect_product SL_3(Z)` — that is the prerequisite
`literal-base-presentation-complete`, listed explicitly because the
identifications `Gamma_n ~= Z^3 semidirect SL_3(Z)` and `V ~= <Gammabar, D>`
below are statements about the PRESENTED base and were conditional on it until
`LiteralBaseCompleteness.baseAffineEquiv` closed the gap; the split structure
over the presented telescope never needed it.  The six stable-letter relators
are exactly the
ascending HNN presentation for the doubling endomorphism `alpha`, injective
with index-eight image by `literal-kazhdan-clifford-inputs` and
`lem:linear`.  Hence that subpresentation is
`V = lim(B,alpha) semidirect_product Z`, the base embeds, and the manuscript's
proof of Theorem E identifies `V` with `<Gammabar, D> <= GL_4(Q)`.

Adjoining `c` with `c^2 = 1` and `[c, B] = 1` is by definition the pushout
`V *_B (B x Z/2)`, so the relator-deleted group is `Ehat`.  Setting `c -> 1`
respects every relator, giving a retraction `Ehat -> V` that kills `w` and
hence descends to `E`; the composite `V -> E -> V` is the identity, so both
`Ehat` and `E` split over their lamp kernels.  A Bass-Serre computation on the
tree of the amalgam (normal subgroup meets the conjugates of `V` and of `B`
trivially and each conjugate of `<c>` in order two; quotient graph a star,
hence a tree) gives `ker(Ehat -> V) = *_{X} Z/2` with `X = V/B`.  Finally the
normal closure of the eight commutators `[w,g]` equals the normal closure of
`[w, Ehat]`, so `E` is the universal quotient of `Ehat` making `w` central.
