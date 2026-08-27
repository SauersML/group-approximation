---
rg: 2
id: literal-telescope-split-normal-form
kind: claim
title: The literal group splits as lamp-by-telescope over an explicit linear quotient
distinct_from:
  literal-group-structural-normal-form: That root asks jointly for a normal form, a kernel description and the word problem; this claim isolates only the split extension `E = N ⋊ V` and the identification of `V`.
  literal-lamp-kernel-clifford-block-amalgam: This claim identifies the quotient `V` and the splitting; the other identifies the isomorphism type of the lamp kernel `N`.
artifacts:
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
  - non_mf_groups_exist.tex
---

Let `E` be the literal forty-one-relator group and `N = <<c>>` the normal
closure of the lamp generator.  Then the assignment `c -> 1` is a retraction
`E -> V` onto the telescope group of the manuscript, so

    E = N_E semidirect_product V,

where `V = (Z[1/2]^3 semidirect_product SL_3(Z)) semidirect_product Z` is the
ascending HNN extension of the literal base `B = Z^3 semidirect_product
SL_3(Z)` along the doubling endomorphism, realized faithfully as
`<Gammabar, diag(2,2,2,1)> <= GL_4(Q)`.  Every element of `E` is uniquely a
product `p g` with `p` in the lamp kernel and `g` in `V`.

Deleting the eight centrality relators gives the free lamp group
`Ehat = V *_B (B x Z/2) = (*_X Z/2) semidirect_product V` with `X = V/B`, and
`E` is its largest quotient in which the marked word `w = [c_a, c_b]`
(`a = tau o`, `b = v_1 tau o`) becomes central.
