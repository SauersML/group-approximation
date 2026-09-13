---
rg: 2
id: centralizer-criterion-for-non-inner-amenability
kind: claim
title: "A group with a non-amenable subgroup whose centralizers of nontrivial elements are all amenable is not inner amenable"
---

Let G be a discrete group and `H ≤ G` a non-amenable subgroup such that
`C_H(g) = {h ∈ H : hgh^{-1} = g}` is amenable for every `g ∈ G ∖ {e}`. Then G is not inner
amenable, and neither is any subgroup of G containing H.

G is inner amenable if some finitely additive probability measure on `G ∖ {e}` is invariant under
conjugation.

The derivation is one line. H acts on `G ∖ {e}` by conjugation, with stabilizers `C_H(g)`. A
conjugation-invariant mean would make this action of the non-amenable group H amenable, while all
its stabilizers are amenable, which Rosenblatt's theorem forbids.

Route: `centralizer-criterion-for-non-inner-amenability-citation`.
