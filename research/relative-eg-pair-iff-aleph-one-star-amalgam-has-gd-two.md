---
rg: 2
id: relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two
kind: claim
title: A countable subgroup pair H <= G has a nested pair of aspherical 2-complexes iff every 2-dimensional K(H,1) extends iff the aleph_1-fold amalgam of G over H has geometric dimension 2
distinct_from:
  relative-countable-eg-gives-eg-for-aleph-one-groups: that proves REG_omega implies EG up to aleph_1; this is a per-pair statement giving the converse mechanism (a single uncountable amalgam forces the relative realization) and the independence of the choice of K.
  continuous-free-chain-unions-have-gd-two: that proves the relative extension unconditionally when H is free; this characterizes the relative extension for arbitrary countable H by the geometric dimension of one group.
  eilenberg-ganea-conjecture: that is the absolute conjecture; this is an equivalence between a relative geometric property of a pair and gd of an uncountable amalgam, with no cd hypothesis needed for the equivalence.
artifacts: []
---

**ESTABLISHED** through `relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two-proof`. Unreviewed.

## Notation

Let `H ≤ G` be countable groups. For a cardinal `κ`, let `Γ_κ(H,G) = ⁎_H {G_ξ : ξ < κ}` be the amalgamated free product of `κ` copies `G_ξ` of `G` over the common subgroup `H`.

Call the pair **realizable**, written `RP(H,G)`, if some 2-dimensional aspherical complex `X` with `π_1 X ≅ G` contains a subcomplex `K` that is aspherical, with `K ↪ X` inducing the inclusion `H ≤ G` on `π_1`.

## Claim

For countable `H ≤ G` the following are equivalent.

- **(a)** `RP(H,G)`.
- **(b)** A 2-dimensional `K(H,1)` exists, and *every* 2-dimensional `K(H,1)` is a subcomplex of some 2-dimensional `K(G,1)`, inducing `H ≤ G`. This is the conclusion of REG_ω for this pair.
- **(c)** `gd Γ_{ℵ_1}(H,G) ≤ 2`.
- **(d)** `gd Γ_κ(H,G) ≤ 2` for every cardinal `κ`.

Moreover, if `cd G ≤ 2` and `pd_{ZG} I_{G/H} ≤ 1`, then `cd Γ_κ(H,G) ≤ 2` for every `κ`.

## What is new

- **(a) ⇒ (b), the swap lemma.** Realizability does not depend on the chosen `K`. Given `K' ⊆ X'` and any other 2-dimensional `K(H,1)` `K`, the adjunction space `X' ∪_g K` along a cellular homotopy equivalence `g: K' → K` is a 2-dimensional `K(G,1)` containing `K`. This uses the gluing theorem for cofibrations. So the "arbitrary `K`" in REG_ω costs nothing.
- **(c) ⇒ (a), slicing an uncountable amalgam.** Let `X` be a 2-dimensional `K(Γ_{ℵ_1},1)` and let `M` be a countable elementary submodel containing `X`. Then:
  - the cells of `X` lying in `M` form a `π_1`-injective subcomplex with `π_1 = Γ_δ = ⁎_H {G_ξ : ξ < δ}`, where `δ = M ∩ ω_1`;
  - in the covering space of `X` for `G_δ`, a lift of that subcomplex carries `Γ_δ ∩ G_δ = H`.

  Uncountability is used only to make the slice a proper sub-amalgam. For a countable amalgam the closure argument swallows everything.
- **No cohomological hypothesis** enters the equivalence (a) ⇔ (c). The cd and pd hypotheses are needed only to know that `Γ_{ℵ_1}` is a legitimate test case for the Eilenberg--Ganea conjecture.

## Consequence

See `aleph-one-eg-is-equivalent-to-relative-countable-eg`: REG_ω is equivalent to the Eilenberg--Ganea conjecture for groups of cardinality `≤ ℵ_1`. A counterexample of size `ℵ_1` can always be taken to be `Γ_{ℵ_1}(H,G)` for a single countable pair.
