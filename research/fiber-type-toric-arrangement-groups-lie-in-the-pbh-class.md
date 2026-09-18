---
rg: 2
id: fiber-type-toric-arrangement-groups-lie-in-the-pbh-class
kind: claim
title: The fundamental group of the complement of a fiber-type (equivalently supersolvable) toric or elliptic arrangement lies in B_A and embeds in a finitely presented simple group
distinct_from:
  free-kernel-extensions-stay-in-the-permutational-class: that is the group-theoretic permanence lemma; this applies it along the Bibby--Delucchi towers of toric and elliptic arrangement bundles.
  euclidean-artin-toric-commensurability: that identifies Euclidean Artin groups with toric arrangement groups up to finite index; this is the Boone--Higman consequence for toric arrangements whose poset of layers is supersolvable.
artifacts:
  - research/artifacts/gq-bh-bh-verify-artin-euclidean-toric.md
---

**ESTABLISHED** through `fiber-type-toric-arrangement-groups-lie-in-the-pbh-class-proof`.
This is a lane proof and not independently reviewed. No priority is claimed.

**Setting** (Bibby--Delucchi, *Supersolvable posets and fiber-type abelian arrangements*,
arXiv:2202.11996v2, Selecta Math. 30 (2024) 89; Definitions 3.1.1 and 3.4.1, read from
the PDF). Let `G` be `C^×` (the toric case) or a complex elliptic curve (the elliptic
case). Let `Γ` be a free abelian group of finite rank, `T = Hom(Γ, G)`, and let
`A ⊂ Γ` be a finite essential, irredundant arrangement, with complement
`M(A) = T − ∪_(α ∈ A) H_α`.

**Statement.** If `A` is fiber-type, then `π_1(M(A))` lies in `B_A`. Equivalently, by
their Theorem 3.4.3, the conclusion holds when the poset of layers `P(A)` is
supersolvable. So `π_1(M(A))`, a finitely generated group, embeds in a finitely
presented simple group.

Strict supersolvability, which Bibby--Delucchi need for their iterated-semidirect-product
description of `π_1` (their Corollary B), is **not** needed.

**Examples.**
- The type-C_n toric arrangement `{v_i^2 = 1, v_i = v_j^(±1)}` in `(C^×)^n`. It is
  fiber-type by forgetting the last coordinate, with fibres `C^×` minus `2n` points.
  So the Euclidean Artin groups `A(C̃_n)` lie in `B_A`
  (`euclidean-artin-toric-commensurability`), reproving
  `c-tilde-artin-groups-satisfy-permutational-boone-higman` without braid pictures.
- Toric graphic arrangements of chordal graphs, and Dowling-type orbit configuration
  spaces on `C^×` and on elliptic curves (their Proposition 2.6.1 and Example 3.1.3).

**Limits.** Many Weyl toric arrangements are not fiber-type
(`weyl-toric-arrangements-b-d-e-f-are-not-fiber-type`). So this route does not reach
the Euclidean Artin groups of types B̃_n (n >= 3), D̃_n (n >= 4), Ẽ_6, Ẽ_7, Ẽ_8 and
F̃_4.
