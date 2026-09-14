---
rg: 2
id: amenable-perfect-groups-embed-in-kazhdan-linear-sofic
kind: claim
title: Every finitely generated perfect amenable group embeds in an infinite simple Kazhdan linear sofic group
distinct_from:
  rf-groups-embed-in-simple-kazhdan-lef-groups: that covers residually finite groups and lands them in a LEF envelope; this covers perfect amenable groups, which need not be residually finite, and lands them in a linear sofic envelope.
  simple-kazhdan-linear-sofic-non-lef-group-exists: that exhibits one such group over an Abels--Pruefer subflow; this is an embedding theorem for a whole class of subgroups.
  amenable-groups-embed-in-simple-kazhdan-linear-sofic: that asserts the same conclusion for every amenable group through the swap double; its embedding step is contradicted by wreath-products-keep-the-abelianization-of-the-base, and this claim keeps only the perfect case, which needs no overgroup.
artifacts:
  - research/artifacts/sk-sofic-embedding-a-rank-route-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be a finitely generated perfect amenable group. Then `Γ` is a subgroup of a group
`G` that is infinite, finitely generated, simple, has Kazhdan's property (T), and is `F_2`-linear sofic. One may take
`G = EL_3(LC(X,F_2) ⋊ Γ)` for a free minimal subflow `X ⊆ 2^Γ`.

The hypotheses are used as follows: perfect for the embedding, amenable for the rank models, finitely generated for
property (T) and for finite generation of `G`.

**Examples outside the residually finite theorem.** Every finitely generated simple amenable group qualifies, and no
such group is residually finite. The derived topological full group `[[T]]'` of a minimal `Z`-subshift is one: finitely
generated (Matui), simple, and amenable (Juschenko--Monod).

**Scope.** For a non-perfect amenable `Γ` the statement is open. It would need a finitely generated perfect amenable
overgroup, and `wreath-products-keep-the-abelianization-of-the-base` rules out the wreath-product construction, while
the Ore overgroup of `rf-groups-lie-in-derived-subgroups-of-rf-groups` needs residual finiteness. The envelope is linear
sofic and not sofic: see `rank-models-give-no-hamming-models-through-vector-actions`.

Route: `amenable-perfect-groups-embed-in-kazhdan-linear-sofic-proof`.
