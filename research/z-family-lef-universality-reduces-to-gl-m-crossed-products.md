---
rg: 2
id: z-family-lef-universality-reduces-to-gl-m-crossed-products
kind: claim
title: Every f.g. LEF group lies in some G_X iff every f.g. LEF group lies in some GL_m of a minimal subshift crossed product
distinct_from:
  lef-groups-embed-in-simple-kazhdan-lef-groups: that asks for SOME simple Kazhdan LEF envelope; this reduces the question for the note's Z-family G_X = EL_3(LC(X,F_2)⋊Z) to unit groups of matrix rings over LC(X,F_2)⋊Z.
---

**ESTABLISHED (unreviewed).** Write `R_X = LC(X,F_2) ⋊ Z` for an infinite minimal Z-subshift `X`, and
`G_X = EL_3(R_X)`. The following are equivalent.
- (i) Every finitely generated LEF group is a subgroup of some `G_Y`.
- (ii) Every finitely generated LEF group is a subgroup of `GL_m(R_X)` for some infinite minimal `X` and some `m`.

More precisely, if `Δ` is f.g. and `ρ : Δ -> GL_m(R_X)` is injective, then `g ↦ diag(ρ(g),1,1)` embeds `[Δ,Δ]` in
`EL_3(M_m(R_X)) ≅ G_(X^(m))`.

Route: `z-family-lef-universality-reduces-to-gl-m-crossed-products-proof`. Artifact:
`research/artifacts/sk-lef-embedding-d-z-family-2026-09-13-part1.md` §1.
