---
rg: 2
id: products-with-z-have-rigid-compactifications-with-fixed-points
kind: claim
title: If a group carries a quantum-rigid SFT compactification, its product with Z carries one with two points fixed by the whole group
distinct_from:
  quantum-rigidity-is-product-stable: that multiplies two SFTs coordinatewise over a direct product, which gives the product compactification with no global fixed point; this is a cone, where one coordinate is a C_Z height and the other lives only on the seed slice, which produces global fixed points.
  tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts: that glues compactifications over a free product; this produces compactifications over a direct product with Z whose boundaries contain global fixed points, which the gluing then turns into isotropy.
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that conjectures that rigid minimal topologically free dynamics are amenable; this is the lemma that, fed into the gluing, refutes it.
---

**ESTABLISHED** (2026-09-18, lane proof by bh-break, elementary and self-contained, not reviewed).

## Statement

Let `Λ_0` be finitely generated with finite symmetric generating set `S_0`, and let `(Y_0, π_0)` be an
SFT compactification of `Λ_0` (definitions (C1), (C2) as in
`tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`). Put `Γ = Λ_0 × Z`, `Z = <t>`, with
generating set `S_0 ∪ {t^(±1)}`.

There is an SFT compactification `(Y, π)` of `Γ` such that:
1. `Y` is `D`-quantum rigid over every field `k` over which `Y_0` is `D_0`-quantum rigid, for every
   `D >= max(D_0, r_0, R_0, 1)`, where `r_0` is a radius of the rules of `Y_0` and `R_0` that of `π_0`;
2. `Y` contains two points `y_+`, `y_−` fixed by all of `Γ`.

In particular, if `Λ_0 ∈ 𝒞` then `Λ_0 × Z ∈ 𝒞` through a compactification with a `Γ`-fixed point.
Example: `Λ_0 = F_2 = Z * Z` (which lies in `𝒞` by part 4 of the tree-gluing theorem) gives a rigid
compactification of `F_2 × Z` with a point whose stabilizer is the non-amenable group `F_2 × Z`.

Route: `cone-compactifications-over-z-are-rigid-proof`.

## Lesson for general BH

Rigidity of a compactification says nothing about its boundary isotropy. A `C_Z` height over a
compactification of `Λ_0` pushes the whole of `Λ_0 × Z` onto the two ends `±∞`, and rigidity survives
because the height is a commutative chain and the fibre lives on a single slice.
