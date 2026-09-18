---
rg: 2
id: pisot-box-exchange-groups-satisfy-boone-higman
kind: claim
title: For algebraic units β_1, …, β_s with property (F), every finitely generated group of box exchanges whose i-th coordinates and translations lie in Q(β_i) embeds in a finitely presented simple group
requires:
  - pisot-stein-groups-are-contracting-rsgs
  - contracting-rsgs-embed-in-fp-simple-groups
distinct_from:
  quadratic-rectangle-exchange-groups-satisfy-boone-higman: that (bh-free-03) treats box exchanges with data in Z + α_i Z, α_i quadratic, through products of substitutive Sturmian codings; this allows every (F)-unit field in each coordinate and any rank of data, through the tensor product of β-shifts.
  pisot-interval-exchange-groups-satisfy-boone-higman: that is the one-dimensional case s = 1.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (lane proof, not reviewed; no priority claimed; inputs as in
`pisot-stein-groups-are-contracting-rsgs`).

## Statement

Let `β_1, …, β_s` be algebraic units `> 1` with property (F), not necessarily distinct, and let
`Γ_i ⊆ Q(β_i)` be finitely generated subgroups. Let `BEx(Γ_1,…,Γ_s)` be the group of bijections of a box
`∏[0,ℓ_i)`, `ℓ_i ∈ Γ_i`, that translate each piece of a finite partition into boxes `∏[a_i,b_i)` with
`a_i, b_i ∈ Γ_i`, by vectors in `∏Γ_i`. Then `BEx(Γ_1,…,Γ_s)` and all its subgroups embed in finitely presented
simple groups.

## Proof

1. **Reduction.** Rescale coordinatewise to put all data in `Z[β_i]`, and then embed the box in `[0,1)^s` by
   `x_i ↦ β_i^{−m_i}x_i`. Translations stay translations, so this is an injective homomorphism into the
   box-exchange group of `[0,1)^s` with data in `Z[β_i]`.
2. **Coding.** Code `[0,1)^s` by the tensor product SFT `X = X_{β_1} ⊗ … ⊗ X_{β_s}`: one edge per coordinate
   per step, so cones are products of cylinders of a common level.
   - Each `X_{β_i}` is primitive, since 0 is always admissible, so the tensor product has an irreducible core.
   - Let `G` be the group of homeomorphisms of the Cantorized cube that act on the pieces of a finite box
     partition by `x ↦ (β_1^{k}x_1 + c_1, …, β_s^{k}x_s + c_s)`, with one common exponent `k` and `c_i ∈ Z[β_i]`.
   - `G` contains the box exchanges (`k = 0`) and the tensor Thompson group `V_X`, whose canonical similarities
     change every coordinate's level by the same amount.
3. **Finite nucleus.** Take a deep product cone of level `n` and an affine piece with exponent `k`.
   - By step 3 of `pisot-stein-groups-are-contracting-rsgs-proof`, applied in each coordinate, the image
     interval in coordinate `i` lies in a cylinder of level `≥ n − k − L_{β_i}` and not deeper than
     `n − k + E_i`.
   - The smallest product cone containing the image has common level `m = min_i` of those levels. So
     `m ∈ [n − k − L, n − k + E]`, with `L = max L_{β_i}` and `E = max E_i`.
   - Each coordinate's local slope exponent `k + m − n` therefore lies in `[−L, E]`.
   - Each offset lies in a finite set, by step 4 applied coordinatewise at level `m`.
   - So local actions at deep cones range over a finite set, independent of the element.
4. **Conclusion.** `G` is a contracting RSG containing `V_X`, so it embeds in a finitely presented simple group
   (`contracting-rsgs-embed-in-fp-simple-groups`), and so do its subgroups. ∎

## Remark

A common exponent `k` is essential in this proof. With independent exponents `k_i` per coordinate the
coordinate slopes `k_i − max_j k_j` are unbounded, so the nucleus would be infinite, and nothing is claimed for
such groups.
