---
rg: 2
id: jeandel-rao-minimal-subshift-is-morphic-image-of-labbe-shift
kind: claim
title: The Jeandel-Rao minimal subshift X_0 (ABHT's horizontally expansive fibre) is joined to Labbé's 19-tile shift by a chain of recognizable 2-dimensional morphisms onto up to a shift, one embedding and one shear conjugacy
requires:
  - minimal-aperiodic-wang-shift-exists
distinct_from:
  labbe-substitution-is-primitive-and-recognizable: that imports the self-similarity ω of Ω_U itself; this imports the chain of different morphisms that connects Ω_U to the Jeandel-Rao minimal subshift X_0.
  labbe-shift-is-a-toral-rotation-coding: that imports the rotation coding of Ω_U on R^2/Z^2; this records that X_0 is the coding of a different toral rotation (on R^2/Γ_0) and is linked to Ω_U only through morphisms.
  minimal-aperiodic-wang-shift-exists: that imports minimality and aperiodicity of Ω_U; this imports the substitutive link from Ω_U to X_0 and the identification of X_0 as the fibre used by ABHT.
---

**ESTABLISHED (import).** The sources were read as PDFs; see `jeandel-rao-substitutive-structure-citation`.
No claim is made here beyond the sources.

## Statement

Let `Ω_0` be the Jeandel–Rao Wang shift of 11 tiles. Let `Ω_U` be Labbé's 19-tile self-similar,
minimal, aperiodic Wang shift (`minimal-aperiodic-wang-shift-exists`).

1. **The chain** (Labbé, DCG 2021, Theorem 3 and Corollary 5). There are Wang shifts `Ω_1, …, Ω_12`
   with the following maps.
   - (i) `Ω_i ← Ω_(i+1)` via `ω_i`, for `i ∈ {0,1,2,3}` and for `i ∈ {6,…,11}`. Each `ω_i` is a
     recognizable 2-dimensional morphism in the sense of Labbé §2.9, and it is onto up to a shift:
     `\overline{ω_i(Ω_(i+1))}^σ = Ω_i`.
   - (ii) `ȷ: Ω_5 → Ω_4`, a topological conjugacy onto its image `X_4 := ȷ(Ω_5)`.
   - (iii) `η: Ω_6 → Ω_5`, a shear conjugacy for the matrix `(1 1; 0 1)`. That is, `η` is a
     homeomorphism with `σ^(Mk) ∘ η = η ∘ σ^k`.
   - (iv) `Ω_12` is equivalent to `Ω_U`. The two tile sets differ by bijections of the edge colours, so
     renaming letters is a conjugacy.
2. **Marker shape.** Every `ω_i` comes from Labbé's marker desubstitution (his Theorem 16 and
   Algorithm 2). It sends each tile either to one tile or to a domino of two tiles in one fixed
   direction `e_1` or `e_2`.
3. **The minimal subshift.** Put `X_3 = \overline{ω_3(X_4)}^σ`, `X_2 = \overline{ω_2(X_3)}^σ`,
   `X_1 = \overline{ω_1(X_2)}^σ` and `X_0 = \overline{ω_0(X_1)}^σ`.
   - Then `X_i ⊆ Ω_i` is a minimal aperiodic subshift for `0 <= i <= 4` (Corollary 5).
   - `X_0 ⊊ Ω_0`.
   - Every tiling in `X_0` decomposes uniquely into 19 patches (sizes 45 to 112) that are equivalent
     to the tiles of `U` (Theorem 1).
   - Labbé's `\overline{Y}^σ` means `∪_k σ^k Y`, which is closed here.
4. **Identification** (Labbé–Mann–McLoud-Mann, DCDS 2023, §1 and §4).
   - `X_0` is a subshift of finite type (description credited there to the DCG paper).
   - `X_0 = X_(P_0, R_0)` is the coding of the toral `Z^2`-rotation `x ↦ x + n` on `R^2/Γ_0`, where
     `Γ_0 = ⟨(φ, 0), (1, φ + 3)⟩` (their Theorem 4.1).
   - Its nonexpansive directions have exactly the slopes `{0, φ + 3, −3φ + 2, −φ + 5/2}` (their
     Theorem A). So the vertical direction is expansive.
5. **This is ABHT's fibre.** ABHT (arXiv:2204.11492v3, Theorem `theorem:SFT_Labbe` and §4) take exactly
   this `X_0`. They pass to a conjugate Wang tile shift that is vertically expansive with thickening 0,
   rotate it by `π/2` to get horizontal expansivity, and fold it along the flow on `F_n × Z`.

## Consequence recorded elsewhere

`jeandel-rao-minimal-subshift-is-quantum-rigid-iff-labbe-shift-is` turns item 1 into a Kakutani
equivalence of transformation groupoids.

## Lesson for general BH

Two different codings of related dynamics can carry different geometric properties.
- `Ω_U` codes a rotation of `R^2/Z^2`. Its fault directions include both axes, so it has no expansive
  rational direction and cannot be path-folded.
- `X_0` codes a rotation of `R^2/Γ_0` and has an expansive vertical direction.

The morphism chain joins the two, and any property that is invariant along the chain can be read off
whichever model is convenient.

DERIVATION
jeandel-rao-substitutive-structure-citation
