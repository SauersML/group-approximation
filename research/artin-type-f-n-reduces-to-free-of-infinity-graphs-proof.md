---
rg: 2
id: artin-type-f-n-reduces-to-free-of-infinity-graphs-proof
kind: route
title: "Proof: split along an infinite label into an amalgam of parabolic subgroups and glue classifying spaces with finite skeleta"
target: artin-type-f-n-reduces-to-free-of-infinity-graphs
requires: []
---

Fix `n` finite (for `n = ∞` apply the finite cases for every `n`; for `n = 1` there is
nothing to prove, since `A_Γ` is finitely generated). Argue by induction on `|S|`.

If `S` is free of infinity, the hypothesis applied to `T = S` is the conclusion. This
covers `|S| ≤ 1`.

Otherwise choose `s ≠ t` in `S` with `m_st = ∞`, and put `T = S ∖ {s}`,
`R = S ∖ {t}`, `U = T ∩ R = S ∖ {s, t}`.

**1. Splitting.** Each defining relation of `A_Γ` is a braid relation between two
generators `u ≠ v` with `m_uv < ∞`. Then `{u, v} ≠ {s, t}`, so `{u, v} ⊆ T` or
`{u, v} ⊆ R`, and the relation is a defining relation of `A_{Γ_T}` or of `A_{Γ_R}`.
So the presentation of `A_Γ` is the union of the presentations of `A_{Γ_T}` and
`A_{Γ_R}`, with the generators in `U` identified, and `A_Γ` is the pushout of
`A_{Γ_T} ← A_{Γ_U} → A_{Γ_R}` along the maps sending each generator to itself. These
maps are injective (van der Lek; Paris, arXiv:1211.7339, Theorem 5.4). A pushout of
groups along injective homomorphisms is the amalgamated free product, so

`A_Γ = A_T *_{A_U} A_R`.

**2. Induction.** `T`, `R`, `U` have fewer elements than `S`. A free-of-infinity subset
of `T`, `R` or `U` is a free-of-infinity subset of `S`, and its standard parabolic subgroup
in `A_{Γ_T}` (say) is the same group as in `A_Γ`, again by Theorem 5.4. So the induction
hypothesis applies to `Γ_T`, `Γ_R`, `Γ_U`: the groups `A_T`, `A_R`, `A_U` are of type
`F_n`.

**3. Amalgams.** Let `H`, `L` be of type `F_n` and `K` of type `F_{n−1}`, with injective
homomorphisms `K → H` and `K → L`. Choose `K(π,1)` CW complexes `X_H`, `X_L` with finite
`n`-skeleta and `X_K` with finite `(n − 1)`-skeleton, and cellular maps `f : X_K → X_H`,
`g : X_K → X_L` inducing the given homomorphisms (cellular approximation). Let `X` be the
double mapping cylinder `X_H ∪_f (X_K × [0, 1]) ∪_g X_L`. Its open cells are those of
`X_H`, those of `X_L`, and the products `e × (0, 1)` for cells `e` of `X_K`, so `X` has
finitely many cells in each dimension `≤ n`. By van Kampen's theorem
`π_1(X) = H *_K L`. The universal cover of `X` is a tree of spaces over the Bass–Serre
tree of the amalgam: its vertex spaces are components of the preimages of `X_H` and
`X_L`, which are universal covers because `H` and `L` inject into `H *_K L`, and its edge
spaces are products of universal covers of `X_K` (which injects as well) with `[0, 1]`.
All of these are contractible, and a tree of contractible spaces is contractible (the
classical asphericity theorem for graphs of aspherical spaces, used in exactly this form
in the proof of Theorem 5.6 of arXiv:1211.7339). So `X` is a `K(H *_K L, 1)` with finite
`n`-skeleton, and `H *_K L` is of type `F_n`.

**4. Conclusion.** Apply step 3 with `H = A_T`, `L = A_R`, `K = A_U` (type `F_n`, hence
`F_{n−1}`): `A_Γ` is of type `F_n`. ∎

The only literature input is the injectivity of standard parabolic subgroups (van der
Lek, 1983).
