---
rg: 2
id: sl-2-q-via-hecke-overgroup-and-bliw
kind: route
title: Ihara's amalgam plus a finitely presented Hecke overgroup of SL_2(Z_(l)) puts SL_2(Q) in an HNN extension covered by Bux--Llosa Isenrich--Wu Theorem C
target: sl-2-q-embeds-in-fp-simple-group
requires:
  - sl-2-z-localized-has-fp-hecke-overgroup
  - sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell
  - bliw-locally-finite-tree-actions-embed-in-fp-simple-groups
---

Lane proof of the implication, not independently reviewed. Take `l, Λ, ι, C_1,
C_2, φ` as in `sl-2-z-localized-has-fp-hecke-overgroup`, and let
`K = <Λ, t | t x t^-1 = φ(x) (x in C_1)>` be the HNN extension.

**1. K embeds in a finitely presented simple group.** `K` is the fundamental
group of a graph of groups with one vertex group `Λ` and one edge group `C_1`.
Both inclusions `C_1 -> Λ` and `φ: C_1 -> C_2 <= Λ` have finite index. So
`K in BS_Λ`. `Λ` is finitely presented and (H4) holds, so BLIW Theorem C
(`bliw-locally-finite-tree-actions-embed-in-fp-simple-groups`, quoted there
verbatim) embeds `K` in a finitely presented simple group.

**2. SL_2(Q) embeds in K.** By Ihara, `SL_2(Q) = A *_{Γ_0} A^α`.
- **The map.** Put `ψ_1 = ι` on `A` and `ψ_2(z) = t ι(α^-1 z α) t^-1` on `A^α`.
  For `z in Γ_0`, `y = α^-1 z α in Γ^0`, so `ι(y) in C_1` by (H1), and by (H3)
  `ψ_2(z) = φ(ι(y)) = ι(α y α^-1) = ι(z) = ψ_1(z)`. So `ψ_1, ψ_2` define
  `Ψ: A *_{Γ_0} A^α -> K`.
- **An amalgam inside `K`.** The natural map `Λ *_{C_2} tΛt^-1 -> K` is injective.
  A reduced word in the amalgam is `g_1 (t g_2 t^-1) g_3 (t g_4 t^-1) ...` with
  `g_odd in Λ \ C_2` and `g_even in Λ \ C_1`. As a word in `K` it contains no
  pinch `t c t^-1` (`c in C_1`) or `t^-1 c t` (`c in C_2`), so it is nontrivial by
  Britton's lemma.
- **Matching intersections.** `ι(A) ∩ C_2 = ι(Γ_0)` by (H2). By (H1) and (H3),
  `tι(A)t^-1 ∩ C_2 = t(ι(A) ∩ C_1)t^-1 = tι(Γ^0)t^-1 = ι(Γ_0)`.
- **Sub-amalgam lemma.** If `X <= G_1` and `Y <= G_2` in `G_1 *_H G_2` satisfy
  `X ∩ H = Y ∩ H = Z`, then `<X, Y> ≅ X *_Z Y`: an alternating word in
  `X \ Z` and `Y \ Z` is reduced in `G_1 *_H G_2`.
- **Conclusion.** `Ψ` maps `A` and `A^α` isomorphically onto `ι(A)` and
  `tι(A)t^-1`, and `Γ_0` onto `ι(Γ_0)`. So `Ψ` is the isomorphism
  `A *_{Γ_0} A^α ≅ ι(A) *_{ι(Γ_0)} tι(A)t^-1` followed by an inclusion; it is
  injective.

Composing 1 and 2 embeds `SL_2(Q)` in a finitely presented simple group. ∎

**Calibration.** O1 (divisibility) is consistent. `K` is not residually finite
and contains `(Q,+)`: the `l`-divisibility of the unipotents comes from the stable
letter `t`, which realizes the Hecke conjugation by `α`. Only `Λ`, the vertex
group, is residually finite.
