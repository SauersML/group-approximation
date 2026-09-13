---
rg: 2
id: zp-detection-equals-meyer-nadareishvili-sufficiency-proof
kind: route
title: Detection gives bootstrap membership by coning a Köhler lift; bootstrap membership gives detection by Meyer's little invariant
target: zp-detection-equals-meyer-nadareishvili-sufficiency
requires:
  - kohler-uct-for-zp-equivariant-bootstrap
  - meyer-little-invariant-detects-zero-in-zp-bootstrap
  - mn-cyclic-restrictions-detect-equivariant-bootstrap
---

Notation: `G = Z/p`, and `U = U^(Z/p)` is Köhler's invariant. Its components
include `KK^G_*(C, A) ≅ K_*(A ⋊ G)`, by Green–Julg, and
`KK^G_*(C(G), A) ≅ K_*(Res A)`, by Ind–Res. The little invariant is
`L_*(A) = K_*(A ⋊ G) ⊕ K_*(Res A)`.

**`MN(𝒞) ⟹ Det(𝒞)`, for any class `𝒞`.** Take `D ∈ 𝒞` with `Res D ≃ 0` and
`D ⋊ G ≃ 0`.
1. Both lie in `B`, so `MN` gives `D ∈ B^G`.
2. `L_*(D) = 0`.
3. By Meyer, arXiv:1906.11163v3, Lemma 4.2
   (`meyer-little-invariant-detects-zero-in-zp-bootstrap`), `D ≃_(KK^G) 0`.

No closure property of `𝒞` is used.

**`Det(𝒞) ⟹ MN(𝒞)`.** Take `A ∈ 𝒞` with `Res A ∈ B` and `A ⋊ G ∈ B`.
1. `U(A)` is exact, by Theorem 2.9 (2) ⟹ (3) of
   `kohler-uct-for-zp-equivariant-bootstrap`. By (3) ⟹ (1) there is
   `P ∈ B^G` with `U(P) ≅ U(A)`.
2. By Theorem 2.10, `KK^G(P, A) ↠ Hom_(K_p)(U(P), U(A))`, so the isomorphism
   lifts to some `x ∈ KK^G(P, A)`.
3. Let `D` be the cone of `x`, with exact triangle `P → A → D → ΣP`. `U` is
   stable homological, and `U(x)` is invertible, so the five lemma gives
   `U(D) = 0`. In particular `K_*(Res D) = 0` and `K_*(D ⋊ G) = 0`.
4. `Res` and `− ⋊ G` are triangulated functors. So `Res D` is the cone of
   `Res x : Res P → Res A`, and `D ⋊ G` is the cone of `x ⋊ G`.
5. `Res P` and `P ⋊ G` lie in `B`, because `P ∈ B^G`
   (`mn-cyclic-restrictions-detect-equivariant-bootstrap`).
   `Res A` and `A ⋊ G` lie in `B` by hypothesis. `B` is closed under cones.
   So `Res D, D ⋊ G ∈ B`, both with zero K-theory, hence KK-contractible by
   the Rosenberg–Schochet UCT.
6. If `D ∈ 𝒞`, then `Det(𝒞)` gives `D ≃ 0`. So `x` is invertible and
   `A ≅ P ∈ B^G`.

Step 6 needs `D ∈ 𝒞`.
- **Item 1 (all separable).** This is automatic.
- **Item 2 (nuclear).** Choose `P` of type I. Since `P` is nuclear, `x`
  corresponds to an equivariantly semisplit extension
  `0 → ΣA ⊗ K(ℓ^2(G) ⊗ ℓ^2) → E → P → 0`. This uses Kasparov's
  `KK^G_1(P, B) ≅ Ext^G(P, B)^(-1)` for nuclear `P`; averaging a completely
  positive lift over the finite group makes it equivariant. `E` is nuclear, being
  an extension of nuclear algebras. Its extension triangle identifies the cone
  of `x` with `ΣE` up to Bott periodicity, so `D` may be taken nuclear.
  - These two standard facts were not re-read from source: the equivariant
    Ext–KK correspondence, and that semisplit extensions give exact triangles
    in `KK^G` (Meyer–Nest, *The Baum–Connes conjecture via localisation of
    categories*, §2).

**Item 3.**
- **(⟹)** Let `A` be separable nuclear. With trivial action `τA ∈ B^G`, so
  `A = Res τA ∈ B`. Hence `UCT` holds. For `Det(nuclear)`, `UCT_G` puts every
  such `D` in `B^G`, and `MN ⟹ Det` step 3 applies.
- **(⟸)** Let `A` be a nuclear `G`-algebra. `Res A` is nuclear, and so is
  `A ⋊ G`, since `G` is finite. `UCT` puts both in `B`. Item 2 then gives
  `A ∈ B^G`.
