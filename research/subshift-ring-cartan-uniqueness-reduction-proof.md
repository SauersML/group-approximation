---
rg: 2
id: subshift-ring-cartan-uniqueness-reduction-proof
kind: route
title: Proof of the reduction of Cartan uniqueness in LC(X,F_2)⋊Z to rigidity of effective groupoid models
target: subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity
requires:
  - algebraic-cartan-pairs-are-effective-groupoid-steinberg-algebras
  - diagonal-preserving-isomorphisms-reconstruct-effective-groupoids
  - subshift-crossed-product-growth-is-n-times-complexity
  - minimal-subshift-algebra-is-simple-lef-ring
  - topological-full-groups-determine-flip-conjugacy
  - subshift-elementary-group-diagonal-iso-gives-flip-conjugacy
artifacts:
  - research/artifacts/sk-rigidity-cartan-2026-09-13-part1.md
---

The full derivation is in the artifact, §1–§2. Summary of each step:

**0. The model.** `R_X = A_{F_2}(𝒢_X)`, with `D_X` the diagonal. This is the verbatim cross-product identification in
`subshift-crossed-product-growth-is-n-times-complexity`. `𝒢_X` is effective, since the action is free.

**1. Twists over F_2 are trivial.** Take a discrete `F_2`-twist `(Σ,i,q)`.
- (DT1) gives `q^{-1}(G^(0)) = Σ^(0)`, so `q` is injective: `q(σ) = q(τ)` forces `στ^{-1} ∈ Σ^(0)`.
- (DT2) with `T = {1}` makes `q` a homeomorphism.
- The twisted algebra (`def:A_R(G;Sigma)`, quoted in the artifact §1) consists of compactly supported locally constant
  `f` with `f(t·σ) = t^{-1}f(σ)` for `t ∈ R^×`. For `R^× = {1}` the condition is vacuous, so
  `A_{F_2}(G;Σ) = A_{F_2}(G)`, with the diagonal onto the diagonal.

**2. Item 1.** Apply `prop:effectiveACPprincipalADP` to `𝒢_X`.

**3. Item 2.** `lem:C=>Q`, `thm:main`, `prop:Hausdorff`, `prop:effective`(a) and step 1 give `R_X ≅ A_{F_2}(G_B)` with
`B` onto the diagonal, and `G_B` effective Hausdorff ample.
- Compact unit space: `1 ∈ B`.
- Minimal: a nontrivial invariant open `U` gives a nonzero proper ideal `I_U` = span of `1_S` with `s(S) ⊆ U`,
  contradicting simplicity of `R_X`.
- No isolated points: an isolated `x` has open, hence trivial, isotropy, so `1_{{x}}` is a minimal idempotent. Then the
  simple unital ring `R_X` equals its socle and is `M_n(F_2)`, which is finite. That is a contradiction.

**4. Item 3.**
- *(b) ⇒ (a).* Compose the model isomorphism of step 3 with the diagonal-preserving isomorphism induced by `𝒢_X ≅ G_B`.
- *(a) ⇒ (b).*
  - A ring isomorphism of `F_2`-algebras is `F_2`-linear.
  - `(A_{F_2}(G), D(G))` is an algebraic Cartan pair (`prop:effectiveACPprincipalADP` with step 1), and the pair
    conditions transport along `Φ`.
  - (a) gives `β` with `Φ^{-1}β(D_X) = D(G)`.
  - `diagonal-preserving-isomorphisms-reconstruct-effective-groupoids` with `𝒢_X` effective gives `G ≅ 𝒢_X`.

**5. Item 4.** (b) gives `𝒢_Y ≅ 𝒢_X`. The groupoid isomorphism carries full compact open bisections to full compact
open bisections, so `[[S]] ≅ [[T]]` as abstract groups. `topological-full-groups-determine-flip-conjugacy` gives flip
conjugacy.

**6. Item 5.** Write `B = β(D_Y)`. `EL_3(β)` is an automorphism of `EL_3(R_Y)` with `EL_3(β)(GL_3(D_Y)) = GL_3(B)`. So
`EL_3(β)^{-1}α` carries `GL_3(D_X)` onto `GL_3(D_Y)`, and `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`
applies. ∎
