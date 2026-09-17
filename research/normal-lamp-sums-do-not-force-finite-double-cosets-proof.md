---
rg: 2
id: normal-lamp-sums-do-not-force-finite-double-cosets-proof
kind: route
title: Abels' group over F_p[t,1/t,1/(t-1)] extended by a row scaling, and a Hom-counting argument for split edge data
target: normal-lamp-sums-do-not-force-finite-double-cosets
requires: []
---

## 0. Imported result

Y. Cornulier and R. Tessera, *Dehn function and asymptotic cones of Abels' group*,
J. Topology 6 (2013), arXiv:1203.4696v2. Text read on 2026-09-17 from the arXiv PDF.

- **Definition (1.1):** for a commutative ring `R`, `A_4(R)` is the group of matrices
  `[[1, x12, x13, x14], [0, t22, x23, x24], [0, 0, t33, x34], [0, 0, 0, 1]]` with
  `x_ij ∈ R` and `t_22, t_33 ∈ R^×`.
- **Corollary 1.7 (Theorem 5.1), verbatim:** "The group A4(Fp[t,t^{-1},(t−1)^{-1}])
  is finitely presented and has a quadratic Dehn function."
- Same page: "Note that A4(Fp[t]) is not finitely generated, while A4(Fp[t,t^{-1}])
  is finitely generated but not finitely presented (see Remark 5.5)."

Only the statement of Theorem 5.1 is used; its proof was not re-checked.

## 1. The counterexample

Let `R = F_p[t, t^{-1}, (t-1)^{-1}]`, `E = A_4(R)`, and `z(λ) = I + λE_{14}` for `λ ∈ R`.

**Step 1 (the extension).** Let `δ = diag(t,1,1,1) ∈ GL_4(R)`; `t ∈ R^×`. For `u ∈ E`,
`(δuδ^{-1})_{ij} = δ_i u_{ij} δ_j^{-1}`, so conjugation by `δ` multiplies
`x12, x13, x14` by `t`, fixes every other entry, and keeps the diagonal
`(1, t22, t33, 1)`. Hence `δEδ^{-1} = E` (apply the same with `δ^{-1}`). Put
`A = E⟨δ⟩ ≤ GL_4(R)`. The `(1,1)` entry of `u δ^c` is `t^c`, and `t` has infinite order
in `R^×`, so `E ∩ ⟨δ⟩ = 1` and `A = E ⋊ ⟨δ⟩ ≅ E ⋊ Z`.

**Step 2 (finite presentation).** If `E = ⟨S | Q⟩` is finite, then
`A = ⟨S, δ | Q, δsδ^{-1} = w_s (s ∈ S)⟩`, where `w_s` is a word in `S` for `δsδ^{-1}`.
This is the standard presentation of a semidirect product with `Z`; it is finite by
Theorem 5.1.

**Step 3 (conjugating the lamp).** Every `g ∈ A` is `g = u·d·δ^c` with `u` upper
unitriangular, `d = diag(1, a, b, 1)`, `a, b ∈ R^×`, `c ∈ Z`. For any invertible
matrix `g` with first column `g_{11}e_1` and last row `g_{44}e_4^T`,
`g E_{14} g^{-1} = (g e_1)(e_4^T g^{-1}) = g_{11} g_{44}^{-1} E_{14}`, because
`e_4^T g^{-1} = g_{44}^{-1} e_4^T`. Every element of `A` is upper triangular with
`g_{44} = 1` and `g_{11} = t^c`, so

`g z(λ) g^{-1} = z(t^c λ)`. (★)

**Step 4 (normalizer and index).** Let `W = z(F_p) ≅ Z/p`. By (★), `g ∈ N_A(W)`
iff `t^c F_p = F_p` iff `c = 0`. So `C := N_A(W) = E`, which is normal, finitely
presented, and `A/C ≅ Z`. Since `C` is normal, `C\A/C = A/C` is infinite.

**Step 5 (the lamp sum).** The coset `x = δ^c C` gives `W_x = z(F_p t^c)`, using (★).
`z : (R,+) → A` is an injective homomorphism, and `F_p[t, t^{-1}] = ⊕_{c ∈ Z} F_p t^c`
inside `R`. So the `W_x` generate their direct sum `D_A = z(F_p[t^{±1}])`. By (★),
`D_A` is normal in `A`. By Step 3 with `c = 0`, `z(R)` is central in `E = C`.

This proves item 1.

## 2. Split edge data with normal finitely generated `C`

**Hypotheses.** `C ⊲ A`, `C` finitely generated, `C = V × W`, `aWa^{-1} ≤ V` for
every `a ∈ A \ C`, and `q : W → S` a surjection onto a nontrivial finite group. Let
`π : C → W` be the projection along `V`.

**Claim.** `[A:C] ≤ |Hom(C,S)|`.

*Proof.* For `a ∈ A` define `ψ_a : C → S`, `ψ_a(c) = q(π(a^{-1}ca))`. It is a
homomorphism because `C` is normal, so `c ↦ a^{-1}ca` is an automorphism of `C`.
Pick a set `T` of coset representatives for `A/C`. Let `a ≠ a'` in `T`, so
`a'^{-1}a ∉ C`. For `w ∈ W`, put `c = awa^{-1} ∈ C`.

- `ψ_a(c) = q(π(w)) = q(w)`.
- `ψ_{a'}(c) = q(π(bwb^{-1}))` with `b = a'^{-1}a ∉ C`. By hypothesis
  `bwb^{-1} ∈ V = ker π`, so `ψ_{a'}(c) = 1`.

Choose `w` with `q(w) ≠ 1`. Then `ψ_a ≠ ψ_{a'}`. So `a ↦ ψ_a` is injective on `T`.
A homomorphism from `C` is determined by the images of a finite generating set, so
`|Hom(C,S)| ≤ |S|^k` for `k` generators. ∎

This proves item 2.

## 3. The example is not split

In `E`, `[I + E_{12}, I + λE_{24}] = I + λE_{14}` for `λ ∈ R`. Indeed, with
`X = E_{12}`, `Y = λE_{24}`, we have `XY = λE_{14}`, `YX = 0`, `X² = Y² = 0`, so
`(I+X)(I+Y)(I−X)(I−Y) = I + XY − YX = I + λE_{14}` (the cubic terms contain `XYX`
or `YXY`, both `0`, and `XYXY = 0`). Hence `W ≤ [C,C]` with `C = E`.

If `C = V × W` with `W` abelian, then `[C,C] = [V,V] × [W,W] = [V,V] × 1`, which
meets `W = 1 × W` trivially. Since `W ≠ 1` and `W ≤ [C,C]`, no such `V` exists.
This proves item 3. ∎

## 4. Remarks on scope

- Item 2 needs `C` normal. For the amalgam setting, `C` is normal in `A` only in
  special cases, and the open question of the claim is exactly item 2 without
  normality: then `ψ_a` is only defined on `C ∩ aCa^{-1}`, and the counting of
  `Hom(C,S)` no longer applies directly.
