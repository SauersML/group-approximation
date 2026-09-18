import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarQuadClose
import GroupApproximation.Meta.AxiomGuard

/-!
# Four relative conjugates: the rank-one adjacent-pair case

Lane `bh-met-93q`, step module.  `P = k2DilateSt_pullback s`, `A` a domain, `s ≠ 0`.  Let
`z₁, z₂, z₃, z₄` be relative conjugates with `padMat (z₁ z₂ z₃ z₄) = 1`.

* `k2KarQuad_PairRankOne y`: `padMat y = 1 + V Wᵀ` for some `V, W` with `W ⬝ᵥ V = 0`.
* **`k2KarQuad_stDies_of_pair12`**: if `PairRankOne (z₁ z₂)`, then `z₁ z₂ z₃ z₄` dies after
  padding.  `k2KarTri_rankOneAt_two` makes `z₁ z₂` a rank-one datum (its `W' ⬝ᵥ V'` vanishes by
  `k2KarQuad_dot_eq_of_padMat`), and `k2KarQuad_stDies_datum_mul_two` finishes.
* **`k2KarQuad_stDies_of_pair23`**: the same if `PairRankOne (z₂ z₃)`, by rotating to
  `z₂ z₃ z₄ z₁ = z₁⁻¹ (z₁ z₂ z₃ z₄) z₁`.

(`PairRankOne (z₃ z₄)` and `PairRankOne (z₄ z₁)` are the same conditions, since
`padMat (z₃ z₄) = padMat (z₁ z₂)⁻¹`.)  Relativity (`fst b = 0`) is used only to obtain the
shape `g x_ij(b) g⁻¹` of each factor.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarQuadStepDef

/-- `padMat y` is of rank-one form `1 + V Wᵀ` with `W ⬝ᵥ V = 0`. -/
def k2KarQuad_PairRankOne {R : Type*} [Ring R] {n : ℕ} (y : St n R) : Prop :=
  ∃ V W : Fin n → R, padMat y = 1 + Matrix.vecMulVec V W ∧ W ⬝ᵥ V = 0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_PairRankOne

end KarQuadStepDef

section KarQuadStep

variable {A : Type*} [CommRing A] [IsDomain A] {s : A}

/-- **Case `(z₁ z₂)` rank-one.** -/
theorem k2KarQuad_stDies_of_pair12 (hs : s ≠ 0) {M : ℕ}
    {z₁ z₂ z₃ z₄ : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (h₁ : z₁ ∈ k2KarRel_gens s M) (h₂ : z₂ ∈ k2KarRel_gens s M)
    (h₃ : z₃ ∈ k2KarRel_gens s M) (h₄ : z₄ ∈ k2KarRel_gens s M)
    (h : padMat (z₁ * z₂ * z₃ * z₄) = 1) (hp : k2KarQuad_PairRankOne (z₁ * z₂)) :
    cubeDiagDilate_StDies (z₁ * z₂ * z₃ * z₄) := by
  obtain ⟨V, W, hm, hd⟩ := hp
  have e : [z₁, z₂].prod = z₁ * z₂ := by
    rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
  have hl : ∀ z ∈ [z₁, z₂], z ∈ k2KarRel_gens s M := by
    intro z hz
    rcases List.mem_pair.mp hz with rfl | rfl
    · exact h₁
    · exact h₂
  obtain ⟨V', W', hs', hm'⟩ := k2KarTri_rankOneAt_two hs M [z₁, z₂] (by simp) hl V W
    (by rw [e]; exact hm) hd
  rw [e] at hs' hm'
  have hd' : W' ⬝ᵥ V' = 0 := by rw [k2KarQuad_dot_eq_of_padMat hm hm', hd]
  obtain ⟨g₃, k, l, hkl, c₃, _, rfl⟩ := h₃
  obtain ⟨g₄, i, j, hij, c₄, _, rfl⟩ := h₄
  exact k2KarQuad_stDies_datum_mul_two (k2KarInd_mul_eq_zero hs) hs' hm' hd' g₃ k l hkl c₃
    g₄ i j hij c₄ h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_stDies_of_pair12

/-- **Case `(z₂ z₃)` rank-one**, by rotation. -/
theorem k2KarQuad_stDies_of_pair23 (hs : s ≠ 0) {M : ℕ}
    {z₁ z₂ z₃ z₄ : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (h₁ : z₁ ∈ k2KarRel_gens s M) (h₂ : z₂ ∈ k2KarRel_gens s M)
    (h₃ : z₃ ∈ k2KarRel_gens s M) (h₄ : z₄ ∈ k2KarRel_gens s M)
    (h : padMat (z₁ * z₂ * z₃ * z₄) = 1) (hp : k2KarQuad_PairRankOne (z₂ * z₃)) :
    cubeDiagDilate_StDies (z₁ * z₂ * z₃ * z₄) := by
  have e : z₁ * z₂ * z₃ * z₄ = z₁ * (z₂ * z₃ * z₄ * z₁) * z₁⁻¹ := by group
  rw [e] at h ⊢
  exact cubeDiagDilate_stDies_conj z₁
    (k2KarQuad_stDies_of_pair12 hs h₂ h₃ h₄ h₁ (k2KarTri_padMat_conj_eq_one h) hp)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarQuad_stDies_of_pair23

end KarQuadStep

end GroupApproximation.BooneHigman.Metabelian.ElemFP
