import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabGaussEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, length reduction: the set `P Y X Y H` (lane bh-met-86)

Here `R` is an arbitrary unital ring, `H = stab St_n(R)`, `X = padCol R^n` (last column) and
`Y = padRow R^n` (last row), inside `St_{n+1}(R)`.  `SurjStabLengthMem y` says that
`y = stab g₁ · padCol v · padRow w · padCol c · padRow w' · stab g₂`, i.e. `y ∈ P Y X Y H`
with `P = H X`.  This is the shape of `SurjStabGaussForm` without the conjugation.

## What is proved

* `1 ∈ S`.
* `S` is closed under left multiplication by `H` and by `X`, and under right multiplication
  by `H` and by `Y`.  This uses the normal forms `padCol u · stab g = stab g · padCol (g⁻¹ u)`
  (`surjStab_padCol_mul_stab`) and `stab g · padRow u = padRow (u g⁻¹) · stab g`
  (`surjStabLength_stab_mul_padRow`, from `stab_conj_padRow`).
* `surjStabLength_gaussForm_of_mem`: an element of `S` has the Gauss form, with `z = 1`.

Truth check.  `padRow (w' + u g⁻¹) = padRow w' · padRow (u g⁻¹)` since `Y` is abelian
(`padRow_add`), so trailing `Y H` absorbs a further `Y`.  Leading `H X` absorbs a further `X`
in the same way, since `X` is abelian and normalised by `H`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- `y ∈ P Y X Y H`: `y = stab g₁ · padCol v · padRow w · padCol c · padRow w' · stab g₂`. -/
def SurjStabLengthMem (y : St (n + 1) R) : Prop :=
  ∃ (g₁ g₂ : St n R) (v w c w' : Fin n → R),
    y = stab n R g₁ * padCol v * padRow w * padCol c * padRow w' * stab n R g₂

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.SurjStabLengthMem

/-- Row normal form: `stab g · padRow u = padRow (u ᵥ* padMat g⁻¹) · stab g`. -/
theorem surjStabLength_stab_mul_padRow (g : St n R) (u : Fin n → R) :
    stab n R g * padRow u = padRow (u ᵥ* padMat g⁻¹) * stab n R g := by
  have e := stab_conj_padRow g⁻¹ u
  rw [map_inv (stab n R) g, inv_inv] at e
  rw [← e, inv_mul_cancel_right]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_stab_mul_padRow

/-- Column conjugation by an inverse: `(stab g)⁻¹ · padCol u · stab g = padCol (g⁻¹ u)`. -/
theorem surjStabLength_inv_stab_conj_padCol (g : St n R) (u : Fin n → R) :
    (stab n R g)⁻¹ * padCol u * stab n R g = padCol (padMat g⁻¹ *ᵥ u) := by
  have e := stab_conj_padCol g⁻¹ u
  rwa [map_inv (stab n R) g, inv_inv] at e

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_inv_stab_conj_padCol

theorem surjStabLength_mem_one : SurjStabLengthMem (1 : St (n + 1) R) :=
  ⟨1, 1, 0, 0, 0, 0, by simp only [map_one, padCol_zero, padRow_zero, mul_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_one

theorem surjStabLength_mem_mul_stab {y : St (n + 1) R} (hy : SurjStabLengthMem y)
    (h : St n R) : SurjStabLengthMem (y * stab n R h) := by
  obtain ⟨g₁, g₂, v, w, c, w', rfl⟩ := hy
  refine ⟨g₁, g₂ * h, v, w, c, w', ?_⟩
  rw [map_mul (stab n R) g₂ h]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_mul_stab

theorem surjStabLength_mem_stab_mul {y : St (n + 1) R} (hy : SurjStabLengthMem y)
    (h : St n R) : SurjStabLengthMem (stab n R h * y) := by
  obtain ⟨g₁, g₂, v, w, c, w', rfl⟩ := hy
  refine ⟨h * g₁, g₂, v, w, c, w', ?_⟩
  rw [map_mul (stab n R) h g₁]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_stab_mul

theorem surjStabLength_mem_padCol_mul {y : St (n + 1) R} (hy : SurjStabLengthMem y)
    (u : Fin n → R) : SurjStabLengthMem (padCol u * y) := by
  obtain ⟨g₁, g₂, v, w, c, w', rfl⟩ := hy
  refine ⟨g₁, g₂, padMat g₁⁻¹ *ᵥ u + v, w, c, w', ?_⟩
  rw [padCol_add (padMat g₁⁻¹ *ᵥ u) v,
    ← mul_assoc (stab n R g₁) (padCol (padMat g₁⁻¹ *ᵥ u)) (padCol v),
    ← surjStab_padCol_mul_stab g₁ u]
  simp only [mul_assoc]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_padCol_mul

theorem surjStabLength_mem_mul_padRow {y : St (n + 1) R} (hy : SurjStabLengthMem y)
    (u : Fin n → R) : SurjStabLengthMem (y * padRow u) := by
  obtain ⟨g₁, g₂, v, w, c, w', rfl⟩ := hy
  refine ⟨g₁, g₂, v, w, c, w' + u ᵥ* padMat g₂⁻¹, ?_⟩
  rw [padRow_add w' (u ᵥ* padMat g₂⁻¹), mul_assoc _ (stab n R g₂) (padRow u),
    surjStabLength_stab_mul_padRow g₂ u]
  simp only [mul_assoc]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_mul_padRow

/-- An element of `P Y X Y H` has the Gauss form (take `z = 1`). -/
theorem surjStabLength_gaussForm_of_mem {y : St (n + 1) R} (hy : SurjStabLengthMem y) :
    ∃ w : Fin n → R, SurjStabGaussForm y w := by
  obtain ⟨g₁, g₂, v, w, c, w', hy⟩ := hy
  refine ⟨w, 1, g₁, g₂, v, c, w', ?_⟩
  rw [one_mul, inv_one, mul_one]
  exact hy

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_gaussForm_of_mem

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
