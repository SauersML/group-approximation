import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabLengthGen
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, length reduction: the word `Y X Y X` (lane bh-met-86)

Here `R` is an arbitrary unital ring, and `S = P Y X Y H` is `SurjStabLengthMem`.  This file
reduces membership of the word `Y_w X_c Y_{w'} X_{c'}` in `S` to the case where the middle row
`w'` is a single-entry vector `e_i β` and the final column `c'` is supported at the same index.

* `surjStabLength_mem_word_of_conj`: the word conjugated by `stab h` has the same membership,
  because `S` is stable under `H`-conjugation.  Conjugation acts by
  `Y_w ↦ Y_{w h}` (`stab_conj_padRow`) and `X_c ↦ X_{h⁻¹ c}`
  (`surjStabLength_inv_stab_conj_padCol`).
* `surjStabLength_mem_word_single`: we split `c' = d + e_i (c' i)`, where `d` is supported
  away from `i`.  Then `Y_{e_i β} X_d Y_{e_i β}⁻¹ = stab g · X_v`
  (`surjStabFactor_conj_row_padCol_mem`, disjoint supports), and
  `Y_w X_c · stab g = stab g · Y_{w g} X_{g⁻¹ c}`.  So the word equals
  `stab g · Y_{w g} X_{g⁻¹ c + v} Y_{e_i β} X_{e_i (c' i)}`.

Truth check.  Both are exact group identities in `St_{n+1}(R)`.  `X` and `Y` are abelian
(`padCol_add`, `padRow_add`), and `H` normalises both.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- `H`-conjugation invariance of the word `Y X Y X` modulo `S`. -/
theorem surjStabLength_mem_word_of_conj (h : St n R) (w c w' c' : Fin n → R)
    (hm : SurjStabLengthMem (padRow (w ᵥ* padMat h) * padCol (padMat h⁻¹ *ᵥ c) *
      padRow (w' ᵥ* padMat h) * padCol (padMat h⁻¹ *ᵥ c'))) :
    SurjStabLengthMem (padRow w * padCol c * padRow w' * padCol c') := by
  have e : padRow w * padCol c * padRow w' * padCol c' =
      stab n R h * (padRow (w ᵥ* padMat h) * padCol (padMat h⁻¹ *ᵥ c) *
        padRow (w' ᵥ* padMat h) * padCol (padMat h⁻¹ *ᵥ c')) * stab n R h⁻¹ := by
    rw [← stab_conj_padRow h w, ← stab_conj_padRow h w',
      ← surjStabLength_inv_stab_conj_padCol h c, ← surjStabLength_inv_stab_conj_padCol h c',
      map_inv (stab n R) h]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  rw [e]
  exact surjStabLength_mem_mul_stab (surjStabLength_mem_stab_mul hm h) h⁻¹

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_word_of_conj

/-- Reduction of `Y_w X_c Y_{e_i β} X_{c'}` to the case `c' = e_i (c' i)`. -/
theorem surjStabLength_mem_word_single (w c : Fin n → R) (i : Fin n) (β : R)
    (c' : Fin n → R)
    (hG : ∀ w₁ c₁ : Fin n → R, SurjStabLengthMem (padRow w₁ * padCol c₁ *
      padRow (Pi.single i β) * padCol (Pi.single i (c' i)))) :
    SurjStabLengthMem (padRow w * padCol c * padRow (Pi.single i β) * padCol c') := by
  obtain ⟨d, hd⟩ : ∃ d : Fin n → R, d = c' - Pi.single i (c' i) := ⟨_, rfl⟩
  have hdisj : ∀ k, d k = 0 ∨ (Pi.single i β : Fin n → R) k = 0 := by
    intro k
    by_cases hk : k = i
    · left
      rw [hk, hd, Pi.sub_apply, Pi.single_eq_same, sub_self]
    · right
      rw [Pi.single_eq_of_ne hk]
  obtain ⟨g, v, hg⟩ := surjStabFactor_conj_row_padCol_mem (Pi.single i β) d hdisj
  have hc' : padCol c' = padCol d * padCol (Pi.single i (c' i)) := by
    rw [← padCol_add, hd, sub_add_cancel]
  have hv : padCol v = (stab n R g)⁻¹ *
      (padRow (Pi.single i β) * padCol d * (padRow (Pi.single i β))⁻¹) := by
    rw [hg, inv_mul_cancel_left]
  have hcg := surjStabLength_inv_stab_conj_padCol g c
  have e : padRow w * padCol c * padRow (Pi.single i β) * padCol c' =
      stab n R g * (padRow (w ᵥ* padMat g) * padCol (padMat g⁻¹ *ᵥ c + v) *
        padRow (Pi.single i β) * padCol (Pi.single i (c' i))) := by
    rw [hc', padCol_add (padMat g⁻¹ *ᵥ c) v, hv, ← stab_conj_padRow g w, ← hcg]
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  rw [e]
  exact surjStabLength_mem_stab_mul (hG _ _) g

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabLength_mem_word_single

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
