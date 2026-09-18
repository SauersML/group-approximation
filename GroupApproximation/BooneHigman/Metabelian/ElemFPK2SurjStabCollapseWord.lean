import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabCollapseEuclid
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, rank-two collapse: word moves (lane bh-met-89)

Here `R` is an arbitrary unital ring and `S = H X Y X Y H` is `SurjStabLengthMem`.  We work
with the rank-two word `Y_w X_c Y_{e_i β} X_{e_i γ}` of `SurjStabLengthRankTwoStatement`.

* `surjStabCollapse_mem_word_of_fix`: conjugating by `stab h` with `h` fixing `e_i`
  (`SurjStabCollapseFix`) changes only `w ↦ w h` and `c ↦ h⁻¹ c`.  This is
  `surjStabLength_mem_word_of_conj` with the last two factors unchanged.
* `surjStabCollapse_mem_word_split`: if `w` is supported on `{i, k}`, then the column `c` can
  be cut down to `e_i (c i) + e_k (c k)`.  Write `c = d + c''` with `d` vanishing at `i` and
  `k`.  Then `d` and `w` have disjoint supports, so
  `Y_w X_d Y_w⁻¹ = stab g · X_v` (`surjStabFactor_conj_row_padCol_mem`).  Hence
  `Y_w X_c Y_a X_b = stab g · X_v · (Y_w X_{c''} Y_a X_b)`, and `S` absorbs `stab g · X_v`
  on the left (`surjStabLength_mem_stab_mul`, `surjStabLength_mem_padCol_mul`).

Truth check.  Both are exact group identities in `St_{n+1}(R)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- Conjugation by an element fixing `e_i`. -/
theorem surjStabCollapse_mem_word_of_fix {i : Fin n} {h : St n R}
    (hh : SurjStabCollapseFix i h) (w c : Fin n → R) (β γ : R)
    (hm : SurjStabLengthMem (padRow (w ᵥ* padMat h) * padCol (padMat h⁻¹ *ᵥ c) *
      padRow (Pi.single i β) * padCol (Pi.single i γ))) :
    SurjStabLengthMem (padRow w * padCol c * padRow (Pi.single i β) *
      padCol (Pi.single i γ)) := by
  obtain ⟨h1, h2⟩ := hh
  refine surjStabLength_mem_word_of_conj h w c (Pi.single i β) (Pi.single i γ) ?_
  rw [h1 β, h2 γ]
  exact hm

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_mem_word_of_fix

/-- Cutting the column down to `{i, k}` when the row is supported on `{i, k}`. -/
theorem surjStabCollapse_mem_word_split (w : Fin n → R) (i k : Fin n) (hki : k ≠ i)
    (hw : ∀ l, l ≠ i → l ≠ k → w l = 0) (c a b : Fin n → R)
    (hm : SurjStabLengthMem (padRow w * padCol (Pi.single i (c i) + Pi.single k (c k)) *
      padRow a * padCol b)) :
    SurjStabLengthMem (padRow w * padCol c * padRow a * padCol b) := by
  obtain ⟨d, hd⟩ : ∃ d : Fin n → R, d = c - (Pi.single i (c i) + Pi.single k (c k)) :=
    ⟨_, rfl⟩
  have hdisj : ∀ l, d l = 0 ∨ w l = 0 := by
    intro l
    by_cases hli : l = i
    · left
      rw [hli, hd, Pi.sub_apply, Pi.add_apply, Pi.single_eq_same i (c i),
        Pi.single_eq_of_ne (Ne.symm hki), add_zero, sub_self]
    · by_cases hlk : l = k
      · left
        rw [hlk, hd, Pi.sub_apply, Pi.add_apply, Pi.single_eq_same k (c k), Pi.single_eq_of_ne hki,
          zero_add, sub_self]
      · right
        exact hw l hli hlk
  obtain ⟨g, v, hg⟩ := surjStabFactor_conj_row_padCol_mem w d hdisj
  have hc : padCol c = padCol d * padCol (Pi.single i (c i) + Pi.single k (c k)) := by
    rw [← padCol_add, hd, sub_add_cancel]
  have hv : padCol v = (stab n R g)⁻¹ * (padRow w * padCol d * (padRow w)⁻¹) := by
    rw [hg, inv_mul_cancel_left]
  have e : padRow w * padCol c * padRow a * padCol b =
      stab n R g * (padCol v * (padRow w * padCol (Pi.single i (c i) + Pi.single k (c k)) *
        padRow a * padCol b)) := by
    rw [hc, hv]
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  rw [e]
  exact surjStabLength_mem_stab_mul (surjStabLength_mem_padCol_mul hm v) g

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_mem_word_split

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
