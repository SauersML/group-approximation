import GroupApproximation.Higman.OmegaTowerDescent
import GroupApproximation.Higman.OmegaTowerLocalGlobalCoordinates
import GroupApproximation.Higman.SwapCarrierWitness

/-!
# Order-correct collapse at the inner Omega seam

The first-stage centralizer only moves a selected window block past a row word
supported strictly to its right.  In that case the resulting conjugator is
the canonical increasing row word for the sum of the two sequences.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

theorem bElt_add_rightTail {m : ℕ} {β l : E}
    (hβ : β ∈ blockSet m)
    (hl : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i) :
    bElt (β + l) = bElt β * bElt l := by
  apply bElt_add_of_lt
  intro i hi j hj
  have hiWindow : i ∈ Finset.Ico (0 : ℤ) (m : ℤ) := by
    by_contra hiOutside
    exact (Finsupp.mem_support_iff.mp hi) (hβ i hiOutside)
  have hjTail : (m : ℤ) ≤ j :=
    hl j (Finsupp.mem_support_iff.mp hj)
  simp only [Finset.mem_Ico] at hiWindow
  omega

theorem blockAt_add (m : ℕ) (i : ℤ) (f g : E) :
    blockAt m i (f + g) = blockAt m i f + blockAt m i g := by
  apply Finsupp.ext
  intro j
  simp only [blockAt_apply, Finsupp.coe_add, Pi.add_apply]
  split_ifs <;> rfl

theorem blockAt_zero_eq_zero_of_rightTail {m : ℕ} {l : E}
    (hl : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i) :
    blockAt m 0 l = 0 := by
  apply Finsupp.ext
  intro j
  rw [blockAt_apply]
  by_cases hj : j ∈ Finset.Ico (0 : ℤ) (m : ℤ)
  · rw [if_pos hj]
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    by_contra hlj
    have hlj' : l j ≠ 0 := by simpa using hlj
    have := hl j hlj'
    simp only [Finset.mem_Ico] at hj
    omega
  · rw [if_neg hj]
    rfl

/-- Prepending one selected zeroth block preserves the full blockwise
language. -/
theorem add_rightTail_mem_omegaOp {m : ℕ} (hm : 0 < m)
    {B : Set E} {β l : E} (hβ : β ∈ B ∩ blockSet m)
    (hlTail : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i)
    (hlOmega : l ∈ omegaOp m B) :
    β + l ∈ omegaOp m B := by
  intro i
  rw [blockAt_add]
  by_cases hi : i = 0
  · subst i
    rw [blockAt_zero_eq_self hβ.2,
      blockAt_zero_eq_zero_of_rightTail hlTail, add_zero]
    exact hβ.1
  · rw [blockAt_eq_zero_of_ne_zero hm hi hβ.2, zero_add]
    exact hlOmega i

/-- Removing the zeroth window block from a right-tail decomposition also
preserves the full blockwise language, provided the zero block is allowed. -/
theorem rightTail_mem_omegaOp_of_add {m : ℕ} (hm : 0 < m)
    {B : Set E} (h0 : (0 : E) ∈ B) {beta l : E}
    (hbeta : beta ∈ blockSet m)
    (hlTail : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i)
    (hsum : beta + l ∈ omegaOp m B) :
    l ∈ omegaOp m B := by
  intro i
  by_cases hi : i = 0
  · subst i
    rw [blockAt_zero_eq_zero_of_rightTail hlTail]
    exact h0
  · have hblock := hsum i
    rw [blockAt_add, blockAt_eq_zero_of_ne_zero hm hi hbeta, zero_add] at hblock
    exact hblock

/-- A legal selected block prepended to a right-tail conjugator remains in
canonical increasing row order. -/
theorem rowConj_aElt_eq_aElt_add_rightTail {m : ℕ} {β l : E}
    (hβ : β ∈ blockSet m)
    (hl : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i) :
    (bElt l)⁻¹ * aElt β * bElt l = aElt (β + l) := by
  rw [aElt, aElt, bElt_add_rightTail hβ hl]
  group

/-- The surviving one-letter inner pinch is exactly the canonical conjugate
obtained by prepending its selected block. -/
theorem slimGen_conj_aElt_eq_aElt_add_rightTail
    {m : ℕ} {β l : E} (hβ : β ∈ blockSet m)
    (hl : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i) :
    (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
        slimPiOf m (slimGenCode m β) =
      slimPiF3Hom m (aElt (β + l)) := by
  rw [slimGen_conj_aElt_eq_rowConj_of_rightTail hβ hl,
    ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (slimPiF3Hom m)
    (rowConj_aElt_eq_aElt_add_rightTail hβ hl)

/-- A surviving selected-code pinch prepends one legal block and produces an
explicit new sequence in the blockwise language. -/
theorem exists_omega_sequence_of_slimGen_conj_rightTail
    {m : ℕ} (hm : 0 < m) {B : Set E} {β l : E}
    (hβ : β ∈ B ∩ blockSet m)
    (hlTail : ∀ i : ℤ, l i ≠ 0 → (m : ℤ) ≤ i)
    (hlOmega : l ∈ omegaOp m B) :
    ∃ f ∈ omegaOp m B,
      (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
          slimPiOf m (slimGenCode m β) = slimPiF3Hom m (aElt f) := by
  exact ⟨β + l, add_rightTail_mem_omegaOp hm hβ hlTail hlOmega,
    slimGen_conj_aElt_eq_aElt_add_rightTail hβ.2 hlTail⟩

/-- Exact one-letter scan step: if the selected-code conjugate of an existing
Omega letter returns to the embedded `F₃`, the normal-form obstruction forces
the required right-tail order and the result is again an Omega letter. -/
theorem exists_omega_sequence_of_surviving_slimGen_conj
    {m : ℕ} (hm : 0 < m) {B : Set E} {β l : E}
    (hβ : β ∈ B ∩ blockSet m) (hlOmega : l ∈ omegaOp m B)
    (hsurvives :
      (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
          slimPiOf m (slimGenCode m β) ∈ (slimPiF3Hom m).range) :
    ∃ f ∈ omegaOp m B,
      (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
          slimPiOf m (slimGenCode m β) = slimPiF3Hom m (aElt f) := by
  exact exists_omega_sequence_of_slimGen_conj_rightTail hm hβ
    ((slimGen_conj_aElt_mem_F3Range_iff hβ.2).mp hsurvives) hlOmega

/-- Cases 2 and 3 of the inner scan in their constructive form.  A surviving
sandwich forces the two selected labels to match; its middle Omega letter is
right-tail ordered, and the collapsed letter is again explicitly in
`omegaOp m B`. -/
theorem exists_omega_sequence_of_surviving_slimGen_pair
    {m : ℕ} (hm : 0 < m) {B : Set E} {β γ l : E}
    (hβ : β ∈ B ∩ blockSet m) (hγ : γ ∈ B ∩ blockSet m)
    (hlOmega : l ∈ omegaOp m B)
    (hsurvives :
      (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
          slimPiOf m (slimGenCode m γ) ∈ (slimPiF3Hom m).range) :
    ∃ f ∈ omegaOp m B,
      (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
          slimPiOf m (slimGenCode m γ) = slimPiF3Hom m (aElt f) := by
  have hclassified :=
    (slimGen_inv_mul_aElt_mul_gen_mem_F3Range_iff hβ.2 hγ.2).mp hsurvives
  obtain ⟨rfl, hlTail⟩ := hclassified
  exact exists_omega_sequence_of_slimGen_conj_rightTail hm hβ hlTail hlOmega

end Omega
end Higman
end GroupApproximation
