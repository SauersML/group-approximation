import GroupApproximation.Analysis.ExactnessPermanence
import GroupApproximation.Sofic.AmenableActionSofic
import GroupApproximation.Sofic.SoficByAmenablePermanence
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.SolvableAmenable
import Mathlib.GroupTheory.Solvable

/-!
# Amenable groups have property A

`non_mf_group_notes.tex`, paragraph `\paragraph{Exactness.}` after
`prop:blocknormalform`: the Guentner--Higson--Weinberger argument for
`Σ ≤ GL₄(ℚ)` pulls property A back from a solvable, hence amenable, group.
This file supplies the amenable input in the repository's finite-scale form
(`ExactnessPermanence.HasPropertyA`):

* `hasAlmostInvariantWeights_of_isAmenable`: the normalised indicator of a
  Følner set (`AmenableActionSofic.exists_folner`) is an almost invariant
  weight in Day's `ℓ¹` form;
* `hasPropertyA_of_isAmenable`, and the corollaries for solvable groups,
  commutative groups and `ℤ`.
-/

namespace GroupApproximation.Full.NN09b

open GroupApproximation.ExactnessPermanence

universe u

/-- Summing a constant over a filtered window. -/
theorem sum_ite_const_eq_card_mul {G : Type u} (T : Finset G) (c : ℝ) (p : G → Prop)
    [DecidablePred p] :
    ∑ x ∈ T, (if p x then c else 0) = ((T.filter p).card : ℝ) * c := by
  calc ∑ x ∈ T, (if p x then c else 0) = ∑ _x ∈ T.filter p, c :=
        (Finset.sum_filter p fun _ ↦ c).symm
    _ = ((T.filter p).card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Følner sets give almost invariant weights.**  The weight is the
normalised indicator of a Følner set `A`; its `ℓ¹` displacement under
translation by `r` is the number of points of `A` leaving `A` under `r⁻¹` or
under `r`, divided by `#A`. -/
theorem hasAlmostInvariantWeights_of_isAmenable {G : Type u} [Group G]
    (hG : Amenability.IsAmenable G) : HasAlmostInvariantWeights G := by
  classical
  intro R ε hε
  obtain ⟨A, hAne, hA⟩ := AmenableActionSofic.exists_folner hG
    (R ∪ R.image fun r ↦ r⁻¹) (δ := ε / 2) (half_pos hε)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((A.card : ℝ))⁻¹ := ⟨_, rfl⟩
  have hApos : (0 : ℝ) < A.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hAne)
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact inv_nonneg.mpr hApos.le
  refine ⟨A, fun x ↦ if x ∈ A then c else 0, ?_, ?_, ?_, ?_⟩
  · intro x
    show (0 : ℝ) ≤ (if x ∈ A then c else 0)
    by_cases hx : x ∈ A
    · rw [if_pos hx]
      exact hc0
    · exact le_of_eq (if_neg hx).symm
  · intro x hx
    exact if_neg hx
  · show ∑ x ∈ A, (if x ∈ A then c else 0) = 1
    have hsum : ∑ x ∈ A, (if x ∈ A then c else 0) = ∑ _x ∈ A, c :=
      Finset.sum_congr rfl fun x hx ↦ if_pos hx
    rw [hsum, Finset.sum_const, nsmul_eq_mul, hc]
    exact mul_inv_cancel₀ hApos.ne'
  · intro r hr T _ _
    show ∑ x ∈ T, |(if x ∈ A then c else 0) - (if r⁻¹ * x ∈ A then c else 0)| ≤ ε
    have hpt : ∀ x ∈ T,
        |(if x ∈ A then c else 0) - (if r⁻¹ * x ∈ A then c else 0)| ≤
          (if x ∈ A ∧ r⁻¹ * x ∉ A then c else 0) +
            (if r⁻¹ * x ∈ A ∧ x ∉ A then c else 0) := by
      intro x _
      by_cases h1 : x ∈ A
      · by_cases h2 : r⁻¹ * x ∈ A
        · rw [if_pos h1, if_pos h2,
            if_neg (show ¬(x ∈ A ∧ r⁻¹ * x ∉ A) from fun h ↦ h.2 h2),
            if_neg (show ¬(r⁻¹ * x ∈ A ∧ x ∉ A) from fun h ↦ h.2 h1)]
          exact le_of_eq (by rw [sub_self, abs_zero, add_zero])
        · rw [if_pos h1, if_neg h2,
            if_pos (show x ∈ A ∧ r⁻¹ * x ∉ A from ⟨h1, h2⟩),
            if_neg (show ¬(r⁻¹ * x ∈ A ∧ x ∉ A) from fun h ↦ h2 h.1)]
          exact le_of_eq (by rw [sub_zero, add_zero, abs_of_nonneg hc0])
      · by_cases h2 : r⁻¹ * x ∈ A
        · rw [if_neg h1, if_pos h2,
            if_neg (show ¬(x ∈ A ∧ r⁻¹ * x ∉ A) from fun h ↦ h1 h.1),
            if_pos (show r⁻¹ * x ∈ A ∧ x ∉ A from ⟨h2, h1⟩)]
          exact le_of_eq (by rw [zero_sub, abs_neg, zero_add, abs_of_nonneg hc0])
        · rw [if_neg h1, if_neg h2,
            if_neg (show ¬(x ∈ A ∧ r⁻¹ * x ∉ A) from fun h ↦ h1 h.1),
            if_neg (show ¬(r⁻¹ * x ∈ A ∧ x ∉ A) from fun h ↦ h2 h.1)]
          exact le_of_eq (by rw [sub_zero, abs_zero, add_zero])
    have hb1 : (T.filter fun x ↦ x ∈ A ∧ r⁻¹ * x ∉ A).card ≤
        (AmenableActionSofic.boundary A r⁻¹).card := by
      refine Finset.card_le_card fun x hx ↦ ?_
      obtain ⟨-, hxA, hrx⟩ := Finset.mem_filter.mp hx
      exact AmenableActionSofic.mem_boundary.mpr ⟨hxA, hrx⟩
    have hb2 : (T.filter fun x ↦ r⁻¹ * x ∈ A ∧ x ∉ A).card ≤
        (AmenableActionSofic.boundary A r).card := by
      refine Finset.card_le_card_of_injOn (fun x ↦ r⁻¹ * x) ?_ ?_
      · intro x hx
        obtain ⟨-, hxA, hx'⟩ := Finset.mem_filter.mp hx
        refine AmenableActionSofic.mem_boundary.mpr ⟨hxA, ?_⟩
        show r * (r⁻¹ * x) ∉ A
        rwa [mul_inv_cancel_left]
      · intro a _ b _ hab
        exact mul_left_cancel hab
    have hr1 : r⁻¹ ∈ R ∪ R.image fun r ↦ r⁻¹ :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hr)
    have hr2 : r ∈ R ∪ R.image fun r ↦ r⁻¹ := Finset.mem_union_left _ hr
    have hF1 := hA _ hr1
    have hF2 := hA _ hr2
    calc ∑ x ∈ T, |(if x ∈ A then c else 0) - (if r⁻¹ * x ∈ A then c else 0)|
        ≤ ∑ x ∈ T, ((if x ∈ A ∧ r⁻¹ * x ∉ A then c else 0) +
            (if r⁻¹ * x ∈ A ∧ x ∉ A then c else 0)) := Finset.sum_le_sum hpt
      _ = ((T.filter fun x ↦ x ∈ A ∧ r⁻¹ * x ∉ A).card : ℝ) * c +
            ((T.filter fun x ↦ r⁻¹ * x ∈ A ∧ x ∉ A).card : ℝ) * c := by
          rw [Finset.sum_add_distrib]
          exact congrArg₂ (· + ·)
            (sum_ite_const_eq_card_mul T c fun x ↦ x ∈ A ∧ r⁻¹ * x ∉ A)
            (sum_ite_const_eq_card_mul T c fun x ↦ r⁻¹ * x ∈ A ∧ x ∉ A)
      _ ≤ ((AmenableActionSofic.boundary A r⁻¹).card : ℝ) * c +
            ((AmenableActionSofic.boundary A r).card : ℝ) * c :=
          add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb1) hc0)
            (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb2) hc0)
      _ ≤ ε := by
          rw [← add_mul, hc, ← div_eq_mul_inv, div_le_iff₀ hApos]
          linarith

/-- **Amenable groups have property A.** -/
theorem hasPropertyA_of_isAmenable {G : Type u} [Group G]
    (hG : Amenability.IsAmenable G) : HasPropertyA G :=
  hasPropertyA_of_hasAlmostInvariantWeights (hasAlmostInvariantWeights_of_isAmenable hG)

/-- **Solvable groups have property A** (solvable groups are amenable,
`Full.Kharlampovich.isAmenable_of_isSolvable`). -/
theorem hasPropertyA_of_isSolvable (G : Type) [Group G] [IsSolvable G] : HasPropertyA G :=
  hasPropertyA_of_isAmenable (Full.Kharlampovich.isAmenable_of_isSolvable G)

/-- **Commutative groups have property A.** -/
theorem hasPropertyA_of_mul_comm (G : Type) [Group G] (h : ∀ a b : G, a * b = b * a) :
    HasPropertyA G :=
  haveI : IsSolvable G := isSolvable_of_comm h
  hasPropertyA_of_isSolvable G

/-- **`ℤ` has property A.** -/
theorem hasPropertyA_multiplicativeInt : HasPropertyA (Multiplicative ℤ) :=
  hasPropertyA_of_isAmenable SoficByAmenablePermanence.isAmenable_int

end GroupApproximation.Full.NN09b
