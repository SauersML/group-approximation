import GroupApproximation.GroupTheory.HydeLodha.QTwoFinitePresentationDefs
import GroupApproximation.Meta.AxiomGuard

/-!
# Normalizing a point stabilizer to one period

Hyde–Lodha, proof of Proposition 4.7: "Since `Γ` is `1`-periodic, `Γ_K = Γ_{K+ℤ}`", after which
`K` may be moved into one period.  For a point `k₀ ∈ K`:

* `normalShift k₀ t`: the representative of `t + ℤ` in `[k₀, k₀ + 1)`;
* `normalShift_mem_Ioo`, `dyadic6_normalShift`: it lies in `(k₀, k₀ + 1)` unless it is `k₀`, and it
  stays in `ℤ[1/6]`;
* `stabK_eq_upsilon_inf_stabK`: for `Γ ≤ Γ₂`, `Γ_K = Υ_Γ([k₀, k₀ + 1]) ∩ Γ_{K'}` with
  `K' = normalShift k₀ '' K \ {k₀} ⊂ (k₀, k₀ + 1)`.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

/-- `k₀ + fract (t - k₀)`, the representative of `t + ℤ` in `[k₀, k₀ + 1)`. -/
def normalShift (k₀ t : ℚ) : ℚ := k₀ + Int.fract (t - k₀)

theorem normalShift_add_floor (k₀ t : ℚ) : normalShift k₀ t + ((⌊t - k₀⌋ : ℤ) : ℚ) = t := by
  have h := Int.self_sub_fract (t - k₀)
  unfold normalShift
  linarith

theorem normalShift_mem_Ioo {k₀ t : ℚ} (ht : normalShift k₀ t ≠ k₀) :
    k₀ < normalShift k₀ t ∧ normalShift k₀ t < k₀ + 1 := by
  have h0 := Int.fract_nonneg (t - k₀)
  have h1 := Int.fract_lt_one (t - k₀)
  refine ⟨lt_of_le_of_ne ?_ ht.symm, ?_⟩ <;> unfold normalShift <;> linarith

theorem dyadic6_normalShift {k₀ t : ℚ} (ht : Dyadic6 t) : Dyadic6 (normalShift k₀ t) := by
  obtain ⟨N, hN⟩ := ht
  refine ⟨N, ?_⟩
  have e : normalShift k₀ t = t - ((⌊t - k₀⌋ : ℤ) : ℚ) := by
    have h := normalShift_add_floor k₀ t
    linarith
  rw [e]
  exact grid_sub hN (int_mem_grid N _)

/-- `k₀` is not in `(k₀, k₀ + 1) + ℤ`. -/
theorem self_not_mem_perIoo_add_one (k₀ : ℚ) : k₀ ∉ perIoo k₀ (k₀ + 1) := by
  rintro ⟨k, h1, h2⟩
  have h1' : (0 : ℤ) < k := by exact_mod_cast (show (0 : ℚ) < k by linarith)
  have h2' : k < 1 := by exact_mod_cast (show (k : ℚ) < 1 by linarith)
  omega

/-- The complement of `(k₀, k₀ + 1) + ℤ` is `k₀ + ℤ`. -/
theorem normalShift_eq_of_not_mem_perIoo {k₀ x : ℚ} (hx : x ∉ perIoo k₀ (k₀ + 1)) :
    normalShift k₀ x = k₀ := by
  by_contra h
  obtain ⟨h1, h2⟩ := normalShift_mem_Ioo h
  have e := normalShift_add_floor k₀ x
  exact hx ⟨-⌊x - k₀⌋, by push_cast; linarith, by push_cast; linarith⟩

/-- An element of `Γ₂` fixes `t` if and only if it fixes `normalShift k₀ t`. -/
theorem apply_eq_self_iff_normalShift {f : Equiv.Perm ℚ} (hf : f ∈ gammaTwo) (k₀ t : ℚ) :
    f t = t ↔ f (normalShift k₀ t) = normalShift k₀ t := by
  have e := normalShift_add_floor k₀ t
  have hadd := gammaTwo_add_int hf (normalShift k₀ t) ⌊t - k₀⌋
  rw [e] at hadd
  constructor <;> intro h <;> linarith

/-- **`Γ_K = Υ_Γ([k₀, k₀ + 1]) ∩ Γ_{K'}`.** -/
theorem stabK_eq_upsilon_inf_stabK {Γ : Subgroup (Equiv.Perm ℚ)} (hΓ : Γ ≤ gammaTwo)
    {K : Set ℚ} {k₀ : ℚ} (hk₀ : k₀ ∈ K) :
    stabK Γ K = upsilon Γ k₀ (k₀ + 1) ⊓ stabK Γ (normalShift k₀ '' K \ {k₀}) := by
  ext f
  simp only [Subgroup.mem_inf, mem_stabK, mem_upsilon]
  constructor
  · rintro ⟨hf, hK⟩
    refine ⟨⟨hf, fun x hx => ?_⟩, hf, ?_⟩
    · rw [apply_eq_self_iff_normalShift (hΓ hf) k₀ x, normalShift_eq_of_not_mem_perIoo hx]
      exact hK k₀ hk₀
    · rintro _ ⟨⟨t, ht, rfl⟩, -⟩
      exact (apply_eq_self_iff_normalShift (hΓ hf) k₀ t).mp (hK t ht)
  · rintro ⟨⟨hf, hsupp⟩, -, hK⟩
    refine ⟨hf, fun t ht => (apply_eq_self_iff_normalShift (hΓ hf) k₀ t).mpr ?_⟩
    by_cases h : normalShift k₀ t = k₀
    · rw [h]
      exact hsupp k₀ (self_not_mem_perIoo_add_one k₀)
    · exact hK (normalShift k₀ t) ⟨⟨t, ht, rfl⟩, h⟩

#audit_axioms GroupApproximation.HydeLodha.normalShift_mem_Ioo
#audit_axioms GroupApproximation.HydeLodha.dyadic6_normalShift
#audit_axioms GroupApproximation.HydeLodha.stabK_eq_upsilon_inf_stabK

end HydeLodha
end GroupApproximation
