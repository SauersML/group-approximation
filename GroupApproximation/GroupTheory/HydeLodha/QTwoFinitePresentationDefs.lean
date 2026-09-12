import GroupApproximation.GroupTheory.HydeLodha.GammaTwoSimple
import GroupApproximation.Meta.AxiomGuard

/-!
# Periodic interval stabilizers `Υ_Γ(I)` and point stabilizers `Γ_K`

Hyde–Lodha, §4: "Given a `1`-periodic group `G ≤ Homeo⁺(ℝ)` and an interval `I ⊂ ℝ`, `|I| ≤ 1`,
define `Υ_G(I) = Rstab_G(Int(I) + ℤ)`", and "for `K ⊂ ℤ[1/η_n]` define `Γ_K = {f ∈ Γ | k·f = k,
∀ k ∈ K}`".  On `ℚ`:

* `perIoo a b`: the periodic open set `(a, b) + ℤ`;
* `upsilon Γ a b`: the elements of `Γ` supported in `(a, b) + ℤ`;
* `stabK Γ K`: the pointwise stabilizer of `K` in `Γ`.

* `perIoo_add_int`, `upsilon_add_int` (D1): translating `[a, b]` by an integer changes nothing.
* `image_perIoo`, `conj_mem_upsilon` (D2): for `g ∈ Γ₂` normalizing `Γ`, `g Υ_Γ([a, b]) g⁻¹ ≤
  Υ_Γ([g a, g b])`.
-/

namespace GroupApproximation
namespace HydeLodha

open scoped commutatorElement
open HigmanThompson

/-- `(a, b) + ℤ`. -/
def perIoo (a b : ℚ) : Set ℚ := {t | ∃ k : ℤ, a < t + k ∧ t + k < b}

/-- **`Υ_Γ([a, b])`**, Hyde–Lodha §4. -/
def upsilon (Γ : Subgroup (Equiv.Perm ℚ)) (a b : ℚ) : Subgroup (Equiv.Perm ℚ) where
  carrier := {f | f ∈ Γ ∧ SupportedIn f (perIoo a b)}
  one_mem' := ⟨Γ.one_mem, supportedIn_one _⟩
  mul_mem' := by
    rintro f g ⟨hf, hfs⟩ ⟨hg, hgs⟩
    exact ⟨Γ.mul_mem hf hg, (hfs.mul hgs).mono (Set.union_subset subset_rfl subset_rfl)⟩
  inv_mem' := by
    rintro f ⟨hf, hfs⟩
    exact ⟨Γ.inv_mem hf, hfs.inv⟩

/-- **`Γ_K`**, Hyde–Lodha §4. -/
def stabK (Γ : Subgroup (Equiv.Perm ℚ)) (K : Set ℚ) : Subgroup (Equiv.Perm ℚ) where
  carrier := {f | f ∈ Γ ∧ ∀ k ∈ K, f k = k}
  one_mem' := ⟨Γ.one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨hf, hfk⟩ ⟨hg, hgk⟩
    refine ⟨Γ.mul_mem hf hg, fun k hk => ?_⟩
    show f (g k) = k
    rw [hgk k hk, hfk k hk]
  inv_mem' := by
    rintro f ⟨hf, hfk⟩
    refine ⟨Γ.inv_mem hf, fun k hk => ?_⟩
    rw [Equiv.Perm.inv_eq_iff_eq, hfk k hk]

theorem mem_upsilon {Γ : Subgroup (Equiv.Perm ℚ)} {a b : ℚ} {f : Equiv.Perm ℚ} :
    f ∈ upsilon Γ a b ↔ f ∈ Γ ∧ SupportedIn f (perIoo a b) := Iff.rfl

theorem mem_stabK {Γ : Subgroup (Equiv.Perm ℚ)} {K : Set ℚ} {f : Equiv.Perm ℚ} :
    f ∈ stabK Γ K ↔ f ∈ Γ ∧ ∀ k ∈ K, f k = k := Iff.rfl

/-! ## D1: integer translation -/

theorem perIoo_add_int (a b : ℚ) (j : ℤ) : perIoo (a + j) (b + j) = perIoo a b := by
  ext t
  constructor
  · rintro ⟨k, hk1, hk2⟩
    refine ⟨k - j, ?_, ?_⟩ <;> push_cast <;> linarith
  · rintro ⟨k, hk1, hk2⟩
    refine ⟨k + j, ?_, ?_⟩ <;> push_cast <;> linarith

theorem upsilon_add_int (Γ : Subgroup (Equiv.Perm ℚ)) (a b : ℚ) (j : ℤ) :
    upsilon Γ (a + j) (b + j) = upsilon Γ a b := by
  ext f
  rw [mem_upsilon, mem_upsilon, perIoo_add_int]

/-! ## D2: conjugation -/

theorem image_perIoo_subset {g : Equiv.Perm ℚ} (hg : g ∈ gammaTwo) (a b : ℚ) :
    g '' perIoo a b ⊆ perIoo (g a) (g b) := by
  have hmono := gammaTwo_strictMono hg
  rintro _ ⟨t, ⟨k, hk1, hk2⟩, rfl⟩
  refine ⟨k, ?_, ?_⟩
  · have h := hmono hk1
    rwa [gammaTwo_add_int hg t k] at h
  · have h := hmono hk2
    rwa [gammaTwo_add_int hg t k] at h

/-- **D2.** -/
theorem conj_mem_upsilon {Γ : Subgroup (Equiv.Perm ℚ)} {g : Equiv.Perm ℚ} (hg : g ∈ gammaTwo)
    (hΓg : ∀ x ∈ Γ, g * x * g⁻¹ ∈ Γ) {a b : ℚ} {f : Equiv.Perm ℚ} (hf : f ∈ upsilon Γ a b) :
    g * f * g⁻¹ ∈ upsilon Γ (g a) (g b) := by
  obtain ⟨hfΓ, hfs⟩ := mem_upsilon.mp hf
  exact mem_upsilon.mpr ⟨hΓg f hfΓ, (hfs.conj g).mono (image_perIoo_subset hg a b)⟩

/-- A subgroup containing `Q₂` is normalized by `Γ₂`. -/
theorem normalized_of_qTwo_le {Γ : Subgroup (Equiv.Perm ℚ)} (hQ : qTwo ≤ Γ) (hΓ : Γ ≤ gammaTwo) :
    ∀ x ∈ Γ, ∀ g ∈ gammaTwo, g * x * g⁻¹ ∈ Γ := by
  intro x hx g hg
  have hc : ⁅g, x⁆ ∈ qTwo := Subgroup.commutator_mem_commutator hg (hΓ hx)
  have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Γ.mul_mem (hQ hc) hx

#audit_axioms GroupApproximation.HydeLodha.upsilon_add_int
#audit_axioms GroupApproximation.HydeLodha.conj_mem_upsilon
#audit_axioms GroupApproximation.HydeLodha.normalized_of_qTwo_le

end HydeLodha
end GroupApproximation
