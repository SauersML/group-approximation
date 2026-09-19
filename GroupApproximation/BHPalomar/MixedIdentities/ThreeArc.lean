import GroupApproximation.GroupTheory.HydeLodha.PeriodicCore
import GroupApproximation.Meta.AxiomGuard

/-!
# The three-arc mixed identity for periodic order-preserving permutations of `ℚ`

A strictly increasing permutation `f` of `ℚ` that commutes with the integer translations is a lift
of an orientation-preserving bijection of the circle `ℚ/ℤ`. Take three arcs
`A_i = (α_i, β_i)` in `[0, 1]`, met in this order, and permutations `a_i` supported in the
periodic sets `perSet A_i = A_i + ℤ`. Put `s_ij = [a_i, f a_j f⁻¹]`. Then
`[[s₁₂, s₂₁], s₃₃] = 1`
(the circle version of `homeo-circle-three-arc-commutator-word-is-mixed-identity`).

* **Disjoint supports commute.** `f a_j f⁻¹` is supported in `f (perSet A_j)`, so `s_ij = 1`
  unless `perSet A_i` meets `f (perSet A_j)`.
* **Orientation (`not_all_overlap`).** If all three overlaps happened, there would be points
  `r_i ∈ A_i` with `f r₁ ∈ A₂ + k₁`, `f r₂ ∈ A₁ + k₂` and `f r₃ ∈ A₃ + k₃`. Monotonicity on
  `r₁ < r₂ < r₃ < r₁ + 1` forces `k₂ = k₁ + 1`, then `k₃ ≥ k₂`, then `k₃ ≤ k₁`, a contradiction.
* `threeArcWord`: the word `[[s₁₂, s₂₁], s₃₃]` in `G ∗ ⟨x⟩`, with `x` the free generator.
-/

namespace GroupApproximation
namespace BHPalomar
namespace MixedIdentities

open scoped commutatorElement
open HydeLodha

section Circle

variable {f : Equiv.Perm ℚ}

/-- A periodic permutation carries the fractional part along. -/
theorem fract_apply_fract (hper : ∀ (t : ℚ) (k : ℤ), f (t + k) = f t + k) (q : ℚ) :
    Int.fract (f (Int.fract q)) = Int.fract (f q) := by
  have h : f q = f (Int.fract q) + ⌊q⌋ := by
    rw [← hper, Int.fract_add_floor]
  rw [h, Int.fract_add_int]

/-- **Orientation.** A strictly increasing periodic permutation cannot send `A₁` into `A₂`,
`A₂` into `A₁` and `A₃` into `A₃` (all modulo `ℤ`) at once. -/
theorem not_all_overlap (hmono : StrictMono f) (hper : ∀ (t : ℚ) (k : ℤ), f (t + k) = f t + k)
    {α₁ β₁ α₂ β₂ α₃ β₃ : ℚ} (h0 : 0 ≤ α₁) (h12 : β₁ ≤ α₂) (h23 : β₂ ≤ α₃) (h1 : β₃ ≤ 1)
    {q₁ q₂ q₃ : ℚ}
    (hq₁ : q₁ ∈ perSet (Set.Ioo α₁ β₁)) (hfq₁ : f q₁ ∈ perSet (Set.Ioo α₂ β₂))
    (hq₂ : q₂ ∈ perSet (Set.Ioo α₂ β₂)) (hfq₂ : f q₂ ∈ perSet (Set.Ioo α₁ β₁))
    (hq₃ : q₃ ∈ perSet (Set.Ioo α₃ β₃)) (hfq₃ : f q₃ ∈ perSet (Set.Ioo α₃ β₃)) : False := by
  obtain ⟨hr₁a, hr₁b⟩ : Int.fract q₁ ∈ Set.Ioo α₁ β₁ := hq₁
  obtain ⟨hr₂a, hr₂b⟩ : Int.fract q₂ ∈ Set.Ioo α₂ β₂ := hq₂
  obtain ⟨hr₃a, hr₃b⟩ : Int.fract q₃ ∈ Set.Ioo α₃ β₃ := hq₃
  obtain ⟨hc₁a, hc₁b⟩ : Int.fract (f (Int.fract q₁)) ∈ Set.Ioo α₂ β₂ := by
    rw [fract_apply_fract hper]
    exact hfq₁
  obtain ⟨hc₂a, hc₂b⟩ : Int.fract (f (Int.fract q₂)) ∈ Set.Ioo α₁ β₁ := by
    rw [fract_apply_fract hper]
    exact hfq₂
  obtain ⟨hc₃a, hc₃b⟩ : Int.fract (f (Int.fract q₃)) ∈ Set.Ioo α₃ β₃ := by
    rw [fract_apply_fract hper]
    exact hfq₃
  set r₁ := Int.fract q₁
  set r₂ := Int.fract q₂
  set r₃ := Int.fract q₃
  have e₁ := Int.floor_add_fract (f r₁)
  have e₂ := Int.floor_add_fract (f r₂)
  have e₃ := Int.floor_add_fract (f r₃)
  set k₁ := ⌊f r₁⌋
  set k₂ := ⌊f r₂⌋
  set k₃ := ⌊f r₃⌋
  set c₁ := Int.fract (f r₁)
  set c₂ := Int.fract (f r₂)
  set c₃ := Int.fract (f r₃)
  have m₁₂ : f r₁ < f r₂ := hmono (by linarith)
  have m₂₃ : f r₂ < f r₃ := hmono (by linarith)
  have m₃₁ : f r₃ < f r₁ + 1 := by
    have h := hmono (show r₃ < r₁ + ((1 : ℤ) : ℚ) by push_cast; linarith)
    rw [hper] at h
    push_cast at h
    exact h
  have i₁ : (k₁ : ℚ) < k₂ := by linarith
  have i₂ : (k₂ : ℚ) < k₁ + 2 := by linarith
  have i₃ : (k₂ : ℚ) < k₃ + 1 := by linarith
  have i₄ : (k₃ : ℚ) < k₁ + 1 := by linarith
  have j₁ : k₁ < k₂ := by exact_mod_cast i₁
  have j₂ : k₂ < k₁ + 2 := by exact_mod_cast i₂
  have j₃ : k₂ < k₃ + 1 := by exact_mod_cast i₃
  have j₄ : k₃ < k₁ + 1 := by exact_mod_cast i₄
  omega

/-- **The three-arc word is trivial at every strictly increasing periodic permutation.** -/
theorem threeArc_word_eq_one (hmono : StrictMono f)
    (hper : ∀ (t : ℚ) (k : ℤ), f (t + k) = f t + k) {a₁ a₂ a₃ : Equiv.Perm ℚ}
    {α₁ β₁ α₂ β₂ α₃ β₃ : ℚ} (h0 : 0 ≤ α₁) (h12 : β₁ ≤ α₂) (h23 : β₂ ≤ α₃) (h1 : β₃ ≤ 1)
    (ha₁ : SupportedIn a₁ (perSet (Set.Ioo α₁ β₁)))
    (ha₂ : SupportedIn a₂ (perSet (Set.Ioo α₂ β₂)))
    (ha₃ : SupportedIn a₃ (perSet (Set.Ioo α₃ β₃))) :
    ⁅⁅⁅a₁, f * a₂ * f⁻¹⁆, ⁅a₂, f * a₁ * f⁻¹⁆⁆, ⁅a₃, f * a₃ * f⁻¹⁆⁆ = 1 := by
  by_cases d12 : Disjoint (perSet (Set.Ioo α₁ β₁)) (f '' perSet (Set.Ioo α₂ β₂))
  · have h : ⁅a₁, f * a₂ * f⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr (commute_of_supportedIn ha₁ (ha₂.conj f) d12)
    rw [h, commutatorElement_one_left, commutatorElement_one_left]
  by_cases d21 : Disjoint (perSet (Set.Ioo α₂ β₂)) (f '' perSet (Set.Ioo α₁ β₁))
  · have h : ⁅a₂, f * a₁ * f⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr (commute_of_supportedIn ha₂ (ha₁.conj f) d21)
    rw [h, commutatorElement_one_right, commutatorElement_one_left]
  by_cases d33 : Disjoint (perSet (Set.Ioo α₃ β₃)) (f '' perSet (Set.Ioo α₃ β₃))
  · have h : ⁅a₃, f * a₃ * f⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_commute.mpr (commute_of_supportedIn ha₃ (ha₃.conj f) d33)
    rw [h, commutatorElement_one_right]
  exfalso
  obtain ⟨y₂, hy₂, q₂, hq₂, rfl⟩ := Set.not_disjoint_iff.mp d12
  obtain ⟨y₁, hy₁, q₁, hq₁, rfl⟩ := Set.not_disjoint_iff.mp d21
  obtain ⟨y₃, hy₃, q₃, hq₃, rfl⟩ := Set.not_disjoint_iff.mp d33
  exact not_all_overlap hmono hper h0 h12 h23 h1 hq₁ hy₁ hq₂ hy₂ hq₃ hy₃

end Circle

/-! ## The word -/

/-- The three-arc word `[[s₁₂, s₂₁], s₃₃]`, `s_ij = [a_i, x a_j x⁻¹]`, in `G ∗ ⟨x⟩`. -/
def threeArcWord {G : Type} [Group G] (a₁ a₂ a₃ : G) : Monoid.Coprod G (FreeGroup (Fin 1)) :=
  ⁅⁅⁅Monoid.Coprod.inl a₁,
        Monoid.Coprod.inr (FreeGroup.of (0 : Fin 1)) * Monoid.Coprod.inl a₂ *
          (Monoid.Coprod.inr (FreeGroup.of (0 : Fin 1)))⁻¹⁆,
      ⁅Monoid.Coprod.inl a₂,
        Monoid.Coprod.inr (FreeGroup.of (0 : Fin 1)) * Monoid.Coprod.inl a₁ *
          (Monoid.Coprod.inr (FreeGroup.of (0 : Fin 1)))⁻¹⁆⁆,
    ⁅Monoid.Coprod.inl a₃,
      Monoid.Coprod.inr (FreeGroup.of (0 : Fin 1)) * Monoid.Coprod.inl a₃ *
        (Monoid.Coprod.inr (FreeGroup.of (0 : Fin 1)))⁻¹⁆⁆

#audit_axioms GroupApproximation.BHPalomar.MixedIdentities.fract_apply_fract
#audit_axioms GroupApproximation.BHPalomar.MixedIdentities.not_all_overlap
#audit_axioms GroupApproximation.BHPalomar.MixedIdentities.threeArc_word_eq_one

end MixedIdentities
end BHPalomar
end GroupApproximation
