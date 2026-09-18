import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiTowerPerm
import GroupApproximation.Meta.AxiomGuard

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

/-!
# Moving a three-cycle into the room

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

Part of work order WO-A2.  Consider an eight-level tower with base `A` along some `f₀ ∈ [[T]]`,
where `f` moves `A` to level `1` and `f²` moves `A` to level `2`, and levels `3, …, 7` lie in the
room `V`.  Then `threeCycle f A ∈ N` for every subgroup `N` that is normalised by
`⁅[[T]], [[T]]⁆` and contains the commutators `⁅a, b⁆` of elements of `⁅[[T]], [[T]]⁆` supported in
`V` (`threeCycle_mem_of_eight_tower`).

In `S₈` the three-cycle `⁅(0 1), (0 2)⁆` is the conjugate by `ρ` of `⁅α, β⁆`, where `α` and `β`
are commutators moving only the points `3, …, 7` and `ρ` is a product of two commutators (a finite
computation, `swap_commutator_eq_fin_eight`).
-/

open scoped commutatorElement

variable {X : Type*}

/-- A commutator of `S₈` moving only the points `3, 4, 6, 7`. -/
def alpha8 : Equiv.Perm (Fin 8) := ⁅Equiv.swap 3 4, Equiv.swap 3 6 * Equiv.swap 4 7⁆

/-- A commutator of `S₈` moving only the points `3, 5, 6, 7`. -/
def beta8 : Equiv.Perm (Fin 8) := ⁅Equiv.swap 3 5, Equiv.swap 3 6 * Equiv.swap 5 7⁆

/-- A product of two commutators of `S₈`. -/
def rho8 : Equiv.Perm (Fin 8) :=
  ⁅Equiv.swap 0 3, Equiv.swap 0 1 * Equiv.swap 3 4⁆ *
    ⁅Equiv.swap 2 5, Equiv.swap 2 6 * Equiv.swap 5 7⁆

/-- The three-cycle `(0 1 2)` of `S₈` is conjugate by `ρ` to a commutator on `3, …, 7`. -/
theorem swap_commutator_eq_fin_eight :
    (⁅Equiv.swap (0 : Fin 8) 1, Equiv.swap 0 2⁆ : Equiv.Perm (Fin 8)) =
      rho8 * ⁅alpha8, beta8⁆ * rho8⁻¹ := by
  decide +kernel

theorem alpha8_fix : ∀ i : Fin 8, alpha8 i ≠ i → 3 ≤ (i : ℕ) := by
  decide +kernel

theorem beta8_fix : ∀ i : Fin 8, beta8 i ≠ i → 3 ≤ (i : ℕ) := by
  decide +kernel

/-- **Moving a three-cycle into the room** along an eight-level tower. -/
theorem threeCycle_mem_of_eight_tower [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {T : X ≃ₜ X} {N : Subgroup (Equiv.Perm X)} {V : Set X}
    (hN : ∀ n ∈ N, ∀ g ∈ ⁅fullGroup T, fullGroup T⁆, g * n * g⁻¹ ∈ N)
    (hroom : ∀ a ∈ ⁅fullGroup T, fullGroup T⁆, ∀ b ∈ ⁅fullGroup T, fullGroup T⁆,
      HydeLodha.SupportedIn a V → HydeLodha.SupportedIn b V → ⁅a, b⁆ ∈ N)
    {f₀ : Equiv.Perm X} (hf₀ : f₀ ∈ fullGroup T) {A : Set X} (hA : IsClopen A)
    {E : Fin 8 → ℤ} (hdisj : ∀ i j x, (f₀ ^ (-E i)) x ∈ A → (f₀ ^ (-E j)) x ∈ A → i = j)
    (hE0 : E 0 = 0) {f : Equiv.Perm X} (h1 : ∀ y ∈ A, f y = (f₀ ^ E 1) y)
    (h2 : ∀ y ∈ A, (f * f) y = (f₀ ^ E 2) y)
    (hV : ∀ i : Fin 8, 3 ≤ (i : ℕ) → ∀ x, (f₀ ^ (-E i)) x ∈ A → x ∈ V) :
    threeCycle f A ∈ N := by
  have s1 : swapAlong f A = towerPerm f₀ A E hdisj (Equiv.swap 0 1) :=
    swapAlong_eq_towerPerm hdisj (i₀ := 0) (j := 1) hE0 (by decide) h1
  have s2 : swapAlong (f * f) A = towerPerm f₀ A E hdisj (Equiv.swap 0 2) :=
    swapAlong_eq_towerPerm hdisj (i₀ := 0) (j := 2) hE0 (by decide) h2
  have hφ : ∀ σ τ : Equiv.Perm (Fin 8), towerPerm f₀ A E hdisj ⁅σ, τ⁆ =
      ⁅towerPerm f₀ A E hdisj σ, towerPerm f₀ A E hdisj τ⁆ := fun σ τ => by
    rw [map_commutatorElement]
  have hthree : threeCycle f A = towerPerm f₀ A E hdisj rho8 *
      towerPerm f₀ A E hdisj ⁅alpha8, beta8⁆ * (towerPerm f₀ A E hdisj rho8)⁻¹ := by
    show ⁅swapAlong f A, swapAlong (f * f) A⁆ = _
    rw [s1, s2, ← hφ, swap_commutator_eq_fin_eight, map_mul, map_mul, map_inv]
  have hsupp : ∀ σ : Equiv.Perm (Fin 8), (∀ i : Fin 8, σ i ≠ i → 3 ≤ (i : ℕ)) →
      HydeLodha.SupportedIn (towerPerm f₀ A E hdisj σ) V := fun σ hσ =>
    towerPerm_supportedIn hdisj fun i hi x hx => hV i (hσ i hi) x hx
  have hα : towerPerm f₀ A E hdisj alpha8 ∈ ⁅fullGroup T, fullGroup T⁆ :=
    towerPerm_commutator_mem hf₀ hA hdisj (Equiv.swap 3 4) (Equiv.swap 3 6 * Equiv.swap 4 7)
  have hβ : towerPerm f₀ A E hdisj beta8 ∈ ⁅fullGroup T, fullGroup T⁆ :=
    towerPerm_commutator_mem hf₀ hA hdisj (Equiv.swap 3 5) (Equiv.swap 3 6 * Equiv.swap 5 7)
  have hc : towerPerm f₀ A E hdisj ⁅alpha8, beta8⁆ ∈ N := by
    rw [hφ]
    exact hroom _ hα _ hβ (hsupp alpha8 alpha8_fix) (hsupp beta8 beta8_fix)
  have eρ : rho8 = ⁅Equiv.swap 0 3, Equiv.swap 0 1 * Equiv.swap 3 4⁆ *
      ⁅Equiv.swap 2 5, Equiv.swap 2 6 * Equiv.swap 5 7⁆ := rfl
  have hρ : towerPerm f₀ A E hdisj rho8 ∈ ⁅fullGroup T, fullGroup T⁆ := by
    rw [eρ, map_mul]
    exact mul_mem (towerPerm_commutator_mem hf₀ hA hdisj _ _)
      (towerPerm_commutator_mem hf₀ hA hdisj _ _)
  rw [hthree]
  exact hN _ hc _ hρ

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.swap_commutator_eq_fin_eight
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.alpha8_fix
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.beta8_fix
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.threeCycle_mem_of_eight_tower
