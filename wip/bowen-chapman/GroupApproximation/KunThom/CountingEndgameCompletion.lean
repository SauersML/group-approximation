import GroupApproximation.Matching.FiniteGroupoidBisection

/-!
# Completing a partial bisection of a finite groupoid

The last combinatorial step of Kun and Thom's proof of Theorem 4.1
(arXiv:2608.06222, §4) selects arrows of the cluster groupoid on a large set of
objects, with distinct sources and distinct targets, and completes them to a
total bisection.  Every selected arrow stays inside its connected component, so
inside each component the selected sources and the selected targets have the
same number of objects, and the unselected objects can be paired by arbitrary
arrows.

* `exists_mem_orbit_notMem_image`: an orbit meeting the unselected sources also
  meets the unselected targets.
* `exists_injective_extend`, `exists_equiv_extend`: an object map that is
  injective on `S` and keeps every object of `S` in its orbit extends to a
  permutation of the objects that keeps every object in its orbit.
* `exists_bisection_extend`: arrows `X ⟶ τ X` for `X ∈ S`, with `τ` injective
  on `S`, extend to a total bisection whose arrow at every `X ∈ S` is the given
  one.
-/

namespace GroupApproximation
namespace CountingEndgame

open CategoryTheory

universe u v

/-- If `τ` is injective on `S` and keeps every object of `S` in its orbit, an
orbit that meets the complement of `S` also meets the complement of the image
of `S`. -/
theorem exists_mem_orbit_notMem_image {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] (S : Finset C) (τ : C → C) (hinj : Set.InjOn τ (S : Set C))
    (horb : ∀ X ∈ S, τ X ∈ FiniteGroupoid.orbit X) {X₀ : C} (hX₀ : X₀ ∉ S) :
    ∃ Y ∈ FiniteGroupoid.orbit X₀, Y ∉ S.image τ := by
  by_contra hcon
  have hsub : FiniteGroupoid.orbit X₀ ⊆ (FiniteGroupoid.orbit X₀ ∩ S).image τ := by
    intro Y hY
    have hYim : Y ∈ S.image τ := by
      by_contra hY'
      exact hcon ⟨Y, hY, hY'⟩
    obtain ⟨X, hXS, hXY⟩ := Finset.mem_image.mp hYim
    refine Finset.mem_image.mpr ⟨X, Finset.mem_inter.mpr ⟨?_, hXS⟩, hXY⟩
    have hτX : τ X ∈ FiniteGroupoid.orbit X₀ := by
      rw [hXY]
      exact hY
    obtain ⟨g⟩ := (FiniteGroupoid.mem_orbit X₀ (τ X)).mp hτX
    obtain ⟨k⟩ := (FiniteGroupoid.mem_orbit X (τ X)).mp (horb X hXS)
    exact (FiniteGroupoid.mem_orbit X₀ X).mpr ⟨g ≫ inv k⟩
  have h₁ := Finset.card_le_card hsub
  have h₂ : ((FiniteGroupoid.orbit X₀ ∩ S).image τ).card =
      (FiniteGroupoid.orbit X₀ ∩ S).card := by
    apply Finset.card_image_of_injOn
    apply Set.InjOn.mono _ hinj
    intro Y hY
    exact Finset.mem_coe.mpr (Finset.mem_inter.mp (Finset.mem_coe.mp hY)).2
  have h₃ := Finset.card_sdiff_add_card_inter (FiniteGroupoid.orbit X₀) S
  have h₄ : 0 < (FiniteGroupoid.orbit X₀ \ S).card :=
    Finset.card_pos.mpr ⟨X₀, Finset.mem_sdiff.mpr ⟨FiniteGroupoid.self_mem_orbit X₀, hX₀⟩⟩
  omega

/-- An object map that is injective on `S` and keeps every object of `S` in its
orbit extends to an injective object map that keeps every object in its orbit.
The induction runs on the number `k` of objects outside `S`. -/
theorem exists_injective_extend {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] :
    ∀ (k : ℕ) (S : Finset C) (τ : C → C), (Finset.univ \ S).card = k →
      Set.InjOn τ (S : Set C) → (∀ X ∈ S, τ X ∈ FiniteGroupoid.orbit X) →
      ∃ σ : C → C, Function.Injective σ ∧ (∀ X, σ X ∈ FiniteGroupoid.orbit X) ∧
        ∀ X ∈ S, σ X = τ X := by
  intro k
  induction k with
  | zero =>
    intro S τ hk hinj horb
    have hS : ∀ X, X ∈ S := by
      intro X
      by_contra hX
      have hpos : 0 < (Finset.univ \ S).card :=
        Finset.card_pos.mpr ⟨X, Finset.mem_sdiff.mpr ⟨Finset.mem_univ X, hX⟩⟩
      omega
    refine ⟨τ, ?_, fun X ↦ horb X (hS X), fun X _ ↦ rfl⟩
    intro X Y hXY
    exact hinj (Finset.mem_coe.mpr (hS X)) (Finset.mem_coe.mpr (hS Y)) hXY
  | succ k ih =>
    intro S τ hk hinj horb
    obtain ⟨X₀, hX₀⟩ : (Finset.univ \ S).Nonempty := Finset.card_pos.mp (by omega)
    have hX₀S : X₀ ∉ S := (Finset.mem_sdiff.mp hX₀).2
    obtain ⟨Y₀, hY₀orb, hY₀im⟩ := exists_mem_orbit_notMem_image S τ hinj horb hX₀S
    obtain ⟨τ', hτ'S, hτ'X₀⟩ : ∃ τ' : C → C, (∀ X ∈ S, τ' X = τ X) ∧ τ' X₀ = Y₀ :=
      ⟨Function.update τ X₀ Y₀,
        fun X hX ↦ Function.update_of_ne (fun hXe ↦ hX₀S (by rw [← hXe]; exact hX)) Y₀ τ,
        Function.update_self X₀ Y₀ τ⟩
    have hk' : (Finset.univ \ insert X₀ S).card = k := by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem hX₀]
      omega
    have hinj' : Set.InjOn τ' ((insert X₀ S : Finset C) : Set C) := by
      intro X hX Y hY hXY
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hX) with hXe | hXS <;>
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hY) with hYe | hYS
      · rw [hXe, hYe]
      · exfalso
        apply hY₀im
        rw [← hτ'X₀, ← hXe, hXY, hτ'S Y hYS]
        exact Finset.mem_image_of_mem τ hYS
      · exfalso
        apply hY₀im
        rw [← hτ'X₀, ← hYe, ← hXY, hτ'S X hXS]
        exact Finset.mem_image_of_mem τ hXS
      · rw [hτ'S X hXS, hτ'S Y hYS] at hXY
        exact hinj (Finset.mem_coe.mpr hXS) (Finset.mem_coe.mpr hYS) hXY
    have horb' : ∀ X ∈ insert X₀ S, τ' X ∈ FiniteGroupoid.orbit X := by
      intro X hX
      rcases Finset.mem_insert.mp hX with hXe | hXS
      · rw [hXe, hτ'X₀]
        exact hY₀orb
      · rw [hτ'S X hXS]
        exact horb X hXS
    obtain ⟨σ, hσinj, hσorb, hσext⟩ := ih (insert X₀ S) τ' hk' hinj' horb'
    exact ⟨σ, hσinj, hσorb, fun X hX ↦
      (hσext X (Finset.mem_insert_of_mem hX)).trans (hτ'S X hX)⟩

/-- An object map that is injective on `S` and keeps every object of `S` in its
orbit extends to a permutation of the objects that keeps every object in its
orbit. -/
theorem exists_equiv_extend {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    (S : Finset C) (τ : C → C) (hinj : Set.InjOn τ (S : Set C))
    (horb : ∀ X ∈ S, τ X ∈ FiniteGroupoid.orbit X) :
    ∃ σ : C ≃ C, (∀ X, σ X ∈ FiniteGroupoid.orbit X) ∧ ∀ X ∈ S, σ X = τ X := by
  obtain ⟨σ, hσinj, hσorb, hσext⟩ :=
    exists_injective_extend (Finset.univ \ S).card S τ rfl hinj horb
  exact ⟨Equiv.ofBijective σ ((Fintype.bijective_iff_injective_and_card σ).2 ⟨hσinj, rfl⟩),
    hσorb, hσext⟩

/-- **Completion of a partial bisection.**  Arrows `X ⟶ τ X` for the objects
`X ∈ S`, with `τ` injective on `S`, extend to a total bisection whose arrow at
every `X ∈ S` is the given arrow, up to the identification of its target. -/
theorem exists_bisection_extend {C : Type u} [Groupoid.{v} C] [Fintype C]
    [DecidableEq C] (S : Finset C) (τ : C → C) (hinj : Set.InjOn τ (S : Set C))
    (arrow : ∀ X ∈ S, X ⟶ τ X) :
    ∃ b : FiniteGroupoid.Bisection C, ∀ X (hX : X ∈ S),
      ∃ e : b.objEquiv X = τ X, b.hom X ≫ eqToHom e = arrow X hX := by
  have horb : ∀ X ∈ S, τ X ∈ FiniteGroupoid.orbit X :=
    fun X hX ↦ (FiniteGroupoid.mem_orbit X (τ X)).mpr ⟨arrow X hX⟩
  obtain ⟨σ, hσorb, hσext⟩ := exists_equiv_extend S τ hinj horb
  refine ⟨⟨σ, fun X ↦ if hX : X ∈ S then arrow X hX ≫ eqToHom (hσext X hX).symm
    else Classical.choice ((FiniteGroupoid.mem_orbit X (σ X)).mp (hσorb X))⟩, ?_⟩
  intro X hX
  refine ⟨hσext X hX, ?_⟩
  simp only [dif_pos hX, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end CountingEndgame
end GroupApproximation
