/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BooneHigman.Statement.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.SetTheory.Cardinal.Free

/-!
# Basic API for the Boone–Higman statements

**Metabelian groups.**
* `isMetabelianGroup_iff_derivedSeries_two`: the definition is `derivedSeries G 2 = ⊥`.
* `IsMetabelianGroup.isSolvable`.
* `isMetabelianGroup_iff_exists_commutator_le`: `G` is metabelian iff some subgroup `N ≥ G'` has
  `⁅N, N⁆ = ⊥`.
* `isMetabelianGroup_of_commute`: commutative groups are metabelian.
* Closure: `IsMetabelianGroup.of_injective`, `IsMetabelianGroup.subgroup`,
  `IsMetabelianGroup.of_surjective`, `IsMetabelianGroup.prod`.
* `isMetabelianGroup_semidirectProduct`: `N ⋊[φ] K` is metabelian for commutative `N` and `K`.

**Embeddings.**
* `EmbedsInFinitelyPresentedSimpleGroup.of_injective` and `.of_mulEquiv`.
* `embedsInFinitelyPresentedSimpleGroup_of_injective`: the constructor from an injective map.
* `fg_of_isFinitelyPresented` and `countable_of_isFinitelyPresented`;
  `EmbedsInFinitelyPresentedSimpleGroup.countable`.
* `finitelyPresentedMetabelianStatement_of_finitelyGenerated`: T2 implies T1.
-/

namespace GroupApproximation.BooneHigman

section Metabelian

variable {G H : Type*} [Group G] [Group H]

theorem isMetabelianGroup_iff_derivedSeries_two :
    IsMetabelianGroup G ↔ derivedSeries G 2 = ⊥ := by
  show ⁅commutator G, commutator G⁆ = ⊥ ↔ ⁅derivedSeries G 1, derivedSeries G 1⁆ = ⊥
  rw [derivedSeries_one]

theorem IsMetabelianGroup.isSolvable (h : IsMetabelianGroup G) : IsSolvable G :=
  ⟨⟨2, isMetabelianGroup_iff_derivedSeries_two.mp h⟩⟩

theorem isMetabelianGroup_of_commutator_le {N : Subgroup G} (hle : commutator G ≤ N)
    (hN : ⁅N, N⁆ = ⊥) : IsMetabelianGroup G := by
  rw [IsMetabelianGroup, eq_bot_iff, ← hN]
  exact Subgroup.commutator_mono hle hle

theorem isMetabelianGroup_iff_exists_commutator_le :
    IsMetabelianGroup G ↔ ∃ N : Subgroup G, commutator G ≤ N ∧ ⁅N, N⁆ = ⊥ :=
  ⟨fun h ↦ ⟨commutator G, le_rfl, h⟩,
    fun ⟨_, hle, hN⟩ ↦ isMetabelianGroup_of_commutator_le hle hN⟩

theorem isMetabelianGroup_of_commute (h : ∀ a b : G, a * b = b * a) : IsMetabelianGroup G := by
  refine isMetabelianGroup_of_commutator_le (N := ⊥) ?_ (by simp)
  rw [commutator, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact h g₁ g₂

theorem IsMetabelianGroup.of_injective {f : H →* G} (hf : Function.Injective f)
    (h : IsMetabelianGroup G) : IsMetabelianGroup H := by
  rw [isMetabelianGroup_iff_derivedSeries_two] at h ⊢
  have hle := map_derivedSeries_le_derivedSeries f 2
  rw [h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hf] at hle
  exact hle

theorem IsMetabelianGroup.subgroup (h : IsMetabelianGroup G) (K : Subgroup G) :
    IsMetabelianGroup K :=
  h.of_injective K.subtype_injective

theorem IsMetabelianGroup.of_surjective {f : G →* H} (hf : Function.Surjective f)
    (h : IsMetabelianGroup G) : IsMetabelianGroup H := by
  rw [isMetabelianGroup_iff_derivedSeries_two] at h ⊢
  have hle := derivedSeries_le_map_derivedSeries hf 2
  rw [h, Subgroup.map_bot, le_bot_iff] at hle
  exact hle

theorem IsMetabelianGroup.prod (hG : IsMetabelianGroup G) (hH : IsMetabelianGroup H) :
    IsMetabelianGroup (G × H) := by
  have hc : commutator (G × H) = (commutator G).prod (commutator H) := by
    rw [commutator, commutator, commutator, ← Subgroup.top_prod_top,
      Subgroup.commutator_prod_prod]
  rw [IsMetabelianGroup, hc, Subgroup.commutator_prod_prod, hG, hH, Subgroup.bot_prod_bot]

/-- A semidirect product of commutative groups is metabelian: the derived subgroup lies in the
kernel of the projection to `K`, which is the commutative image of `N`. -/
theorem isMetabelianGroup_semidirectProduct {N K : Type*} [Group N] [Group K]
    (φ : K →* MulAut N) (hN : ∀ a b : N, a * b = b * a) (hK : ∀ a b : K, a * b = b * a) :
    IsMetabelianGroup (N ⋊[φ] K) := by
  refine isMetabelianGroup_of_commutator_le
    (N := (SemidirectProduct.rightHom : N ⋊[φ] K →* K).ker) ?_ ?_
  · rw [commutator, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hK _ _
  · rw [← SemidirectProduct.range_inl_eq_ker_rightHom, eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul, hN a b]

end Metabelian

section Embeds

variable {G H : Type*} [Group G] [Group H]

theorem EmbedsInFinitelyPresentedSimpleGroup.of_injective {f : H →* G}
    (hf : Function.Injective f) (h : EmbedsInFinitelyPresentedSimpleGroup G) :
    EmbedsInFinitelyPresentedSimpleGroup H := by
  obtain ⟨S, _, hS, hsimple, g, hg⟩ := h
  exact ⟨S, inferInstance, hS, hsimple, g.comp f, hg.comp hf⟩

theorem EmbedsInFinitelyPresentedSimpleGroup.of_mulEquiv (e : H ≃* G)
    (h : EmbedsInFinitelyPresentedSimpleGroup G) : EmbedsInFinitelyPresentedSimpleGroup H :=
  h.of_injective (f := e.toMonoidHom) e.injective

theorem embedsInFinitelyPresentedSimpleGroup_of_injective {S : Type} [Group S]
    [Group.IsFinitelyPresented S] [IsSimpleGroup S] {f : G →* S} (hf : Function.Injective f) :
    EmbedsInFinitelyPresentedSimpleGroup G :=
  ⟨S, inferInstance, inferInstance, inferInstance, f, hf⟩

theorem fg_of_isFinitelyPresented (G : Type*) [Group G] [h : Group.IsFinitelyPresented G] :
    Group.FG G := by
  obtain ⟨_, φ, hφ, -⟩ := h.out
  exact Group.fg_of_surjective hφ

theorem countable_of_isFinitelyPresented (G : Type*) [Group G]
    [h : Group.IsFinitelyPresented G] : Countable G := by
  obtain ⟨_, φ, hφ, -⟩ := h.out
  exact hφ.countable

theorem EmbedsInFinitelyPresentedSimpleGroup.countable
    (h : EmbedsInFinitelyPresentedSimpleGroup G) : Countable G := by
  obtain ⟨S, _, hS, -, f, hf⟩ := h
  haveI := hS
  haveI := countable_of_isFinitelyPresented S
  exact hf.countable

/-- **T2 implies T1**: a finitely presented group is finitely generated. -/
theorem finitelyPresentedMetabelianStatement_of_finitelyGenerated
    (h : FinitelyGeneratedMetabelianStatement) : FinitelyPresentedMetabelianStatement := by
  intro G _ hfp hmet
  haveI := hfp
  exact h G (fg_of_isFinitelyPresented G) hmet

end Embeds

end GroupApproximation.BooneHigman
