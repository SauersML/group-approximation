import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiFullGroup
import GroupApproximation.GroupTheory.HydeLodha.HigmanEpstein
import GroupApproximation.Manuscript.SimpleKazhdanSofic.RingPartitions
import GroupApproximation.Meta.AxiomGuard

/-!
# Assembly lemmas for Matui's simplicity theorem

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

Let `D = ⁅[[T]], [[T]]⁆` and `A = alternatingFullGroup T`.  This file proves the parts of the
argument that are group theory and point-set topology.

* `isSimpleGroup_of_le`: if `D ≤ A`, `D ≠ ⊥`, and every nontrivial subgroup of `D` normalized by
  `D` contains `A`, then `D` is simple.
* `commutator_closure_le`: commutators of a generated subgroup lie in a normalized subgroup once the
  commutators of the generators do.  This is the reduction used for `D ≤ A`.
* `exists_room_of_ne_bot`: a nontrivial subgroup `N ≤ D` normalized by `D` contains `⁅a, b⁆` for all
  `a, b ∈ D` supported in some nonempty clopen `V`.  This is the displacement step: take `f ∈ N`,
  `f ≠ 1`, and `V` with `f V ∩ V = ∅`.
* `exists_threeCycle_ne_one`, `commutator_fullGroup_ne_bot`: for an infinite minimal system the
  three-cycle along `T` on a small clopen set is nontrivial, so `D ≠ ⊥`.
-/

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

open scoped commutatorElement

variable {X : Type*}

/-! ## Group theory -/

/-- Commutators of `closure S` lie in `A` once `A` is normalized by `closure S` and contains the
commutators of elements of `S`. -/
theorem commutator_closure_le {M : Type*} [Group M] {S : Set M} {A : Subgroup M}
    (hA : ∀ a ∈ A, ∀ g ∈ Subgroup.closure S, g * a * g⁻¹ ∈ A)
    (hS : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ A) :
    ⁅Subgroup.closure S, Subgroup.closure S⁆ ≤ A := by
  have h1 : ∀ t ∈ S, ∀ g ∈ Subgroup.closure S, ⁅g, t⁆ ∈ A := by
    intro t ht g hg
    refine Subgroup.closure_induction (k := S) (p := fun g _ => ⁅g, t⁆ ∈ A) ?_ ?_ ?_ ?_ hg
    · intro x hx
      exact hS x hx t ht
    · show ⁅(1 : M), t⁆ ∈ A
      rw [commutatorElement_one_left]
      exact A.one_mem
    · intro x y hx _ ihx ihy
      show ⁅x * y, t⁆ ∈ A
      have e : ⁅x * y, t⁆ = x * ⁅y, t⁆ * x⁻¹ * ⁅x, t⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact A.mul_mem (hA _ ihy x hx) ihx
    · intro x hx ihx
      show ⁅x⁻¹, t⁆ ∈ A
      have e : ⁅x⁻¹, t⁆ = x⁻¹ * ⁅x, t⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hA _ (A.inv_mem ihx) _ ((Subgroup.closure S).inv_mem hx)
  rw [Subgroup.commutator_le]
  intro g hg u hu
  refine Subgroup.closure_induction (k := S) (p := fun u _ => ⁅g, u⁆ ∈ A) ?_ ?_ ?_ ?_ hu
  · intro x hx
    exact h1 x hx g hg
  · show ⁅g, (1 : M)⁆ ∈ A
    rw [commutatorElement_one_right]
    exact A.one_mem
  · intro x y hx _ ihx ihy
    show ⁅g, x * y⁆ ∈ A
    have e : ⁅g, x * y⁆ = ⁅g, x⁆ * (x * ⁅g, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact A.mul_mem ihx (hA _ ihy x hx)
  · intro x hx ihx
    show ⁅g, x⁻¹⁆ ∈ A
    have e : ⁅g, x⁻¹⁆ = x⁻¹ * ⁅g, x⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hA _ (A.inv_mem ihx) _ ((Subgroup.closure S).inv_mem hx)

/-- **Simplicity from a minimal normal piece.**  If `D ≤ A`, `D ≠ ⊥` and every nontrivial subgroup
`N ≤ D` normalized by `D` contains `A`, then `D` is simple. -/
theorem isSimpleGroup_of_le {M : Type*} [Group M] {D A : Subgroup M} (hDA : D ≤ A) (hne : D ≠ ⊥)
    (hmin : ∀ N : Subgroup M, N ≤ D → N ≠ ⊥ → (∀ n ∈ N, ∀ g ∈ D, g * n * g⁻¹ ∈ N) → A ≤ N) :
    IsSimpleGroup ↥D := by
  have hnt : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun H hH => ?_ }
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨⟨f, hfD⟩, hfH⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have hNnorm : ∀ n ∈ H.map D.subtype, ∀ g ∈ D, g * n * g⁻¹ ∈ H.map D.subtype := by
    rintro n ⟨x, hxH, rfl⟩ g hg
    exact ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, hH.conj_mem x hxH ⟨g, hg⟩, rfl⟩
  have hNle : H.map D.subtype ≤ D := by
    rintro n ⟨x, _, rfl⟩
    exact x.2
  have hNne : H.map D.subtype ≠ ⊥ := by
    intro hN
    have hfN : f ∈ H.map D.subtype := ⟨⟨f, hfD⟩, hfH, rfl⟩
    rw [hN, Subgroup.mem_bot] at hfN
    exact hf1 (Subtype.ext (Subtype.ext hfN))
  have hle : A ≤ H.map D.subtype := hmin _ hNle hNne hNnorm
  rw [Subgroup.eq_top_iff']
  intro x
  obtain ⟨y, hyH, hyx⟩ := hle (hDA x.2)
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hyH

/-! ## Displacement -/

/-- A continuous permutation `g ≠ 1` of a totally separated space displaces a nonempty clopen set. -/
theorem exists_displaced_clopen [TopologicalSpace X] [TotallySeparatedSpace X]
    {g : Equiv.Perm X} (hg : Continuous g) (hg1 : g ≠ 1) :
    ∃ V : Set X, IsClopen V ∧ V.Nonempty ∧ ∀ y ∈ V, g y ∉ V := by
  have hx : ∃ x, g x ≠ x := by
    by_contra h
    exact hg1 (Equiv.ext fun x => Classical.byContradiction fun hne => h ⟨x, hne⟩)
  obtain ⟨x, hx⟩ := hx
  obtain ⟨C, hC, hxC, hgxC⟩ := exists_isClopen_of_totally_separated hx.symm
  refine ⟨C ∩ ⇑g ⁻¹' Cᶜ, hC.inter (hC.compl.preimage hg), ⟨x, hxC, hgxC⟩, fun y hy hgy => ?_⟩
  have h2 : g y ∉ C := hy.2
  exact h2 hgy.1

/-- If `f ∈ N` displaces `V`, then `N` contains `⁅a, b⁆` for `a, b` supported in `V` in a subgroup
normalizing `N`. -/
theorem commutatorElement_mem_of_displaced {L N : Subgroup (Equiv.Perm X)}
    (hN : ∀ n ∈ N, ∀ g ∈ L, g * n * g⁻¹ ∈ N) {f : Equiv.Perm X} (hf : f ∈ N) {V : Set X}
    (hV : ∀ y ∈ V, f y ∉ V) {a b : Equiv.Perm X} (ha : a ∈ L) (hb : b ∈ L)
    (haV : HydeLodha.SupportedIn a V) (hbV : HydeLodha.SupportedIn b V) : ⁅a, b⁆ ∈ N := by
  have hdisp : Disjoint (⇑f '' V) V := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hfy
    exact hV y hy hfy
  rw [← HydeLodha.commutatorElement_commutatorElement_of_displaced hdisp haV hbV]
  exact HydeLodha.commutatorElement_mem_left hN (HydeLodha.commutatorElement_mem_right hN ha hf) hb

/-- **Room in a nontrivial normal subgroup.**  A nontrivial subgroup `N` of the derived full group,
normalized by it, contains `⁅a, b⁆` for all `a, b` in the derived full group supported in some
nonempty clopen set `V`. -/
theorem exists_room_of_ne_bot [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X] (T : X ≃ₜ X) {N : Subgroup (Equiv.Perm X)}
    (hND : N ≤ ⁅fullGroup T, fullGroup T⁆) (hne : N ≠ ⊥)
    (hN : ∀ n ∈ N, ∀ g ∈ ⁅fullGroup T, fullGroup T⁆, g * n * g⁻¹ ∈ N) :
    ∃ V : Set X, IsClopen V ∧ V.Nonempty ∧ ∀ a ∈ ⁅fullGroup T, fullGroup T⁆,
      ∀ b ∈ ⁅fullGroup T, fullGroup T⁆, HydeLodha.SupportedIn a V →
        HydeLodha.SupportedIn b V → ⁅a, b⁆ ∈ N := by
  obtain ⟨⟨f, hfN⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
  have hfc : Continuous f :=
    IsFullGroupElement.continuous (mem_fullGroup.mp (HydeLodha.commutator_le_self _ (hND hfN)))
  obtain ⟨V, hV, hVne, hdisp⟩ := exists_displaced_clopen hfc hf1'
  exact ⟨V, hV, hVne, fun a ha b hb haV hbV =>
    commutatorElement_mem_of_displaced hN hfN hdisp ha hb haV hbV⟩

/-! ## Nontriviality -/

theorem notMem_of_disjoint_zpow [TopologicalSpace X] {T : X ≃ₜ X} {U : Set X} {j : ℤ}
    (h : Disjoint U (⇑(T ^ j) '' U)) {x : X} (hx : x ∈ U) : (T ^ j) x ∉ U :=
  fun hjx => Set.disjoint_left.mp h hjx ⟨x, hx, rfl⟩

/-- For an infinite minimal system, the three-cycle along `T` on a small clopen set is a nontrivial
element of `alternatingFullGroup T`. -/
theorem exists_threeCycle_ne_one [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X] [Infinite X] (T : X ≃ₜ X)
    (hmin : SimpleKazhdanSofic.IsMinimalSystem T) :
    ∃ U : Set X, IsClopen U ∧ IsThreeCycleDatum T.toEquiv U ∧ threeCycle T.toEquiv U ≠ 1 := by
  have hfree : ∀ j : ℤ, j ≠ 0 → ∀ y : X, (T ^ j) y ≠ y := fun j hj y =>
    SimpleKazhdanSofic.zpow_apply_ne_self T hmin hj y
  obtain ⟨y⟩ : Nonempty X := inferInstance
  obtain ⟨U, hU, hyU, hdis⟩ := SimpleKazhdanSofic.exists_clopen_nbhd_disjoint_translates T hfree 2 y
  have hT1 : ∀ x, (T ^ (1 : ℤ)) x = T.toEquiv x := fun x => by
    show (T ^ (1 : ℤ)) x = T x
    rw [zpow_one]
  have hT2 : ∀ x, (T ^ (2 : ℤ)) x = T.toEquiv (T.toEquiv x) := fun x => by
    show (T ^ (2 : ℤ)) x = T (T x)
    rw [zpow_two, Homeomorph.mul_apply]
  have hdat : IsThreeCycleDatum T.toEquiv U := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [← hT1 x]
      exact notMem_of_disjoint_zpow
        (hdis 1 one_ne_zero (abs_le.mpr ⟨by norm_num, by norm_num⟩)) hx
    · rw [← hT2 x]
      exact notMem_of_disjoint_zpow
        (hdis 2 two_ne_zero (abs_le.mpr ⟨by norm_num, by norm_num⟩)) hx
  refine ⟨U, hU, hdat, fun h1 => ?_⟩
  have h2 : threeCycle T.toEquiv U y = T.toEquiv y := threeCycle_apply_of_mem hdat hyU
  rw [h1, Equiv.Perm.one_apply, ← hT1 y] at h2
  exact hfree 1 one_ne_zero y h2.symm

/-- **The derived full group is nontrivial** for an infinite minimal system. -/
theorem commutator_fullGroup_ne_bot [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X] [Infinite X] (T : X ≃ₜ X)
    (hmin : SimpleKazhdanSofic.IsMinimalSystem T) : ⁅fullGroup T, fullGroup T⁆ ≠ ⊥ := by
  obtain ⟨U, hU, _, hne⟩ := exists_threeCycle_ne_one T hmin
  intro hbot
  have hmem : threeCycle T.toEquiv U ∈ ⁅fullGroup T, fullGroup T⁆ :=
    threeCycle_mem_commutator (toEquiv_mem_fullGroup T) hU
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne hmem

/-- The alternating full group of an infinite minimal system is nontrivial. -/
theorem alternatingFullGroup_ne_bot [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X] [Infinite X] (T : X ≃ₜ X)
    (hmin : SimpleKazhdanSofic.IsMinimalSystem T) : alternatingFullGroup T ≠ ⊥ := by
  obtain ⟨U, hU, hdat, hne⟩ := exists_threeCycle_ne_one T hmin
  intro hbot
  have hmem : threeCycle T.toEquiv U ∈ alternatingFullGroup T :=
    threeCycle_mem_alternatingFullGroup (toEquiv_mem_fullGroup T) hU hdat
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne hmem

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.commutator_closure_le
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.isSimpleGroup_of_le
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.exists_room_of_ne_bot
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.commutator_fullGroup_ne_bot
