import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiAssembly
import GroupApproximation.Meta.AxiomGuard

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

/-!
# Returns of a minimal orbit

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

Part of work order WO-A2.  For an infinite minimal system on a compact Hausdorff space, the orbit
of every point visits every nonempty open set `V` at times outside any given finite set of
exponents (`exists_zpow_mem_notMem`).  Otherwise `V` is a finite set, so some point of `V` is
isolated; minimality then makes every point isolated, and the compact discrete space is finite.
-/

variable {X : Type*}

/-- **Returns avoiding finitely many exponents.** -/
theorem exists_zpow_mem_notMem [TopologicalSpace X] [CompactSpace X] [T2Space X] [Infinite X]
    (T : X ≃ₜ X) (hmin : SimpleKazhdanSofic.IsMinimalSystem T) {V : Set X} (hV : IsOpen V)
    (hVne : V.Nonempty) (x : X) (F : Finset ℤ) : ∃ m : ℤ, m ∉ F ∧ (T ^ m) x ∈ V := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Set X, P = (fun m : ℤ => (T ^ m) x) '' (F : Set ℤ) := ⟨_, rfl⟩
  have hPf : P.Finite := by
    rw [hPdef]
    exact F.finite_toSet.image _
  by_cases hne : (V \ P).Nonempty
  · obtain ⟨y, hy, hyV⟩ := (hmin x).exists_mem_open (hV.sdiff hPf.isClosed) hne
    obtain ⟨m, rfl⟩ := hy
    refine ⟨m, fun hm => hyV.2 ?_, hyV.1⟩
    rw [hPdef]
    exact Set.mem_image_of_mem _ (Finset.mem_coe.mpr hm)
  · exfalso
    have hVP : V ⊆ P := fun y hy => by
      by_contra hyP
      exact hne ⟨y, hy, hyP⟩
    obtain ⟨v, hv⟩ := hVne
    have hPvf : (P \ {v}).Finite := hPf.sdiff
    have hsing : ({v} : Set X) = V \ (P \ {v}) := by
      ext y
      constructor
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact ⟨hv, fun h => h.2 (Set.mem_singleton v)⟩
      · intro hy
        by_contra hyv
        exact hy.2 ⟨hVP hy.1, hyv⟩
    have hvo : IsOpen ({v} : Set X) := by
      rw [hsing]
      exact hV.sdiff hPvf.isClosed
    have hopen : ∀ y : X, IsOpen ({y} : Set X) := by
      intro y
      obtain ⟨z, hz, hzv⟩ := (hmin y).exists_mem_open hvo (Set.singleton_nonempty v)
      obtain ⟨k, rfl⟩ := hz
      have hkv : (T ^ k) y = v := hzv
      have e : ({y} : Set X) = ⇑(T ^ k) ⁻¹' {v} := by
        ext w
        rw [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hw
          rw [hw, hkv]
        · intro hw
          exact (T ^ k).injective (hw.trans hkv.symm)
      rw [e]
      exact hvo.preimage (T ^ k).continuous
    haveI : DiscreteTopology X := discreteTopology_iff_isOpen_singleton.mpr hopen
    haveI : Finite X := finite_of_compact_of_discrete
    exact not_finite X

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.exists_zpow_mem_notMem
