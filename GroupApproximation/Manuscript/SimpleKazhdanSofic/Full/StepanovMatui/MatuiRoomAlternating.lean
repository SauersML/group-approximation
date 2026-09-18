import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiLocal
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiLocalStep
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiMoveTower
import GroupApproximation.Meta.AxiomGuard

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

/-!
# Room gives the alternating full group

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

Work order WO-A2.  Let `T` be an infinite minimal homeomorphism of a compact totally separated
space and `N` a subgroup normalized by `D = ⁅[[T]], [[T]]⁆` that contains `⁅a, b⁆` for all
`a, b ∈ D` supported in a nonempty clopen set `V`.  Then `N` contains `alternatingFullGroup T`
(`alternatingFullGroup_le_of_room`).

Every three-cycle `threeCycle f U` is a finite product of three-cycles on small clopen pieces
(`threeCycle_mem_of_local`).  Each small piece is the base of an eight-level tower along `T` with
levels `3, …, 7` in `V` (`exists_local_eight_tower`), and on such a tower the three-cycle is
conjugate by an element of `D` to a commutator of elements of `D` supported in `V`
(`threeCycle_mem_of_eight_tower`).
-/

open scoped commutatorElement

variable {X : Type*}

/-- **Room gives the alternating full group** (Matui, Lemma 3.4). -/
theorem alternatingFullGroup_le_of_room [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallySeparatedSpace X] [Infinite X] (T : X ≃ₜ X)
    (hmin : SimpleKazhdanSofic.IsMinimalSystem T) {N : Subgroup (Equiv.Perm X)}
    (hN : ∀ n ∈ N, ∀ g ∈ ⁅fullGroup T, fullGroup T⁆, g * n * g⁻¹ ∈ N) {V : Set X}
    (hV : IsClopen V) (hVne : V.Nonempty)
    (hroom : ∀ a ∈ ⁅fullGroup T, fullGroup T⁆, ∀ b ∈ ⁅fullGroup T, fullGroup T⁆,
      HydeLodha.SupportedIn a V → HydeLodha.SupportedIn b V → ⁅a, b⁆ ∈ N) :
    alternatingFullGroup T ≤ N := by
  refine Subgroup.closure_le.mpr ?_
  rintro σ ⟨f, hf, U, hU, hdat, rfl⟩
  refine threeCycle_mem_of_local hU hdat fun x hxU => ?_
  have hx1 : f x ≠ x := fun h => hdat.1 x hxU (by rw [h]; exact hxU)
  have hx2 : f (f x) ≠ x := fun h => hdat.2 x hxU (by rw [h]; exact hxU)
  obtain ⟨W, hWc, hxW, E, hE0, hdisj, h1, h2, hV8⟩ :=
    exists_local_eight_tower T hmin hV hVne hf hx1 hx2
  refine ⟨W, hWc, hxW, fun A hA _ hAW => ?_⟩
  exact threeCycle_mem_of_eight_tower hN hroom (toEquiv_mem_fullGroup T) hA (hdisj A hAW) hE0
    (fun y hy => h1 y (hAW hy)) (fun y hy => h2 y (hAW hy))
    (fun i hi y hy => hV8 i hi y (hAW hy))

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.alternatingFullGroup_le_of_room
