import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiTowerPerm
import GroupApproximation.Meta.AxiomGuard

namespace GroupApproximation
namespace Full
namespace StepanovMatui
namespace Matui

/-!
# Three-cycles on a five-tower inside the room

`simple_kazhdan_sofic_group.tex`, remark at tex l.307–309:

> For derived topological full groups, Matui showed by a similar argument that a nontrivial normal
> subgroup meets a simple union of products of alternating groups on towers
> [Matui, Lemma 3.4 and Theorem 4.9].

Work order WO-A1.  Let `N` contain `⁅a, b⁆` for all `a, b ∈ ⁅[[T]], [[T]]⁆` supported in `V`.  If
`U, f U, …, f⁴ U` are pairwise disjoint and lie in `V`, then the three-cycle `threeCycle f U` lies
in `N` (`threeCycle_mem_of_room`).

The swaps along `f` and `f²` are the tower actions of the transpositions `(0 1)` and `(0 2)` of
`Fin 5` (`swapAlong_eq_towerPerm`), so the three-cycle is the tower action of `⁅(0 1), (0 2)⁆`.  In
`S₅` this three-cycle is the commutator of the commutators `⁅(0 1), (0 3)(1 4)⁆` and
`⁅(0 2), (0 3)(2 4)⁆` (a finite computation), whose tower actions lie in `⁅[[T]], [[T]]⁆` and are
supported in `V`.
-/

open scoped commutatorElement

variable {X : Type*}

/-- The exponents `0, 1, …, n - 1` of the tower `U, f U, …, f^{n-1} U`. -/
def natExps (n : ℕ) (i : Fin n) : ℤ := ((i : ℕ) : ℤ)

theorem natExps_apply (n : ℕ) (i : Fin n) : natExps n i = ((i : ℕ) : ℤ) := rfl

/-- The three-cycle `(0 1 2)` of `S₅` as a commutator of two commutators. -/
theorem swap_commutator_eq_fin_five :
    (⁅Equiv.swap (0 : Fin 5) 1, Equiv.swap 0 2⁆ : Equiv.Perm (Fin 5)) =
      ⁅⁅Equiv.swap 0 1, Equiv.swap 0 3 * Equiv.swap 1 4⁆,
        ⁅Equiv.swap 0 2, Equiv.swap 0 3 * Equiv.swap 2 4⁆⁆ := by
  decide +kernel

/-- **WO-A1**: a three-cycle on a five-tower inside the room `V` lies in `N`. -/
theorem threeCycle_mem_of_room [TopologicalSpace X] [CompactSpace X] [T2Space X] {T : X ≃ₜ X}
    {N : Subgroup (Equiv.Perm X)} {V : Set X}
    (hroom : ∀ a ∈ ⁅fullGroup T, fullGroup T⁆, ∀ b ∈ ⁅fullGroup T, fullGroup T⁆,
      HydeLodha.SupportedIn a V → HydeLodha.SupportedIn b V → ⁅a, b⁆ ∈ N)
    {f : Equiv.Perm X} (hf : f ∈ fullGroup T) {U : Set X} (hU : IsClopen U)
    (hdisj : ∀ i j : Fin 5, i ≠ j → Disjoint (⇑(f ^ (i : ℕ)) '' U) (⇑(f ^ (j : ℕ)) '' U))
    (hV : ∀ i : Fin 5, ⇑(f ^ (i : ℕ)) '' U ⊆ V) : threeCycle f U ∈ N := by
  have hlev : ∀ (i : Fin 5) (x : X), (f ^ (-natExps 5 i)) x ∈ U → x ∈ ⇑(f ^ (i : ℕ)) '' U := by
    intro i x hx
    refine ⟨(f ^ (-natExps 5 i)) x, hx, ?_⟩
    rw [natExps_apply, ← zpow_natCast, perm_zpow_apply_zpow_apply, add_neg_cancel, zpow_zero,
      Equiv.Perm.one_apply]
  have hdisj' : ∀ i j x, (f ^ (-natExps 5 i)) x ∈ U → (f ^ (-natExps 5 j)) x ∈ U → i = j := by
    intro i j x hi hj
    by_contra hij
    exact Set.disjoint_left.mp (hdisj i j hij) (hlev i x hi) (hlev j x hj)
  have e1 : natExps 5 1 = 1 := rfl
  have e2 : natExps 5 2 = 2 := rfl
  have s1 : swapAlong f U = towerPerm f U (natExps 5) hdisj' (Equiv.swap 0 1) :=
    swapAlong_eq_towerPerm hdisj' (i₀ := 0) (j := 1) rfl (by decide) fun y _ => by
      rw [e1, zpow_one]
  have s2 : swapAlong (f * f) U = towerPerm f U (natExps 5) hdisj' (Equiv.swap 0 2) :=
    swapAlong_eq_towerPerm hdisj' (i₀ := 0) (j := 2) rfl (by decide) fun y _ => by
      rw [e2, zpow_two]
  have hφ : ∀ σ τ : Equiv.Perm (Fin 5), towerPerm f U (natExps 5) hdisj' ⁅σ, τ⁆ =
      ⁅towerPerm f U (natExps 5) hdisj' σ, towerPerm f U (natExps 5) hdisj' τ⁆ := fun σ τ => by
    rw [map_commutatorElement]
  have hthree : threeCycle f U = towerPerm f U (natExps 5) hdisj'
      ⁅⁅Equiv.swap (0 : Fin 5) 1, Equiv.swap 0 3 * Equiv.swap 1 4⁆,
        ⁅Equiv.swap 0 2, Equiv.swap 0 3 * Equiv.swap 2 4⁆⁆ := by
    show ⁅swapAlong f U, swapAlong (f * f) U⁆ = _
    rw [s1, s2, ← hφ, swap_commutator_eq_fin_five]
  have hsupp : ∀ σ : Equiv.Perm (Fin 5),
      HydeLodha.SupportedIn (towerPerm f U (natExps 5) hdisj' σ) V := fun σ =>
    towerPerm_supportedIn hdisj' fun i _ x hx => hV i (hlev i x hx)
  rw [hthree, hφ]
  exact hroom _ (towerPerm_commutator_mem hf hU hdisj' _ _) _
    (towerPerm_commutator_mem hf hU hdisj' _ _) (hsupp _) (hsupp _)

end Matui
end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.swap_commutator_eq_fin_five
#audit_axioms GroupApproximation.Full.StepanovMatui.Matui.threeCycle_mem_of_room
