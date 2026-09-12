import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Extension.Linear

/-!
# Consistent schedules of proper subsets

A fixed linear extension of inclusion orders every Boolean interval. Sorting
in reverse order puts a subset before all its proper subsets, and the same
global order makes restriction between intervals consistent.
-/

namespace GroupApproximation.Surjunctivity

universe u

/-- A consistent reverse ordering of proper subsets. -/
structure SubsetSchedule (X : Type u) [DecidableEq X] where
  proper : Finset X → List (Finset X)
  mem_proper : ∀ U V, V ∈ proper U ↔ V ⊂ U
  restrict : ∀ U V, V ⊂ U →
    (proper U).filter (fun W => W ⊆ V) = V :: proper V

variable {X : Type u} [DecidableEq X]

/-- Reverse a single global linear extension of finite-set inclusion. -/
def subsetScheduleRel (U V : Finset X) : Prop :=
  toLinearExtension V ≤ toLinearExtension U

noncomputable instance : DecidableRel (subsetScheduleRel (X := X)) := Classical.decRel _

instance : IsTrans (Finset X) subsetScheduleRel where
  trans _ _ _ hab hbc := le_trans hbc hab

instance : Std.Antisymm (subsetScheduleRel (X := X)) where
  antisymm a b hab hba :=
    show (toLinearExtension a : LinearExtension (Finset X)) = toLinearExtension b from
      le_antisymm hba hab

instance : Std.Total (subsetScheduleRel (X := X)) where
  total a b := le_total (toLinearExtension b) (toLinearExtension a)

omit [DecidableEq X] in
theorem subsetScheduleRel_of_subset {U V : Finset X} (h : V ⊆ U) :
    subsetScheduleRel U V := toLinearExtension.monotone h

/-- Proper subsets sorted with the fixed reverse inclusion extension. -/
noncomputable def properSubsetList (U : Finset X) : List (Finset X) :=
  (U.powerset.erase U).sort subsetScheduleRel

theorem mem_properSubsetList (U V : Finset X) :
    V ∈ properSubsetList U ↔ V ⊂ U := by
  simp only [properSubsetList, Finset.mem_sort, Finset.mem_erase, Finset.mem_powerset]
  exact and_comm.trans Finset.ssubset_iff_subset_ne.symm

theorem properSubsetList_nodup (U : Finset X) : (properSubsetList U).Nodup :=
  Finset.sort_nodup _ _

theorem properSubsetList_pairwise (U : Finset X) :
    (properSubsetList U).Pairwise subsetScheduleRel := Finset.pairwise_sort _ _

theorem properSubsetList_restrict (U V : Finset X) (hVU : V ⊂ U) :
    (properSubsetList U).filter (fun W => W ⊆ V) = V :: properSubsetList V := by
  have hl : ((properSubsetList U).filter (fun W => W ⊆ V)).Nodup :=
    (properSubsetList_nodup U).filter _
  have hr : (V :: properSubsetList V).Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨fun h => (Finset.ssubset_iff_subset_ne.mp
      ((mem_properSubsetList V V).mp h)).2 rfl,
      properSubsetList_nodup V⟩
  have hp : ((properSubsetList U).filter (fun W => W ⊆ V)).Perm
      (V :: properSubsetList V) := by
    apply (List.perm_ext_iff_of_nodup hl hr).mpr
    intro W
    simp only [List.mem_filter, decide_eq_true_eq, mem_properSubsetList, List.mem_cons]
    constructor
    · rintro ⟨hWU, hWV⟩
      by_cases h : W = V
      · exact Or.inl h
      · exact Or.inr (Finset.ssubset_iff_subset_ne.mpr ⟨hWV, h⟩)
    · rintro (rfl | hWV)
      · exact ⟨hVU, Finset.Subset.refl _⟩
      · exact ⟨hWV.trans hVU, hWV.subset⟩
  apply hp.eq_of_pairwise' ((properSubsetList_pairwise U).filter _)
  apply List.pairwise_cons.mpr
  exact ⟨fun W hW => subsetScheduleRel_of_subset ((mem_properSubsetList V W).mp hW).subset,
    properSubsetList_pairwise V⟩

/-- A schedule exists for every site type, with all restriction identities
proved using a single fixed linear extension of inclusion. -/
noncomputable def canonicalSubsetSchedule (X : Type u) [DecidableEq X] : SubsetSchedule X where
  proper := properSubsetList
  mem_proper := mem_properSubsetList
  restrict := properSubsetList_restrict

end GroupApproximation.Surjunctivity
