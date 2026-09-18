import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFree.Configuration
import GroupApproximation.Sofic.HullSuitableDefectSubgroup

/-!
# `N = ⟨⟨S'⟩⟩` is infinite and s-normal

`non_mf_group_notes.tex`, Theorem `thm:torsionfree` (l.2786-2789): *"Put
`N = ⟨⟨S'⟩⟩_{G_0}`. This subgroup is infinite and normal, so s-normal."*

The printed proof takes infiniteness from `S'` being infinite. Here it comes
from torsion-freeness of `G_0`: the protected element `a ∈ S'` is not the
identity, so it has infinite order, and its powers all lie in `N`. This is the
algebraic half of the suitability input for Hull's Theorem 7.1. The geometric
half, that `N` acts non-elementarily, is Osin's Lemma 7.1.
-/

namespace GroupApproximation.Full.NN07b

namespace NotesConfiguration

variable (C : NotesConfiguration)

/-- The protected element of `S'` has infinite order, since `G_0` is
torsion-free (`thm:torsionfree`). -/
theorem a_not_isOfFinOrder : ¬ IsOfFinOrder C.a := by
  intro h
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  exact C.a_ne_one (C.torsionFree C.a n hn hpow)

/-- The protected element lies in `N = ⟨⟨S'⟩⟩`. -/
theorem a_mem_normalClosure : C.a ∈ Subgroup.normalClosure (C.S : Set C.G₀) :=
  Subgroup.subset_normalClosure C.a_mem

/-- `thm:torsionfree` (l.2786-2787): `N = ⟨⟨S'⟩⟩` is infinite. -/
theorem normalClosure_infinite :
    ((Subgroup.normalClosure (C.S : Set C.G₀) : Subgroup C.G₀) : Set C.G₀).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℤ => C.a ^ n)
    (injective_zpow_iff_not_isOfFinOrder.mpr C.a_not_isOfFinOrder)
    (fun n => Subgroup.zpow_mem _ C.a_mem_normalClosure n)

/-- `thm:torsionfree` (l.2787): `N = ⟨⟨S'⟩⟩` is s-normal in the sense of Osin. -/
theorem isSNormal_normalClosure :
    HullSuitable.IsSNormal (Subgroup.normalClosure (C.S : Set C.G₀)) :=
  HullSuitable.isSNormal_of_normal_of_mem_not_isOfFinOrder _
    C.a_mem_normalClosure C.a_not_isOfFinOrder

end NotesConfiguration

end GroupApproximation.Full.NN07b
