import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Subgroup.Center
import GroupApproximation.Meta.AxiomGuard

/-!
# Central kernels: finite normal generation is finite generation

Lane `bh-met-36`, helper module for route (c) of the base part `K₂(N, ℤ[1/m])`.  These lemmas hold
for any ring.  The endpoint does not use them.

* `normalClosure_eq_closure_of_subset_center`: a set of central elements has the same normal
  closure and closure;
* `k2_fg_of_le_center`: if `St_I(R)` and `E_I(R)` are finitely presented and `K₂(I, R)` is central
  in `St_I(R)`, then `K₂(I, R)` is finitely generated.  The proof takes a finite normal generating
  set from the Tietze converse `SteinbergBasic.K2_isFinitelyNormallyGenerated_of`.

**Caution.**  For `R = ℤ[1/m]`, finite presentation of `E_N(R)` is what lane `bh-met-17` reduces to
finite generation of `K₂`, so feeding it here is circular.  Full centrality of `K₂` in `St_N` is not
in the repository either.  `K₂(ℤ[1/m]) ≠ 0` (the symbol `{-1,-1}`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic

/-- A set of central elements has the same normal closure and closure. -/
theorem normalClosure_eq_closure_of_subset_center {G : Type*} [Group G] {s : Set G}
    (hs : s ⊆ Subgroup.center G) : Subgroup.normalClosure s = Subgroup.closure s := by
  have hc : Subgroup.closure s ≤ Subgroup.center G :=
    (Subgroup.closure_le (K := Subgroup.center G)).mpr hs
  have hnormal : (Subgroup.closure s).Normal := ⟨fun n hmem g ↦ by
    rw [Subgroup.mem_center_iff.mp (hc hmem) g, mul_inv_cancel_right]
    exact hmem⟩
  exact le_antisymm (Subgroup.normalClosure_le_normal Subgroup.subset_closure)
    ((Subgroup.closure_le (K := Subgroup.normalClosure s)).mpr Subgroup.subset_normalClosure)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.normalClosure_eq_closure_of_subset_center

section Kernel

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- If `St_I(R)` and `E_I(R)` are finitely presented and `K₂(I, R)` is central, then `K₂(I, R)` is
finitely generated. -/
theorem k2_fg_of_le_center [Group.IsFinitelyPresented (SteinbergGroup I R)]
    [Group.IsFinitelyPresented (elementaryGroup I R)]
    (hc : K2 I R ≤ Subgroup.center (SteinbergGroup I R)) : Group.FG (K2 I R) := by
  obtain ⟨s, hs, hcl⟩ := K2_isFinitelyNormallyGenerated_of (I := I) (R := R)
  have hsc : s ⊆ Subgroup.center (SteinbergGroup I R) := by
    intro g hg
    have hgK : g ∈ K2 I R := by
      rw [← hcl]
      exact Subgroup.subset_normalClosure hg
    exact hc hgK
  rw [normalClosure_eq_closure_of_subset_center hsc] at hcl
  exact (Group.fg_iff_subgroup_fg _).mpr ((Subgroup.fg_iff _).mpr ⟨s, hcl, hs⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.k2_fg_of_le_center

end Kernel

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
