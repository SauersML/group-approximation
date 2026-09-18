import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarRelSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# `ker fst` as products of relative conjugates

Lane `bh-met-92u`, list module.  From `k2KarRel_ker_eq_normalClosure`:

* `k2KarRel_ker_le_closure`, `k2KarRel_ker_eq_closure`:
  `k2PullRel_ker s M = closure (k2KarRel_gens s M)`;
* `k2KarRel_exists_list`: every `y ∈ ker fst` is `l.prod` for a list `l` of conjugates
  `g x_ij(b) g⁻¹` with `fst b = 0` (inverses are absorbed by `b ↦ -b`, `k2KarRel_gens_inv`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped Pointwise

section KarRelList

variable {A : Type*} [CommRing A] {s : A} {M : ℕ}

theorem k2KarRel_ker_le_closure :
    k2PullRel_ker s M ≤ Subgroup.closure (k2KarRel_gens s M) := by
  rw [k2KarRel_ker_eq_normalClosure]
  show Subgroup.closure (Group.conjugatesOfSet (k2KarRel_relGens s M)) ≤ _
  refine Subgroup.closure_mono ?_
  intro y hy
  obtain ⟨z, ⟨i, j, hij, b, hb, rfl⟩, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  exact ⟨c, i, j, hij, b, hb, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_ker_le_closure

/-- **`ker fst = closure {g x_ij(b) g⁻¹ : fst b = 0}`.** -/
theorem k2KarRel_ker_eq_closure :
    k2PullRel_ker s M = Subgroup.closure (k2KarRel_gens s M) :=
  le_antisymm k2KarRel_ker_le_closure
    ((Subgroup.closure_le _).mpr fun _ hy ↦ k2KarRel_gens_mem_ker hy)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_ker_eq_closure

/-- **Every `y ∈ ker fst` is a finite product of relative conjugates.** -/
theorem k2KarRel_exists_list {y : SteinbergGroup (Fin M) (k2DilateSt_pullback s)}
    (hy : y ∈ k2PullRel_ker s M) :
    ∃ l : List (SteinbergGroup (Fin M) (k2DilateSt_pullback s)),
      (∀ z ∈ l, z ∈ k2KarRel_gens s M) ∧ l.prod = y := by
  have h1 : y ∈ (Subgroup.closure (k2KarRel_gens s M)).toSubmonoid :=
    (Subgroup.mem_toSubmonoid _ y).mpr (k2KarRel_ker_le_closure hy)
  rw [Subgroup.closure_toSubmonoid] at h1
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure h1
  refine ⟨l, fun z hz ↦ ?_, hprod⟩
  rcases hl z hz with h | h
  · exact h
  · have h2 := k2KarRel_gens_inv (Set.mem_inv.mp h)
    rwa [inv_inv] at h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarRel_exists_list

end KarRelList

end GroupApproximation.BooneHigman.Metabelian.ElemFP
