import NonsoficGroupsExist.KOne.RefineLoopDischarge
import NonsoficGroupsExist.Leavitt.ElementaryStabilization
import NonsoficGroupsExist.Leavitt.LeavittSelfSimilarity

/-!
# `GL_n = EL_n` for the binary Leavitt algebra: dependency-clean core

This file isolates the all-ranks algebraic theorem from the later nonsofic
applications.  Its proof is the existing block-flattening/self-similarity
argument, ultimately resting on the internally proved rank-two elimination.
-/

namespace NonsoficGroupsExist

section Transport

variable {R S : Type*} [Ring R] [Ring S]
variable {iota : Type*} [Fintype iota] [DecidableEq iota]

private theorem map_eq_top_iff {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (hmap : A.map e.toMonoidHom = B) : A = ⊤ ↔ B = ⊤ := by
  constructor
  · intro hA
    rw [← hmap, hA]
    exact Subgroup.map_top_of_surjective _ e.surjective
  · intro hB
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ B := by
      rw [hB]
      exact Subgroup.mem_top _
    rw [← hmap, Subgroup.mem_map_equiv] at hx
    simpa using hx

private theorem coefficientGroup_map (f : R ≃+* S) :
    (elementaryGroup iota R).map
        (Units.mapEquiv (f.mapMatrix (m := iota)).toMulEquiv).toMonoidHom =
      elementaryGroup iota S := by
  have hmap : (Units.mapEquiv
      (f.mapMatrix (m := iota)).toMulEquiv).toMonoidHom =
      elementaryMatrixUnitMap f.toRingHom := by
    ext u
    rfl
  rw [hmap]
  exact elementaryGroup_map_eq_of_surjective f.toRingHom f.surjective

private theorem eq_top_coeff (f : R ≃+* S)
    (h : elementaryGroup iota R = ⊤) : elementaryGroup iota S = ⊤ :=
  (map_eq_top_iff (Units.mapEquiv (f.mapMatrix (m := iota)).toMulEquiv)
    (coefficientGroup_map f)).mp h

variable {kappa : Type*} [Fintype kappa] [DecidableEq kappa]

private theorem eq_top_flatten [Nontrivial iota]
    (h : elementaryGroup iota (Matrix kappa kappa R) = ⊤) :
    elementaryGroup (iota × kappa) R = ⊤ :=
  (map_eq_top_iff elementaryBlockUnitEquiv elementaryBlockGroup_map).mp h

private theorem eq_top_unflatten [Nontrivial iota]
    (h : elementaryGroup (iota × kappa) R = ⊤) :
    elementaryGroup iota (Matrix kappa kappa R) = ⊤ :=
  (map_eq_top_iff elementaryBlockUnitEquiv elementaryBlockGroup_map).mpr h

private theorem eq_top_reindex (e : iota ≃ kappa)
    (h : elementaryGroup iota R = ⊤) : elementaryGroup kappa R = ⊤ :=
  (map_eq_top_iff (elementaryReindexUnitEquiv e)
    (elementaryReindexGroup_map e)).mp h

end Transport

namespace BinaryLeavitt

open LeavittFamily

variable (k : Type) [Field k]

/-- `GL_n(L_k(1,2)) = EL_n(L_k(1,2))` for every `n ≥ 2`.
This dependency-clean form is the one used by the `(TT)/T` development. -/
theorem elementaryGroup_eq_top (n : ℕ) (hn : 2 ≤ n) :
    elementaryGroup (Fin n) (BinaryLeavittAlgebra k) = ⊤ := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  haveI : Nontrivial (Fin (n' + 1)) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h
      simpa using congrArg Fin.val h⟩⟩
  have htwo : elementaryGroup (Fin 2) (BinaryLeavittAlgebra k) = ⊤ := by
    ext M
    simp only [Subgroup.mem_top, iff_true]
    exact glTwo_eq_elementary_holds k M
  have h2M : elementaryGroup (Fin 2)
      (Matrix (Fin (n' + 1)) (Fin (n' + 1)) (BinaryLeavittAlgebra k)) = ⊤ :=
    eq_top_coeff
      ((family k).prefixRingEquiv (leftCombCode n')
        ((family k).leftCombCode_complete n')).symm
      htwo
  have hprod : elementaryGroup (Fin 2 × Fin (n' + 1))
      (BinaryLeavittAlgebra k) = ⊤ := eq_top_flatten h2M
  have hprod' : elementaryGroup (Fin (n' + 1) × Fin 2)
      (BinaryLeavittAlgebra k) = ⊤ :=
    eq_top_reindex (Equiv.prodComm (Fin 2) (Fin (n' + 1))) hprod
  have hnM : elementaryGroup (Fin (n' + 1))
      (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k)) = ⊤ :=
    eq_top_unflatten hprod'
  exact eq_top_coeff
    ((family k).prefixRingEquiv (leftCombCode 1)
      ((family k).leftCombCode_complete 1)) hnM

end BinaryLeavitt

end NonsoficGroupsExist
