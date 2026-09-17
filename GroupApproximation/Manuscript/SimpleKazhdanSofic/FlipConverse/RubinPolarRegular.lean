import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinPolarRigid
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin polars, part 3: rigid stabilisers of regular open sets are rigid polars (the `⇐` half)

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"), lane
`sk-flip-16`.  `T` is a minimal homeomorphism of a compact Hausdorff totally disconnected perfect
space (no `Nonempty`/metrizability needed).

* `isRigidPolar_rubinRigidSubgroup_of_regular`: if `O` is regular open
  (`interior (closure O) = O`), then `F_O` is a rigid polar.  Writing `C` for the centraliser,
  `C F_O = F_{Oᶜ} = F_{(closure O)ᶜ}` (interior-invariance), so `C (C F_O) = F_{closure O} =
  F_{interior (closure O)} = F_O`; `F_O ⊓ F_{Oᶜ} = ⊥`; and both conjugation clauses are
  `rubinRigid_dichotomy` for the open sets `O`, `(closure O)ᶜ` and their translates.
* `rigidPolar_of_clopen` (lane endpoint, `⇐`): if `(P : Set _) = F_U` with `U` clopen then
  `IsRigidPolar P` (clopen sets are regular open).

WARNING: the lane's `⇒` half is FALSE; regular open sets that are not closed give rigid polars
which are not `F_U` for any clopen `U` (see RubinPolarFalse.lean).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

section RubinRegular

variable {X : Type*} [TopologicalSpace X]

/-- `F_{Oᶜ} = F_{(closure O)ᶜ}` (T₂). -/
theorem rubinRigidSubgroup_compl_eq_compl_closure [T2Space X] (T : X ≃ₜ X) (O : Set X) :
    rubinRigidSubgroup T Oᶜ = rubinRigidSubgroup T (closure O)ᶜ := by
  rw [← rubinRigidSubgroup_interior (T := T) (S := Oᶜ), interior_compl]

/-- For regular open `O`, `F_{closure O} = F_O` (T₂). -/
theorem rubinRigidSubgroup_closure_of_regular [T2Space X] {T : X ≃ₜ X} {O : Set X}
    (hreg : interior (closure O) = O) :
    rubinRigidSubgroup T (closure O) = rubinRigidSubgroup T O := by
  rw [← rubinRigidSubgroup_interior (T := T) (S := closure O), hreg]

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X]

/-- For regular open `O`, `C(C(F_O)) = F_O`. -/
theorem centralizer_centralizer_rubinRigidSubgroup {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {O : Set X} (hO : IsOpen O) (hreg : interior (closure O) = O) :
    Subgroup.centralizer
        (Subgroup.centralizer (rubinRigidSubgroup T O : Set (topologicalFullGroup T)) :
          Set (topologicalFullGroup T)) =
      rubinRigidSubgroup T O := by
  rw [centralizer_rubinRigidSubgroup hT hO, rubinRigidSubgroup_compl_eq_compl_closure T O,
    centralizer_rubinRigidSubgroup hT (isClosed_closure (s := O)).isOpen_compl, compl_compl,
    rubinRigidSubgroup_closure_of_regular hreg]

/-- The rigid stabiliser of a regular open set is a rigid polar. -/
theorem isRigidPolar_rubinRigidSubgroup_of_regular {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {O : Set X} (hO : IsOpen O) (hreg : interior (closure O) = O) :
    IsRigidPolar (rubinRigidSubgroup T O) := by
  have hC : Subgroup.centralizer (rubinRigidSubgroup T O : Set (topologicalFullGroup T)) =
      rubinRigidSubgroup T (closure O)ᶜ := by
    rw [centralizer_rubinRigidSubgroup hT hO, rubinRigidSubgroup_compl_eq_compl_closure T O]
  have hcl : IsOpen (closure O)ᶜ := (isClosed_closure (s := O)).isOpen_compl
  refine ⟨(centralizer_centralizer_rubinRigidSubgroup hT hO hreg).symm, ?_, fun g => ?_,
    fun g => ?_⟩
  · rw [centralizer_rubinRigidSubgroup hT hO]
    exact rubinRigidSubgroup_inf_compl_eq_bot T O
  · rw [centralizer_rubinRigidSubgroup hT hO, rubinConjSubgroup_rubinRigidSubgroup]
    exact rubinRigid_dichotomy hT hO (hO.preimage ((g : X ≃ₜ X)⁻¹).continuous)
  · rw [hC, rubinConjSubgroup_rubinRigidSubgroup]
    have h := rubinRigid_dichotomy hT hcl (hcl.preimage ((g : X ≃ₜ X)⁻¹).continuous)
    rw [compl_compl, rubinRigidSubgroup_closure_of_regular hreg] at h
    exact h

/-- Clopen sets are regular open, so their rigid stabilisers are rigid polars. -/
theorem isRigidPolar_rubinRigidSubgroup_of_isClopen {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {U : Set X} (hU : IsClopen U) :
    IsRigidPolar (rubinRigidSubgroup T U) := by
  have hreg : interior (closure U) = U := by
    rw [hU.isClosed.closure_eq, hU.isOpen.interior_eq]
  exact isRigidPolar_rubinRigidSubgroup_of_regular hT hU.isOpen hreg

/-- Lane `sk-flip-16`, `⇐`: a subgroup of `[[T]]` equal to `F_U` for a clopen `U` is a rigid
polar. -/
theorem rigidPolar_of_clopen {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {P : Subgroup (topologicalFullGroup T)}
    (h : ∃ U : Set X, IsClopen U ∧ (P : Set (topologicalFullGroup T)) = rigidStabSet T U) :
    IsRigidPolar P := by
  obtain ⟨U, hU, hPU⟩ := h
  have hP : P = rubinRigidSubgroup T U := SetLike.coe_injective hPU
  rw [hP]
  exact isRigidPolar_rubinRigidSubgroup_of_isClopen hT hU

end RubinRegular

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinRigidSubgroup_compl_eq_compl_closure
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rubinRigidSubgroup_closure_of_regular
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.centralizer_centralizer_rubinRigidSubgroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.isRigidPolar_rubinRigidSubgroup_of_regular
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.isRigidPolar_rubinRigidSubgroup_of_isClopen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidPolar_of_clopen
