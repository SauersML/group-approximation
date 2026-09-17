import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidCentralizer
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.TransportPolarGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Transport of polars, part 2: isomorphisms of topological full groups and rigid polars

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"), lane
`sk-flip-14`.  Write `F_U := {g ∈ [[T]] | SupportedIn g U}` and `C(A)` for the centraliser in
`[[T]]`.

* `centralizer_rigid_open_eq_compl` (Cantor minimal, `U` open): `C(F_U) = F_{Uᶜ}`.
  `⊆` is `supportedIn_compl_of_forall_commute` (RigidCentralizer.lean); `⊇` is
  `SupportedIn.commute_of_compl`.  This is the lane-06 interface; it is recorded as
  `RigidCentralizerStatement` (clopen `U`) and proved here (`rigidCentralizerStatement_true`),
  so nothing below is conditional.
* `map_rigid_compl_eq_centralizer_map_rigid` (U open): for every `Φ : [[T]] ≃* [[S]]`,
  `Φ '' F_{Uᶜ} = C(Φ '' F_U)`, from `C(F_U) = F_{Uᶜ}` and `map_centralizer_eq`.
* `map_rigid_eq_centralizer_map_rigid_compl` (U closed): `Φ '' F_U = C(Φ '' F_{Uᶜ})`.
* `map_rigid_eq_centralizer_centralizer` (U clopen): `Φ '' F_U = C(C(Φ '' F_U))`, since
  `C(C(F_U)) = C(F_{Uᶜ}) = F_U` and `map_centralizer_centralizer`.
* `map_rigid_compl_eq_centralizer_of_rigidCentralizer`: the `_of_` form through the Statement.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- Lane-06 interface: in `[[T]]` for a Cantor minimal `T`, the centraliser of the rigid
stabiliser of a clopen `U` is the rigid stabiliser of `Uᶜ`. -/
def RigidCentralizerStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] (T : X ≃ₜ X), IsMinimalHomeo T → ∀ U : Set X, IsClopen U →
      (Subgroup.centralizer {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) U} :
        Set (topologicalFullGroup T)) = {g | SupportedIn (g : X ≃ₜ X) Uᶜ}

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidCentralizerStatement

/-- `C(F_U) = F_{Uᶜ}` in `[[T]]` for an open set `U`. -/
theorem centralizer_rigid_open_eq_compl {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {U : Set X} (hU : IsOpen U) :
    (Subgroup.centralizer {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) U} :
      Set (topologicalFullGroup T)) = {g | SupportedIn (g : X ≃ₜ X) Uᶜ} := by
  ext h
  constructor
  · intro hh
    have hh' : ∀ k ∈ {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) U}, k * h = h * k :=
      Subgroup.mem_centralizer_iff.1 (SetLike.mem_coe.1 hh)
    show SupportedIn (h : X ≃ₜ X) Uᶜ
    refine supportedIn_compl_of_forall_commute hT hU fun σ hσ hσU => ?_
    have hσU' : (⟨σ, hσ⟩ : topologicalFullGroup T) ∈
        {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) U} := hσU
    exact (congrArg Subtype.val (hh' ⟨σ, hσ⟩ hσU')).symm
  · intro hh
    have hh' : SupportedIn (h : X ≃ₜ X) Uᶜ := hh
    refine SetLike.mem_coe.2 (Subgroup.mem_centralizer_iff.2 fun k hk => ?_)
    have hk' : SupportedIn (k : X ≃ₜ X) U := hk
    exact Subtype.ext (SupportedIn.commute_of_compl hk' hh')

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.centralizer_rigid_open_eq_compl

/-- The lane-06 interface holds. -/
theorem rigidCentralizerStatement_true : RigidCentralizerStatement :=
  fun _ _ _ _ _ _ _ _ hT _ hU => centralizer_rigid_open_eq_compl hT hU.isOpen

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidCentralizerStatement_true

section Transport

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} {S : Y ≃ₜ Y}

/-- `Φ '' F_{Uᶜ} = C(Φ '' F_U)` for an isomorphism `Φ : [[T]] ≃* [[S]]` and open `U`. -/
theorem map_rigid_compl_eq_centralizer_map_rigid (hT : IsMinimalHomeo T)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) {U : Set X} (hU : IsOpen U) :
    Φ '' {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) Uᶜ} =
      Subgroup.centralizer (Φ '' {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) U}) :=
  map_eq_centralizer_of_eq_centralizer Φ (centralizer_rigid_open_eq_compl hT hU).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.map_rigid_compl_eq_centralizer_map_rigid

/-- `Φ '' F_U = C(Φ '' F_{Uᶜ})` for an isomorphism `Φ : [[T]] ≃* [[S]]` and closed `U`. -/
theorem map_rigid_eq_centralizer_map_rigid_compl (hT : IsMinimalHomeo T)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) {U : Set X} (hU : IsClosed U) :
    Φ '' {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) U} =
      Subgroup.centralizer (Φ '' {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) Uᶜ}) := by
  have h := centralizer_rigid_open_eq_compl hT hU.isOpen_compl
  rw [compl_compl] at h
  exact map_eq_centralizer_of_eq_centralizer Φ h.symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.map_rigid_eq_centralizer_map_rigid_compl

/-- `Φ '' F_U = C(C(Φ '' F_U))` for an isomorphism `Φ : [[T]] ≃* [[S]]` and clopen `U`:
images of rigid stabilisers of clopen sets are polars. -/
theorem map_rigid_eq_centralizer_centralizer (hT : IsMinimalHomeo T)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) {U : Set X} (hU : IsClopen U) :
    Φ '' {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) U} =
      Subgroup.centralizer (Subgroup.centralizer
        (Φ '' {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) U}) :
          Set (topologicalFullGroup S)) := by
  have h1 := centralizer_rigid_open_eq_compl hT hU.isOpen
  have h2 := centralizer_rigid_open_eq_compl hT hU.isClosed.isOpen_compl
  rw [compl_compl] at h2
  rw [← map_centralizer_centralizer Φ, h1, h2]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.map_rigid_eq_centralizer_centralizer

end Transport

/-- The specialisation `Φ '' F_{Uᶜ} = C(Φ '' F_U)` (clopen `U`), derived from the lane-06
interface `RigidCentralizerStatement` only. -/
theorem map_rigid_compl_eq_centralizer_of_rigidCentralizer (hC : RigidCentralizerStatement)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (Φ : topologicalFullGroup T ≃* topologicalFullGroup S)
    {U : Set X} (hU : IsClopen U) :
    Φ '' {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) Uᶜ} =
      Subgroup.centralizer (Φ '' {g : topologicalFullGroup T | SupportedIn (g : X ≃ₜ X) U}) :=
  map_eq_centralizer_of_eq_centralizer Φ (hC X T hT U hU).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.map_rigid_compl_eq_centralizer_of_rigidCentralizer

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
