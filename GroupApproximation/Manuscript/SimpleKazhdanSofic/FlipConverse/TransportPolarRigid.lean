import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InfraPolar
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.TransportPolarGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Transport of polars, part 2: isomorphisms of topological full groups and rigid polars

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"), lane
`sk-flip-14`, Rubin route.  Write `F_U := rigidStabSet T U = {g ∈ [[T]] | SupportedIn g U}`
(InfraPolar.lean, lane sk-flip-06) and `C(A)` for the centraliser.

Lane 06 is on disk, so its formula `C(F_O) = F_{Oᶜ}` for open `O`
(`coe_centralizer_rigidStabSet_of_isOpen`) is imported and used directly; nothing below is
conditional.  For every group isomorphism `Φ : [[T]] ≃* [[S]]` (`T` minimal):

* `map_rigidStabSet_compl_eq_centralizer` (U open): `Φ '' F_{Uᶜ} = C(Φ '' F_U)`, from
  `F_{Uᶜ} = C(F_U)` and `map_eq_centralizer_of_eq_centralizer` (TransportPolarGroup.lean).
* `map_rigidStabSet_eq_centralizer_compl` (U closed): `Φ '' F_U = C(Φ '' F_{Uᶜ})`, the same with
  the open set `Uᶜ` and `compl_compl`.
* `map_rigidStabSet_eq_centralizer_centralizer` (U clopen): `Φ '' F_U = C(C(Φ '' F_U))`, from
  `F_U = C(C(F_U))` (`centralizer_rigid_eq_double`) and `map_centralizer_centralizer`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

section Transport

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} {S : Y ≃ₜ Y}

/-- `Φ '' F_{Uᶜ} = C(Φ '' F_U)` for an isomorphism `Φ : [[T]] ≃* [[S]]` and open `U`. -/
theorem map_rigidStabSet_compl_eq_centralizer (hT : IsMinimalHomeo T)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) {U : Set X} (hU : IsOpen U) :
    Φ '' rigidStabSet T Uᶜ = Subgroup.centralizer (Φ '' rigidStabSet T U) :=
  map_eq_centralizer_of_eq_centralizer Φ (coe_centralizer_rigidStabSet_of_isOpen hT hU).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.map_rigidStabSet_compl_eq_centralizer

/-- `Φ '' F_U = C(Φ '' F_{Uᶜ})` for an isomorphism `Φ : [[T]] ≃* [[S]]` and closed `U`. -/
theorem map_rigidStabSet_eq_centralizer_compl (hT : IsMinimalHomeo T)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) {U : Set X} (hU : IsClosed U) :
    Φ '' rigidStabSet T U = Subgroup.centralizer (Φ '' rigidStabSet T Uᶜ) := by
  have h := coe_centralizer_rigidStabSet_of_isOpen hT hU.isOpen_compl
  rw [compl_compl] at h
  exact map_eq_centralizer_of_eq_centralizer Φ h.symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.map_rigidStabSet_eq_centralizer_compl

/-- `Φ '' F_U = C(C(Φ '' F_U))` for an isomorphism `Φ : [[T]] ≃* [[S]]` and clopen `U`: images
of rigid stabilisers of clopen sets are polars. -/
theorem map_rigidStabSet_eq_centralizer_centralizer (hT : IsMinimalHomeo T)
    (Φ : topologicalFullGroup T ≃* topologicalFullGroup S) {U : Set X} (hU : IsClopen U) :
    Φ '' rigidStabSet T U =
      Subgroup.centralizer
        (Subgroup.centralizer (Φ '' rigidStabSet T U) : Set (topologicalFullGroup S)) := by
  rw [← map_centralizer_centralizer Φ, centralizer_rigid_eq_double hT hU]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.map_rigidStabSet_eq_centralizer_centralizer

end Transport

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse
