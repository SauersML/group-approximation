import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplitSupport
import GroupApproximation.Meta.AxiomGuard

/-!
# Infrastructure: centralizers of rigid stabilizers in `[[T]]` (lane sk-flip-06)

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"); Rubin route.

For a minimal homeomorphism `T` of a compact Hausdorff totally disconnected perfect space and
`O ⊆ X`, write `F_O = rigidStabSet T O = {g ∈ [[T]] | SupportedIn g O}`.

* `coe_centralizer_rigidStabSet_of_isOpen`: for open `O`, `C(F_O) = F_{Oᶜ}` as sets.
  `⊆` is `supportedIn_compl_of_forall_commute` (RigidCentralizer.lean), `⊇` is
  `SupportedIn.commute_of_compl` (which holds for every set `O`).
* `centralizer_rigid_eq`: the clopen case `C(F_U) = F_{Uᶜ}`.
* `centralizer_rigid_eq_double`: for clopen `U`, `C(C(F_U)) = F_U`, applying the formula to `U`
  and to the open set `Uᶜ`, then `compl_compl`.
* `center_rigid_trivial`: for open `O`, an element of `F_O` commuting with all of `F_O` lies in
  `F_O ∩ F_{Oᶜ}`, hence is the identity.
* `rigidStabSet_interior_eq`: in a Hausdorff space the moved set `{x | g x ≠ x}` of a
  homeomorphism is open (`isOpen_ne_fun`), so `F_{interior S} = F_S` for every `S`.
* `centralizer_rigid_open_eq`: for open `O`, `C(F_O) = F_{interior Oᶜ}`.

The hypotheses are only those used (no `Nonempty`/metrizability), so the statements are at least
as strong as their Cantor-minimal specialisations.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

variable {X : Type*} [TopologicalSpace X]

/-- The rigid stabilizer `F_U = {g ∈ [[T]] | SupportedIn g U}`, as a set of elements of `[[T]]`. -/
def rigidStabSet (T : X ≃ₜ X) (U : Set X) : Set (topologicalFullGroup T) :=
  {g | SupportedIn (g : X ≃ₜ X) U}

theorem mem_rigidStabSet {T : X ≃ₜ X} {U : Set X} {g : topologicalFullGroup T} :
    g ∈ rigidStabSet T U ↔ SupportedIn (g : X ≃ₜ X) U :=
  Iff.rfl

/-- In a Hausdorff space the moved set of a homeomorphism is open. -/
theorem isOpen_movedSet_of_t2Space [T2Space X] (g : X ≃ₜ X) : IsOpen (movedSet g) :=
  isOpen_ne_fun g.continuous continuous_id

/-- Rigid stabilizers do not see the difference between a set and its interior. -/
theorem rigidStabSet_interior_eq [T2Space X] {T : X ≃ₜ X} {S : Set X} :
    rigidStabSet T (interior S) = rigidStabSet T S := by
  ext g
  constructor
  · intro hg
    exact mem_rigidStabSet.2 ((mem_rigidStabSet.1 hg).mono interior_subset)
  · intro hg
    refine mem_rigidStabSet.2 (supportedIn_iff_movedSet_subset.2 ?_)
    exact interior_maximal (supportedIn_iff_movedSet_subset.1 (mem_rigidStabSet.1 hg))
      (isOpen_movedSet_of_t2Space (g : X ≃ₜ X))

/-- For open `O`, the centralizer of `F_O` in `[[T]]` is `F_{Oᶜ}`. -/
theorem coe_centralizer_rigidStabSet_of_isOpen [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T)
    {O : Set X} (hO : IsOpen O) :
    (Subgroup.centralizer (rigidStabSet T O) : Set (topologicalFullGroup T)) =
      rigidStabSet T Oᶜ := by
  ext g
  constructor
  · intro hg
    have hg' : g ∈ Subgroup.centralizer (rigidStabSet T O) := SetLike.mem_coe.1 hg
    refine mem_rigidStabSet.2 (supportedIn_compl_of_forall_commute hT hO fun σ hσ hσO => ?_)
    have hmem : (⟨σ, hσ⟩ : topologicalFullGroup T) ∈ rigidStabSet T O := hσO
    have h1 : (⟨σ, hσ⟩ : topologicalFullGroup T) * g = g * ⟨σ, hσ⟩ :=
      Subgroup.mem_centralizer_iff.1 hg' ⟨σ, hσ⟩ hmem
    exact (congrArg Subtype.val h1).symm
  · intro hg
    refine SetLike.mem_coe.2 (Subgroup.mem_centralizer_iff.2 fun k hk => ?_)
    have hkg : (k : X ≃ₜ X) * (g : X ≃ₜ X) = (g : X ≃ₜ X) * (k : X ≃ₜ X) :=
      SupportedIn.commute_of_compl (mem_rigidStabSet.1 hk) (mem_rigidStabSet.1 hg)
    exact Subtype.ext hkg

/-- Lane endpoint: for clopen `U`, `C(F_U) = F_{Uᶜ}` in `[[T]]`. -/
theorem centralizer_rigid_eq [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {U : Set X} (hU : IsClopen U) :
    (Subgroup.centralizer (rigidStabSet T U) : Set (topologicalFullGroup T)) =
      rigidStabSet T Uᶜ :=
  coe_centralizer_rigidStabSet_of_isOpen hT hU.isOpen

/-- Lane endpoint: for clopen `U`, `C(C(F_U)) = F_U` in `[[T]]`. -/
theorem centralizer_rigid_eq_double [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {U : Set X} (hU : IsClopen U) :
    (Subgroup.centralizer
        (Subgroup.centralizer (rigidStabSet T U) : Set (topologicalFullGroup T)) :
        Set (topologicalFullGroup T)) = rigidStabSet T U := by
  rw [centralizer_rigid_eq hT hU,
    coe_centralizer_rigidStabSet_of_isOpen hT hU.isClosed.isOpen_compl, compl_compl]

/-- Lane endpoint: for open `O`, the only element of `F_O` central in `F_O` is the identity. -/
theorem center_rigid_trivial [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {O : Set X} (hO : IsOpen O)
    {g : topologicalFullGroup T} (hg : g ∈ rigidStabSet T O)
    (hc : ∀ k ∈ rigidStabSet T O, g * k = k * g) : g = 1 := by
  have hgc : g ∈ rigidStabSet T Oᶜ := by
    rw [← coe_centralizer_rigidStabSet_of_isOpen hT hO]
    exact SetLike.mem_coe.2 (Subgroup.mem_centralizer_iff.2 fun k hk => (hc k hk).symm)
  refine Subtype.ext (Homeomorph.ext fun x => ?_)
  show (g : X ≃ₜ X) x = x
  by_cases hx : x ∈ O
  · exact (mem_rigidStabSet.1 hgc) x (Set.notMem_compl_iff.2 hx)
  · exact (mem_rigidStabSet.1 hg) x hx

/-- Lane endpoint: for open `O`, `C(F_O) = F_{interior Oᶜ}` in `[[T]]`. -/
theorem centralizer_rigid_open_eq [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] {T : X ≃ₜ X} (hT : IsMinimalHomeo T) {O : Set X} (hO : IsOpen O) :
    (Subgroup.centralizer (rigidStabSet T O) : Set (topologicalFullGroup T)) =
      rigidStabSet T (interior Oᶜ) := by
  rw [coe_centralizer_rigidStabSet_of_isOpen hT hO, rigidStabSet_interior_eq]

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidStabSet
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.mem_rigidStabSet
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.isOpen_movedSet_of_t2Space
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidStabSet_interior_eq
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.coe_centralizer_rigidStabSet_of_isOpen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.centralizer_rigid_eq
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.centralizer_rigid_eq_double
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.center_rigid_trivial
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.centralizer_rigid_open_eq
