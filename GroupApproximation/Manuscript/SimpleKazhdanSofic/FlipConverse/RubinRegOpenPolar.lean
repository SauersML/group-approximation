import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplitSupport
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin dictionary, part 1: regular-open polars of rigid stabilisers

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"); lane
`sk-flip-13` of the flip-converse region (Rubin route, infrastructure).

Let `T` be a minimal homeomorphism of a Cantor space `X` and, for `O ⊆ X`, let
`F_O = {g ∈ [[T]] | SupportedIn g O}` be the rigid stabiliser of `O`, and `C(A)` the centraliser
in `[[T]]`.

* `regOpen_centralizer_rigid_open` (open-set centraliser formula): for `O` open,
  `C(F_O) = F_{interior Oᶜ}`.
  `⊆`: an `h` commuting with `F_O` fixes `O` pointwise (`supportedIn_compl_of_forall_commute`), so
  `movedSet h ⊆ Oᶜ`; as `T` is aperiodic, `movedSet h` is clopen (`isClopen_movedSet`), hence open,
  hence contained in `interior Oᶜ`.
  `⊇`: `interior Oᶜ ⊆ Oᶜ` and `SupportedIn.commute_of_compl`.
* `regOpen_centralizer_centralizer_rigid_open`: for `O` open,
  `C(C(F_O)) = F_{interior (closure O)}`.
  Apply the formula twice (`interior Oᶜ` is open) and use `(interior Oᶜ)ᶜ = closure O`
  (`closure_compl`, `compl_compl`).

The open formula is also the interface of lane `sk-flip-06`, which is not yet on disk; it is
recorded as `RigidCentralizerOpenStatement` with the reduction
`regOpen_centralizer_centralizer_rigid_open_of_rigidCentralizerOpen`, and the statement is proved
here outright (`rigidCentralizerOpenStatement_holds`), so no endpoint of this file is conditional.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

section RegOpenPolar

variable {X : Type*} [TopologicalSpace X]

/-- Open-set centraliser formula: `C(F_O) = F_{interior Oᶜ}` in `[[T]]` for `O` open. -/
theorem regOpen_centralizer_rigid_open [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {O : Set X} (hO : IsOpen O) :
    (Subgroup.centralizer {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O} :
        Set (topologicalFullGroup T)) =
      {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) (interior Oᶜ)} := by
  haveI : Infinite X := infinite_of_perfectSpace
  have hTa : IsAperiodic T := isAperiodic_of_isMinimalHomeo hT
  ext h
  constructor
  · intro hc
    have hc' : ∀ g ∈ {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O},
        g * h = h * g :=
      Subgroup.mem_centralizer_iff.1 hc
    have h1 : SupportedIn (h : X ≃ₜ X) Oᶜ := by
      refine supportedIn_compl_of_forall_commute hT hO fun σ hσ hσO => ?_
      have hmem : (⟨σ, hσ⟩ : topologicalFullGroup T) ∈
          {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O} := hσO
      have h2 : (⟨σ, hσ⟩ : topologicalFullGroup T) * h = h * ⟨σ, hσ⟩ := hc' _ hmem
      exact (congrArg Subtype.val h2).symm
    have hcl : IsClopen (movedSet (h : X ≃ₜ X)) := isClopen_movedSet hTa h.2
    have h3 : SupportedIn (h : X ≃ₜ X) (interior Oᶜ) :=
      supportedIn_iff_movedSet_subset.2
        (interior_maximal (supportedIn_iff_movedSet_subset.1 h1) hcl.isOpen)
    exact h3
  · intro hs
    have hs' : SupportedIn (h : X ≃ₜ X) (interior Oᶜ) := hs
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    have hg' : SupportedIn (g : X ≃ₜ X) O := hg
    exact Subtype.ext (SupportedIn.commute_of_compl hg' (hs'.mono interior_subset))

/-- Regular-open polars: `C(C(F_O)) = F_{interior (closure O)}` in `[[T]]` for `O` open. -/
theorem regOpen_centralizer_centralizer_rigid_open [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {O : Set X} (hO : IsOpen O) :
    (Subgroup.centralizer
        (Subgroup.centralizer {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O} :
          Set (topologicalFullGroup T)) : Set (topologicalFullGroup T)) =
      {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) (interior (closure O))} := by
  rw [regOpen_centralizer_rigid_open hT hO,
    regOpen_centralizer_rigid_open hT (O := interior Oᶜ) isOpen_interior, ← closure_compl,
    compl_compl]

end RegOpenPolar

/-- The open-set centraliser formula of lane `sk-flip-06`: for a minimal homeomorphism `T` of a
Cantor space and `O` open, `C(F_O) = F_{interior Oᶜ}` in `[[T]]`.  (Proved below.) -/
def RigidCentralizerOpenStatement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] (T : X ≃ₜ X), IsMinimalHomeo T → ∀ O : Set X, IsOpen O →
      (Subgroup.centralizer {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O} :
          Set (topologicalFullGroup T)) =
        {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) (interior Oᶜ)}

/-- The open-set centraliser formula holds. -/
theorem rigidCentralizerOpenStatement_holds : RigidCentralizerOpenStatement :=
  fun _ _ _ _ _ _ _ _ hT _ hO => regOpen_centralizer_rigid_open hT hO

/-- Regular-open polars from the lane-06 interface: `C(C(F_O)) = F_{interior (closure O)}`. -/
theorem regOpen_centralizer_centralizer_rigid_open_of_rigidCentralizerOpen
    (hC : RigidCentralizerOpenStatement) {X : Type} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X] {T : X ≃ₜ X}
    (hT : IsMinimalHomeo T) {O : Set X} (hO : IsOpen O) :
    (Subgroup.centralizer
        (Subgroup.centralizer {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) O} :
          Set (topologicalFullGroup T)) : Set (topologicalFullGroup T)) =
      {k : topologicalFullGroup T | SupportedIn (k : X ≃ₜ X) (interior (closure O))} := by
  rw [hC X T hT O hO, hC X T hT (interior Oᶜ) isOpen_interior, ← closure_compl, compl_compl]

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.regOpen_centralizer_rigid_open
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.regOpen_centralizer_centralizer_rigid_open
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidCentralizerOpenStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidCentralizerOpenStatement_holds
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.regOpen_centralizer_centralizer_rigid_open_of_rigidCentralizerOpen
