import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RubinPolarRigid
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolReduceStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# Rubin polars, part 5: transport of rigid polars onto open rigid stabilisers

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds"; the row is
absent from the current tex), lane `sk-flip-16` (Rubin route).

The lane target `RigidPolarCharacterizationStatement` is FALSE (RubinPolarFalse.lean), so its
reduction is replaced by one from the strictly weaker, TRUE statement
`RigidPolarOpenTransportStatement`: an isomorphism `Φ : [[T]] ≃* [[S]]` carries the rigid
stabiliser `F_U` of a clopen `U ⊆ X` onto the rigid stabiliser `F_O` of some OPEN `O ⊆ Y`.

* Truth: `rigidPolarOpenTransport_of_rigidStabilizerTransport` derives it from
  `RigidStabilizerTransportStatement` (take `O = V`, clopen hence open).  That statement is true by
  spatial realisation (note N1 of the cartography).  The derived statement is strictly weaker in
  form: `O` is only open, not clopen.
* Reduction (`supportDisjointnessTransport_of_rigidPolarOpenTransport`): let `f, k` have disjoint
  moved sets and `M = movedSet f`, a clopen set.  Then `f ∈ F_M` and `k ∈ F_{Mᶜ} = C(F_M)`.  If
  `Φ F_M = F_O` with `O` open, then `Φ f ∈ F_O` and
  `Φ k ∈ Φ C(F_M) = C(Φ F_M) = C(F_O) = F_{Oᶜ}` (`rubinTransport_centralizer`,
  `centralizer_rubinRigidSubgroup`).  So `movedSet (Φ f) ⊆ O` and `movedSet (Φ k) ⊆ Oᶜ`.  No
  clopenness of `O` is needed.
* Composing with the corpus chain gives `RigidStabilizerTransportStatement`, the involution
  statement, and the printed converse.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- Isomorphisms of topological full groups of Cantor minimal systems carry the rigid stabiliser of
each clopen set onto the rigid stabiliser of some open set.  TRUE: it follows from
`RigidStabilizerTransportStatement` (`rigidPolarOpenTransport_of_rigidStabilizerTransport`). -/
def RigidPolarOpenTransportStatement : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    [TopologicalSpace.MetrizableSpace X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y),
    IsMinimalHomeo T → IsMinimalHomeo S →
      ∀ Φ : topologicalFullGroup T ≃* topologicalFullGroup S, ∀ U : Set X, IsClopen U →
        ∃ O : Set Y, IsOpen O ∧
          rubinTransport Φ (rubinRigidSubgroup T U) = rubinRigidSubgroup S O

/-- Truth check: transport of clopen rigid stabilisers implies the open version. -/
theorem rigidPolarOpenTransport_of_rigidStabilizerTransport
    (hrs : RigidStabilizerTransportStatement) : RigidPolarOpenTransportStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ U hU => by
    obtain ⟨V, hV, hUV⟩ := hrs X Y T S hT hS Φ U hU
    refine ⟨V, hV.isOpen, ?_⟩
    ext k
    rw [mem_rubinTransport, mem_rubinRigidSubgroup, mem_rubinRigidSubgroup]
    have e := hUV (Φ.symm k)
    rw [MulEquiv.apply_symm_apply] at e
    exact e

/-- The open transport of rigid polars implies transport of disjointness of supports. -/
theorem supportDisjointnessTransport_of_rigidPolarOpenTransport
    (h : RigidPolarOpenTransportStatement) : SupportDisjointnessTransportStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ f k hfk => by
    haveI : Infinite X := infinite_of_perfectSpace
    have hTa : IsAperiodic T := isAperiodic_of_isMinimalHomeo hT
    have hM : IsClopen (movedSet (f : X ≃ₜ X)) := isClopen_movedSet hTa f.2
    obtain ⟨O, hO, hPO⟩ := h X Y T S hT hS Φ (movedSet (f : X ≃ₜ X)) hM
    have hf : SupportedIn (f : X ≃ₜ X) (movedSet (f : X ≃ₜ X)) :=
      supportedIn_iff_movedSet_subset.2 fun _ hx => hx
    have hk : SupportedIn (k : X ≃ₜ X) (movedSet (f : X ≃ₜ X))ᶜ :=
      supportedIn_iff_movedSet_subset.2 fun x hx =>
        (Set.mem_compl_iff _ _).2 fun hxf => Set.disjoint_left.1 hfk hxf hx
    have hΦf : Φ f ∈ rubinRigidSubgroup S O := by
      rw [← hPO, mem_rubinTransport, MulEquiv.symm_apply_apply]
      exact mem_rubinRigidSubgroup.2 hf
    have hΦk : Φ k ∈ rubinRigidSubgroup S Oᶜ := by
      rw [← centralizer_rubinRigidSubgroup hS hO, ← hPO, rubinTransport_centralizer,
        mem_rubinTransport, MulEquiv.symm_apply_apply, centralizer_rubinRigidSubgroup hT hM.isOpen]
      exact mem_rubinRigidSubgroup.2 hk
    have hΦf' : SupportedIn ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y) O :=
      mem_rubinRigidSubgroup.1 hΦf
    have hΦk' : SupportedIn ((Φ k : topologicalFullGroup S) : Y ≃ₜ Y) Oᶜ :=
      mem_rubinRigidSubgroup.1 hΦk
    refine Set.disjoint_left.2 fun y hy1 hy2 => ?_
    exact (Set.mem_compl_iff _ _).1 (supportedIn_iff_movedSet_subset.1 hΦk' hy2)
      (supportedIn_iff_movedSet_subset.1 hΦf' hy1)

/-- The open transport of rigid polars implies the transport of clopen rigid stabilisers. -/
theorem rigidStabilizerTransport_of_rigidPolarOpenTransport
    (h : RigidPolarOpenTransportStatement) : RigidStabilizerTransportStatement :=
  rigidStabilizerTransport_of_rigidStabilizerSplit
    (rigidStabilizerSplit_of_supportDisjointnessTransport
      (supportDisjointnessTransport_of_rigidPolarOpenTransport h))

/-- The open transport of rigid polars implies the involution disjointness statement (the known
open gap of the involution route). -/
theorem involutionDisjointnessTransport_of_rigidPolarOpenTransport
    (h : RigidPolarOpenTransportStatement) : InvolutionDisjointnessTransportStatement :=
  involutionDisjointnessTransport_of_supportDisjointnessTransport
    (supportDisjointnessTransport_of_rigidPolarOpenTransport h)

/-- The printed converse for topological full groups, reduced to
`RigidPolarOpenTransportStatement`. -/
theorem manuscriptSentence_flipConjugateConverse_of_rigidPolarOpenTransport
    (h : RigidPolarOpenTransportStatement) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S :=
  manuscriptSentence_flipConjugateConverse_of_supportDisjointnessTransport
    (supportDisjointnessTransport_of_rigidPolarOpenTransport h) hT hS

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidPolarOpenTransportStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidPolarOpenTransport_of_rigidStabilizerTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportDisjointnessTransport_of_rigidPolarOpenTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidStabilizerTransport_of_rigidPolarOpenTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.involutionDisjointnessTransport_of_rigidPolarOpenTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateConverse_of_rigidPolarOpenTransport
