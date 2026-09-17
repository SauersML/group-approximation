import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.RigidSplitCover
import GroupApproximation.Meta.AxiomGuard

/-!
# Rigid split, part 3: reduction to transport of disjointness of supports

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds").

The gap `RigidStabilizerSplitStatement` is reduced to the element-level
`SupportDisjointnessTransportStatement`: an isomorphism `Φ : [[T]] ≃* [[S]]` carries pairs of
elements with disjoint moved sets to pairs with disjoint moved sets
(`rigidStabilizerSplit_of_supportDisjointnessTransport`, via `exists_split_of_disjoint`).

The new statement is a statement about pairs of group elements, while the split statement
quantifies over clopen sets and whole rigid stabilizers; the reduction uses compactness, the
clopenness of moved sets and the centralizer computation of `RigidCentralizer`.  Conversely the
split statement applied to `U = movedSet f` gives back the new statement
(`supportDisjointnessTransport_of_rigidStabilizerSplit`), so the two are equivalent over the
results of this lane, but not by a trivial rewriting.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

open Topology

/-- Isomorphisms of topological full groups of Cantor minimal systems preserve disjointness of
moved sets.

Why this is true: by spatial realization every `Φ : [[T]] ≃* [[S]]` is `g ↦ h g h⁻¹` for a
homeomorphism `h : X ≃ₜ Y`; then `movedSet (Φ g) = h '' movedSet g`, and images under the
bijection `h` of disjoint sets are disjoint.  Group-theoretically it is Rubin's algebraic
characterization of disjointness of supports in `[[T]]`. -/
def SupportDisjointnessTransportStatement : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [PerfectSpace X] [Nonempty X]
    [TopologicalSpace.MetrizableSpace X] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] (T : X ≃ₜ X) (S : Y ≃ₜ Y),
    IsMinimalHomeo T → IsMinimalHomeo S →
      ∀ Φ : topologicalFullGroup T ≃* topologicalFullGroup S, ∀ f k : topologicalFullGroup T,
        Disjoint (movedSet (f : X ≃ₜ X)) (movedSet (k : X ≃ₜ X)) →
          Disjoint (movedSet ((Φ f : topologicalFullGroup S) : Y ≃ₜ Y))
            (movedSet ((Φ k : topologicalFullGroup S) : Y ≃ₜ Y))

/-- Reduction of the split statement to transport of disjointness of supports. -/
theorem rigidStabilizerSplit_of_supportDisjointnessTransport
    (hd : SupportDisjointnessTransportStatement) : RigidStabilizerSplitStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ U hU => by
    haveI : Infinite X := infinite_of_perfectSpace
    haveI : Infinite Y := infinite_of_perfectSpace
    exact exists_split_of_disjoint hT hS (isAperiodic_of_isMinimalHomeo hT)
      (isAperiodic_of_isMinimalHomeo hS) Φ (hd X Y T S hT hS Φ) (hd Y X S T hS hT Φ.symm) hU

/-- The converse reduction: the split statement implies transport of disjointness. -/
theorem supportDisjointnessTransport_of_rigidStabilizerSplit
    (hsplit : RigidStabilizerSplitStatement) : SupportDisjointnessTransportStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ f k hfk => by
    haveI : Infinite X := infinite_of_perfectSpace
    have hTa : IsAperiodic T := isAperiodic_of_isMinimalHomeo hT
    obtain ⟨V, -, h1, h2⟩ :=
      hsplit X Y T S hT hS Φ (movedSet (f : X ≃ₜ X)) (isClopen_movedSet hTa f.2)
    have hf : SupportedIn (f : X ≃ₜ X) (movedSet (f : X ≃ₜ X)) :=
      supportedIn_iff_movedSet_subset.2 fun _ hx => hx
    have hk : SupportedIn (k : X ≃ₜ X) (movedSet (f : X ≃ₜ X))ᶜ :=
      supportedIn_iff_movedSet_subset.2 fun x hx =>
        (Set.mem_compl_iff _ _).2 fun hxf => Set.disjoint_left.1 hfk hxf hx
    refine Set.disjoint_left.2 fun y hy1 hy2 => ?_
    exact (Set.mem_compl_iff _ _).1 (supportedIn_iff_movedSet_subset.1 (h2 k hk) hy2)
      (supportedIn_iff_movedSet_subset.1 (h1 f hf) hy1)

/-- The printed converse for topological full groups, reduced to
`SupportDisjointnessTransportStatement`. -/
theorem manuscriptSentence_flipConjugateConverse_of_supportDisjointnessTransport
    (hd : SupportDisjointnessTransportStatement) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S :=
  manuscriptSentence_flipConjugateConverse_of_rigidStabilizerSplit
    (rigidStabilizerSplit_of_supportDisjointnessTransport hd) hT hS

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.SupportDisjointnessTransportStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidStabilizerSplit_of_supportDisjointnessTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportDisjointnessTransport_of_rigidStabilizerSplit
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateConverse_of_supportDisjointnessTransport
