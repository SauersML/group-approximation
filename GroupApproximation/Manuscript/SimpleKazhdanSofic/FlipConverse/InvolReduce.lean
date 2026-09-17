import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolReduceStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# Involution reduction, part 2: support disjointness from involution disjointness

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds").  Lane
`sk-flip-10`.

The open gap `SupportDisjointnessTransportStatement` (`RigidSplit.lean`) is reduced to its
special case for involutions, `InvolutionDisjointnessTransportStatement`.  The reduction goes
through the involution split cover `InvolutionSplitCoverStatement`.  That cover is the interface
of lane `sk-flip-09` and is stated as a `Statement` because the lane is not yet on disk.

1. `rigidStabilizerSplit_of_involutionDisjointnessTransport`.  Both Statements quantify over
   all pairs of Cantor minimal systems.  The involution statement applied to `Φ` and to
   `Φ.symm` gives the two transport hypotheses of the involution split cover.  The cover
   then yields `RigidStabilizerSplitStatement`.  Aperiodicity comes from
   `isAperiodic_of_isMinimalHomeo` and `infinite_of_perfectSpace`.
2. `supportDisjointnessTransport_of_involutionDisjointnessTransport`.  Compose with the
   corpus reduction `supportDisjointnessTransport_of_rigidStabilizerSplit`.
3. `manuscriptSentence_flipConjugateConverse_of_involutionDisjointnessTransport`.  Compose
   with `manuscriptSentence_flipConjugateConverse_of_rigidStabilizerSplit`.

Together with `involutionDisjointnessTransport_of_supportDisjointnessTransport`, the involution
statement and the support statement are therefore equivalent, modulo the lane 09 cover.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

/-- The split statement from transport of disjointness for involutions, given the involution
split cover of lane `sk-flip-09`. -/
theorem rigidStabilizerSplit_of_involutionDisjointnessTransport
    (hc : InvolutionSplitCoverStatement) (h : InvolutionDisjointnessTransportStatement) :
    RigidStabilizerSplitStatement :=
  fun X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ T S hT hS Φ U hU => by
    haveI : Infinite X := infinite_of_perfectSpace
    haveI : Infinite Y := infinite_of_perfectSpace
    exact hc X Y T S hT hS (isAperiodic_of_isMinimalHomeo hT)
      (isAperiodic_of_isMinimalHomeo hS) Φ (h X Y T S hT hS Φ) (h Y X S T hS hT Φ.symm) U hU

/-- Reduction of transport of disjointness of supports to transport of disjointness for
involutions, given the involution split cover of lane `sk-flip-09`. -/
theorem supportDisjointnessTransport_of_involutionDisjointnessTransport
    (hc : InvolutionSplitCoverStatement) (h : InvolutionDisjointnessTransportStatement) :
    SupportDisjointnessTransportStatement :=
  supportDisjointnessTransport_of_rigidStabilizerSplit
    (rigidStabilizerSplit_of_involutionDisjointnessTransport hc h)

/-- The printed converse for topological full groups, reduced to
`InvolutionDisjointnessTransportStatement` and the involution split cover of lane
`sk-flip-09`. -/
theorem manuscriptSentence_flipConjugateConverse_of_involutionDisjointnessTransport
    (hc : InvolutionSplitCoverStatement) (h : InvolutionDisjointnessTransportStatement)
    {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S :=
  manuscriptSentence_flipConjugateConverse_of_rigidStabilizerSplit
    (rigidStabilizerSplit_of_involutionDisjointnessTransport hc h) hT hS

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.rigidStabilizerSplit_of_involutionDisjointnessTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportDisjointnessTransport_of_involutionDisjointnessTransport
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateConverse_of_involutionDisjointnessTransport
