import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolReduce
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.InvolSplitCover
import GroupApproximation.Meta.AxiomGuard

/-!
# Involution reduction, part 3: plugging in the involution split cover

Census row `2e7c7d9ab149` (tex: "for topological full groups the converse holds").  Lanes
`sk-flip-09` and `sk-flip-10`.

Lane 09 proves `exists_split_of_involution_disjoint`.  That closes the interface
`InvolutionSplitCoverStatement` of lane 10, so the reductions of `InvolReduce.lean` no longer
need the hypothesis `hc`.  The only remaining input is `InvolutionDisjointnessTransportStatement`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

/-- The involution split cover holds unconditionally (lane `sk-flip-09`). -/
theorem involutionSplitCoverStatement_holds : InvolutionSplitCoverStatement :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hT hS hTa hSa Φ hΦ hΦs _ hU =>
    exists_split_of_involution_disjoint hT hS hTa hSa Φ hΦ hΦs hU

/-- Transport of disjointness of supports follows from transport of disjointness for
involutions. -/
theorem supportDisjointnessTransport_of_involutionDisjointnessTransport'
    (h : InvolutionDisjointnessTransportStatement) : SupportDisjointnessTransportStatement :=
  supportDisjointnessTransport_of_involutionDisjointnessTransport
    involutionSplitCoverStatement_holds h

/-- The printed converse for topological full groups, reduced to
`InvolutionDisjointnessTransportStatement` alone. -/
theorem manuscriptSentence_flipConjugateConverse_of_involutionDisjointnessTransport'
    (h : InvolutionDisjointnessTransportStatement)
    {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    [PerfectSpace X] [Nonempty X] [TopologicalSpace.MetrizableSpace X] [CompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [PerfectSpace Y] [Nonempty Y]
    [TopologicalSpace.MetrizableSpace Y] {T : X ≃ₜ X} {S : Y ≃ₜ Y}
    (hT : IsMinimalHomeo T) (hS : IsMinimalHomeo S) :
    Nonempty (topologicalFullGroup T ≃* topologicalFullGroup S) ↔ FlipConjugate T S :=
  manuscriptSentence_flipConjugateConverse_of_involutionDisjointnessTransport
    involutionSplitCoverStatement_holds h hT hS

end GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.involutionSplitCoverStatement_holds
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.supportDisjointnessTransport_of_involutionDisjointnessTransport'
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.FlipConverse.manuscriptSentence_flipConjugateConverse_of_involutionDisjointnessTransport'
