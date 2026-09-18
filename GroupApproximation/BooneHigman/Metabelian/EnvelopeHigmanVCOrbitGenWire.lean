import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitGenReduce
import GroupApproximation.Meta.AxiomGuard

/-!
# Root wiring of the residual `W'''` (lane bh-met-91l)

`HigmanVSwapSectionStatement` from the residual `W''' = HigmanVCOrbitGenStatement` (see
`EnvelopeHigmanVCOrbitGenReduce`) and the short-relation section `τ`, via
`higmanVCOrbitGen_gap_of_gen` and `higmanVCOrbitGap_swapSection_of_tau`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Root wiring.**  `W'''` and the short-relation section `τ` give the swap section. -/
theorem higmanVCOrbitGen_swapSection_of_tau (hG : HigmanVCOrbitGenStatement)
    (hB : ∀ d : ℕ, 1 < d → ∃ τ : List (Fin d) × List (Fin d) → higmanVC_Q d,
      ∀ t ∈ higmanVC_rels d (fun _ => True),
        t ∉ higmanVC_rels d (fun l => l.length ≤ 3) → higmanVC_psi d τ t = 1) :
    HigmanVSwapSectionStatement :=
  higmanVCOrbitGap_swapSection_of_tau (higmanVCOrbitGen_gap_of_gen hG) hB

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitGen_swapSection_of_tau

end GroupApproximation.BooneHigman.Metabelian.Envelope
