import GroupApproximation.BooneHigman.Metabelian.EnvelopeSplit
import GroupApproximation.BooneHigman.Metabelian.EnvelopeFPSection
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSection
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleBridge
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleGap
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleDisplaceClauses
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain wiring, part 2: the self-similar envelope from its smallest gaps (lane `bh-met-27`)

`Products.FPSelfSimilarEnvelopeStatement` is reduced on disk as follows.

* `Envelope.fpSelfSimilarEnvelope_of_rnEnvelope`: from `RoverNekrashevychEnvelopeStatement`;
* `Envelope.rnEnvelope_of_four`: from the four facts about `V = V_{Fin 2 × X}(K)`,
  `RNFinitelyPresentedStatement`, `RNCommutatorFiniteIndexStatement`,
  `RNCommutatorSimpleStatement`, `RNWreathEmbedStatement`;
* finite presentation: `RNFinitelyPresentedStatement'` (general alphabet) from
  `RNFreeSectionStatement` (`rnFinitelyPresented_of_freeSection`), and that from
  `HigmanVFinSectionStatement` and `RNFreeSectionCoreStatement`
  (`rnFreeSection_of_finSection_core`);
* simplicity: `RNCommutatorSimpleStatement` from `RNCommutatorSimpleStatement'`
  (`rnCommutatorSimple_of_prime`), from `RNDisplaceCompressStatement` (`rnCommutatorSimple_of_gap`),
  from `RNDisplaceStatement`, `RNCompressStatement`, `RNFragmentsStatement`
  (`rnDisplaceCompress_of_clauses`).

The only missing link was the passage from the general-alphabet statement
`RNFinitelyPresentedStatement'` to the envelope instance `RNFinitelyPresentedStatement`; it is
`rnFinitelyPresented_of_prime` here (the regrouped copy `envelopeK 2 H` of `H` is self-similar and
finitely presented, `Envelope.isSelfSimilar_envelopeK`, `Envelope.isFinitelyPresented_envelopeK`,
and `envelopeV X H` is by definition `roverNekrashevych (envelopeY X 2) (envelopeK 2 H)`).

* `fpSelfSimilarEnvelope_of_frontier`: the envelope from the seven smallest open envelope gaps.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- The general-alphabet finite-presentation statement gives the envelope instance. -/
theorem rnFinitelyPresented_of_prime (h : Envelope.RNFinitelyPresentedStatement') :
    Envelope.RNFinitelyPresentedStatement := by
  intro X _ _ H hH hfp
  exact h (Envelope.envelopeY X 2) (Envelope.envelopeK 2 H) (Envelope.isSelfSimilar_envelopeK hH)
    (Envelope.isFinitelyPresented_envelopeK hfp)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.rnFinitelyPresented_of_prime

/-- **The self-similar envelope from its smallest open gaps**:
`Envelope.HigmanVFinSectionStatement`, `Envelope.RNFreeSectionCoreStatement` (finite
presentation), `Envelope.RNCommutatorFiniteIndexStatement` (finite index),
`Envelope.RNDisplaceStatement`, `Envelope.RNCompressStatement`, `Envelope.RNFragmentsStatement`
(simplicity) and `Envelope.RNWreathEmbedStatement` (wreath embedding). -/
theorem fpSelfSimilarEnvelope_of_frontier (hV : Envelope.HigmanVFinSectionStatement)
    (hcore : Envelope.RNFreeSectionCoreStatement)
    (hfi : Envelope.RNCommutatorFiniteIndexStatement) (hD : Envelope.RNDisplaceStatement)
    (hC : Envelope.RNCompressStatement) (hF : Envelope.RNFragmentsStatement)
    (hw : Envelope.RNWreathEmbedStatement) : Products.FPSelfSimilarEnvelopeStatement :=
  Envelope.fpSelfSimilarEnvelope_of_rnEnvelope
    (Envelope.rnEnvelope_of_four
      (rnFinitelyPresented_of_prime
        (Envelope.rnFinitelyPresented_of_freeSection
          (Envelope.rnFreeSection_of_finSection_core hV hcore)))
      hfi
      (Envelope.rnCommutatorSimple_of_prime
        (Envelope.rnCommutatorSimple_of_gap (Envelope.rnDisplaceCompress_of_clauses hD hC hF)))
      hw)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.fpSelfSimilarEnvelope_of_frontier

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
