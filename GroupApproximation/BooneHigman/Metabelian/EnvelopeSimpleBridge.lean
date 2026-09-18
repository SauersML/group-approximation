import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleStatement
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# The envelope case of simplicity of `[V_X(H), V_X(H)]`

`rnCommutatorSimple_of_prime`: `RNCommutatorSimpleStatement'` (every finite nontrivial `X`,
every self-similar `H`) gives `RNCommutatorSimpleStatement` (`EnvelopeSplit.lean`).

Route: specialise to the alphabet `envelopeY X 2 = Fin 2 × X` and the self-similar group
`envelopeK 2 H` (`isSelfSimilar_envelopeK`); `envelopeV X H` is by definition
`roverNekrashevych (envelopeY X 2) (envelopeK 2 H)`.  Finite presentation of `H` is not used.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees

/-- The general statement gives the envelope statement. -/
theorem rnCommutatorSimple_of_prime (h : RNCommutatorSimpleStatement') :
    RNCommutatorSimpleStatement := by
  intro X _ _ H hH _
  exact h (envelopeY X 2) (envelopeK 2 H) (isSelfSimilar_envelopeK hH)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCommutatorSimple_of_prime

end GroupApproximation.BooneHigman.Metabelian.Envelope
