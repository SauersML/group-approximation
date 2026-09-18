import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleGap
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleBridge
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleCompressClose
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleFragStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Simplicity of `[V_X(H), V_X(H)]`, closed (lane `bh-met-49`)

Every clause of the dynamical gap `RNDisplaceCompressStatement` (`EnvelopeSimpleGap.lean:55`) is
proved on disk, so the gap and the simplicity statements it feeds hold unconditionally.

* `rnDisplaceCompressStatement_holds : RNDisplaceCompressStatement`: compression
  `rnCompressStatement_holds` (`EnvelopeSimpleCompressClose.lean:74`) plugged into
  `rnDisplaceCompress_of_compress` (`EnvelopeSimpleFragStep.lean:160`), which already discharges
  fragmentation (`rnFragmentsStatement_proof`) and displacement (`rnDisplace`).
* `rnCommutatorSimpleStatement'_holds : RNCommutatorSimpleStatement'`: for every finite `X` with
  at least two letters and every self-similar `H ≤ Aut(T_X)`, the commutator subgroup of the
  Röver–Nekrashevych group `V_X(H)` is simple; `rnCommutatorSimple_of_gap`
  (`EnvelopeSimpleGap.lean:66`).
* `rnCommutatorSimpleStatement_holds : RNCommutatorSimpleStatement`: the envelope instance
  `V_{Fin 2 × X}(envelopeK 2 H)`; `rnCommutatorSimple_of_prime` (`EnvelopeSimpleBridge.lean:21`).

No new mathematics: every proof is a term application of on-disk declarations.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **Displacement, compression and fragmentation for `V_X(H)`**, unconditionally. -/
theorem rnDisplaceCompressStatement_holds : RNDisplaceCompressStatement :=
  rnDisplaceCompress_of_compress rnCompressStatement_holds

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnDisplaceCompressStatement_holds

/-- **The commutator subgroup of a Röver–Nekrashevych group is simple**, unconditionally. -/
theorem rnCommutatorSimpleStatement'_holds : RNCommutatorSimpleStatement' :=
  rnCommutatorSimple_of_gap rnDisplaceCompressStatement_holds

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCommutatorSimpleStatement'_holds

/-- **Simplicity of `[V, V]` for the envelope group `V = V_{Fin 2 × X}(envelopeK 2 H)`**,
unconditionally. -/
theorem rnCommutatorSimpleStatement_holds : RNCommutatorSimpleStatement :=
  rnCommutatorSimple_of_prime rnCommutatorSimpleStatement'_holds

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnCommutatorSimpleStatement_holds

end GroupApproximation.BooneHigman.Metabelian.Envelope
