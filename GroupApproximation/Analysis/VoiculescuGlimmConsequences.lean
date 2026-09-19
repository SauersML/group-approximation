import GroupApproximation.Analysis.VoiculescuGlimmAssembly
import GroupApproximation.Analysis.VoiculescuBlockAbsorption

/-!
# The closed Glimm input propagated through the Voiculescu assembly

This module removes the now-discharged `GlimmLemmaStatement` premise from the
two consumers that delimit the finite-dimensional and block-diagonal parts of
the absorption argument.  The remaining passage to Enders--Shulman's
`CompatibleTargetPairStatement` is therefore beyond Glimm's lemma: it is the
general essential-representation absorption and Calkin-unitary assembly.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

/-- The finite-dimensional intertwining step with no named Glimm premise. -/
theorem voiculescuIntertwiningStep : IntertwiningStepStatement :=
  intertwiningStep_of_glimm glimmLemma

/-- The separable block-diagonal absorption theorem with no named Glimm
premise. -/
theorem separableBlockDiagonalAbsorption :
    SeparableBlockDiagonalAbsorptionStatement :=
  separableBlockDiagonalAbsorption_of_glimm glimmLemma

end

end ShulmanFill
end GroupApproximation
