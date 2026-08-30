import GroupApproximation.GGT.DGOTheorem68ProjectionReduction
import GroupApproximation.GGT.OsinTheorem12OneDebt

/-!
# Osin Theorem 1.2 from the projection-complex inputs

The arbitrary-family implication `(AH₄) → (AH₁)` is already unconditional.
Combining it with the projection-complex route to DGO Theorem 6.8 leaves
exactly DGO Theorem 4.42 and the geometric cores of DGO Lemmas 6.5 and 6.7.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

universe u v

/-- The long-overlap-to-common-power core of DGO Lemma 6.7 for every `(AH₃)`
datum. -/
def ElementaryDiameterForcesConjugatePowerStatement : Prop :=
  ∀ (G : Type u) [Group G] (D : AH3Data.{u, u} G),
    @DiameterForcesConjugatePowerAt G _ D.Space D.metricSpace D.mulAction
      D.elt D.base

/-- The two geometric inputs assemble into the projection geometry used by
DGO Theorem 6.8. -/
theorem elementaryProjectionGeometry_of_inputs
    (hct : ElementaryClosureCoarseTranslationStatement.{u})
    (hpower : ElementaryDiameterForcesConjugatePowerStatement.{u}) :
    ElementaryProjectionGeometry.{u} := by
  intro G _inst D
  exact ⟨hct G D, hpower G D⟩

/-- **Osin Theorem 1.2**, reduced to the three remaining source theorems.

Everything after these inputs is proved in the repository: Lemma 6.5's finite
index, quasiconvexity and properness consequences; Lemma 6.7's algebraic
finish; DGO Theorem 6.8's assembly; and Osin's arbitrary-family enlargement. -/
theorem osinTheorem12_of_projection_inputs
    (h442 : DGOTheorem442.{u, u})
    (hct : ElementaryClosureCoarseTranslationStatement.{u})
    (hpower : ElementaryDiameterForcesConjugatePowerStatement.{u}) :
    OsinTheorem12.{u, v} :=
  osinTheorem12_of_dgoTheorem68
    (dgoTheorem68_of_projection h442
      (elementaryProjectionGeometry_of_inputs hct hpower))

end Elementary
end GGT
end GroupApproximation
