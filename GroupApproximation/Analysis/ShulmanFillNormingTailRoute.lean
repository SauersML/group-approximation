import GroupApproximation.Analysis.CStarInfiniteFaithfulRepresentation

/-!
# The legacy conditional route from a unital tail-pair package

`ShulmanFill.conjugateWordNorming_of_printedPair_of_compatible'` derives
`ConjugateWordNormingStatement` from `Theorem4PrintedPairStatement`, which
`Analysis/ShulmanFillNormingPrintedPairRefuted` and
`Analysis/ShulmanFillNormingPrintedPairCharacter` refute.  These are the same two
theorems on `UnitalTailPairPackageStatement`, the legacy conditional package.

The bodies are the landed ones with two substitutions.  Theorem 10 comes from
`isMFAlgebra_amalgam_of_tailPair` instead of `isMFAlgebra_amalgam_of_printedPair`,
and the Hilbert space comes from
`CStarState.separableFaithfulInfiniteRepresentation` instead of
`CStarState.separableFaithfulRepresentation` --- the same construction, carrying
the dimension clause the repaired binder asks for.  Everything else, including
the two nontriviality instances read off `π` and the identification of the glued
evaluation through `eval_limitRep_eq_of_comp`, is unchanged.

## What the route rests on

`UnitalTailPairPackageStatement`,
`ShulmanSymmetricDouble.CompatibleTargetPairStatement`, and
`ShiftedPrintedMFStatement`, which the unshifted route carries too
(there `Analysis/ShulmanFillNormingEllTwoTheorem10` discharges it; what is known
about discharging it here is in `Analysis/ShulmanFillNormingTailPrintedPair`'s
docstring).  Gelfand--Naimark is not among them: it is a theorem.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

variable [∀ m, Nontrivial (DoubledModel EllTwoCoefficient m)]

omit [∀ (m : ℕ), Nontrivial (DoubledModel EllTwoCoefficient m)] in
/-- **Shulman's Theorem 10 from the repaired package.**  The landed
`symmetricDoubleMF_of_printedPair`, with the refuted binder replaced and the
Gelfand--Naimark input discharged rather than assumed. -/
theorem symmetricDoubleMF_of_tailPair
    (hT4 : UnitalTailPairPackageStatement) (hMF : ShiftedPrintedMFStatement) :
    ShulmanSymmetricDouble.SymmetricDoubleMFStatement := by
  intro C D _ _ k _ hDmf
  haveI : TopologicalSpace.SeparableSpace D := hDmf.1
  haveI : Nontrivial D := nontrivial_left_of_nonempty_representation k k
  haveI : TopologicalSpace.SeparableSpace (UniversalCStarAmalgam k k) :=
    separableSpace_universalCStarAmalgam k k
  haveI : Nontrivial (UniversalCStarAmalgam k k) :=
    nontrivial_universalCStarAmalgam k k
  obtain ⟨H, hgroup, hinner, hcomplete, hsep, hfd, π, hπ⟩ :=
    CStarState.separableFaithfulInfiniteRepresentation.{1}
      (UniversalCStarAmalgam k k)
  letI : NormedAddCommGroup H := hgroup
  letI : InnerProductSpace ℂ H := hinner
  haveI : CompleteSpace H := hcomplete
  haveI : TopologicalSpace.SeparableSpace H := hsep
  -- Nontriviality of the two operator algebras, read off `π` and `hBlockOp`.
  haveI : Nontrivial (H →L[ℂ] H) := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne (UniversalCStarAmalgam k k)
    exact ⟨⟨π a, π b, fun h ↦ hab (hπ h)⟩⟩
  haveI : Nontrivial (BlockSpace H 2 →L[ℂ] BlockSpace H 2) := by
    obtain ⟨X, Y, hXY⟩ :=
      exists_pair_ne (CStarMatrix (Fin 2) (Fin 2) (H →L[ℂ] H))
    exact ⟨⟨hBlockOp X, hBlockOp Y, fun h ↦ hXY (hBlockOp_injective h)⟩⟩
  have hρ : ((π.comp (universalCStarAmalgamLeft k k)).comp k)
      = ((π.comp (universalCStarAmalgamRight k k)).comp k) :=
    congrArg π.comp (universalCStarAmalgam_compatible k k)
  refine isMFAlgebra_amalgam_of_tailPair k hT4 hMF hfd hDmf
    (π.comp (universalCStarAmalgamLeft k k))
    (π.comp (universalCStarAmalgamRight k k))
    (hπ.comp (injective_universalCStarAmalgamLeft_symmetric k))
    (hπ.comp (injective_universalCStarAmalgamRight_symmetric k)) hρ ?_
  intro x y hxy
  apply hπ
  exact (eval_limitRep_eq_of_comp k π hρ x).symm.trans
    (hxy.trans (eval_limitRep_eq_of_comp k π hρ y))

omit [∀ (m : ℕ), Nontrivial (DoubledModel EllTwoCoefficient m)] in
/-- **The recognition statement from the legacy conditional package.**  Where
`conjugateWordNorming_of_printedPair_of_compatible'` rests on a Prop that is
false, this rests on the stronger tail package, on Enders--Shulman's Theorem 4.11, and on the
printed-model MF input the unshifted route carries as well. -/
theorem conjugateWordNorming_of_tailPair_of_compatible
    (hT4 : UnitalTailPairPackageStatement) (hMF : ShiftedPrintedMFStatement)
    (hCTP : ShulmanSymmetricDouble.CompatibleTargetPairStatement) :
    ConjugateWordNormingStatement :=
  conjugateWordNorming_of_typeZeroWitness
    (symmetricDoubleMF_of_tailPair hT4 hMF)
    (factorMapInjective_of_compatibleTargetPair hCTP)

end

end ShulmanFill
end GroupApproximation
