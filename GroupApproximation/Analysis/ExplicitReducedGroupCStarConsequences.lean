import GroupApproximation.Analysis.ReducedGroupCStarMFObstruction
import GroupApproximation.Analysis.UniversalKazhdanCStarConsequences
import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.LiteralKazhdanCompression

/-!
# Reduced-group-C-star consequences for the explicit MF obstructions

The repository's concrete reduced group C-star algebra has a faithful
canonical trace, hence finite matrix amplifications.  A faithful embedding
into a norm-matrix corona would, on canonical group unitaries, yield a
faithful group representation.  This file instantiates that obstruction for
the unconditional chosen witness and, conditionally, for the literal printed
group.
-/

namespace GroupApproximation

open ReducedGroupCStarTrace

noncomputable section

universe u

/-- One nontrivial element of the norm-MF residual forbids a faithful unitary
restriction of a reduced-group-C-star corona embedding. -/
theorem no_faithfulReducedCoronaUnitaryRestriction_of_nontrivial_residual
    (G : Type u) [Group G] {g : G}
    (hg : g ∈ normMFResidual G) (hne : g ≠ 1) :
    IsEmpty (FaithfulReducedCoronaUnitaryRestriction G) :=
  ⟨fun D ↦ D.false_of_mem_normMFResidual G hg hne⟩

namespace ChosenReducedGroupCStar

open ChosenMarkedPresentation ChosenNonMFTheorem

/-- The unconditional finitely presented witness has no faithful reduced
group-C-star unitary restriction into any norm-matrix ultraproduct. -/
theorem no_faithfulCoronaUnitaryRestriction :
    IsEmpty (FaithfulReducedCoronaUnitaryRestriction MarkedGroup) :=
  no_faithfulReducedCoronaUnitaryRestriction_of_nontrivial_residual
    MarkedGroup (mem_normMFResidual_iff.mpr mark_normMFInvisible)
    mark_ne_one

/-- Every finite matrix amplification of the chosen witness's concrete
reduced group C-star algebra is finite. -/
theorem matrix_isometry_is_unitary
    (n : Type*) [Fintype n] [DecidableEq n] (hn : Nonempty n)
    {v : CStarMatrix n n (ReducedGroupCStar MarkedGroup)}
    (hv : star v * v = 1) : v * star v = 1 :=
  reduced_matrix_mul_star_eq_one_of_star_mul_eq_one MarkedGroup n hn hv

end ChosenReducedGroupCStar

namespace LiteralReducedGroupCStar

open LiteralNonMFPresentation LiteralKazhdanCompression

/-- Literal printed-group version, with its remaining property-`(T)` boundary
kept explicit. -/
theorem no_faithfulCoronaUnitaryRestriction
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    IsEmpty (FaithfulReducedCoronaUnitaryRestriction MarkedGroup) :=
  no_faithfulReducedCoronaUnitaryRestriction_of_nontrivial_residual
    MarkedGroup
    (mem_normMFResidual_iff.mpr
      (mark_normMFInvisible_of_hasKazhdanPropertyT hT))
    LiteralNonMFLinearWitness.literal_mark_ne_one

/-- The split affine--Clifford witness has the same reduced-C-star corona
obstruction under the literal-base property-`(T)` input. -/
theorem witness_no_faithfulCoronaUnitaryRestriction
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    IsEmpty (FaithfulReducedCoronaUnitaryRestriction
      LiteralNonMFLinearWitness.WitnessGroup) :=
  no_faithfulReducedCoronaUnitaryRestriction_of_nontrivial_residual
    LiteralNonMFLinearWitness.WitnessGroup
    (mem_normMFResidual_iff.mpr
      (witness_sign_normMFInvisible_of_hasKazhdanPropertyT hT))
    (MarkedCompression.signAmbient_ne_one
      LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective)

end LiteralReducedGroupCStar

end
end GroupApproximation
