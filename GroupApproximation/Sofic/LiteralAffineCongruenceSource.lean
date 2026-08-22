import GroupApproximation.Sofic.LiteralAffineCongruenceBase
import GroupApproximation.Sofic.LiteralBaseDoublingIndex
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Algebra.HNNFinitePresentation
import GroupApproximation.Sofic.BareDefectSource

/-!
# The torsion-free affine congruence compression source

Conjugation by the affine doubling matrix fixes the linear part and doubles
the translation lattice.  It therefore restricts from the full literal affine
base to the inverse image of `Γ(3)`.  The first translation is still omitted
from its range.  This file feeds that restricted proper embedding to the
existing HNN/Britton source constructor.
-/

namespace GroupApproximation
namespace LiteralAffineCongruenceSource

open LiteralNonMFPresentation
open LiteralBaseRelations
open LiteralBaseRotationRetract
open LiteralBaseAffineQuotient
open LiteralBaseCompleteness
open LiteralBaseDoublingIndex
open LiteralNonMFLinearWitness
open ExplicitLinearModel
open LiteralAffineCongruenceBase

noncomputable section

private noncomputable def baseCompression : Base →* Base :=
  baseAffineEquiv.symm.toMonoidHom.comp
    (conjD.comp baseAffineEquiv.toMonoidHom)

private theorem baseCompression_injective : Function.Injective baseCompression := by
  intro g h hgh
  change baseAffineEquiv.symm (conjD (baseAffineEquiv g)) =
    baseAffineEquiv.symm (conjD (baseAffineEquiv h)) at hgh
  exact baseAffineEquiv.injective
    (conjD_injective (baseAffineEquiv.symm.injective hgh))

private theorem baseCompression_v1 : baseCompression v1 = v1 ^ 2 := by
  apply baseAffineEquiv.injective
  simpa [baseCompression, affineQuotient_v1, map_pow] using conjD_v1G

private theorem baseCompression_v2 : baseCompression v2 = v2 ^ 2 := by
  apply baseAffineEquiv.injective
  simpa [baseCompression, affineQuotient_v2, map_pow] using conjD_v2G

private theorem baseCompression_v3 : baseCompression v3 = v3 ^ 2 := by
  apply baseAffineEquiv.injective
  simpa [baseCompression, affineQuotient_v3, map_pow] using conjD_v3G

private theorem baseCompression_x : baseCompression x = x := by
  apply baseAffineEquiv.injective
  simpa [baseCompression, affineQuotient_x] using conjD_xG

private theorem baseCompression_y : baseCompression y = y := by
  apply baseAffineEquiv.injective
  simpa [baseCompression, affineQuotient_y] using conjD_yG

private theorem baseCompression_z : baseCompression z = z := by
  apply baseAffineEquiv.injective
  simpa [baseCompression, affineQuotient_z] using conjD_zG

/-- Doubling translations does not change the rotation quotient. -/
theorem baseToRotation_comp_baseCompression :
    baseToRotation.comp baseCompression = baseToRotation := by
  apply PresentedGroup.ext
  intro i
  fin_cases i
  · simpa [v1, v1Index] using congrArg baseToRotation baseCompression_v1
  · simpa [v2, v2Index] using congrArg baseToRotation baseCompression_v2
  · simpa [v3, v3Index] using congrArg baseToRotation baseCompression_v3
  · simpa [x, xIndex] using congrArg baseToRotation baseCompression_x
  · simpa [y, yIndex] using congrArg baseToRotation baseCompression_y
  · simpa [z, zIndex] using congrArg baseToRotation baseCompression_z

theorem linearPart_baseCompression (g : Base) :
    linearPart (baseCompression g) = linearPart g := by
  exact congrArg (fun r : Rotation => rotationEquivSL3 r)
    (DFunLike.congr_fun baseToRotation_comp_baseCompression g)

/-- The affine doubling map preserves the level-three subgroup. -/
theorem baseCompression_mem_levelThree {g : Base} (hg : g ∈ levelThree) :
    baseCompression g ∈ levelThree := by
  change linearPart (baseCompression g) ∈ CongruenceSubgroup.gamma3
  rw [linearPart_baseCompression]
  exact hg

/-- Doubling translations, restricted to `ℤ³ ⋊ Γ(3)`. -/
noncomputable def compression : P →* P where
  toFun g := ⟨baseCompression g, baseCompression_mem_levelThree g.property⟩
  map_one' := Subtype.ext (map_one baseCompression)
  map_mul' g h := Subtype.ext (map_mul baseCompression g h)

theorem compression_injective : Function.Injective compression := by
  intro g h hgh
  apply Subtype.ext
  exact baseCompression_injective (congrArg Subtype.val hgh)

/-- The first integral translation, as an element of the congruence base. -/
noncomputable def omitted : P := ⟨v1, v1_mem_levelThree⟩

theorem omitted_not_mem_range : omitted ∉ Set.range compression := by
  rintro ⟨g, hg⟩
  apply v1G_not_mem_range
  refine ⟨baseAffineEquiv (g : Base), ?_⟩
  have hbase := congrArg Subtype.val hg
  have haffine := congrArg baseAffineEquiv hbase
  change conjD (baseAffineEquiv (g : Base)) = v1G
  simpa [baseCompression, affineQuotient_v1] using haffine

/-- The HNN envelope of the proper level-three affine compression. -/
noncomputable abbrev Envelope : Type :=
  ConcreteCompressionSource.SourceGroup compression compression_injective

noncomputable def compressionSourceData :
    ConcreteCompressionSource.CompressionSourceData P Envelope :=
  ConcreteCompressionSource.sourceData compression compression_injective
    omitted_not_mem_range

/-- The closed source datum used by the torsion-free router. -/
noncomputable def literalBareDefectSourceData :
    BareDefectSourceData P Envelope :=
  compressionSourceData.toBareDefectSourceData p_hasKazhdanPropertyT

/-- The HNN envelope is torsion-free because its affine congruence base and
the auxiliary infinite-cyclic direction are torsion-free. -/
theorem envelope_isPowerTorsionFree : IsPowerTorsionFree Envelope := by
  have hz : IsPowerTorsionFree (Multiplicative ℤ) :=
    IsPowerTorsionFree.of_isMulTorsionFree
  exact HNNBritton.isPowerTorsionFree_sourceGroup compression
    compression_injective (p_isPowerTorsionFree.prod hz)

/-- The HNN envelope remains finitely presented. -/
theorem envelope_isFinitelyPresented : Group.IsFinitelyPresented Envelope := by
  letI : Group.IsFinitelyPresented P := p_isFinitelyPresented
  letI : Group.FG P := ProductFinitePresentation.fg_of_isFinitelyPresented P
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension
    (ConcreteCompressionSource.sourceEquiv compression compression_injective)

end

end LiteralAffineCongruenceSource
end GroupApproximation
