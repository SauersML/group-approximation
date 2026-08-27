import GroupApproximation.Analysis.MFAlgebraMatrixAmplification

/-!
# Finite-index MF amplification for tensor synchronization
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TensorSynchronizationAssembly

noncomputable section

universe u v

noncomputable local instance tensorMFPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorMFStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- Matrix amplification by any nonempty finite index type preserves MF. -/
theorem isMFAlgebra_cstarMatrix_fintype
    {A : Type u} [CStarAlgebra A] [Nontrivial A]
    {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
    (hA : IsMFAlgebra A) : IsMFAlgebra (CStarMatrix I I A) := by
  letI : Nonempty (Fin (Fintype.card I)) :=
    ⟨⟨0, Fintype.card_pos_iff.mpr inferInstance⟩⟩
  have hFin := MFAlgebraMatrixAmplification.isMFAlgebra_cstarMatrix
    (Fintype.card I) hA
  exact hFin.of_injective_nonUnitalStarAlgHom
    (CStarMatrix.reindexₐ ℂ A (Fintype.equivFin I)).toNonUnitalStarAlgHom
    (CStarMatrix.reindexₐ ℂ A (Fintype.equivFin I)).injective

end


end TensorSynchronizationAssembly
end OneSidedMFRadical
end Manuscript
end GroupApproximation
