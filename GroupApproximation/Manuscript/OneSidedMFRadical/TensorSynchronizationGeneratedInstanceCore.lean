import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationGeneratedDefinitionCore

/-!
# C-star structure on the tensor-synchronized generated algebra

This instance is isolated from the underlying generated-subalgebra definition
so downstream typeclass elaboration does not slow that definition's module.
-/

namespace GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly

open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationMatrixCore
open PolarLiftingGeneralCStar Filter

noncomputable section

universe u w

noncomputable local instance tensorGeneratedInstancePartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorGeneratedInstanceStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The explicit C-star structure on the synchronized generated subalgebra.
Its closed-subalgebra fields are supplied directly, avoiding typeclass search
through the reduced-product quotient. -/
instance synchronizedGeneratedCStar_isClosed
    {G : Type w} {D : Type u} [CStarAlgebra D]
    (rho : G → unitary D) :
    IsClosed (SynchronizedGeneratedCStar rho : Set D) :=
  StarSubalgebra.isClosed_topologicalClosure _

@[reducible] noncomputable def synchronizedGeneratedCStar_cStarAlgebra
    {G : Type w} {D : Type u} [CStarAlgebra D]
    (rho : G → unitary D) :
    CStarAlgebra (SynchronizedGeneratedCStar rho) :=
  { toNormedRing := inferInstance
    toStarRing := inferInstance
    toCompleteSpace :=
      (synchronizedGeneratedCStar_isClosed rho).completeSpace_coe
    toCStarRing := inferInstance
    toNormedAlgebra :=
      (SynchronizedGeneratedCStar rho).toSubalgebra.toNormedAlgebra
    toStarModule := StarSubalgebra.starModule (SynchronizedGeneratedCStar rho) }

noncomputable instance synchronizedGeneratedCStar_cStarAlgebraInstance
    {G : Type w} {D : Type u} [CStarAlgebra D]
    (rho : G → unitary D) :
    CStarAlgebra (SynchronizedGeneratedCStar rho) :=
  synchronizedGeneratedCStar_cStarAlgebra rho

end

end GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly
