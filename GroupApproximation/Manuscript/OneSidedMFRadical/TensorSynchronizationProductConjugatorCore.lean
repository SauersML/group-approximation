import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationCoordinateConjugatorCore

/-!
# Product-corona conjugator for tensor synchronization
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TensorSynchronizationAssembly

open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationMatrixCore
open PolarLiftingGeneralCStar Filter

noncomputable section

universe u v w

noncomputable local instance tensorProductConjugatorPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorProductConjugatorStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The coordinate conjugators form a unitary in the C-star reduced product. -/
def synchronizedProductConjugator
    {S : Type w} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type u} [Group Q] {A : Type v} [CStarAlgebra A]
    (E : ℕ → Type u) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
    [∀ n, DecidableEq (E n)] [∀ n, Nonempty (E n)]
    (R : RegularRealizationData Gamma A)
    (ell : ∀ n, Gamma × Q →* E n)
    (source target : S →* Gamma × Q)
    (hfirst : ∀ s : S, (source s).1 = (target s).1)
    (hker : ∀ n, ((ell n).comp source).ker = ((ell n).comp target).ker) :
    letI : Nontrivial A := regularRealization_nontrivial R
    unitary (CStarProductCorona
      (fun n ↦ TensorCoordinateAlgebra A E n) cofinite) := by
  letI : Nontrivial A := regularRealization_nontrivial R
  exact unitaryCStarSequenceToProductCorona
    (fun n ↦ TensorCoordinateAlgebra A E n)
    (fun n ↦ synchronizedCoordinateConjugator E R ell source target
      hfirst hker n)

end


end TensorSynchronizationAssembly
end OneSidedMFRadical
end Manuscript
end GroupApproximation
