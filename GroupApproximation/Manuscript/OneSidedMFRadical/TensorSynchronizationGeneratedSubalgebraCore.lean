import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationConjugatorCore

/-!
# Generated subalgebra core for tensor synchronization

This module restricts the synchronized product representation and conjugator
to the C-star subalgebra they generate.  The coordinate and ambient-corona
constructions live in `TensorSynchronizationGeneratedCore`.
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

noncomputable local instance tensorGeneratedSubalgebraPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorGeneratedSubalgebraStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The single coproduct representation whose generated C-star algebra is the
manuscript's final synchronized algebra.  Its left free factor is the product
representation and its integer generator is the corona conjugator. -/
def synchronizedAdjoinedHom
    {S : Type w} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type u} [Group Q] {A : Type v} [CStarAlgebra A] [Nontrivial A]
    (E : ℕ → Type u) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
    [∀ n, DecidableEq (E n)] [∀ n, Nonempty (E n)]
    (R : RegularRealizationData Gamma A)
    (ell : ∀ n, Gamma × Q →* E n)
    (source target : S →* Gamma × Q)
    (hfirst : ∀ s : S, (source s).1 = (target s).1)
    (hker : ∀ n, ((ell n).comp source).ker = ((ell n).comp target).ker) :
    Monoid.Coprod (Gamma × Q) (Multiplicative ℤ) →*
      unitary (CStarProductCorona
        (fun n ↦ TensorCoordinateAlgebra A E n) cofinite) :=
  representedGroupWithUnitaryHom (synchronizedProductHom E R ell)
    (synchronizedProductConjugator E R ell source target hfirst hker)

end

end TensorSynchronizationAssembly
end OneSidedMFRadical
end Manuscript
end GroupApproximation
