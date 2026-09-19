import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationProductConjugatorCore

/-!
# Product-corona conjugators for tensor synchronization
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

noncomputable local instance tensorConjugatorPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorConjugatorStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The reduced-product representation and reduced-product conjugator satisfy
the manuscript covariance relation exactly. -/
theorem synchronizedProductConjugator_covariance
    {S : Type w} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type u} [Group Q] {A : Type v} [CStarAlgebra A]
    (E : ℕ → Type u) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
    [∀ n, DecidableEq (E n)] [∀ n, Nonempty (E n)]
    (R : RegularRealizationData Gamma A)
    (ell : ∀ n, Gamma × Q →* E n)
    (source target : S →* Gamma × Q)
    (hfirst : ∀ s : S, (source s).1 = (target s).1)
    (hker : ∀ n, ((ell n).comp source).ker = ((ell n).comp target).ker)
    (s : S) :
    letI : Nontrivial A := regularRealization_nontrivial R
    let V := synchronizedProductHom E R ell
    let W := synchronizedProductConjugator E R ell source target hfirst hker
    (W : CStarProductCorona
        (fun n ↦ TensorCoordinateAlgebra A E n) cofinite) *
          (V (source s) : CStarProductCorona
            (fun n ↦ TensorCoordinateAlgebra A E n) cofinite) *
        star (W : CStarProductCorona
          (fun n ↦ TensorCoordinateAlgebra A E n) cofinite) =
      (V (target s) : CStarProductCorona
        (fun n ↦ TensorCoordinateAlgebra A E n) cofinite) := by
  letI : Nontrivial A := regularRealization_nontrivial R
  exact productCorona_covariance_of_coordinate
    (fun n ↦ TensorCoordinateAlgebra A E n)
    (fun n ↦ synchronizedCoordinateHom E R ell n)
    source target
    (fun n ↦ synchronizedCoordinateConjugator E R ell source target
      hfirst hker n)
    (synchronizedCoordinateConjugator_covariance E R ell source target
      hfirst hker) s

end

end TensorSynchronizationAssembly
end OneSidedMFRadical
end Manuscript
end GroupApproximation
