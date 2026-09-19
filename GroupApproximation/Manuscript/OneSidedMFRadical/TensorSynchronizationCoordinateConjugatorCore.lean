import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationGeneratedCore

/-!
# Finite-coordinate conjugators for tensor synchronization
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TensorSynchronizationAssembly

open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationMatrixCore

noncomputable section

universe u v w

/-- Choose the exact coordinate conjugator supplied by equal finite-image
kernels. -/
def synchronizedCoordinateConjugator
    {S : Type w} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type u} [Group Q] {A : Type v} [CStarAlgebra A]
    (E : ℕ → Type u) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
    [∀ n, DecidableEq (E n)]
    (R : RegularRealizationData Gamma A)
    (ell : ∀ n, Gamma × Q →* E n)
    (source target : S →* Gamma × Q)
    (hfirst : ∀ s : S, (source s).1 = (target s).1)
    (hker : ∀ n, ((ell n).comp source).ker = ((ell n).comp target).ker)
    (n : ℕ) : unitary (TensorCoordinateAlgebra A E n) :=
  Classical.choose
    (exists_finiteProductTensor_conjugator R.rho (ell n) source target
      hfirst (hker n))

/-- The chosen coordinate conjugator has the required covariance. -/
theorem synchronizedCoordinateConjugator_covariance
    {S : Type w} [Group S] {Gamma : Type v} [Group Gamma]
    {Q : Type u} [Group Q] {A : Type v} [CStarAlgebra A]
    (E : ℕ → Type u) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
    [∀ n, DecidableEq (E n)]
    (R : RegularRealizationData Gamma A)
    (ell : ∀ n, Gamma × Q →* E n)
    (source target : S →* Gamma × Q)
    (hfirst : ∀ s : S, (source s).1 = (target s).1)
    (hker : ∀ n, ((ell n).comp source).ker = ((ell n).comp target).ker)
    (n : ℕ) (s : S) :
    let W := synchronizedCoordinateConjugator E R ell source target hfirst hker n
    (W : TensorCoordinateAlgebra A E n) *
          (synchronizedCoordinateHom E R ell n (source s) :
            TensorCoordinateAlgebra A E n) *
        star (W : TensorCoordinateAlgebra A E n) =
      (synchronizedCoordinateHom E R ell n (target s) :
        TensorCoordinateAlgebra A E n) := by
  exact (Classical.choose_spec
    (exists_finiteProductTensor_conjugator R.rho (ell n) source target
      hfirst (hker n))) s

end


end TensorSynchronizationAssembly
end OneSidedMFRadical
end Manuscript
end GroupApproximation
