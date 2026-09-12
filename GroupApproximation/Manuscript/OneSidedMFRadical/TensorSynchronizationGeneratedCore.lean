import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationCoordinateCore
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationCoronaCore
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationMFCore

/-!
# Product-corona generation core for tensor synchronization

This module assembles the exact coordinate representations and conjugators in
the C-star product corona.  Restriction to their generated C-star subalgebra
is isolated in `TensorSynchronizationGeneratedSubalgebraCore`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace TensorSynchronizationAssembly

open HNNCoronaConjugatorSentenceAudit
open TensorSynchronizationMatrixCore
open PolarLiftingGeneralCStar Filter
open scoped ComplexOrder

noncomputable section

universe u v w

noncomputable local instance tensorGeneratedPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorGeneratedStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- The free product representation whose generated C-star algebra contains
both a represented group and one prescribed unitary. -/
def representedGroupWithUnitaryHom
    {G : Type w} [Group G] {A : Type u} [CStarAlgebra A]
    (rho : G →* unitary A) (W : unitary A) :
    Monoid.Coprod G (Multiplicative ℤ) →* unitary A :=
  Monoid.Coprod.lift rho
    { toFun := fun n ↦ W ^ Multiplicative.toAdd n
      map_one' := by simp
      map_mul' := by intro m n; simp [zpow_add] }

/-- The `n`th coefficient algebra `A ⊗ M_{|E_n|}`, presented as matrices
over `A`. -/
abbrev TensorCoordinateAlgebra
    (A : Type u) [CStarAlgebra A]
    (E : ℕ → Type v) [∀ n, Fintype (E n)] (n : ℕ) :=
  CStarMatrix (E n) (E n) A

/-- The exact tensor-product representation at coordinate `n`. -/
def synchronizedCoordinateHom
    {Gamma : Type w} [Group Gamma] {Q : Type u} [Group Q]
    {A : Type v} [CStarAlgebra A]
    (E : ℕ → Type u) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
    [∀ n, DecidableEq (E n)]
    (R : RegularRealizationData Gamma A)
    (ell : ∀ n, Gamma × Q →* E n) (n : ℕ) :
    Gamma × Q →* unitary (TensorCoordinateAlgebra A E n) :=
  finiteProductTensorHom R.rho (ell n)

/-- The coordinate representations assembled in the C-star reduced product. -/
def synchronizedProductHom
    {Gamma : Type w} [Group Gamma] {Q : Type u} [Group Q]
    {A : Type v} [CStarAlgebra A]
    (E : ℕ → Type u) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
    [∀ n, DecidableEq (E n)] [∀ n, Nonempty (E n)]
    (R : RegularRealizationData Gamma A)
    (ell : ∀ n, Gamma × Q →* E n) :
    letI : Nontrivial A := regularRealization_nontrivial R
    Gamma × Q →* unitary
      (CStarProductCorona (fun n ↦ TensorCoordinateAlgebra A E n) cofinite) := by
  letI : Nontrivial A := regularRealization_nontrivial R
  exact coordinateProductCoronaHom (fun n ↦ TensorCoordinateAlgebra A E n)
    (fun n ↦ synchronizedCoordinateHom E R ell n)

/-- Every tensor coordinate is an MF algebra, by finite matrix
amplification of the original regular realization algebra. -/
theorem synchronizedCoordinate_isMF
    {Gamma : Type w} [Group Gamma] {A : Type v} [CStarAlgebra A]
    (E : ℕ → Type u) [∀ n, Fintype (E n)] [∀ n, DecidableEq (E n)]
    [∀ n, Nonempty (E n)] (R : RegularRealizationData Gamma A) (n : ℕ) :
    IsMFAlgebra (TensorCoordinateAlgebra A E n) := by
  letI : Nontrivial A := regularRealization_nontrivial R
  exact isMFAlgebra_cstarMatrix_fintype R.mf

end

end TensorSynchronizationAssembly
end OneSidedMFRadical
end Manuscript
end GroupApproximation
