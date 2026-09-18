import GroupApproximation.BooneHigman.Metabelian.SuslinBase3Statement
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidInstances
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-3 base of R2, congruence core: the Statement and the entrywise lemmas

Lane `bh-met-91h`.  Target: `SuslinBase3GlobalStatement` (`SuslinBase3Endpoint.lean`), i.e.
`SuslinBase3StabLocal A 2` for the two families.

**The residual.**  `SuslinBase3CoreStab A n` is `SuslinBase3StabLocal A n` restricted to those
normalized `σ ∈ SL_n(A[X])` that are moreover congruent to `1` modulo `𝔪`, i.e. whose image in
`SL_n((A/𝔪)[X])` is the identity.  The reduction `SuslinBase3CoreStab A n → SuslinBase3StabLocal
A n` (`SuslinBase3CoreLift.lean`) is the residue-field step: over the field `κ = A/𝔪` the ring
`κ[X]` is Euclidean, so `SL_n(κ[X]) = E_n(κ[X])` (division with remainder and elementary row
reduction, `specialLinearInElementary_of_hasWellFoundedDivision`); the elementary factorization
lifts to `A[X]`, is normalized at `X = 0`, and divides `σ` down to the congruence core.

This file holds the definition, `SL_n(κ[X]) = E_n(κ[X])` for a field `κ`, and the entrywise
compatibilities of `C`, `constantCoeff` and `map π`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open Polynomial

/-- **The congruence core** at rank `n`.  For every `σ ∈ SL_n(A[X])` with `σ(0) = 1`, every
maximal `𝔪`, and `σ ≡ 1 mod 𝔪 A[X]`, the stabilization `diag(σ_𝔪, 1)` lies in
`E_{n+1}(A_𝔪[X])`.  It is the special case of `SuslinBase3StabLocal A n` with the extra
congruence hypothesis, hence TRUE wherever that is (for the two families, as a truth check
only, by Suslin's local case: `suslinBase3Core_global_of_localCaseFamily`). -/
def SuslinBase3CoreStab (A : Type*) [CommRing A] (n : ℕ) : Prop :=
  ∀ σ : Matrix.GeneralLinearGroup (Fin n) (Polynomial A),
    Matrix.det (σ : Matrix (Fin n) (Fin n) (Polynomial A)) = 1 →
      elementaryMatrixUnitMap (ι := Fin n) (Polynomial.constantCoeff (R := A)) σ = 1 →
        ∀ (𝔪 : Ideal A) (_ : 𝔪.IsMaximal),
          elementaryMatrixUnitMap (ι := Fin n)
              (Polynomial.mapRingHom (Ideal.Quotient.mk 𝔪)) σ = 1 →
            stabilizeUnit (R := Polynomial (Localization.AtPrime 𝔪)) (κ := Unit)
                (elementaryMatrixUnitMap (ι := Fin n)
                  (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime 𝔪))) σ) ∈
              elementaryGroup (Fin n ⊕ Unit) (Polynomial (Localization.AtPrime 𝔪))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.SuslinBase3CoreStab

/-- **`SL_n(κ[X]) = E_n(κ[X])` over a field `κ`**, at every positive rank: `κ[X]` is a
Euclidean domain, so division with remainder and elementary row reduction apply. -/
theorem suslinBase3Core_slField (K : Type*) [Field K] {n : ℕ} (hn : 0 < n) :
    SpecialLinearInElementary K[X] n :=
  specialLinearInElementary_of_hasWellFoundedDivision
    (hasWellFoundedDivision_of_euclideanDomain K[X]) hn

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_slField

/-- `constantCoeff ∘ C = id`, entrywise on invertible matrices. -/
theorem suslinBase3Core_cc_C {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι A)ˣ) :
    elementaryMatrixUnitMap (Polynomial.constantCoeff (R := A))
        (elementaryMatrixUnitMap (Polynomial.C (R := A)) u) = u := by
  apply Units.ext
  ext i j
  change Polynomial.coeff (Polynomial.C ((u : Matrix ι ι A) i j)) 0 = (u : Matrix ι ι A) i j
  exact Polynomial.coeff_C_zero

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_cc_C

/-- `map π ∘ C = C ∘ π`, entrywise on invertible matrices. -/
theorem suslinBase3Core_map_C {A K ι : Type*} [CommRing A] [CommRing K] [Fintype ι]
    [DecidableEq ι] (π : A →+* K) (u : (Matrix ι ι A)ˣ) :
    elementaryMatrixUnitMap (Polynomial.mapRingHom π)
        (elementaryMatrixUnitMap (Polynomial.C (R := A)) u) =
      elementaryMatrixUnitMap (Polynomial.C (R := K)) (elementaryMatrixUnitMap π u) := by
  apply Units.ext
  refine Matrix.ext fun i j ↦ ?_
  change Polynomial.map π (Polynomial.C ((u : Matrix ι ι A) i j)) =
    Polynomial.C (π ((u : Matrix ι ι A) i j))
  exact Polynomial.map_C π

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_map_C

/-- `π ∘ constantCoeff = constantCoeff ∘ map π`, entrywise on invertible matrices. -/
theorem suslinBase3Core_map_cc {A K ι : Type*} [CommRing A] [CommRing K] [Fintype ι]
    [DecidableEq ι] (π : A →+* K) (v : (Matrix ι ι A[X])ˣ) :
    elementaryMatrixUnitMap π
        (elementaryMatrixUnitMap (Polynomial.constantCoeff (R := A)) v) =
      elementaryMatrixUnitMap (Polynomial.constantCoeff (R := K))
        (elementaryMatrixUnitMap (Polynomial.mapRingHom π) v) := by
  apply Units.ext
  ext i j
  change π (Polynomial.coeff ((v : Matrix ι ι A[X]) i j) 0) =
    Polynomial.coeff (Polynomial.map π ((v : Matrix ι ι A[X]) i j)) 0
  exact (Polynomial.coeff_map π 0).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinBase3Core_map_cc

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
