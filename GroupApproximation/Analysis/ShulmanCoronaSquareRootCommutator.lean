import GroupApproximation.Analysis.ShulmanCoronaSquareRootQuotient
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# Asymptotic commutation with coordinatewise positive square roots

The proof is qualitative.  A null commutator becomes an exact commutation
relation in the C-star product corona.  Naturality of continuous functional
calculus identifies the quotient class of coordinatewise square roots with
the square root of the quotient class, and functional calculus preserves the
exact commutation relation.  No quantitative square-root estimate is used.
-/

namespace GroupApproximation
namespace ShulmanCoronaSquareRoot

open Filter PolarLiftingGeneralCStar

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ) [l.NeBot]

noncomputable local instance commutatorCoordinatePartialOrder (n : ℕ) :
    PartialOrder (A n) := CStarAlgebra.spectralOrder (A n)

noncomputable local instance commutatorCoordinateStarOrderedRing (n : ℕ) :
    StarOrderedRing (A n) := CStarAlgebra.spectralOrderedRing (A n)

noncomputable local instance commutatorCoronaPartialOrder :
    PartialOrder (CStarProductCorona A l) :=
  quotientNonnegCoronaPartialOrder A l

noncomputable local instance commutatorCoronaStarOrderedRing :
    StarOrderedRing (CStarProductCorona A l) :=
  quotientNonnegCoronaStarOrderedRing A l

noncomputable local instance commutatorCoronaComplexCFC :
    NonUnitalContinuousFunctionalCalculus ℂ
      (CStarProductCorona A l) IsStarNormal :=
  coronaComplexCFC A l

noncomputable local instance commutatorCoronaRealCFC :
    NonUnitalContinuousFunctionalCalculus ℝ
      (CStarProductCorona A l) IsSelfAdjoint :=
  coronaRealCFC A l

noncomputable local instance commutatorCoronaNonnegSpectrum :
    NonnegSpectrumClass ℝ (CStarProductCorona A l) :=
  coronaNonnegSpectrum A l

noncomputable local instance commutatorCoronaNNRealCFC :
    NonUnitalContinuousFunctionalCalculus NNReal
      (CStarProductCorona A l)
      (fun a : CStarProductCorona A l ↦ 0 ≤ a) :=
  coronaNNRealCFC A l

omit [l.NeBot] in
/-- If a bounded positive sequence asymptotically commutes with another
bounded sequence, then its coordinatewise positive square root does too. -/
theorem isNull_commutator_sqrtSequence
    (a b : BoundedCStarSequence A) (ha : ∀ n, 0 ≤ a n)
    (hab : IsNullCStarSequence A l (a * b - b * a)) :
    IsNullCStarSequence A l
      (sqrtSequence A a ha * b - b * sqrtSequence A a ha) := by
  let q := cStarProductCoronaQuotient A l
  have hcomm : Commute (q a) (q b) := by
    rw [commute_iff_eq]
    have hzero : q (a * b - b * a) = 0 :=
      (cStarProductCoronaQuotient_eq_zero_iff A l _).2 hab
    simpa only [map_sub, map_mul, sub_eq_zero] using hzero
  have hsqrtComm : Commute (CFC.sqrt (q a)) (q b) :=
    hcomm.cfcₙ_nnreal NNReal.sqrt
  apply (cStarProductCoronaQuotient_eq_zero_iff A l _).1
  rw [map_sub, map_mul, map_mul, quotient_sqrtSequence A l a ha]
  exact sub_eq_zero.mpr hsqrtComm.eq

end

end ShulmanCoronaSquareRoot
end GroupApproximation
