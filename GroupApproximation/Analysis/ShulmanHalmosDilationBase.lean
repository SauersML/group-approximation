import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Tactic

/-! Core definitions for the Halmos dilation. -/

namespace GroupApproximation
namespace ShulmanHalmosDilation

open scoped CStarAlgebra

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

noncomputable local instance : PartialOrder A := CStarAlgebra.spectralOrder A
noncomputable local instance : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

abbrev Mat₂ (A : Type u) := CStarMatrix (Fin 2) (Fin 2) A

noncomputable local instance matComplexCFC [Nontrivial A] :
    ContinuousFunctionalCalculus ℂ (Mat₂ A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

noncomputable local instance matRealCFC [Nontrivial A] :
    ContinuousFunctionalCalculus ℝ (Mat₂ A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

noncomputable local instance matPartialOrder [Nontrivial A] :
    PartialOrder (Mat₂ A) := CStarAlgebra.spectralOrder (Mat₂ A)

noncomputable local instance matStarOrderedRing [Nontrivial A] :
    StarOrderedRing (Mat₂ A) := CStarAlgebra.spectralOrderedRing (Mat₂ A)

noncomputable local instance matNonnegSpectrum [Nontrivial A] :
    NonnegSpectrumClass ℝ (Mat₂ A) :=
  CStarAlgebra.instNonnegSpectrumClass

/-- A two-by-two diagonal matrix over a C-star algebra. -/
def diag₂ (a b : A) : Mat₂ A :=
  CStarMatrix.ofMatrix !![a, 0; 0, b]

/-- A selfadjoint off-diagonal matrix associated to an element. -/
def selfAdjointOffDiag (x : A) : Mat₂ A :=
  CStarMatrix.ofMatrix !![0, x; star x, 0]

/-- The left defect of a contraction. -/
def leftDefect (x : A) : A := CFC.sqrt (1 - x * star x)

/-- The right defect of a contraction. -/
def rightDefect (x : A) : A := CFC.sqrt (1 - star x * x)

/-- The Halmos two-by-two dilation of a contraction. -/
def halmos (x : A) : Mat₂ A :=
  CStarMatrix.ofMatrix !![x, leftDefect x; rightDefect x, -star x]

end

end ShulmanHalmosDilation
end GroupApproximation
