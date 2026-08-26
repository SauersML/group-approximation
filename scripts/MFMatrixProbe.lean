import GroupApproximation.Analysis.MFAlgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

open GroupApproximation

variable {A : Type} [CStarAlgebra A] (k : ℕ) [Nonempty (Fin k)]

#synth NormedRing (CStarMatrix (Fin k) (Fin k) A)
#synth CompleteSpace (CStarMatrix (Fin k) (Fin k) A)
#synth StarRing (CStarMatrix (Fin k) (Fin k) A)
#synth NormedStarGroup (CStarMatrix (Fin k) (Fin k) A)
#synth CStarRing (CStarMatrix (Fin k) (Fin k) A)
#synth Algebra ℂ (CStarMatrix (Fin k) (Fin k) A)
#synth NormedAlgebra ℂ (CStarMatrix (Fin k) (Fin k) A)
#synth StarModule ℂ (CStarMatrix (Fin k) (Fin k) A)
