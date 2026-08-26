import GroupApproximation.Analysis.MFAlgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

open GroupApproximation

variable {A : Type} [CStarAlgebra A] [Nontrivial A]

#synth NormedRing (CStarMatrix (Fin 1) (Fin 1) A)
#synth CStarRing (CStarMatrix (Fin 1) (Fin 1) A)
#synth NormedAlgebra ℂ (CStarMatrix (Fin 1) (Fin 1) A)
#synth CStarAlgebra (CStarMatrix (Fin 1) (Fin 1) A)
