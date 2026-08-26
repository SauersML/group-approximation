import GroupApproximation.Analysis.MFAlgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

open GroupApproximation

example {A : Type} [CStarAlgebra A] (k : ℕ) [Nonempty (Fin k)] :
    NonUnitalCStarAlgebra (CStarMatrix (Fin k) (Fin k) A) := by
  infer_instance

example {A : Type} [CStarAlgebra A] (k : ℕ) [Nonempty (Fin k)] :
    CStarAlgebra (CStarMatrix (Fin k) (Fin k) A) := by
  infer_instance
