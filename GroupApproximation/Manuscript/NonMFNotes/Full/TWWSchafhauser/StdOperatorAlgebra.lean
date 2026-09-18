import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.StdOperatorAlgebraComplete
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# `𝓛(H_J)` is a unital C⋆-algebra

Lane `TWWSch3d3-2C`, work order `WO-3d3-2C`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), through the Busby picture of `Ext(S, J)` used in
Schafhauser's proof of the Tikuisis--White--Winter theorem.

The bounded adjointable operators `StdBdd J` on `H_J = standardModule ℕ J` form a unital
C⋆-algebra (Lance, *Hilbert C⋆-modules*, Ch. 2). The axioms were proved in
`StdOperatorAlgebraNorm` (normed algebra, C⋆-identity) and `StdOperatorAlgebraComplete`
(completeness); this file assembles them and installs the spectral order:

* `StdBdd.instCStarAlgebra : CStarAlgebra (StdBdd J)`;
* `StdBdd.instPartialOrder`, `StdBdd.instStarOrderedRing`: the order `S ≤ T` iff `T - S` is
  selfadjoint with nonnegative spectrum (`CStarAlgebra.spectralOrder`).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.HilbertModule

noncomputable section

variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **`𝓛(H_J)` is a unital C⋆-algebra** (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`; Lance, Ch. 2). -/
instance StdBdd.instCStarAlgebra : CStarAlgebra (StdBdd J) where

/-- The spectral order on `𝓛(H_J)` (`non_mf_group_notes.tex`, `thm:fixed-radical-membership`). -/
instance StdBdd.instPartialOrder : PartialOrder (StdBdd J) := CStarAlgebra.spectralOrder _

/-- `𝓛(H_J)` is a star-ordered ring for the spectral order (`non_mf_group_notes.tex`,
`thm:fixed-radical-membership`). -/
instance StdBdd.instStarOrderedRing : StarOrderedRing (StdBdd J) :=
  CStarAlgebra.spectralOrderedRing _

end

end GroupApproximation.Full.TWWSchafhauser
