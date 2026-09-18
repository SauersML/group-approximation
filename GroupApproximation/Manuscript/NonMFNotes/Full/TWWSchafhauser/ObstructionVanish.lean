import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochet
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtBoundaryDescendExt

/-!
# The UCT kills the obstruction class

Lane `TWWSch3d3-3D`, work order `WO-TWWSchafhauser-3d3-3D` (Target 2, originally
`WO-TWWSchafhauser-3d-3`). Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership`
(l.1376--1378), through C. Schafhauser, J. reine angew. Math. 759 (2020), §5.

Let `0 → J → E → S → 0` be an extension with `S` separable, nuclear and in the UCT class, and
with `K₁(J) = 0` and `K₀(J)` divisible. If its index map `K₀(S) → K₁(J)` and exponential map
`K₁(S) → K₀(J)` vanish, then its class `extClass X ∈ Ext(S, J)` is zero. This is
`ExtGroup.eq_zero_of_boundary_eq_zero` applied to `extClass X`, after identifying the boundary
maps of the class with the index and exponential maps of the extension
(`ExtGroup.boundaryZero_extClass`, `ExtGroup.boundaryOne_extClass`).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open GroupApproximation.KK

/-- **The obstruction class vanishes** (`thm:fixed-radical-membership`, `non_mf_group_notes.tex`
l.1376--1378; Schafhauser 2020 §5, Rosenberg–Schochet 1987 Thm. 4.1). For an extension of a
separable nuclear UCT algebra `S` by `J` with `K₁(J) = 0` and `K₀(J)` divisible, vanishing index
and exponential maps force `extClass X = 0`. -/
theorem extClass_eq_zero {S : SepCStarAlgebra.{0}}
    (hnuc : GroupApproximation.CStarExactness.IsNuclearCStarAlgebra S)
    (hS : GroupApproximation.Full.TWWKK.kasparovKK.SatisfiesUCT S)
    {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]
    [TopologicalSpace.SeparableSpace J] [Subsingleton (KOneN J)]
    (h0 : IsDivisibleGroup (KZeroN J)) (X : CStarExtension S J)
    (hidx : X.indexMap = 0) (hexp : X.expMap = 0) : extClass X = 0 :=
  ExtGroup.eq_zero_of_boundary_eq_zero S hnuc hS J h0 (extClass X)
    ((ExtGroup.boundaryZero_extClass X).trans hidx)
    ((ExtGroup.boundaryOne_extClass X).trans hexp)

end GroupApproximation.Full.TWWSchafhauser
