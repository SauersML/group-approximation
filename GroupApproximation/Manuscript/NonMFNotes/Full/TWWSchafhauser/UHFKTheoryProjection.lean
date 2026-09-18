import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.UHFInterface
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Data.Fintype.Fin

/-!
# Projections of every rational trace `j / m!` in `Q`

Lane `TWWSch3d2Q1` (work order `WO-TWWSch-3d2-Q1`, item (1)).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), §4, which uses that the tracial state of the universal
UHF algebra `Q` takes every rational value on projections (Glimm, Trans. AMS
**95** (1960); Rørdam--Larsen--Laustsen, *An introduction to K-theory for
C⋆-algebras*, Ex. 7.7.7; Davidson, *C⋆-algebras by example*, III.5).

The projection is the image under `ι m : M_{m!} → Q` of the diagonal projection
with `j` ones.  Its trace is `normTrace = trace / m! = j / m!` because
`trace = normTrace ∘ expect m` and `expect m ∘ ι m = id`.

## Main declarations

* `uhfK_isStarProjection_diagonal`: a `{0,1}`-diagonal matrix is a projection;
* `UHFModel.exists_isStarProjection_trace`: item (1).
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Matrix

/-- A diagonal matrix with entries in `{0, 1}` is a projection (the building block
of the rational-trace projections in `Q`, `thm:fixed-radical-membership` in
`non_mf_group_notes.tex`). -/
theorem uhfK_isStarProjection_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (s : n → Prop) [DecidablePred s] :
    IsStarProjection (Matrix.diagonal fun i => if s i then (1 : ℂ) else 0) := by
  refine ⟨?_, ?_⟩
  · show diagonal _ * diagonal _ = diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  · show star (diagonal _) = diagonal _
    rw [star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    funext i
    simp only [Pi.star_apply]
    split_ifs <;> simp

namespace UHFModel

variable {Q : Type} [CStarAlgebra Q] (M : UHFModel Q)

/-- **Item (1) of `WO-TWWSch-3d2-Q1`: `Q` has a projection of every trace
`j / m!`**, for `j ≤ m!` (Glimm; Schafhauser, Crelle 759 (2020), §4, used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`). -/
theorem exists_isStarProjection_trace (m j : ℕ) (hj : j ≤ m.factorial) :
    ∃ p : Q, IsStarProjection p ∧ M.trace p = (j : ℂ) / m.factorial := by
  refine ⟨M.ι m (Matrix.diagonal fun i : uhfLevel m =>
      if (Fin.val (n := m.factorial) i) < j then (1 : ℂ) else 0),
    (uhfK_isStarProjection_diagonal
      (fun i : uhfLevel m => (Fin.val (n := m.factorial) i) < j)).map (M.ι m), ?_⟩
  have hc : (∑ i : Fin m.factorial, if (i : ℕ) < j then (1 : ℂ) else 0) = j := by
    rw [Finset.sum_boole, Fin.card_filter_val_lt, min_eq_right hj]
  rw [M.trace_eq m, M.expect_ι, normTrace, card_uhfLevel, Matrix.trace_diagonal]
  exact congrArg (· / (m.factorial : ℂ)) hc

end UHFModel

end GroupApproximation.Full.TWWSchafhauser
