import GroupApproximation.Manuscript.NonMF.Full.GL06h4.NearestShortPocket
import GroupApproximation.Manuscript.NonMF.Full.GL06h3.Assembly
import GroupApproximation.Manuscript.NonMF.Full.GL06h2.ShortConjugate
import GroupApproximation.Manuscript.NonMF.Full.GL06e.Refuted
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h5: the slit pocket up to a lexicographic descent

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), the all-cells case.  Infrastructure for
`thm:hull` (non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7).

`GL06h4.gl06h4Nearest_shortPocketStatement` asks for a near-or-short slit pocket on *every*
least-area, letter-labelled diagram `Δ` with at least two relator cells and `|∂Δ| ≤ ε + ε`.
The residual here, `gl06h5_descentPocketStatement`, asks for less: a least-area,
letter-labelled diagram `Y` with `|∂Y| ≤ ε + ε` and no more relator cells than `Δ`, which
either carries the pocket, or has positive relator count and is lexicographically smaller than
`Δ` in (relator count, boundary length).  So a proof may assume `Δ` minimal in that order, and
discard, for instance, diagrams whose boundary folds or pinches.

* `gl06h5_descentPocketStatement`: the residual.
* `gl06h5_descentPocket_of_shortPocket`: the residual follows from GL06h4's (take `Y = Δ`).
* `gl06h5_shortBoundaryRefutedBelowInput_of_descent`: the short-boundary refutation at fixed
  parameters, by strong induction on `rCellCount · (ε + ε + 1) + |∂|`.
* `gl06h5_shortBoundaryRefutedBelowSection_of_descent`: the same beyond thresholds.
* `gl06h5_allCellsShort_of_descent`, `gl06h5_refutedBelow_of_corrected_of_descent`: GL06e.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.  `gl06h5_descentPocketStatement` is a combinatorial clause of Osin's proof, not a
literature statement.
-/

namespace GroupApproximation.Full.GL06h5

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.WordMetric

/-- **The slit pocket up to a lexicographic descent** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121).  The residual of this lane. -/
def gl06h5_descentPocketStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (Delta : DiscDiagram.{u, w, v} W),
    Delta.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (Delta.label d)) →
      (∀ word ∈ W, 1 < word.length) → 2 ≤ Delta.rCellCount →
        Delta.boundaryWord.length ≤ eps + eps →
          ∃ Y : DiscDiagram.{u, w, v} W, Y.LeastArea ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (Y.label d)) ∧
            Y.rCellCount ≤ Delta.rCellCount ∧ Y.boundaryWord.length ≤ eps + eps ∧
            (Nonempty (GL06h4.gl06h4Nearest_Pocket D eps Y) ∨
              (0 < Y.rCellCount ∧ (Y.rCellCount < Delta.rCellCount ∨
                Y.boundaryWord.length < Delta.boundaryWord.length)))

/-- **GL06h4's residual gives this one** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121): take `Y = Δ` and the pocket. -/
theorem gl06h5_descentPocket_of_shortPocket
    (h : GL06h4.gl06h4Nearest_shortPocketStatement.{u, w, v}) :
    gl06h5_descentPocketStatement.{u, w, v} := by
  intro _G _ _Lambda D eps W Delta hlea hletters hW hcells hboundary
  exact ⟨Delta, hlea, hletters, Nat.le_refl _, hboundary,
    Or.inl (h D eps W Delta hlea hletters hW hcells hboundary)⟩

section Measure

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- The descent measure `rCellCount · (ε + ε + 1) + |∂|`. -/
def gl06h5_measure (eps : ℕ) (X : DiscDiagram.{u, w, v} W) : ℕ :=
  X.rCellCount * (eps + eps + 1) + X.boundaryWord.length

/-- Lexicographic descent below a bound on the second coordinate. -/
theorem gl06h5_measure_lt_aux {a a' l l' K : ℕ} (hK : l' < K) (ha : a' ≤ a)
    (h : a' < a ∨ l' < l) : a' * K + l' < a * K + l := by
  rcases h with h | h
  · have h1 : a' * K + K ≤ a * K := by
      have h2 := Nat.mul_le_mul_right K (show a' + 1 ≤ a from h)
      rw [Nat.add_mul, Nat.one_mul] at h2
      exact h2
    calc a' * K + l' < a' * K + K := Nat.add_lt_add_left hK _
      _ ≤ a * K := h1
      _ ≤ a * K + l := Nat.le_add_right _ _
  · calc a' * K + l' < a' * K + l := Nat.add_lt_add_left h _
      _ ≤ a * K + l := Nat.add_le_add_right (Nat.mul_le_mul_right K ha) _

/-- The measure drops along a lexicographic descent with a short boundary. -/
theorem gl06h5_measure_lt {eps : ℕ} {X Y : DiscDiagram.{u, w, v} W}
    (hY : Y.boundaryWord.length ≤ eps + eps) (hcount : Y.rCellCount ≤ X.rCellCount)
    (h : Y.rCellCount < X.rCellCount ∨ Y.boundaryWord.length < X.boundaryWord.length) :
    gl06h5_measure eps Y < gl06h5_measure eps X := by
  unfold gl06h5_measure
  exact gl06h5_measure_lt_aux (K := eps + eps + 1) (by omega) hcount h

end Measure

