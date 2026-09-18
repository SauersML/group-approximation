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

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The short-boundary refutation at fixed parameters, from the descent** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  Strong induction on
`gl06h5_measure`: one cell is refuted by `GL06h3.false_of_oneCell`; a pocket gives a
nearest-cell cut, refuted by `GL06h3.NearestCellCut.false_of_below`; a descent lowers the
measure. -/
theorem gl06h5_shortBoundaryRefutedBelowInput_of_descent
    (h : gl06h5_descentPocketStatement.{u, w, v}) {D : RelGenSet G Lambda}
    {W : Set (List (RelLetter G Lambda))} {lambda c mu : ℝ} {eps rho : ℕ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 < lambda) (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu)
    (hmuUpper : mu ≤ 1 / 16) (hrho : 0 < rho)
    (hlarge : lambda⁻¹ * (4 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    (hconj : ∀ word ∈ W, RelLetter.listVal word ≠ 1 →
      ∀ (g : G) (u : List (RelLetter G Lambda)),
        (∀ x ∈ u, (symmetricLabelAlphabet D).IsLetter x) →
        u.length ≤ eps + eps →
          RelLetter.listVal u ≠ g * RelLetter.listVal word * g⁻¹) :
    GL06h3.ShortBoundaryRefutedBelowInput.{u, w, v} D lambda c mu eps W := by
  have key : ∀ m : ℕ, ∀ Xi : DiscDiagram.{u, w, v} W, gl06h5_measure eps Xi = m →
      Xi.LeastArea → OsinLemma97Below.{u, w, v} D lambda c mu eps W Xi.rCellCount →
      (∀ d, (symmetricLabelAlphabet D).IsLetter (Xi.label d)) →
      (∀ word ∈ W, 1 < word.length) → 0 < Xi.rCellCount →
      Xi.boundaryWord.length ≤ eps + eps → False := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro Xi hm hlea hbelow hletters hW hpos hshort
    by_cases hone : Xi.rCellCount = 1
    · exact GL06h3.false_of_oneCell hcondition.inv_mem hconj Xi hlea hletters hone hshort
    · have htwo : 2 ≤ Xi.rCellCount := by omega
      obtain ⟨Y, hleaY, hlettersY, hcountY, hshortY, hcase⟩ :=
        h D eps W Xi hlea hletters hW htwo hshort
      have hbelowY : OsinLemma97Below.{u, w, v} D lambda c mu eps W Y.rCellCount :=
        OsinLemma97Below.mono hbelow hcountY
      rcases hcase with ⟨N⟩ | ⟨hposY, hdesc⟩
      · exact GL06h3.NearestCellCut.false_of_below
          (GL06h4.NearestCellPocket.toNearestCellCut
            (GL06h4.gl06h4Nearest_toNearestCellPocket N) hcondition hlambda1 hc hleaY hshortY)
          hcondition hlambda hmu hmuUpper hrho hlarge hleaY hbelowY
      · exact ih (gl06h5_measure eps Y)
          (lt_of_lt_of_eq (gl06h5_measure_lt hshortY hcountY hdesc) hm)
          Y rfl hleaY hbelowY hlettersY hW hposY hshortY
  intro Xi hlea hbelow hletters hW hpos hshort
  exact key _ Xi rfl hlea hbelow hletters hW hpos hshort

end Input

/-- **The short-boundary refutation beyond thresholds, from the descent** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The thresholds are those of
`GL06h2.shortWordNeConjRelatorStatement_holds`, with `ρ` also at least `2` and making
`λ⁻¹(4ε + c) < (μ/2)ρ`. -/
theorem gl06h5_shortBoundaryRefutedBelowSection_of_descent
    (h : gl06h5_descentPocketStatement.{u, w, v}) :
    GL06h3.ShortBoundaryRefutedBelowSectionStatement.{u, w, v} := by
  intro _G _ _Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨eps2, heps2⟩ :=
    GL06h2.shortWordNeConjRelatorStatement_holds D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨eps2, fun eps heps => ?_⟩
  obtain ⟨rho2, _hrho2pos, hrho2⟩ := heps2 eps heps
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (lambda⁻¹ * (4 * (eps : ℝ) + c)) / mu)
  refine ⟨max rho2 (max 2 N), ?_, fun rho hrho W hcondition => ?_⟩
  · have htwo : 2 ≤ max rho2 (max 2 N) :=
      le_trans (le_max_left 2 N) (le_max_right rho2 (max 2 N))
    omega
  have hrho2' : rho2 ≤ rho := le_of_max_le_left hrho
  have hrest : max 2 N ≤ rho := le_of_max_le_right hrho
  have hrhotwo : 2 ≤ rho := le_of_max_le_left hrest
  have hNrho : (N : ℝ) ≤ (rho : ℝ) := Nat.cast_le.mpr (le_of_max_le_right hrest)
  have hmul : 2 * (lambda⁻¹ * (4 * (eps : ℝ) + c)) < (rho : ℝ) * mu :=
    (div_lt_iff₀ hmu).mp (lt_of_lt_of_le hN hNrho)
  have hlarge : lambda⁻¹ * (4 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) := by linarith
  have hrhopos : 0 < rho := by omega
  exact gl06h5_shortBoundaryRefutedBelowInput_of_descent h hcondition hlambda hlambda1 hc hmu
    hmu1 hrhopos hlarge (hrho2 rho hrho2' W hcondition)

/-- **GL06e's all-cells clause, from the descent** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem gl06h5_allCellsShort_of_descent (h : gl06h5_descentPocketStatement.{u, w, v}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  GL06h3.allCellsShortEnclosedRefutedBelowSection_of_shortBoundarySection
    (gl06h5_shortBoundaryRefutedBelowSection_of_descent h)

/-- **GL06e's refutation below the section count, from the corrected enclosed pocket and the
descent** (Osin, proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem gl06h5_refutedBelow_of_corrected_of_descent
    (hencl : GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v})
    (h : gl06h5_descentPocketStatement.{u, w, v}) :
    GL06e.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  GL06e.refutedBelowSection_of_innerPocketEnclosedCorrected_of_allCells hencl
    (gl06h5_allCellsShort_of_descent h)

end GroupApproximation.Full.GL06h5

#audit_axioms GroupApproximation.Full.GL06h5.gl06h5_descentPocketStatement
#audit_axioms GroupApproximation.Full.GL06h5.gl06h5_descentPocket_of_shortPocket
#audit_axioms GroupApproximation.Full.GL06h5.gl06h5_measure
#audit_axioms GroupApproximation.Full.GL06h5.gl06h5_measure_lt_aux
#audit_axioms GroupApproximation.Full.GL06h5.gl06h5_measure_lt
#audit_axioms GroupApproximation.Full.GL06h5.gl06h5_shortBoundaryRefutedBelowInput_of_descent
#audit_axioms GroupApproximation.Full.GL06h5.gl06h5_shortBoundaryRefutedBelowSection_of_descent
#audit_axioms GroupApproximation.Full.GL06h5.gl06h5_allCellsShort_of_descent
#audit_axioms GroupApproximation.Full.GL06h5.gl06h5_refutedBelow_of_corrected_of_descent
