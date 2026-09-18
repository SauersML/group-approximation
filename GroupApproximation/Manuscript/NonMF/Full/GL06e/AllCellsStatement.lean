import GroupApproximation.Manuscript.NonMF.Full.GL06e.Statements
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSucc
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06e: the all-cells short enclosed face set, statements

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

The corrected enclosed inner pocket statement `GL03BPinch.InnerPocketEnclosedTwoArcCorrected` has a
second disjunct: an enclosed face set holding every relator cell, with an outer walk of length at
most `2ε`.  This file names the statement that refutes it.

* `AllCellsShortEnclosedRefutedBelowInput`: at fixed parameters, a least-area diagram with at least
  one relator cell and clause (b) of Lemma 9.7 below its relator count has no successor-form
  enclosed face set that holds every relator cell and has an outer walk of length at most `ε + ε`.
* `AllCellsShortEnclosedRefutedBelowSectionStatement`: the same, beyond thresholds.

Neither is a literature statement.  Both are combinatorial clauses of the induction step of
Lemma 9.7(b), consumed by `Full/GL06e/Refuted`.
-/

namespace GroupApproximation.Full.GL06e

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The all-cells short enclosed face set does not exist, below the inductive bound, at fixed
parameters** (Osin, proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
def AllCellsShortEnclosedRefutedBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (X : DiscDiagram.{u, w, v} W), X.LeastArea →
    OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    0 < X.rCellCount →
    ∀ (faces : Finset X.toCombMap.Face) (outerWalk : List X.toCombMap.Dart),
      EnclosedFaceSetSucc X faces outerWalk →
      (∀ C ∈ X.relatorCells, C.face ∈ faces) →
      outerWalk.length ≤ eps + eps →
        False

end Input

/-- **The all-cells short enclosed face set does not exist, below the inductive bound, beyond
thresholds** (Osin, proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
def AllCellsShortEnclosedRefutedBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              AllCellsShortEnclosedRefutedBelowInput.{u, w, v} D lambda c mu eps W

end GroupApproximation.Full.GL06e
