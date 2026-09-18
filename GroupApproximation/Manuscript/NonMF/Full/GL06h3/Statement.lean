import GroupApproximation.Manuscript.NonMF.Full.GL06e.AllCellsStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h3: short-boundary refutation below the inductive bound, statements

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

* `ShortBoundaryRefutedBelowInput`: at fixed parameters, a least-area diagram with at least one
  relator cell, letter labels and clause (b) of Lemma 9.7 below its relator count has boundary
  length larger than `ε + ε`.
* `ShortBoundaryRefutedBelowSectionStatement`: the same, beyond thresholds.

Neither is a literature statement.  Both are combinatorial clauses of the induction step of
Lemma 9.7(b); `Full/GL06h3/Assembly` derives
`GL06e.AllCellsShortEnclosedRefutedBelowInput` from the first one.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h3

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A short boundary is refuted below the inductive bound, at fixed parameters** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
def ShortBoundaryRefutedBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Xi : DiscDiagram.{u, w, v} W), Xi.LeastArea →
    OsinLemma97Below.{u, w, v} D lambda c mu eps W Xi.rCellCount →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (Xi.label d)) →
    (∀ word ∈ W, 1 < word.length) →
    0 < Xi.rCellCount →
    Xi.boundaryWord.length ≤ eps + eps →
      False

end Input

/-- **A short boundary is refuted below the inductive bound, beyond thresholds** (Osin, proof of
Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121). -/
def ShortBoundaryRefutedBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              ShortBoundaryRefutedBelowInput.{u, w, v} D lambda c mu eps W

end GroupApproximation.Full.GL06h3
