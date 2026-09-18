import GroupApproximation.Manuscript.NonMF.Full.GL06h3.NearestCell
import GroupApproximation.Manuscript.NonMF.Full.GL06h3.Assembly
import GroupApproximation.Manuscript.NonMF.Full.GL06h2.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h3: the nearest-cell cut and the thresholds

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

* `NearestCellCutInput`: at fixed parameters, every least-area diagram with letter labels, at
  least two relator cells and boundary length at most `ε + ε` has a least-area diagram of the same
  relator count carrying a `NearestCellCut`.
* `NearestCellCutSectionStatement`: the same, beyond thresholds.  Its proof is the geometric cut
  along a shortest path to a nearest cell (Osin, proof of Lemma 9.7(b)).
* `shortBoundaryRefutedBelowSection_of_nearestCellCut`: the threshold assembly, from the cut and
  the short-conjugate clause of GL06h2.
* `allCellsShortEnclosedRefutedBelowSection_of_nearestCellCut`: GL06e's all-cells clause.

Neither Prop is a literature statement; both are combinatorial clauses of the induction step of
Lemma 9.7(b).  The theorems below are assembly steps; the unconditional theorem instantiates them
with the proofs of both clauses.

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

/-- **A nearest-cell cut at fixed parameters** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
def NearestCellCutInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ Xi : DiscDiagram.{u, w, v} W, Xi.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (Xi.label d)) →
    (∀ word ∈ W, 1 < word.length) → 2 ≤ Xi.rCellCount →
    Xi.boundaryWord.length ≤ eps + eps →
      ∃ Delta : DiscDiagram.{u, w, v} W, Delta.LeastArea ∧
        Delta.rCellCount = Xi.rCellCount ∧
        Nonempty (NearestCellCut D lambda c eps Delta)

end Input

/-- **A nearest-cell cut beyond thresholds** (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
def NearestCellCutSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              NearestCellCutInput.{u, w, v} D lambda c eps W

/-- **The short-boundary refutation beyond thresholds, assembled** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121).  The thresholds are the maxima of those of the two
clauses, with `ρ` also at least `2` and making `λ⁻¹(4ε + c) < (μ/2)ρ`. -/
theorem shortBoundaryRefutedBelowSection_of_nearestCellCut
    (hcut : NearestCellCutSectionStatement.{u, w, v})
    (hconj : GL06h2.ShortWordNeConjRelatorStatement.{u, w}) :
    ShortBoundaryRefutedBelowSectionStatement.{u, w, v} := by
  intro _G _ _Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨eps2, heps2⟩ := hconj D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨eps3, heps3⟩ := hcut D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max eps2 eps3, fun eps heps => ?_⟩
  obtain ⟨rho2, _hrho2pos, hrho2⟩ := heps2 eps (le_of_max_le_left heps)
  obtain ⟨rho3, _hrho3pos, hrho3⟩ := heps3 eps (le_of_max_le_right heps)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (lambda⁻¹ * (4 * (eps : ℝ) + c)) / mu)
  refine ⟨max rho2 (max rho3 (max 2 N)), ?_, fun rho hrho W hcondition => ?_⟩
  · have htwo : 2 ≤ max rho2 (max rho3 (max 2 N)) :=
      le_trans (le_max_left 2 N) (le_trans (le_max_right rho3 (max 2 N))
        (le_max_right rho2 (max rho3 (max 2 N))))
    omega
  have hrho2' : rho2 ≤ rho := le_of_max_le_left hrho
  have hrest : max rho3 (max 2 N) ≤ rho := le_of_max_le_right hrho
  have hrho3' : rho3 ≤ rho := le_of_max_le_left hrest
  have hrest' : max 2 N ≤ rho := le_of_max_le_right hrest
  have hrhotwo : 2 ≤ rho := le_of_max_le_left hrest'
  have hNrho : (N : ℝ) ≤ (rho : ℝ) := Nat.cast_le.mpr (le_of_max_le_right hrest')
  have hmul : 2 * (lambda⁻¹ * (4 * (eps : ℝ) + c)) < (rho : ℝ) * mu :=
    (div_lt_iff₀ hmu).mp (lt_of_lt_of_le hN hNrho)
  have hlarge : lambda⁻¹ * (4 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ) := by linarith
  have hrhopos : 0 < rho := by omega
  exact shortBoundaryRefutedBelowInput_of_parts hcondition hlambda hmu hmu1 hrhopos hlarge
    (hrho2 rho hrho2' W hcondition) (hrho3 rho hrho3' W hcondition)

/-- **GL06e's all-cells clause beyond thresholds, assembled** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem allCellsShortEnclosedRefutedBelowSection_of_nearestCellCut
    (hcut : NearestCellCutSectionStatement.{u, w, v})
    (hconj : GL06h2.ShortWordNeConjRelatorStatement.{u, w}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} :=
  allCellsShortEnclosedRefutedBelowSection_of_shortBoundarySection
    (shortBoundaryRefutedBelowSection_of_nearestCellCut hcut hconj)

end GroupApproximation.Full.GL06h3

#audit_axioms GroupApproximation.Full.GL06h3.shortBoundaryRefutedBelowSection_of_nearestCellCut
#audit_axioms GroupApproximation.Full.GL06h3.allCellsShortEnclosedRefutedBelowSection_of_nearestCellCut
