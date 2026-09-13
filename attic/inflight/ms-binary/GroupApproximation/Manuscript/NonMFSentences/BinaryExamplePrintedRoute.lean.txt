import GroupApproximation.Manuscript.NonMFSentences.BinaryExampleSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional
import GroupApproximation.Meta.AxiomGuard

/-!
# `non_mf_groups_exist.tex`, "The binary example": three sentences along the printed route

`BinaryExampleSentences` carries every sentence of the proof of Theorem `thm:headline`.
Three of those carriers reach the printed conclusion by a different route from the printed one.
This module supplies the printed route for each of them.

* "The relations give `t₀s₀=1` and `t₁(1-s₀t₀)s₁=1`, so `R` satisfies the hypothesis of
  Theorem~\ref{thm:full-defect-ring}, and every homomorphism from `H` to an MF group is
  trivial."  The existing carrier takes the conclusion from the rank-four configuration
  `rankFour_actualCoronaMFResidual_eq_top`.  Here the printed hypothesis is stated at `R`,
  and `thm:full-defect-ring` itself is applied to `R`, `s = s₀`, `t = t₀` and `n = 4`.
* "It is nontrivial, and every homomorphism from it to an MF group is trivial, so `H` is not
  MF."  Here the printed inference is used: if `H` were MF, its identity would be trivial.
* "Since `R≠0` satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring},
  Corollary~\ref{cor:one-sided-ring-maximal} shows that `C*_r(H)` is separable, stably finite,
  and not MF, and that `C*_max(H)` contains a proper isometry."  Here the corollary is applied
  to `R` at `n = 4`, and the isometry is literal: `star v * v = 1` with `v` not a unit.

The printed notion of an MF group is for countable groups (tex, the definition opening the
Introduction), so the triviality clauses quantify over countable targets with the CDE
predicate, as `BinaryExampleSentences` does.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace BinaryExamplePrintedRoute

open OneSidedMFRadical.RankFourEndpoint
open ReducedGroupCStarTrace

/-- `H = EL₄(R)` is countable, being finitely generated. -/
local instance binaryExamplePrintedRouteCountable : Countable H :=
  OneSidedMFRadical.RankFourEndpoint.countable

/-! ## "so `R` satisfies the hypothesis of Theorem `thm:full-defect-ring`" -/

/-- **The printed hypothesis of `thm:full-defect-ring` at `R`**, with `s = s₀` and `t = t₀`:
`ts = 1`, and `1 - st` is full, `1 = ∑ⱼ aⱼ(1-st)bⱼ` for finitely many `aⱼ, bⱼ` (tex,
`thm:full-defect-ring`, displayed hypothesis and the sentence after it). -/
def PrintedBinaryExampleFullDefectHypothesis : Prop :=
  leavittFamily.t0 * leavittFamily.s0 = 1 ∧
    ∃ (m : ℕ) (a b : Fin m → R),
      ∑ k, a k * (1 - leavittFamily.s0 * leavittFamily.t0) * b k = 1

/-- **Printed (proof of `thm:headline`):** "The relations give `t₀s₀=1` and
`t₁(1-s₀t₀)s₁=1`, so `R` satisfies the hypothesis of Theorem~\ref{thm:full-defect-ring}".
The fullness witness is the single term `t₁ · (1 - s₀t₀) · s₁`. -/
theorem binaryExampleFullDefectHypothesis : PrintedBinaryExampleFullDefectHypothesis := by
  obtain ⟨hts, hfull, -⟩ :=
    BinaryExampleSentences.manuscriptSentence_relationsGiveTrivialHomomorphisms
  refine ⟨hts, 1, fun _ ↦ leavittFamily.t1, fun _ ↦ leavittFamily.s1, ?_⟩
  rw [Fin.sum_univ_one]
  exact hfull

/-! ## "and every homomorphism from `H` to an MF group is trivial" -/

/-- **Printed (proof of `thm:headline`):** "so `R` satisfies the hypothesis of
Theorem~\ref{thm:full-defect-ring}, and every homomorphism from `H` to an MF group is
trivial." -/
def PrintedBinaryExampleTrivialMFHomomorphisms : Prop :=
  PrintedBinaryExampleFullDefectHypothesis ∧
    ∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
      ∀ (f : H →* M) (x : H), f x = 1

/-- The conclusion is `thm:full-defect-ring` in its every-rank form, closed in
`FullDefectRingEJZUnconditional`, applied to `R`, `s₀`, `t₀` and `n = 4`. -/
theorem binaryExampleTrivialMFHomomorphisms : PrintedBinaryExampleTrivialMFHomomorphisms := by
  refine ⟨binaryExampleFullDefectHypothesis, ?_⟩
  intro M _ _ hM f x
  obtain ⟨hts, hfull⟩ := binaryExampleFullDefectHypothesis
  exact OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
    R leavittFamily.s0 leavittFamily.t0 hts hfull 4 (by norm_num) M
    ((isCDEOperatorMF_iff_isOperatorMF M).mp hM) f x

/-! ## "so `H` is not MF" -/

/-- **Printed (proof of `thm:headline`):** "It is nontrivial, and every homomorphism from it
to an MF group is trivial, so `H` is not MF\@." -/
def PrintedBinaryExampleNotMF : Prop :=
  Nontrivial H ∧
    (∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
      ∀ (f : H →* M) (x : H), f x = 1) ∧
    ¬ IsCDEOperatorMF H

/-- The printed inference: were `H` MF, the identity of `H` would be a homomorphism to an MF
group, hence trivial, and `H` would be trivial. -/
theorem binaryExampleNotMF : PrintedBinaryExampleNotMF := by
  have htriv := binaryExampleTrivialMFHomomorphisms.2
  refine ⟨OneSidedMFRadical.RankFourEndpoint.nontrivial, htriv, fun hH ↦ ?_⟩
  obtain ⟨x, y, hxy⟩ := (OneSidedMFRadical.RankFourEndpoint.nontrivial).exists_pair_ne
  have hx : (MonoidHom.id H) x = 1 := htriv H hH (MonoidHom.id H) x
  have hy : (MonoidHom.id H) y = 1 := htriv H hH (MonoidHom.id H) y
  exact hxy (by simpa using hx.trans hy.symm)

/-! ## The C⋆-clauses, through Corollary `cor:one-sided-ring-maximal` -/

/-- **Printed (proof of `thm:headline`):** "Since `R≠0` satisfies the hypothesis of
Theorem~\ref{thm:full-defect-ring}, Corollary~\ref{cor:one-sided-ring-maximal} shows that
`C*_r(H)` is separable, stably finite, and not MF, and that `C*_max(H)` contains a proper
isometry." -/
def PrintedBinaryExampleCStarClauses : Prop :=
  (Nontrivial R ∧ PrintedBinaryExampleFullDefectHypothesis) ∧
    TopologicalSpace.SeparableSpace (ReducedGroupCStar H) ∧
    IsStablyFiniteCStarAlgebra (ReducedGroupCStar H) ∧
    ¬ IsMFAlgebra (ReducedGroupCStar H) ∧
    ∃ v : MaximalGroupCStar H, star v * v = 1 ∧ ¬ IsUnit v

/-- The four C⋆-conclusions are Corollary `cor:one-sided-ring-maximal` in its every-rank form,
closed in `FullDefectRingEJZUnconditional`, applied to `R`, `s₀`, `t₀` and `n = 4`. -/
theorem binaryExampleCStarClauses : PrintedBinaryExampleCStarClauses := by
  obtain ⟨hts, hfull⟩ := binaryExampleFullDefectHypothesis
  obtain ⟨hrank, -⟩ :=
    OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptOneSidedRingMaximalRankTwoAllCharacteristics
      R leavittFamily.s0 leavittFamily.t0 hts hfull
  obtain ⟨hiso, hsep, hsf, hnot⟩ := hrank 4 (by norm_num)
  exact ⟨⟨inferInstance, hts, hfull⟩, hsep, hsf, hnot, hiso⟩

end BinaryExamplePrintedRoute
end NonMFSentences
end Manuscript
end GroupApproximation

-- Closed endpoints (no leading binders): `#audit_closed_axioms`.
#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.BinaryExamplePrintedRoute.binaryExampleFullDefectHypothesis
#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.BinaryExamplePrintedRoute.binaryExampleTrivialMFHomomorphisms
#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.BinaryExamplePrintedRoute.binaryExampleNotMF
#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.BinaryExamplePrintedRoute.binaryExampleCStarClauses
