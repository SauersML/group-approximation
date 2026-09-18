import GroupApproximation.Manuscript.OneSidedMFRadical.IntroductionClaimSentences
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Meta.AxiomGuard

/-!
# The Introduction's MF definition, as a predicate

`non_mf_groups_exist.tex`, Introduction (the operator-norm definition of MF used throughout
Theorem `thm:amenable-trace`, tex 263–292): a countable group `G` is MF when there are
unitaries `V_n : G → U(d_n)` with `‖V_n(gh) - V_n(g)V_n(h)‖ → 0` and
`limsup_n ‖V_n(g) - 1‖ > 0` for `g ≠ 1`.

This module packages the printed right-hand side as the predicate `LiteralMF` and records
that it coincides with the corpus predicate `IsOperatorMF` on countable groups, by the closed
theorem `OneSidedMFRadical.manuscriptIntroductionMFDefinition` together with
`isCDEOperatorMF_iff_isOperatorMF`.  The lane modules state their endpoints for both
predicates.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroAmenable

open scoped Matrix.Norms.L2Operator

/-- The Introduction's printed definition of MF: a sequence of finite-dimensional unitary maps,
normalized at the identity, asymptotically multiplicative in operator norm and separating every
nontrivial element in `limsup`. -/
def LiteralMF (G : Type) [Group G] : Prop :=
  ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
    (∀ n, 0 < Fintype.card (X n)) ∧
      (∀ n, V n 1 = 1) ∧
      (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
          (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
      (∀ g : G, g ≠ 1 → 0 < Filter.limsup
        (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop)

/-- On countable groups the printed definition is the corpus operator-MF predicate. -/
theorem literalMF_iff_isOperatorMF (G : Type) [Group G] [Countable G] :
    LiteralMF G ↔ GroupApproximation.IsOperatorMF G :=
  (GroupApproximation.Manuscript.OneSidedMFRadical.manuscriptIntroductionMFDefinition G).symm.trans
    (GroupApproximation.isCDEOperatorMF_iff_isOperatorMF G)

end IntroAmenable
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroAmenable.literalMF_iff_isOperatorMF
