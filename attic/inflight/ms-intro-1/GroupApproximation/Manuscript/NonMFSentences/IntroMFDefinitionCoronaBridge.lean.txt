import GroupApproximation.Manuscript.OneSidedMFRadical.IntroductionClaimSentences
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Meta.AxiomGuard

/-!
# The printed MF definition at the corona form `IsOperatorMF` (tex 87–98)

`non_mf_groups_exist.tex`, Introduction (lines 87–98):

> A countable group `G` is MF~\cite{CDE} if there are positive integers `d_n` and maps
> `V_n : G → U(d_n)`, with `V_n(1) = 1`, such that `‖V_n(gh) − V_n(g)V_n(h)‖ → 0` for
> `g, h ∈ G`, and `limsup_n ‖V_n(g) − 1‖ > 0` for `g ∈ G ∖ {1}`.

Much of the tree produces MF-ness in the corona form `IsOperatorMF`: an injective
homomorphism into the unitary group of a norm matrix corona over positive finite models.
For example, `isOperatorMF_of_isLEF` gives "countable LEF groups are MF" in that form.
`PrintedMFDefinitionLiteral` identifies the printed definition with the literal CDE form
`IsCDEOperatorMF` (increasing dimensions), and `isCDEOperatorMF_iff_isOperatorMF` identifies
the two corona forms.  This module states the composite as one closed proposition: for every
countable group, `IsOperatorMF` holds exactly when the printed definition does.  A
corona-form conclusion is therefore a conclusion about the printed notion.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace IntroMFDefinitionCoronaBridge

open OneSidedMFRadical
open scoped Matrix.Norms.L2Operator

/-- **Printed (tex 87–98), at the corona form.**  For every countable group, `IsOperatorMF`
is equivalent to the printed definition: finite-dimensional unitary models with
`V_n(1) = 1`, asymptotically multiplicative in operator norm, and positive `limsup`
separation of every nonidentity element. -/
def PrintedMFDefinitionCoronaForm : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    IsOperatorMF G ↔
      ∃ (X : ℕ → FiniteModel) (V : ∀ n, G → Matrix.unitaryGroup (X n) ℂ),
        (∀ n, 0 < Fintype.card (X n)) ∧
          (∀ n, V n 1 = 1) ∧
          (∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
            ‖(V n (g * h) : Matrix (X n) (X n) ℂ) -
              (V n g : Matrix (X n) (X n) ℂ) * V n h‖ ≤ ε) ∧
          (∀ g : G, g ≠ 1 → 0 < Filter.limsup
            (fun n ↦ ‖(V n g : Matrix (X n) (X n) ℂ) - 1‖) Filter.atTop)

/-- Closed proof: the corona forms agree (`isCDEOperatorMF_iff_isOperatorMF`), and the
literal CDE form is the printed definition (`manuscriptIntroductionMFDefinition`). -/
theorem manuscriptSentence_mfDefinitionCoronaForm : PrintedMFDefinitionCoronaForm := by
  intro G _ _
  exact (isCDEOperatorMF_iff_isOperatorMF G).symm.trans (manuscriptIntroductionMFDefinition G)

end IntroMFDefinitionCoronaBridge
end NonMFSentences
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.IntroMFDefinitionCoronaBridge.manuscriptSentence_mfDefinitionCoronaForm
