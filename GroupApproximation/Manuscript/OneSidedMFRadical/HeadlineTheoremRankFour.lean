import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourConfiguration
import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourSimplicity

/-!
# `thm:headline` (Theorem B) at rank four, as one closed proposition

`non_mf_groups_exist.tex`, Theorem `thm:headline`: "Put `R = L_{𝔽₂}(1,2)` and
`H = EL₄(R)`.  Then `H` is finitely generated, nontrivial, simple, has
property~(T), and every homomorphism from `H` to an MF group is trivial.  So
`H` is not MF, and `C*_r(H)` is separable and stably finite but not MF, while
`C*_max(H)` is not finite: it contains a proper isometry."

`BinaryLeavittFullRadicalRankFour` packages the radical and approximation
clauses; `manuscriptBinaryLeavittHeadlineRankFour` proves the whole of
`RankFourEndpoint.HeadlineConclusion`, including simplicity, without
hypotheses.  The two C⋆-algebra clauses and the printed statement as a single
proposition are in `ReducedCStarConsequenceRankFour`.

## Why the headline does not depend on simplicity

The printed proof of `thm:headline` invokes `prop:simple` to pass from `d ≠ 1`
to `⟪d⟫_H = H`, which is what makes the printed defect `𝔇_H(L)` equal to `H`.

That step is available here without any normal-subgroup theorem.
`GroupApproximation.normalClosure_elementaryRoot_p1_eq_top` proves that the
normal closure of `e_{ij}(e)` is already all of `EL_ι(R)`, for every ring
carrying a binary Leavitt family and every index type with at least three
indices; the only input is the unit sandwich `t₁(s₁t₁)s₁ = 1` together with the
Steinberg commutator relations.  Its rank-four instance is
`RankFourEndpoint.normalClosure_defect_eq_top`, and that is what
`RankFourEndpoint.printedDefect_eq_top_of_configuration` consumes.  So the
full-radical calculation, the triviality of every MF-target homomorphism, and
the failure of MF-ness are all obtained here with no simplicity input at all.

This is also why the printed footnote's rank hypothesis `n ≥ 4` is exactly what
the Lean route needs: three indices for normal generation, and a fourth for the
centralizer of the corner.

## Simplicity

`RankFourEndpoint.manuscriptPropositionSimple` proves simplicity by direct root
extraction.  For a nonidentity element of a normal subgroup, the diagonal case
is reduced to triviality of central units.  An off-diagonal entry is split
according to whether the matching inverse entry vanishes; the zero branch uses
the sparse double-commutator calculation, and the nonzero branch uses the
Leavitt relations to annihilate the forward coefficient while preserving a
nonzero reversed coefficient.  The resulting row-supported commutator contains
a nonzero elementary root, which normally generates the whole group.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankFourEndpoint

/-- `H = EL₄(L_{𝔽₂}(1,2))` is countable; it is even finitely generated
(`RankFourEndpoint.finitelyGenerated`). -/
local instance headlineCountableRankFour : Countable H :=
  RankFourEndpoint.countable

/-- `H` is nontrivial, witnessed by the printed defect `d = e₀₂(e)`. -/
local instance headlineNontrivialRankFour : Nontrivial H :=
  RankFourEndpoint.nontrivial

/-! ## The headline, hypothesis-free -/

/-- **Theorem B (`thm:headline`) minus the simplicity and C⋆ clauses, as one
closed proposition.**  For `R = L_{𝔽₂}(1,2)` and `H = EL₄(R)`:

* `H` is countable (indeed finitely generated) and nontrivial;
* `H` has Kazhdan's property `(T)`;
* `Rad_MF(H) = H`, in both of the manuscript's readings of the radical — the
  literal natural-dimension corona `manuscriptCoronaMFResidual` and the
  basis-free `actualCoronaMFResidual`;
* every homomorphism from `H` to a countable MF group is trivial; and
* `H` is not MF.

The printed simplicity clause is deliberately absent from this intermediate
package because none of the clauses above uses it.  It is proved separately by
`RankFourEndpoint.manuscriptPropositionSimple`, and joined to this package in
the complete `manuscriptBinaryLeavittHeadlineRankFour` theorem below. -/
def BinaryLeavittFullRadicalRankFour : Prop :=
  Countable H ∧
    Nontrivial H ∧
    HasKazhdanPropertyT.{0, 0} H ∧
    manuscriptCoronaMFResidual H = ⊤ ∧
    actualCoronaMFResidual H = ⊤ ∧
    (∀ (M : Type) [Group M] [Countable M],
        IsCDEOperatorMF M → ∀ (f : H →* M) (x : H), f x = 1) ∧
    ¬ IsCDEOperatorMF H

/-- **Theorem B, proved.**  The route is exactly the manuscript's, with the one
substitution described in the module docstring: property `(T)` for `EL₄` over a
finitely generated ring, the printed compression configuration at rank four,
normal generation by the printed defect in place of simplicity, the one-sided
compression criterion `thm:compression-criterion`, and then the two formal
consequences of a full radical. -/
theorem manuscriptBinaryLeavittFullRadicalRankFour :
    BinaryLeavittFullRadicalRankFour := by
  have hactual : actualCoronaMFResidual H = ⊤ :=
    rankFour_actualCoronaMFResidual_eq_top
  have hmanuscript : manuscriptCoronaMFResidual H = ⊤ := by
    rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
    exact hactual
  refine ⟨RankFourEndpoint.countable, RankFourEndpoint.nontrivial,
    RankFourEndpoint.hasKazhdanPropertyT, hmanuscript, hactual, ?_, ?_⟩
  · intro M _ _ hM f x
    exact manuscriptFullRadicalKillsMFTargets (G := H) (M := M) hmanuscript
      ((isCDEOperatorMF_iff_isOperatorMF M).mp hM) f x
  · exact not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top hactual

/-! ## The complete headline -/

/-- **Theorem B (`thm:headline`), group clauses, fully and unconditionally.**
The exact rank-four binary Leavitt elementary group is nontrivial and simple,
has property `(T)`, has full MF radical, kills every homomorphism to a
countable MF group, and is not MF. -/
theorem manuscriptBinaryLeavittHeadlineRankFour : HeadlineConclusion :=
  headlineConclusion_of RankFourEndpoint.manuscriptPropositionSimple
    rankFour_actualCoronaMFResidual_eq_top

end OneSidedMFRadical
end Manuscript
end GroupApproximation
