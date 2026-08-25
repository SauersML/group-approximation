import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity

/-!
# `thm:headline` (Theorem B), as one closed proposition

`non_mf_groups_exist.tex`, Theorem `thm:headline`.  With `R = L_{𝔽₂}(1,2)` and
`H = EL₁₂(R)`, the printed statement is that `H` is nontrivial, simple, has
property `(T)`, and satisfies `Rad_MF(H) = H`; equivalently every homomorphism
from `H` to an MF group is trivial, and in particular `H` is not MF.

`BinaryLeavittFullRadical` packages the radical and approximation clauses,
while `manuscriptBinaryLeavittHeadline` proves the entire printed conclusion,
including simplicity, without hypotheses.

## Why the headline does not depend on simplicity

The printed proof of `thm:headline` invokes `prop:simple` twice, and both times
for the same purpose: to pass from `d ≠ 1` to `⟪d⟫_H = H`, which is what feeds
`prop:defect-saturation` and makes the printed defect `𝔇_H(L)` equal to `H`.

That single step is available in this development without any normal-subgroup
theorem.  `GroupApproximation.normalClosure_elGen_p1_eq_top` proves that the
normal closure of `e_{ij}(q)` is already all of `EL_ι(R)`, for every ring
carrying a binary Leavitt family and every index type with at least three
indices; the only input is the unit sandwich `t₁ (s₁ t₁) s₁ = 1` together with
the Steinberg commutator relations.  Its rank-twelve instance is
`RankTwelveEndpoint.normalClosure_defect_eq_top`, and that is what
`RankTwelveEndpoint.printedDefect_eq_top_of_configuration` consumes.  So the
full-radical calculation, the triviality of every MF-target homomorphism, and
the failure of MF-ness are all obtained here with no simplicity input at all.

## Simplicity

`RankTwelveEndpoint.manuscriptPropositionSimple` proves simplicity by direct
root extraction.  For a nonidentity element of a normal subgroup, the diagonal
case is reduced to triviality of central units.  An off-diagonal entry is split
according to whether the matching inverse entry vanishes; the zero branch uses
the sparse double-commutator calculation, and the nonzero branch uses the
Leavitt relations to annihilate the forward coefficient while preserving a
nonzero reversed coefficient.  The resulting row-supported commutator contains
a nonzero elementary root, which normally generates the whole group.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint

/-- `H = EL₁₂(L_{𝔽₂}(1,2))` is countable; it is even finitely generated
(`RankTwelveEndpoint.finitelyGenerated`). -/
local instance headlineCountable : Countable H := RankTwelveEndpoint.countable

/-- `H` is nontrivial, witnessed by the printed defect `d = e₀₂(s₁t₁)`. -/
local instance headlineNontrivial : Nontrivial H := RankTwelveEndpoint.nontrivial

/-! ## The headline, hypothesis-free -/

/-- **Theorem B (`thm:headline`) minus the simplicity clause, as one closed
proposition.**  For `R = L_{𝔽₂}(1,2)` and `H = EL₁₂(R)`:

* `H` is countable (indeed finitely generated) and nontrivial;
* `H` has Kazhdan's property `(T)`;
* `Rad_MF(H) = H`, in both of the manuscript's readings of the radical — the
  literal natural-dimension corona `manuscriptCoronaMFResidual` and the
  basis-free `actualCoronaMFResidual`;
* every homomorphism from `H` to a countable MF group is trivial; and
* `H` is not MF.

The printed simplicity clause is deliberately absent.  It is not used by any of
the clauses above, and it is not proved in this development; see
`BinaryLeavittSimplicityClause`. -/
def BinaryLeavittFullRadical : Prop :=
  Countable H ∧
    Nontrivial H ∧
    HasKazhdanPropertyT.{0, 0} H ∧
    manuscriptCoronaMFResidual H = ⊤ ∧
    actualCoronaMFResidual H = ⊤ ∧
    (∀ (M : Type) [Group M] [Countable M],
        IsCDEOperatorMF M → ∀ (f : H →* M) (x : H), f x = 1) ∧
    ¬ IsCDEOperatorMF H

/-- **Theorem B, proved.**  The route is exactly the manuscript's, with the one
substitution described in the module docstring: property `(T)` for `EL₁₂` over a
finitely generated ring, the printed compression configuration at rank twelve,
normal generation by the printed defect in place of simplicity, the one-sided
compression criterion `thm:compression-criterion`, and then the two formal
consequences of a full radical. -/
theorem manuscriptBinaryLeavittFullRadical : BinaryLeavittFullRadical := by
  have hactual : actualCoronaMFResidual H = ⊤ :=
    rankTwelve_actualCoronaMFResidual_eq_top
  have hmanuscript : manuscriptCoronaMFResidual H = ⊤ := by
    rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
    exact hactual
  refine ⟨RankTwelveEndpoint.countable, RankTwelveEndpoint.nontrivial,
    RankTwelveEndpoint.hasKazhdanPropertyT, hmanuscript, hactual, ?_, ?_⟩
  · intro M _ _ hM f x
    exact manuscriptFullRadicalKillsMFTargets (G := H) (M := M) hmanuscript hM f x
  · exact not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top hactual

/-! ## The complete headline -/

/-- **Theorem B (`thm:headline`), fully and unconditionally.**  The exact
rank-twelve binary Leavitt elementary group is nontrivial and simple, has
property `(T)`, has full MF radical, kills every homomorphism to a countable MF
group, and is not MF. -/
theorem manuscriptBinaryLeavittHeadline : HeadlineConclusion :=
  headlineConclusion_of RankTwelveEndpoint.manuscriptPropositionSimple
    rankTwelve_actualCoronaMFResidual_eq_top

end OneSidedMFRadical
end Manuscript
end GroupApproximation
