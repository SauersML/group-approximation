import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity

/-!
# `thm:headline` (Theorem B), as one closed proposition

`non_mf_groups_exist.tex`, Theorem `thm:headline`.  With `R = L_{𝔽₂}(1,2)` and
`H = EL₁₂(R)`, the printed statement is that `H` is nontrivial, simple, has
property `(T)`, and satisfies `Rad_MF(H) = H`; equivalently every homomorphism
from `H` to an MF group is trivial, and in particular `H` is not MF.

`BinaryLeavittFullRadical` is every clause of that statement **except**
simplicity, with all of its quantifiers inside a single proposition, and
`manuscriptBinaryLeavittFullRadical` proves it with no hypotheses whatsoever.

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

## The one clause this development does not discharge

Simplicity of `H` is a strictly different statement, and the manuscript's proof
of it (`prop:simple`) runs on Preusser's normal-subgroup theorem, on pure
infiniteness and the exchange property of `L_{𝔽₂}(1,2)`, and on the computation
of the centre of that algebra.  The ring-side simplicity and centre inputs are
now formalized, but the Preusser normal-structure/root-detection bridge is not;
**nothing in this file proves that `H` is simple.**

What is recorded instead is `BinaryLeavittSimplicityClause`: an *implication*
whose leading hypothesis `NormalRootDetection` names the missing input exactly
(every nontrivial normal subgroup of `H` contains a nontrivial elementary
root).  Its antecedent is unproved here and is not proved anywhere in this
development.  `BinaryLeavittFullRadical` neither mentions nor uses it.
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

/-! ## The simplicity clause, which is *not* proved

Everything below is conditional.  `NormalRootDetection` is an assumption, not a
theorem of this development.
-/

/-- **The missing input, named.**  Every nontrivial normal subgroup of
`H = EL₁₂(L_{𝔽₂}(1,2))` contains a nontrivial elementary root.

This is what the manuscript extracts from Preusser's normal-subgroup theorem
together with pure infiniteness, the exchange property, and the centre
computation for `L_{𝔽₂}(1,2)`.  The latter ring-side ingredients are now
formalized; the normal-subgroup implication is still an unproved assumption
here.  No declaration in this repository establishes it, and no unconditional
statement in this file depends on it. -/
def NormalRootDetection : Prop :=
  ∀ (N : Subgroup H), N.Normal → N ≠ ⊥ →
    ∃ (i j : Fin 12) (hij : i ≠ j) (a : R),
      a ≠ 0 ∧ elementaryRoot i j hij a ∈ N

/-- **The one clause of `thm:headline` this development does not discharge.**

This proposition is an *implication*, and only the implication is proved
(`manuscriptBinaryLeavittSimplicityClause`).  Its hypothesis
`NormalRootDetection` is the unavailable normal-subgroup theorem, kept in
leading position so that the conditionality cannot be lost by reformulation.
Reading `BinaryLeavittSimplicityClause` as a proof that `H` is simple would be
a mistake: what is proved is only that root detection *would* imply simplicity,
and root detection is assumed, not established.

The headline does not depend on this: `BinaryLeavittFullRadical` is proved
outright and does not mention `IsSimpleGroup`. -/
def BinaryLeavittSimplicityClause : Prop :=
  NormalRootDetection → IsSimpleGroup H

/-- The implication is genuine — all the work after a root has been detected is
`RankTwelveEndpoint.normal_eq_top_of_nonzero_elementaryRoot_mem`.  The
antecedent remains an assumption; this theorem asserts nothing about whether
`H` is simple. -/
theorem manuscriptBinaryLeavittSimplicityClause : BinaryLeavittSimplicityClause := by
  intro hdetect
  exact isSimpleGroup_of_normal_root_detection hdetect

/-- The *entire* printed conclusion of `thm:headline`, simplicity included,
under the single named hypothesis `NormalRootDetection`.  The name records the
dependency: this is a conditional statement, and the unconditional content of
the theorem is `manuscriptBinaryLeavittFullRadical`. -/
theorem headlineConclusion_of_normalRootDetection (hdetect : NormalRootDetection) :
    HeadlineConclusion :=
  headlineConclusion_of (manuscriptBinaryLeavittSimplicityClause hdetect)
    rankTwelve_actualCoronaMFResidual_eq_top

end OneSidedMFRadical
end Manuscript
end GroupApproximation
