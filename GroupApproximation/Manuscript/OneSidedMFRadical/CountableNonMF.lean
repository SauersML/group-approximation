import GroupApproximation.Manuscript.OneSidedMFRadical.HeadlineTheorem

/-!
# The abstract's headline: some countable group is not MF

`non_mf_groups_exist.tex`, abstract — "The resulting group is simple, has
property~(T), and every homomorphism from it to an MF group is trivial.  In
particular, not every countable group is MF." — together with the sentence of
Theorem `thm:headline` that the abstract is summarising.

`HeadlineTheorem.manuscriptBinaryLeavittFullRadical` does all of the work, for
the one group `H = EL₁₂(L_{𝔽₂}(1,2))`.  What this module adds is the *shape*
the abstract and the introduction use: statements about no particular group,
each with every quantifier inside a single named proposition, so that a reader
can `#check` one name against one printed sentence.

* `CountableNonMFGroupExists` — there is a countable group that is not MF.
* `NotEveryCountableGroupIsMF` — the same sentence written as the refutation
  of the universal statement it denies.
* `CountableNonOperatorMFGroupExists` — the same existence statement for the
  repository's other reading of MF-ness, `IsOperatorMF`.
* `CountableKazhdanFullMFRadicalGroupExists` — the abstract's realisation
  sentence: a countable nontrivial Kazhdan group whose MF radical is
  everything.
* `SaturatedDefectKillsMFTargets` — "if the defect fills the ambient group,
  every homomorphism to an MF group is trivial", which is
  `thm:compression-criterion` composed with the closure sentence that follows
  the displayed conclusion of Theorem~A.

## Simplicity is not claimed anywhere below

The abstract's realisation sentence begins "The resulting group is simple".
That clause has no proof in this development: the manuscript obtains it from
Preusser's normal-subgroup theorem, from pure infiniteness and the exchange
property of `L_{𝔽₂}(1,2)`, and from the centre computation for that algebra,
and none of those inputs exist in this repository.  `HeadlineTheorem` records
the exact missing input as `NormalRootDetection` and the implication it would
buy as `BinaryLeavittSimplicityClause`; that implication is an assumption in
leading position and is proved only as an implication.

`CountableKazhdanFullMFRadicalGroupExists` therefore omits the simplicity
clause and claims only what is proved — countable, nontrivial, property `(T)`,
full MF radical.  Nothing in this module mentions `IsSimpleGroup`, and nothing
in this module uses simplicity: the route from the printed defect `d = e₀₂(q)`
to `Rad_MF(H) = H` runs through `normalClosure_defect_eq_top`, not through a
normal-subgroup theorem.  Reading any statement below as evidence that `H` is
simple would be a mistake.

## This is not the soficity headline

`GroupApproximation.CountableNonsoficGroupExists` (`Endpoint/MainResults`) has
the same shape and a different subject.  Its predicate is `IsSofic`, its
witness is `EL₄(L_{𝔽₂}(1,2))`, and it belongs to the soficity manuscript.  The
predicate here is `IsCDEOperatorMF`, the literal CDE definition of an MF group,
and the witness is `EL₁₂(L_{𝔽₂}(1,2))`.  Neither statement is derived from the
other anywhere in this development, and neither is offered as evidence for the
other.

## Why countability is a binder and not a conjunct

`IsCDEOperatorMF` takes `[Countable G]` as an instance argument, so
`Countable G ∧ ¬ IsCDEOperatorMF G` does not elaborate — the second conjunct
would have no instance to use.  The existentials below bind countability
instead, `∃ (_ : Countable G), …`, which is the same proposition and is the
form the rest of the repository already uses for MF statements
(`HilbertHotel.Endpoint.NonsoficFullMFRadicalGroupExists`).
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankTwelveEndpoint

/-- `H = EL₁₂(L_{𝔽₂}(1,2))` is countable.  The instance is needed to *state*
`IsCDEOperatorMF H`; `HeadlineTheorem` declares the same instance locally, and
a `local instance` is not exported to importing modules. -/
local instance countableNonMFCountable : Countable H :=
  RankTwelveEndpoint.countable

/-! ## The headline sentence of the abstract -/

/-- **"Not every countable group is MF", as an existence statement.**  There is
a countable group that is not MF, in the literal CDE sense of
`IsCDEOperatorMF`.

Countability is bound rather than conjoined because `IsCDEOperatorMF` consumes
it as an instance; `∃ (_ : Countable G), P` is the proposition
`Countable G ∧ P`. -/
def CountableNonMFGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Countable G), ¬ IsCDEOperatorMF G

/-- **The headline, proved.**  The witness is the manuscript's own group
`H = EL₁₂(L_{𝔽₂}(1,2))`, and the single input is
`manuscriptBinaryLeavittFullRadical`, whose last clause is exactly the failure
of MF-ness.  The printed simplicity clause is used nowhere on this route. -/
theorem manuscriptCountableNonMFGroupExists : CountableNonMFGroupExists := by
  obtain ⟨-, -, -, -, -, -, hnot⟩ := manuscriptBinaryLeavittFullRadical
  exact ⟨H, inferInstance, RankTwelveEndpoint.countable, hnot⟩

/-- **The same sentence, as the refutation it is.**  It is not the case that
every countable group is MF. -/
def NotEveryCountableGroupIsMF : Prop :=
  ¬ ∀ (G : Type) [Group G] [Countable G], IsCDEOperatorMF G

/-- **The universal statement is false.**  Instantiating it at
`H = EL₁₂(L_{𝔽₂}(1,2))` contradicts the last clause of
`manuscriptBinaryLeavittFullRadical`. -/
theorem manuscriptNotEveryCountableGroupIsMF : NotEveryCountableGroupIsMF := by
  intro hall
  obtain ⟨-, -, -, -, -, -, hnot⟩ := manuscriptBinaryLeavittFullRadical
  exact hnot (hall H)

/-- **The headline at the repository's other reading of MF-ness.**  There is a
countable group admitting no faithful representation in the unitary-sequence
quotient of a cofinite norm matrix corona.

`isCDEOperatorMF_iff_isOperatorMF` makes the two readings equivalent for
countable groups, so this is the same mathematics stated against
`IsOperatorMF`, which places no countability restriction of its own. -/
def CountableNonOperatorMFGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Countable G), ¬ IsOperatorMF G

/-- The other reading, proved at the same witness. -/
theorem manuscriptCountableNonOperatorMFGroupExists :
    CountableNonOperatorMFGroupExists := by
  obtain ⟨-, -, -, -, -, -, hnot⟩ := manuscriptBinaryLeavittFullRadical
  refine ⟨H, inferInstance, RankTwelveEndpoint.countable, ?_⟩
  intro hMF
  exact hnot ((isCDEOperatorMF_iff_isOperatorMF H).mpr hMF)

/-! ## The abstract's realisation sentence, minus simplicity -/

/-- **A countable Kazhdan group whose MF radical is the whole group.**  The
four clauses are countability, nontriviality, property `(T)`, and
`Rad_MF(G) = G` at the manuscript's literal natural-dimension radical
`manuscriptCoronaMFResidual`.

The printed adjective *simple* is deliberately absent from this list; see the
module docstring for what it would take to add it, and for why no statement in
this module needs it. -/
def CountableKazhdanFullMFRadicalGroupExists : Prop :=
  ∃ (G : Type) (_ : Group G),
    Countable G ∧ Nontrivial G ∧ HasKazhdanPropertyT.{0, 0} G ∧
      manuscriptCoronaMFResidual G = ⊤

/-- **The realisation, proved.**  Every clause is a clause of
`manuscriptBinaryLeavittFullRadical` at `H = EL₁₂(L_{𝔽₂}(1,2))`. -/
theorem manuscriptCountableKazhdanFullMFRadicalGroupExists :
    CountableKazhdanFullMFRadicalGroupExists := by
  obtain ⟨hcount, hne, hT, hman, -, -, -⟩ := manuscriptBinaryLeavittFullRadical
  exact ⟨H, inferInstance, hcount, hne, hT, hman⟩

/-! ## The abstract's criterion sentence

"A one-sided self-compression of a property (T) subgroup forces a canonically
defined normal subgroup into the MF radical.  Normal generation can then force
the MF radical to be the whole group." — and then, from Section 1, a full
radical kills every homomorphism to an MF group. -/

/-- **Saturated defect ⇒ every MF-target homomorphism is trivial.**  For a
countable Kazhdan group `G` and a property-`(T)` subgroup `L`, if the printed
defect `𝔇_G(L)` fills `G` then

* `Rad_MF(G) = G`;
* every homomorphism from `G` to a countable MF group is trivial; and
* if `G` is nontrivial, `G` itself is not MF.

The third clause carries `Nontrivial G` as an explicit hypothesis because it
genuinely needs it: the trivial group has `⊤ = ⊥` and is MF.

This is `thm:compression-criterion`, third clause, composed with
`manuscriptFullRadicalKillsMFTargets`.  It is stated over an arbitrary
countable Kazhdan group, so it says nothing about `EL₁₂(L_{𝔽₂}(1,2))` in
particular; the rank-twelve instance is `manuscriptBinaryLeavittFullRadical`. -/
def SaturatedDefectKillsMFTargets : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L → HasKazhdanPropertyT.{0, 0} G →
      printedDefect L = ⊤ →
        manuscriptCoronaMFResidual G = ⊤ ∧
          (∀ (M : Type) [Group M] [Countable M],
              IsCDEOperatorMF M → ∀ (f : G →* M) (x : G), f x = 1) ∧
          (Nontrivial G → ¬ IsCDEOperatorMF G)

/-- The composition, proved.  The first clause is the saturated case of
`manuscriptOneSidedCompressionCriterion`, the second is
`manuscriptFullRadicalKillsMFTargets` fed with it, and the third is the
transfer to the basis-free radical followed by
`not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top`. -/
theorem manuscriptSaturatedDefectKillsMFTargets :
    SaturatedDefectKillsMFTargets := by
  intro G _ _ L hL hG hD
  have hfull : manuscriptCoronaMFResidual G = ⊤ :=
    (manuscriptOneSidedCompressionCriterion G L hL).2.2 hG hD
  refine ⟨hfull, ?_, ?_⟩
  · intro M _ _ hM f x
    exact manuscriptFullRadicalKillsMFTargets G M hfull hM f x
  · intro hne
    haveI : Nontrivial G := hne
    have hactual : actualCoronaMFResidual G = ⊤ := by
      rw [← manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
      exact hfull
    exact not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top hactual

end OneSidedMFRadical
end Manuscript
end GroupApproximation
