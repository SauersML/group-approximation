import GroupApproximation.CommutingSoficActions.DiagonalRestriction
import GroupApproximation.CommutingSoficActions.KunThomCosetAction

/-!
# Commuting sofic actions need not combine to a sofic action

Gao–Kunnawalkam Elayavalli–Patchell, arXiv:2401.04945v3, Question 4.2: if
commuting actions `α_i : G_i ↷ X` combine into `α : ⊕_i G_i ↷ X`, is `α` sofic
if and only if every `α_i` is sofic?  The forward direction is their
Proposition 2.15(3).  The theorems below refute the converse.

The witness is `X = (G × G) ⧸ ΔΓ` for the explicit Kun–Thom pair
`Γ = Peripheral ≤ G = Ambient`, with `G × G` acting by left multiplication.
Restricting along `MonoidHom.inl` and `MonoidHom.inr` gives the two commuting
coordinate actions `g · (a, b)ΔΓ = (ga, b)ΔΓ` and `g · (a, b)ΔΓ = (a, gb)ΔΓ`,
and the action they combine to is the given `G × G`-action.  Both coordinate
actions are free and `Ambient` is residually finite, so both are sofic.  The
diagonal orbit of the base coset is the coset `G`-set `G ⧸ Γ`, which is not
sofic, so the combined action is not sofic.  The group `Ambient` is sofic, and
both the group and the set are countable.
-/

namespace GroupApproximation.CommutingSoficActions

open DiagonalCosetAction GroupApproximation.BowenChapman

/-- The set of the counterexample: `(G × G) ⧸ ΔΓ` for the Kun–Thom pair. -/
abbrev KunThomDiagonalCosets : Type := (Ambient × Ambient) ⧸ diagSubgroup Peripheral

theorem kunThomDiagonalCosets_countable : Countable KunThomDiagonalCosets :=
  QuotientGroup.mk_surjective.countable

/-- The first coordinate action is sofic. -/
theorem kunThomDiagonalCosets_isSoficAction_inl :
    @IsSoficAction Ambient _ KunThomDiagonalCosets
      (MulAction.compHom _ (MonoidHom.inl Ambient Ambient)) := by
  haveI : Group.ResiduallyFinite Ambient := ambient_residuallyFinite
  exact isSoficAction_diagonalCosets_inl Peripheral

/-- The second coordinate action is sofic. -/
theorem kunThomDiagonalCosets_isSoficAction_inr :
    @IsSoficAction Ambient _ KunThomDiagonalCosets
      (MulAction.compHom _ (MonoidHom.inr Ambient Ambient)) := by
  haveI : Group.ResiduallyFinite Ambient := ambient_residuallyFinite
  exact isSoficAction_diagonalCosets_inr Peripheral

/-- The combined `G × G`-action is not sofic. -/
theorem kunThomDiagonalCosets_not_isSoficAction :
    ¬ IsSoficAction (Ambient × Ambient) KunThomDiagonalCosets := fun h =>
  not_isSoficAction_ambient_quotient_peripheral
    (isSoficAction_quotient_of_isSoficAction_diagonalCosets Peripheral h)

/-- **Gao–Kunnawalkam Elayavalli–Patchell, Question 4.2: negative answer.**
There are a countable sofic group `G`, a countable set `X` and an action of
`G × G` on `X` whose two coordinate actions of `G` are sofic while the combined
action is not. -/
theorem exists_commuting_sofic_actions_not_sofic :
    ∃ (G X : Type) (_ : Group G) (_ : MulAction (G × G) X),
      Countable G ∧ Countable X ∧ IsSofic G ∧
      @IsSoficAction G _ X (MulAction.compHom X (MonoidHom.inl G G)) ∧
      @IsSoficAction G _ X (MulAction.compHom X (MonoidHom.inr G G)) ∧
      ¬ IsSoficAction (G × G) X :=
  ⟨Ambient, KunThomDiagonalCosets, inferInstance, inferInstance, inferInstance,
    kunThomDiagonalCosets_countable, ambient_isSofic,
    kunThomDiagonalCosets_isSoficAction_inl, kunThomDiagonalCosets_isSoficAction_inr,
    kunThomDiagonalCosets_not_isSoficAction⟩

end GroupApproximation.CommutingSoficActions
