import GroupApproximation.CommutingSoficActions.FreeActionSofic
import GroupApproximation.Sofic.SoficActionEmbedding

/-!
# A sofic combined action restricts to a sofic coset action

Let `G × G` act on `X = (G × G) ⧸ ΔH` by left multiplication.  Restricting
along the diagonal `G →* G × G` keeps the action sofic (`IsSoficAction.compHom`,
Proposition 2.15(3) of arXiv:2401.04945v3).  The map `gH ↦ (g, g)ΔH` is an
injective equivariant map from `G ⧸ H` into this restriction
(`DiagonalCosetAction.diagOrbitMap`), so the coset action `G ↷ G ⧸ H` is
sofic too (`IsSoficAction.of_equivariant_injective`, Proposition 2.15(2)).

Consequently a residually finite `G` with a nonsofic coset action `G ↷ G ⧸ H`
gives two commuting sofic actions on `X`, the coordinate actions, whose
combination is not sofic (`diagonalCosets_counterexample`).
-/

namespace GroupApproximation.CommutingSoficActions

open DiagonalCosetAction

universe u

variable {G : Type u} [Group G] (H : Subgroup G)

/-- If `G × G ↷ (G × G) ⧸ ΔH` is sofic, then so is `G ↷ G ⧸ H`. -/
theorem isSoficAction_quotient_of_isSoficAction_diagonalCosets
    (h : IsSoficAction (G × G) ((G × G) ⧸ diagSubgroup H)) :
    IsSoficAction G (G ⧸ H) := by
  letI : MulAction G ((G × G) ⧸ diagSubgroup H) :=
    MulAction.compHom _ ((MonoidHom.id G).prod (MonoidHom.id G))
  exact IsSoficAction.of_equivariant_injective (diagOrbitMap H)
    (diagOrbitMap_injective H) (fun k x => diagOrbitMap_smul H k x)
    (IsSoficAction.compHom ((MonoidHom.id G).prod (MonoidHom.id G)) h)

/-- **The diagonal-coset counterexample.**  If `G` is residually finite and the
coset action `G ↷ G ⧸ H` is not sofic, then both coordinate actions of `G` on
`(G × G) ⧸ ΔH` are sofic and the combined `G × G`-action is not. -/
theorem diagonalCosets_counterexample [Group.ResiduallyFinite G]
    (hbad : ¬ IsSoficAction G (G ⧸ H)) :
    @IsSoficAction G _ ((G × G) ⧸ diagSubgroup H)
        (MulAction.compHom _ (MonoidHom.inl G G)) ∧
      @IsSoficAction G _ ((G × G) ⧸ diagSubgroup H)
        (MulAction.compHom _ (MonoidHom.inr G G)) ∧
      ¬ IsSoficAction (G × G) ((G × G) ⧸ diagSubgroup H) :=
  ⟨isSoficAction_diagonalCosets_inl H, isSoficAction_diagonalCosets_inr H,
    fun h => hbad (isSoficAction_quotient_of_isSoficAction_diagonalCosets H h)⟩

end GroupApproximation.CommutingSoficActions
