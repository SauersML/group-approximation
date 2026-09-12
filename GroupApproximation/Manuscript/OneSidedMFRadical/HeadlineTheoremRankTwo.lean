import GroupApproximation.Leavitt.BinaryLeavittRankTwoIso
import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequenceRankFour
import GroupApproximation.Meta.AxiomGuard

/-!
# The headline at `EL₂(L_{𝔽₂}(1,2))`

`notes/rank-two-descent-note-2026-09-07.md`, §6, first consequence:

> So the headline transfers to `EL₂` without a rank-two `(T)` or
> normal-structure citation.

With `H₂ = EL₂(L_{𝔽₂}(1,2))` and `H = EL₄(L_{𝔽₂}(1,2))`, the isomorphism
`RankDescent.elementaryRankTwoEquivRankFour` carries every clause of the
rank-four headline to rank two.  Nothing is reproved: simplicity comes from
`RankFourEndpoint.manuscriptPropositionSimple` through
`MulEquiv.isSimpleGroup`, finite generation through `Group.fg_of_surjective`,
and the two MF clauses by composing with the isomorphism.

## Two routes to the MF clauses, and which one is used

The MF clauses are available twice over.  They transfer along the isomorphism,
as everything else does, and they also follow *directly* from
`FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo`, which gives
triviality of every homomorphism out of `EL_n(R)` for every `n ≥ 2` with no
isomorphism in sight.  The transfer route is taken below because it needs no
characteristic hypothesis and no Ershov--Jaikin-Zapirain input at rank two;
the rank-descent route is the one that matters for a general coefficient ring,
where no such isomorphism exists.

## What is not transferred

The maximal-C⋆ clause of the rank-four headline is absent here.  It rests on a
*strict* compression of the corner inside `H`, and carrying that to `H₂` would
need functoriality of `C*_max` along the group isomorphism, which this
repository does not have.  The clause is true at rank two — the note says so —
but it is not proved here, and `PrintedHeadlineRankTwo` accordingly does not
claim it.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open RankFourEndpoint
open ReducedGroupCStarTrace

/-- `H₂ = EL₂(L_{𝔽₂}(1,2))`, the rank-two binary Leavitt elementary group. -/
noncomputable abbrev HTwo : Type := BinaryLeavittSteinberg.ElementaryBase 2

/-- **§6.**  The rank-two and rank-four binary Leavitt elementary groups are
isomorphic. -/
noncomputable def rankTwoEquivRankFour : HTwo ≃* H :=
  RankDescent.elementaryRankTwoEquivRankFour UniversalLeavitt.family

/-! ## The clauses at rank two -/

theorem finitelyGeneratedRankTwo : Group.FG HTwo := by
  haveI : Group.FG H := RankFourEndpoint.finitelyGenerated
  exact Group.fg_of_surjective (f := rankTwoEquivRankFour.symm.toMonoidHom)
    rankTwoEquivRankFour.symm.surjective

theorem countableRankTwo : Countable HTwo :=
  countable_of_fg finitelyGeneratedRankTwo

/-- `H₂` is countable.  The instance is needed to *state* `IsCDEOperatorMF H₂`
and to feed the countability hypothesis of the reduced-C⋆ theorem;
`HeadlineTheoremRankFour` declares the same instance for `H` locally, and a
`local instance` is not exported to importing modules. -/
local instance headlineCountableRankTwo : Countable HTwo := countableRankTwo

/-- `H₂` is nontrivial, witnessed by the same printed coefficient
`q = s₁t₁` as at rank four. -/
theorem nontrivialRankTwo : Nontrivial HTwo :=
  ⟨⟨elementaryRoot (0 : Fin 2) 1 (by decide)
      RankFourEndpoint.leavittFamily.p1, 1,
    LeavittMark.elGen_p1_ne_one RankFourEndpoint.leavittFamily 0 1 (by decide)⟩⟩

/-- Simplicity transfers along the isomorphism; no rank-two normal-structure
theorem is used. -/
theorem isSimpleGroupRankTwo : IsSimpleGroup HTwo := by
  haveI : IsSimpleGroup H := RankFourEndpoint.manuscriptPropositionSimple
  exact rankTwoEquivRankFour.isSimpleGroup

/-- Property `(T)` at rank two is the elementary-base theorem itself, which
already reaches every rank `n ≥ 2`; no citation beyond it is needed. -/
theorem hasKazhdanPropertyTRankTwo : HasKazhdanPropertyT.{0, 0} HTwo :=
  BinaryLeavittSteinberg.elementaryBase_hasKazhdanPropertyT (n := 2) (by omega)

/-- Every homomorphism from `H₂` to a countable MF group is trivial. -/
theorem hom_eq_one_rankTwo (M : Type) [Group M] [Countable M]
    (hM : IsCDEOperatorMF M) (f : HTwo →* M) (x : HTwo) : f x = 1 := by
  obtain ⟨-, -, -, -, hkill, -⟩ := manuscriptBinaryLeavittHeadlineRankFour
  have h := hkill M hM (f.comp rankTwoEquivRankFour.symm.toMonoidHom)
    (rankTwoEquivRankFour x)
  simpa using h

/-- `H₂` is not MF: otherwise its identity homomorphism would be trivial. -/
theorem not_isCDEOperatorMF_rankTwo : ¬ IsCDEOperatorMF HTwo := by
  intro hMF
  obtain ⟨x, y, hxy⟩ := nontrivialRankTwo.exists_pair_ne
  apply hxy
  have hx := hom_eq_one_rankTwo HTwo hMF (MonoidHom.id HTwo) x
  have hy := hom_eq_one_rankTwo HTwo hMF (MonoidHom.id HTwo) y
  simp only [MonoidHom.id_apply] at hx hy
  rw [hx, hy]

/-- The reduced-C⋆ clause at rank two.  It is the general countable-group
statement applied to `H₂`, exactly as at rank four. -/
theorem reducedCStarRankTwo :
    TopologicalSpace.SeparableSpace (ReducedGroupCStar HTwo) ∧
      IsStablyFiniteCStarAlgebra (ReducedGroupCStar HTwo) ∧
        ¬ IsMFAlgebra (ReducedGroupCStar HTwo) := by
  exact reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra HTwo
    not_isCDEOperatorMF_rankTwo

/-! ## The printed statement at rank two -/

/-- **The headline at `H₂ = EL₂(L_{𝔽₂}(1,2))`, as one proposition.**  `H₂` is
finitely generated, nontrivial, simple, has property `(T)`, kills every
homomorphism to a countable MF group, is not MF, and its reduced group
C⋆-algebra is separable and stably finite but not MF.

The maximal-C⋆ clause of the rank-four statement is deliberately absent; see
the module docstring. -/
def PrintedHeadlineRankTwo : Prop :=
  Group.FG HTwo ∧
    Nontrivial HTwo ∧
    IsSimpleGroup HTwo ∧
    HasKazhdanPropertyT.{0, 0} HTwo ∧
    (∀ (M : Type) [Group M] [Countable M],
      IsCDEOperatorMF M → ∀ (f : HTwo →* M) (x : HTwo), f x = 1) ∧
    ¬ IsCDEOperatorMF HTwo ∧
    (TopologicalSpace.SeparableSpace (ReducedGroupCStar HTwo) ∧
      IsStablyFiniteCStarAlgebra (ReducedGroupCStar HTwo) ∧
        ¬ IsMFAlgebra (ReducedGroupCStar HTwo))

theorem manuscriptPrintedHeadlineRankTwo : PrintedHeadlineRankTwo :=
  ⟨finitelyGeneratedRankTwo, nontrivialRankTwo, isSimpleGroupRankTwo,
    hasKazhdanPropertyTRankTwo, hom_eq_one_rankTwo,
    not_isCDEOperatorMF_rankTwo, reducedCStarRankTwo⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical

#audit_closed_axioms manuscriptPrintedHeadlineRankTwo
