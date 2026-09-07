import GroupApproximation.KOne.AllRanksElementary
import GroupApproximation.Manuscript.OneSidedMFRadical.ReducedCStarConsequenceRankFour
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:headline` at the unit group `L_{𝔽₂}(1,2)^×`

`non_mf_groups_exist.tex`, Theorem `thm:headline`, with the headline group
taken to be the whole unit group of the binary Leavitt algebra rather than the
rank-four elementary group.

## The identification is a theorem, not a citation

The two groups are the same group, and this repository proves it outright:

* `BinaryLeavitt.elementaryGroup_eq_top` — `EL_n(L_k(1,2)) = GL_n(L_k(1,2))`
  for every field `k` and every `n ≥ 2`, hypothesis-free.  The chain is rank
  two by Gaussian elimination through the `K₁` refinement loop, then every rank
  by prefix-code self-similarity and block flattening.
* `LeavittFamily.prefixUnitsEquiv` at the four-leaf complete left-comb code
  `leftCombCode 3` — `GL₄(R) ≅ R^×`, an instance of the self-similarity
  `M_r(A) ≅ A` of Proposition `prop:selfsim`.

So `R^× ≅ GL₄(R) = EL₄(R) = H`, and nothing in this module is assumed.  In
particular the identification needs neither the Ara--Goodearl--Pardo
`GE`-ring theorem nor the vanishing of `K₁(L_{𝔽₂}(1,2))` as inputs: those are
the literature route to a statement the development already has.  A citation
here records priority, not a dependency.

## What is transported, and what is not

Every clause of `thm:headline` is invariant under isomorphism of groups, so the
whole of `manuscriptPrintedHeadlineRankFour` moves across `unitsEquivHeadline`.
Three clauses deserve a word.

* The **reduced-C⋆** clause needs no transport of C⋆-algebras at all.
  `reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra` applies to `R^×`
  directly, once `R^×` is known to be countable and not MF; only those two
  group-level facts cross the isomorphism.
* The **maximal-C⋆** clause is `prop:max-infinite` re-run at `R^×`, with the
  printed subgroup and compressor carried over: `unitCorner` is the image of
  the rank-four corner and `unitCompressor` the image of the printed `u`.  The
  strictness `uΓu⁻¹ ⊊ Γ` transports because `Subgroup.map` along an injective
  homomorphism is strictly monotone.
* **Simplicity** is `MulEquiv.isSimpleGroup`, and **finite generation** is
  `Group.fg_of_surjective`; neither needs the Leavitt structure.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace UnitGroupHeadline

open RankFourEndpoint
open ReducedGroupCStarTrace

/-! ## The identification `R^× ≅ H` -/

/-- **`EL₄(R) = GL₄(R)`.**  `BinaryLeavitt.elementaryGroup_eq_top` at the
manuscript's coefficient field `𝔽₂ = ZMod 2` and rank four.  It is proved in
this repository and carries no hypothesis. -/
theorem elementaryGroup_four_eq_top : elementaryGroup (Fin 4) R = ⊤ :=
  BinaryLeavitt.elementaryGroup_eq_top (ZMod 2) 4 (by norm_num)

/-- The headline group is the whole general linear group. -/
noncomputable def headlineEquivGL : H ≃* (Matrix (Fin 4) (Fin 4) R)ˣ :=
  (MulEquiv.subgroupCongr elementaryGroup_four_eq_top).trans Subgroup.topEquiv

/-- **`GL₄(R) ≅ R^×`.**  The self-similarity of `prop:selfsim` at the four-leaf
complete left-comb prefix code. -/
noncomputable def glFourEquivUnits : (Matrix (Fin 4) (Fin 4) R)ˣ ≃* Rˣ :=
  leavittFamily.prefixUnitsEquiv (leftCombCode 3)
    (leavittFamily.leftCombCode_complete 3)

/-- **The printed identification `R^× ≅ EL₄(R)`.** -/
noncomputable def unitsEquivHeadline : Rˣ ≃* H :=
  (headlineEquivGL.trans glFourEquivUnits).symm

/-- `R^×` is countable, being isomorphic to the countable group `H`. -/
local instance unitsCountable : Countable Rˣ :=
  haveI : Countable H := RankFourEndpoint.countable
  Countable.of_equiv H unitsEquivHeadline.symm.toEquiv

/-! ## The printed configuration, carried to the unit group -/

/-- The image of the printed corner `L = EL₃(R)` in `R^×`. -/
noncomputable def unitCorner : Subgroup Rˣ :=
  corner.map unitsEquivHeadline.symm.toMonoidHom

/-- The image of the printed compressor `u` in `R^×`. -/
noncomputable def unitCompressor : Rˣ := unitsEquivHeadline.symm u

theorem unitCorner_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} ↥unitCorner :=
  HasKazhdanPropertyT.of_mulEquiv
    (MulEquiv.subgroupMap unitsEquivHeadline.symm corner).symm
    corner_hasKazhdanPropertyT

/-- **The compression stays strict at the unit group.**  `Subgroup.map` along
an injective homomorphism is strictly monotone, and conjugation by the image of
`u` is the image of conjugation by `u`. -/
theorem unitCorner_conj_lt :
    unitCorner.map (MulAut.conj unitCompressor).toMonoidHom < unitCorner := by
  have hcomp : ((MulAut.conj unitCompressor).toMonoidHom).comp
      unitsEquivHeadline.symm.toMonoidHom =
      (unitsEquivHeadline.symm.toMonoidHom).comp
        (MulAut.conj u).toMonoidHom := by
    refine MonoidHom.ext fun x ↦ ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, unitCompressor, map_mul, map_inv]
  rw [unitCorner, Subgroup.map_map, hcomp, ← Subgroup.map_map]
  exact (Subgroup.map_lt_map_iff_of_injective
    unitsEquivHeadline.symm.injective).mpr u_conj_corner_lt

/-! ## The printed theorem at the unit group -/

/-- **`thm:headline` with `H = L_{𝔽₂}(1,2)^×`, as one proposition.**

`H` is finitely generated, nontrivial, simple, has property `(T)`, and
`Rad_MF(H) = H` — equivalently every homomorphism from `H` to an MF group is
trivial, so in particular `H` is not MF.  Its reduced group C⋆-algebra is
separable and stably finite but is not MF, and its maximal group C⋆-algebra is
not finite: it contains a proper isometry, witnessed by the Kazhdan projection
that the canonical unitary of the printed compressor moves strictly.

The clauses are in printed order, and each is the same clause
`PrintedHeadlineRankFour` carries at `EL₄(R)`. -/
def PrintedUnitGroupHeadline : Prop :=
  Group.FG Rˣ ∧
    Nontrivial Rˣ ∧
    IsSimpleGroup Rˣ ∧
    HasKazhdanPropertyT.{0, 0} Rˣ ∧
    actualCoronaMFResidual Rˣ = ⊤ ∧
    (∀ (M : Type) [Group M] [Countable M],
        IsCDEOperatorMF M → ∀ (f : Rˣ →* M) (x : Rˣ), f x = 1) ∧
    ¬ IsCDEOperatorMF Rˣ ∧
    (TopologicalSpace.SeparableSpace (ReducedGroupCStar Rˣ) ∧
      IsStablyFiniteCStarAlgebra (ReducedGroupCStar Rˣ) ∧
      ¬ IsMFAlgebra (ReducedGroupCStar Rˣ)) ∧
    ((∃ P : MaximalGroupCStar Rˣ,
        IsSelfAdjoint P ∧
        P * P = P ∧
        (maximalGroupCStarGenerator Rˣ unitCompressor * P *
            star (maximalGroupCStarGenerator Rˣ unitCompressor)) * P = P ∧
        P * (maximalGroupCStarGenerator Rˣ unitCompressor * P *
            star (maximalGroupCStarGenerator Rˣ unitCompressor)) = P ∧
        maximalGroupCStarGenerator Rˣ unitCompressor * P *
            star (maximalGroupCStarGenerator Rˣ unitCompressor) ≠ P) ∧
      ¬ IsDedekindFiniteMonoid (MaximalGroupCStar Rˣ) ∧
      ¬ IsStablyFiniteRing (MaximalGroupCStar Rˣ))

/-- **The printed theorem at the unit group, proved, hypothesis-free.** -/
theorem manuscriptPrintedUnitGroupHeadline : PrintedUnitGroupHeadline := by
  obtain ⟨hFG, hconc, -, -⟩ := manuscriptPrintedHeadlineRankFour
  obtain ⟨hnt, hsimple, hT, hres, hkill, -⟩ := hconc
  haveI : Group.FG H := hFG
  haveI : Nontrivial H := hnt
  haveI : IsSimpleGroup H := hsimple
  -- the transported group-level clauses
  have hFGu : Group.FG Rˣ :=
    Group.fg_of_surjective (f := unitsEquivHeadline.symm.toMonoidHom)
      unitsEquivHeadline.symm.surjective
  have hntu : Nontrivial Rˣ := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne H
    exact ⟨⟨unitsEquivHeadline.symm x, unitsEquivHeadline.symm y,
      fun h ↦ hxy (unitsEquivHeadline.symm.injective h)⟩⟩
  haveI : Nontrivial Rˣ := hntu
  have hsimpleu : IsSimpleGroup Rˣ := unitsEquivHeadline.isSimpleGroup
  have hTu : HasKazhdanPropertyT.{0, 0} Rˣ :=
    HasKazhdanPropertyT.of_mulEquiv unitsEquivHeadline hT
  have hresu : actualCoronaMFResidual Rˣ = ⊤ :=
    actualCoronaMFResidual_eq_top_of_mulEquiv unitsEquivHeadline.symm hres
  have hkillu : ∀ (M : Type) [Group M] [Countable M],
      IsCDEOperatorMF M → ∀ (f : Rˣ →* M) (x : Rˣ), f x = 1 := by
    intro M _ _ hM f x
    have h := hkill M hM (f.comp unitsEquivHeadline.symm.toMonoidHom)
      (unitsEquivHeadline x)
    simpa using h
  have hnotu : ¬ IsCDEOperatorMF Rˣ :=
    not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top hresu
  -- the two C⋆ clauses
  have hred := reducedGroupCStar_separable_stablyFinite_not_isMFAlgebra Rˣ hnotu
  have hmax :=
    MaximalCStarPrintedHypotheses.manuscriptMaximalCStarRemarkFromPrintedHypotheses
      Rˣ unitCorner unitCompressor unitCorner_hasKazhdanPropertyT
      unitCorner_conj_lt
  exact ⟨hFGu, hntu, hsimpleu, hTu, hresu, hkillu, hnotu, hred,
    hmax.1, hmax.2.1, hmax.2.2.1⟩

end UnitGroupHeadline
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.UnitGroupHeadline.manuscriptPrintedUnitGroupHeadline
