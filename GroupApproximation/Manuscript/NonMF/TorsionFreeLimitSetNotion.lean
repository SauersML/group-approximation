import GroupApproximation.GGT.AcylindricallyHyperbolicLimitSetEasy
import GroupApproximation.Manuscript.NonMF.TorsionFreeSectionSentences
import GroupApproximation.Meta.AxiomGuard

/-!
# `sec:torsion-free` at the limit-set notion of acylindrical hyperbolicity

The manuscript's *acylindrically hyperbolic* is Osin's: a group with an
acylindrical isometric action on a geodesic hyperbolic space whose limit set has
more than two points, `GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet`.
This module restates the printed endpoints of `sec:torsion-free` at that notion
and derives each from the landed statements at Hull's Cayley-graph notion:

* where acylindrical hyperbolicity is a **conclusion** (`thm:torsion-free`, the
  quotient of `thm:hull`, the quotient of `lem:saturation`,
  `cor:regular-nonmf-algebra`), through the easy direction of Osin's Theorem 1.1,
  `GGT.SequentialBoundary.isAcylindricallyHyperbolicLimitSet_of_isAcylindricallyHyperbolic`;
* `thm:hull` needs nothing more, since a Hull generating set already makes `G`
  acylindrically hyperbolic (`HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet`);
* where it is a **hypothesis** on a group given without a generating set
  (`lem:saturation`, and the choice of Hull's generating set at tex line 1629),
  through the hard direction of Osin's Theorem 1.1, taken as the hypothesis
  `hhard : ∀ G, IsAcylindricallyHyperbolicLimitSet G → IsAcylindricallyHyperbolicOsin G`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TorsionFreeLimitSetNotion

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.TorsionFreePrinted
open GroupApproximation.ReducedGroupCStarTrace
open GroupApproximation.GroupVonNeumann

/-! ## `thm:torsion-free` -/

/-- **`thm:torsion-free`, as printed, at the limit-set notion** (tex line 284). -/
def PrintedTorsionFreeTheoremLimitSet : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
      GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet Q ∧
        HasKazhdanPropertyT.{0, 0} Q ∧
        (∀ (M : Type) (_ : Group M), IsOperatorMF M →
          ∀ (f : Q →* M) (x : Q), f x = 1) ∧
        (∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
          Nontrivial L → ¬ IsOperatorMF L)

/-- The printed theorem at the Cayley-graph notion gives it, by the easy direction
of Osin's Theorem 1.1. -/
theorem printedTorsionFreeTheoremLimitSet_of_printed (h : PrintedTorsionFreeTheorem) :
    PrintedTorsionFreeTheoremLimitSet := by
  obtain ⟨Q, instQ, hgen, hfp, htf, hah, hrest⟩ := h
  exact ⟨Q, instQ, hgen, hfp, htf,
    @GGT.SequentialBoundary.isAcylindricallyHyperbolicLimitSet_of_isAcylindricallyHyperbolic
      Q instQ hah, hrest⟩

/-! ## Hull's generating set and `thm:hull` -/

/-- **"choose the generating set `A` provided by Hull [Theorem 3.12]"** (tex line
1629), for a group acylindrically hyperbolic at the limit-set notion, through the
hard direction of Osin's Theorem 1.1. -/
theorem manuscriptSentence_hullGeneratingSetLimitSet
    (hhard : ∀ (G : Type) [Group G],
      GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G →
        GGT.IsAcylindricallyHyperbolicOsin G)
    (G : Type) [Group G] (hG : GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G) :
    Nonempty (HullGeneratingSet G) :=
  GGT.exists_hullGeneratingSet_of_osin G (hhard G hG)

/-- **`thm:hull`, as printed, at the limit-set notion** (tex lines 1624–1628). -/
def PrintedHullSmallCancellationLimitSet : Prop :=
  ∀ (G : Type) [Group G], GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G →
    ∀ (A : HullGeneratingSet G) {N : Subgroup G}, Suitable A.alphabet N →
      ∀ {m : ℕ} (g : Fin m → G),
        ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
          GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet Q ∧
            (∀ i : Fin m, φ (g i) ∈ N.map φ) ∧
              ∀ y : Q, IsOfFinOrder y → ∃ x : G, φ x = y ∧ orderOf x = orderOf y

/-- The printed theorem at the Cayley-graph notion gives it.  Hull's generating
set makes `G` acylindrically hyperbolic, and the quotient's notion transfers by the
easy direction of Osin's Theorem 1.1. -/
theorem printedHullSmallCancellationLimitSet_of_current
    (h : TorsionFreeSectionSentences.PrintedHullSmallCancellationCurrent.{0}) :
    PrintedHullSmallCancellationLimitSet := by
  intro G _ _hG A N hN m g
  haveI : IsAcylindricallyHyperbolic G :=
    HullSC.isAcylindricallyHyperbolic_of_hullGeneratingSet A
  obtain ⟨H⟩ := h A hN g
  exact ⟨H.Q, H.group, H.q, H.surjective,
    @GGT.SequentialBoundary.isAcylindricallyHyperbolicLimitSet_of_isAcylindricallyHyperbolic
      H.Q H.group H.acylindricallyHyperbolic,
    H.mem_map, H.finiteOrder_lift⟩

/-! ## `lem:saturation` -/

/-- **`lem:saturation`, as printed, at the limit-set notion** (tex line 1650). -/
def PrintedSaturationLimitSet : Prop :=
  ∀ (G : Type) [Group G] [Group.IsFinitelyPresented G],
    GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G → IsPowerTorsionFree G →
      ∀ (N : Subgroup G) [N.Normal], N ≠ ⊥ →
        ∃ (Q : Type) (_ : Group Q) (φ : G →* Q), Function.Surjective φ ∧
          IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
            GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet Q ∧ N.map φ = ⊤

/-- The printed lemma at the Cayley-graph notion gives it, with the hard direction
of Osin's Theorem 1.1 on the hypothesis and the easy direction on the
conclusion. -/
theorem printedSaturationLimitSet_of_noOmega
    (hhard : ∀ (G : Type) [Group G],
      GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet G →
        GGT.IsAcylindricallyHyperbolicOsin G)
    (h : PrintedSaturationNoOmega.{0}) : PrintedSaturationLimitSet := by
  intro G _ _ hG htf N _ hN
  haveI : IsAcylindricallyHyperbolic G := GGT.isAcylindricallyHyperbolic_of_osin (hhard G hG)
  obtain ⟨S⟩ := h G htf N hN
  exact ⟨S.Q, S.group, S.q, S.surjective, ⟨S.generatorOne, S.generatorTwo, S.twoGenerated⟩,
    S.finitelyPresented, S.torsionFree,
    @GGT.SequentialBoundary.isAcylindricallyHyperbolicLimitSet_of_isAcylindricallyHyperbolic
      S.Q S.group S.acylindricallyHyperbolic,
    S.map_eq_top⟩

/-! ## `cor:regular-nonmf-algebra` -/

/-- **`cor:regular-nonmf-algebra`, as printed, at the limit-set notion** (tex line
1718); the group clause records the properties the printed proof uses. -/
def PrintedRegularNonMFAlgebraLimitSet : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    Countable Q ∧ IsPowerTorsionFree Q ∧
      GGT.SequentialBoundary.IsAcylindricallyHyperbolicLimitSet Q ∧
      IsTwoGenerated Q ∧
        TopologicalSpace.SeparableSpace (ReducedGroupCStar Q) ∧
          (1 : ReducedGroupCStar Q) ≠ 0 ∧
            (∃ g₁ g₂ : Q, Subgroup.closure ({g₁, g₂} : Set Q) = ⊤ ∧
              leftRegularOperator Q g₁ ∈
                  unitary (GroupHilbert Q →L[ℂ] GroupHilbert Q) ∧
                leftRegularOperator Q g₂ ∈
                  unitary (GroupHilbert Q →L[ℂ] GroupHilbert Q) ∧
                  (StarAlgebra.adjoin ℂ
                    ({leftRegularOperator Q g₁, leftRegularOperator Q g₂} :
                      Set (GroupHilbert Q →L[ℂ] GroupHilbert Q))).topologicalClosure
                    = reducedGroupCStarSubalgebra Q) ∧
              IsSimpleCStar (ReducedGroupCStar Q) ∧
                HasUniqueTracialState (ReducedGroupCStar Q) ∧
                  IsStableRankOne (ReducedGroupCStar Q) ∧
                    IsStablyFiniteCStarAlgebra (ReducedGroupCStar Q) ∧
                      ¬ IsMFAlgebra (ReducedGroupCStar Q)

/-- The printed corollary at the Cayley-graph notion gives it, by the easy
direction of Osin's Theorem 1.1. -/
theorem printedRegularNonMFAlgebraLimitSet_of_printed (h : PrintedRegularNonMFAlgebra) :
    PrintedRegularNonMFAlgebraLimitSet := by
  obtain ⟨Q, instQ, hc, htf, hah, hrest⟩ := h
  exact ⟨Q, instQ, hc, htf,
    @GGT.SequentialBoundary.isAcylindricallyHyperbolicLimitSet_of_isAcylindricallyHyperbolic
      Q instQ hah, hrest⟩

end TorsionFreeLimitSetNotion
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetNotion.printedTorsionFreeTheoremLimitSet_of_printed
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetNotion.manuscriptSentence_hullGeneratingSetLimitSet
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetNotion.printedHullSmallCancellationLimitSet_of_current
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetNotion.printedSaturationLimitSet_of_noOmega
#audit_axioms GroupApproximation.Manuscript.NonMF.TorsionFreeLimitSetNotion.printedRegularNonMFAlgebraLimitSet_of_printed
