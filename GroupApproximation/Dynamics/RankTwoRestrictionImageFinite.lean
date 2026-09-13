import GroupApproximation.Dynamics.RankTwoCoreImageHaagerup
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-two restriction images are finite

`non_mf_groups_exist.tex`, `sec:chain-core`, the remark after `cor:dynamic-rank-budget`
(tex 1796–1798):

> Its finitely generated restriction image lies in a finite product of groups
> $\GL_2(k[z,z^{-1}])$, hence in a Haagerup group by~\cite[Theorem~4]{GHW}, and is finite.

The image of a Kazhdan subgroup under a homomorphism is Kazhdan and finitely generated, hence
countable; when every countable subgroup of the target is Haagerup, the image is finite
(`finite_map_of_kazhdan_of_haagerup`, through Delorme).  With the closed image steps of
`RankTwoCoreImageHaagerup` this is the printed sentence, closed, for `GL_2(R_X)` over a fixed core
(`printedFixedCoreRestrictionImageFinite`), and for `R_X^×` when every core point has period at
most two (`printedPeriodTwoCoreUnitRestrictionImageFinite`).  Neither uses the remaining kernel.
-/

namespace GroupApproximation
namespace ChainCore
namespace RankTwoLimit

open Haagerup Dynamics

/-- A Kazhdan subgroup has finite image in a group whose countable subgroups are Haagerup. -/
theorem finite_map_of_kazhdan_of_haagerup {G K : Type} [Group G] [Group K] (φ : G →* K)
    (hHaag : ∀ M : Subgroup K, Countable M → HasHaagerupProperty.{0, 0} M)
    (L : Subgroup G) (hL : HasKazhdanPropertyT.{0, 0} L) : Finite (L.map φ) := by
  have hTM : HasKazhdanPropertyT.{0, 0} (L.map φ) :=
    HasKazhdanPropertyT.of_surjective (φ.subgroupMap L) (φ.subgroupMap_surjective L) hL
  haveI : Group.FG (L.map φ) := KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT _ hTM
  exact finite_of_hasKazhdanPropertyT_of_hasHaagerupProperty hTM
    (hHaag _ (Manuscript.OneSidedMFRadical.JacobsonRankTwo.countable_of_groupFG inferInstance))

/-- **Printed (tex 1796–1798), fixed core.**  "Its finitely generated restriction image lies in a
finite product of groups $\GL_2(k[z,z^{-1}])$, hence in a Haagerup group
by~\cite[Theorem~4]{GHW}, and is finite." -/
def PrintedFixedCoreRestrictionImageFinite : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] [Finite k], (∀ y ∈ chainRecurrentSet T, T y = y) →
      ∀ H : Subgroup (GL (Fin 2) (ClopenCrossedProduct T k)), HasKazhdanPropertyT.{0, 0} H →
        Finite (H.map (glMap (Fin 2) (ClopenCrossedProduct.restrict T k (image_chainRecurrentSet T))))

theorem printedFixedCoreRestrictionImageFinite : PrintedFixedCoreRestrictionImageFinite := by
  intro X _ _ _ T k _ _ hfix H hH
  have hY := image_chainRecurrentSet T
  exact finite_map_of_kazhdan_of_haagerup _
    (fixedCoreImageHaagerup _ (ClopenCrossedProduct.restrictHomeo T hY) k fun y ↦
      Subtype.ext (hfix y y.2)) H hH

/-- **Printed (tex 1802–1805), core periods at most two.**  The restriction image in `R_Y^×` of a
Kazhdan subgroup of `R_X^×` is finite. -/
def PrintedPeriodTwoCoreUnitRestrictionImageFinite : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] (T : X ≃ₜ X)
    (k : Type) [Field k] [Finite k], (∀ y ∈ chainRecurrentSet T, T (T y) = y) →
      ∀ H : Subgroup (ClopenCrossedProduct T k)ˣ, HasKazhdanPropertyT.{0, 0} H →
        Finite (H.map (Units.map
          (ClopenCrossedProduct.restrict T k (image_chainRecurrentSet T) :
            ClopenCrossedProduct T k →*
              ClopenCrossedProduct (ClopenCrossedProduct.restrictHomeo T (image_chainRecurrentSet T)) k)))

theorem printedPeriodTwoCoreUnitRestrictionImageFinite :
    PrintedPeriodTwoCoreUnitRestrictionImageFinite := by
  intro X _ _ _ T k _ _ hper H hH
  have hY := image_chainRecurrentSet T
  exact finite_map_of_kazhdan_of_haagerup _
    (periodTwoCoreUnitImageHaagerup _ (ClopenCrossedProduct.restrictHomeo T hY) k fun y ↦
      Subtype.ext (hper y y.2)) H hH

end RankTwoLimit
end ChainCore
end GroupApproximation

#audit_axioms GroupApproximation.ChainCore.RankTwoLimit.finite_map_of_kazhdan_of_haagerup
#audit_closed_axioms GroupApproximation.ChainCore.RankTwoLimit.printedFixedCoreRestrictionImageFinite
#audit_closed_axioms GroupApproximation.ChainCore.RankTwoLimit.printedPeriodTwoCoreUnitRestrictionImageFinite
