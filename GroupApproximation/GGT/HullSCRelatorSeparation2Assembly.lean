import GroupApproximation.GGT.HullSCRelatorSeparation2FillingData

/-!
# The rotating data of Theorem 5.1, from the cone-off along a family

Every geometric clause `HullSC.RotatingDataGeo₂` asks for is now available for a
family: the three rotating-family axioms
(`HullSC.isRotatingFamily_apexRotFamily`), separation and very rotation
(`GGT/HullSCRelatorSeparation2Filling.lean`), and what the rotations generate.
This module assembles them.

One argument is carried rather than read off the cone-off.  The rotating data is
indexed by a single element `w`, and which element a family kills is a property
of *which* subgroups were chosen and not of the geometry, so `hclosure` --
that the normal closure of the family is the normal closure of the relator -- is
supplied.  Over one subgroup the corresponding step is
`HullSC.normalClosure_zpowers`.

Everything else is read off `HullSC.ConeOffData₂` directly, and the two clauses
that are Hull's §5 rather than DGO's line up without translation.
`kernel_moves_base` is the same statement about the same subgroup, because
`rotationNormalClosure_apexRotFamily` identifies what the rotations generate
with the normal closure of the union -- that is why `ConeOffData₂` states its
injectivity radius against that union -- and `finiteOrder_lift` travels along
`hclosure`, the only place the relator is named.  That second clause is here
rather than on the quotient because the statement carrying it there is refuted;
see issue #50 and `GGT/DGORotatingQuotientRefutation.lean`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-- **The rotating data, from the cone-off along a family.**  Every field is
read off `HullSC.ConeOffData₂` or proved from it; only the identification of
what the family kills is supplied. -/
def ConeOffData₂.toRotatingDataGeo {G : Type u} [Group G] {Λ : Type v}
    {A : Alphabet G} {K : Λ → Subgroup G} {L : ℝ} (P : ConeOffData₂ A K L)
    (w : G)
    (hclosure : Subgroup.normalClosure (⋃ lam : Λ, (K lam : Set G))
      = Subgroup.normalClosure ({w} : Set G)) :
    RotatingDataGeo₂ A w L where
  Space := P.Space
  metric := P.metric
  action := P.action
  base := P.base
  letter_dist := P.letter_dist
  delta := P.delta
  delta_pos := P.delta_pos
  hyperbolic := P.hyperbolic
  isGeodesic := P.isGeodesic
  sep := P.sep
  sep_ge := P.sep_ge
  apices := apexOrbitFamily (G := G) P.apex
  rot := apexRotFamily K P.apex P.normal_in_stab P.apex_ne
  isRotatingFamily :=
    isRotatingFamily_apexRotFamily P.isometric K P.apex P.fix P.normal_in_stab
      P.apex_ne
  isSeparated := isSeparated_apexOrbitFamily P.separated
  isVeryRotating := isVeryRotating_apexRotFamily P.veryRotating
  rotationNormalClosure_eq := by
    rw [rotationNormalClosure_apexRotFamily]
    exact hclosure
  injRadius := P.injRadius
  lt_injRadius := P.lt_injRadius
  kernel_moves_base := by
    intro g hg hg1
    rw [rotationNormalClosure_apexRotFamily] at hg
    exact P.kernel_moves g hg hg1
  finiteOrder_lift := by
    intro Q _ q hker
    exact P.finiteOrder_lift q (hker.trans hclosure.symm)

end HullSC
end GroupApproximation
