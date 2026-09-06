import GroupApproximation.CharClass.LerayHirschGradedIso
import GroupApproximation.CharClass.ThomBridgeTotal

/-!
# Leray–Hirsch on the hyperplane, and the Thom data over one class restriction

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`ThomBridgeTotal.thomData_total_of_lerayHirsch` wants a Leray–Hirsch instance on
the hyperplane **presented as a subset** of `P(p⊕1)`, because that is the
presentation `cc-relative`'s subspace comparison forces.  `cc-projective`'s
instance is about `Proj p`.  This file moves it.

Three of the four inputs are free.  The identification is `cc-bundle`'s
`projInclHomeoRange`; that it lies over the base is `hyperIso_hom_comp`, which is
`rfl` once the point is unfolded, because `projIncl` changes only the matrix
coordinate; and the class downstairs is *defined* as the transport, so its
compatibility is `rfl`.

The fourth is not free and is not invented here.  It is that the tautological
class of `P(p⊕1)` **restricts** to the tautological class of `P(p)`.
`cc-cohom-api`'s `CohomologyLHRestrict` names the same fact as an input it does
not construct.  It is named `htaut` below and is the only thing between the two
landed Leray–Hirsch instances and the Thom class at `cc-lix-odd`'s objects.

## Main declarations

* `ThomChernDeg.hyperIso`, `ThomChernDeg.hyperProj` — the hyperplane as a total
  space over the base.
* `ThomChernDeg.hyperIso_hom_comp` — it lies over the base.
* `ThomChernDeg.hyperLH` — **Leray–Hirsch on the hyperplane.**
* `ThomChernDeg.thomData_total_of_taut` — the Thom data, over `htaut`.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The hyperplane as a total space over the base -/

/-- The hyperplane, identified with `P(p)`. -/
def hyperIso [CompactSpace X] [T2Space X] (p : Bundle X ι) :
    TopCat.of ↥(Set.range (Bundle.projIncl p)) ≅ TopCat.of (Bundle.Proj p) :=
  TopCat.isoOfHomeo (Bundle.projInclHomeoRange p).symm

/-- The projection of the hyperplane: the projection of `P(p⊕1)`, restricted. -/
def hyperProj (p : Bundle X ι) :
    TopCat.of ↥(Set.range (Bundle.projIncl p)) ⟶ TopCat.of X :=
  sInclusion (Set.range (Bundle.projIncl p) :
      Set ↥(TopCat.of (Bundle.Proj p.plusOne))) ≫ projMapOf p.plusOne

/-- **The identification lies over the base.**  `projIncl` changes only the matrix
coordinate, so both sides read the same first coordinate. -/
theorem hyperIso_hom_comp [CompactSpace X] [T2Space X] (p : Bundle X ι) :
    (hyperIso p).hom ≫ projMapOf p = hyperProj p := by
  apply TopCat.Hom.ext
  refine ContinuousMap.ext fun w => ?_
  show Bundle.projPi p ((Bundle.projInclHomeoRange p).symm w)
      = Bundle.projPi p.plusOne (w : Bundle.Proj p.plusOne)
  have hw : (w : Bundle.Proj p.plusOne)
      = Bundle.projIncl p ((Bundle.projInclHomeoRange p).symm w) := by
    rw [← Bundle.projInclHomeoRange_coe p ((Bundle.projInclHomeoRange p).symm w),
      (Bundle.projInclHomeoRange p).apply_symm_apply]
  rw [hw]
  rfl

/-- **Leray–Hirsch on the hyperplane**, presented as a subset of `P(p⊕1)`.  The
class is *defined* as the transport, so its compatibility costs nothing. -/
theorem hyperLH [CompactSpace X] [T2Space X] [Nonempty X] (p : Bundle X ι) (r : ℕ)
    (hs : ∀ x, p.rank x = r) (hs1 : 1 ≤ r) :
    LerayHirschGraded (hyperProj p) (pull (hyperIso p).hom 2 (tautEulerOf p)) r :=
  lerayHirschGraded_of_iso (hyperIso p) (projMapOf p) (hyperProj p)
    (hyperIso_hom_comp p) (tautEulerOf p) _ rfl
    (lerayHirschGraded_compact p r hs hs1)

/-! ## 2. The Thom data, over the class restriction -/

/-- **The degreewise Thom data of the vector-bundle pair, over one named input.**

`htaut` says the tautological class of `P(p⊕1)` restricts to the tautological
class of `P(p)`.  Everything else — both Leray–Hirsch instances, the projection
compatibility, the bridge — is landed. -/
theorem thomData_total_of_taut [CompactSpace X] [T2Space X] [Nonempty X]
    (p : Bundle X ι) (r : ℕ) (hs : ∀ x, p.rank x = r) (hs1 : 1 ≤ r)
    (hs' : ∀ x, p.plusOne.rank x = r + 1)
    (htaut : pull (sInclusion (Set.range (Bundle.projIncl p))) 2
        (tautEulerOf p.plusOne) = pull (hyperIso p).hom 2 (tautEulerOf p)) :
    ∃ (jm : ↥(relCohomology (ZMod 2) (TopCat.of (Bundle.Total p))
          ((Subtype.val : Bundle.Total p → X × (ι → ℂ)) ⁻¹' Bundle.puncturedSet p)
          (2 * r))
        →ₗ[ZMod 2] ((i : Fin (r + 1)) → Hmod2 (TopCat.of X) (2 * r - 2 * (i : ℕ))))
      (_ : Function.Injective jm),
      LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap (R := ZMod 2)
        (M := fun i : Fin (r + 1) => Hmod2 (TopCat.of X) (2 * r - 2 * (i : ℕ)))
        (fun i => chernMul (hyperLH p r hs hs1) i)) :=
  thomData_total_of_lerayHirsch p (hyperProj p) rfl
    (pull (hyperIso p).hom 2 (tautEulerOf p)) htaut hs1
    (lerayHirschGraded_compact p.plusOne (r + 1) hs' (Nat.succ_le_succ (Nat.zero_le _)))
    (hyperLH p r hs hs1)

/-! Printed on every build. -/

#print axioms thomData_total_of_taut

end ThomChernDeg

end

end GroupApproximation.CharClass
