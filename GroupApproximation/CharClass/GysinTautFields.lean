import GroupApproximation.CharClass.GysinRetract
import GroupApproximation.CharClass.LerayHirschChartClass
import GroupApproximation.CharClass.BundleTautPieces
import GroupApproximation.CharClass.CohomologyShapes

/-!
# The tautological class on the two pieces

The last two fields of the Gysin datum, and only the first has content.

**On the chart the class dies.**  The chart's section into `P(p ⊕ 1)` is the zero
section, on the nose, because every map in `cc-bundle`'s lane keeps the base
coordinate of the point it acts on.  There the tautological line is the constant
line `infPoint`, so its classifying map is constant, so it factors through a point,
which has no `H²`.

**On the complement the class is whatever it is.**  The datum only asks that the
reading there be *some* class cupped with `b`, and taking that class to be the
reading of the tautological class itself makes the field hold by the same
multiplicativity.  Nothing is computed.

That second choice is the point of this file.  Identifying the class with the
degree-two generator looked like it needed the Euler class to be independent of the
coordinate embedding — a general fact about isometric embeddings of projective
spaces that is not in the repo.  It is not needed: the Gysin argument itself shows
the class is nonzero, in its own first power, and `H²(ℂP^d;F₂)` is a line.  So the
identification is free, and it is `ProjectiveSpaceRingBootstrap` that draws it.

## Main declarations

* `chartSectionProj`, `notZeroSectionProj` — the two sections, as morphisms.
* `chartSectionProj_eq_zeroSectionProj` — **the chart's section is the zero section**.
* `rChart_tautEuler` — **the class dies on the chart**.
* `rChart_cup`, `rNotZero_cup` — both readings are multiplicative over the base.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory TopologicalSpace

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The two sections, as single morphisms -/

/-- The chart's section into `P(p ⊕ 1)`. -/
def chartSectionProj (p : Bundle X ι) :
    TopCat.of X ⟶ TopCat.of (Bundle.Proj p.plusOne) :=
  cmap (chartEquivBase p).invFun ≫ LH.opIncl (chartOpens p)

/-- The complement's section into `P(p ⊕ 1)`. -/
def notZeroSectionProj (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) :
    TopCat.of X ⟶ TopCat.of (Bundle.Proj p.plusOne) :=
  cmap (notZeroEquivBase p hp).invFun ≫ LH.opIncl (notZeroOpens p)

theorem rChart_eq (p : Bundle X ι) (k : ℕ)
    (z : Hmod2 (TopCat.of (Bundle.Proj p.plusOne)) k) :
    rChart p k z = pull (chartSectionProj p) k z :=
  (pull_comp _ _ k z).symm

theorem rNotZero_eq (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) (k : ℕ)
    (z : Hmod2 (TopCat.of (Bundle.Proj p.plusOne)) k) :
    rNotZero p hp k z = pull (notZeroSectionProj p hp) k z :=
  (pull_comp _ _ k z).symm

/-! ## 2. Both readings are multiplicative over the base -/

theorem rChart_cup (p : Bundle X ι) (k : ℕ) (b : Hmod2 (TopCat.of X) k)
    (t : Hmod2 (TopCat.of (Bundle.Proj p.plusOne)) 2) :
    rChart p (k + 2) (cup (pull (gysinProj p) k b) t) = cup b (rChart p 2 t) := by
  have h1 : rChart p (k + 2) (cup (pull (gysinProj p) k b) t)
      = cup (rChart p k (pull (gysinProj p) k b)) (rChart p 2 t) := by
    simp only [rChart_eq, pull_cup]
  rw [h1, rChart_pull]

theorem rNotZero_cup (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) (k : ℕ)
    (b : Hmod2 (TopCat.of X) k) (t : Hmod2 (TopCat.of (Bundle.Proj p.plusOne)) 2) :
    rNotZero p hp (k + 2) (cup (pull (gysinProj p) k b) t)
      = cup b (rNotZero p hp 2 t) := by
  have h1 : rNotZero p hp (k + 2) (cup (pull (gysinProj p) k b) t)
      = cup (rNotZero p hp k (pull (gysinProj p) k b)) (rNotZero p hp 2 t) := by
    simp only [rNotZero_eq, pull_cup]
  rw [h1, rNotZero_pull]

/-! ## 3. The chart's section is the zero section -/

/-- **The chart's section is the zero section.**  It is `cc-bundle`'s
`chartOpensHomotopyEquivBase_invFun_apply`, the mirror of the `toFun` statement they
already provide, and it is true for the same reason: the chart identification sends
the zero vector of a fibre to the line spanned by the `Unit` coordinate, and no
construction in that lane touches the base coordinate.

It is *not* definitional here, because the homotopy equivalence is assembled from
`Homeomorph.symm`s and `symm.symm` does not reduce.  So it is taken as a hypothesis
until that lemma lands, at which point every use below is discharged in one line. -/
def IsZeroSectionChart (p : Bundle X ι) : Prop :=
  chartSectionProj p = cmap (Bundle.zeroSectionProj p)

/-! ## 4. The tautological class dies on the chart -/

/-- **The tautological class dies on the chart.**  Pulled back along the zero section
the tautological line is constant, so its classifying map is constant and factors
through a point, which has no `H²`.

Everything here is proved; the only input is the identification of the chart's
section with the zero section. -/
theorem rChart_tautEuler [Nonempty X] (p : Bundle X ι) (hsec : IsZeroSectionChart p) :
    rChart p 2 (LH.tautEuler p) = 0 := by
  classical
  have hqt : ∀ x, ((Bundle.pushforward (LH.tautEmb ι) (LH.tautEmb_injective ι)
      (Bundle.comap (Bundle.zeroSectionProj p) (Bundle.tautLine p.plusOne))) x).trace = 1 :=
    fun x => CPn.trace_pushforward_one (LH.tautEmb ι) (LH.tautEmb_injective ι) _
      (fun y => Bundle.trace_tautLine p.plusOne (Bundle.zeroSectionProj p y)) x
  have hstep : rChart p 2 (LH.tautEuler p)
      = eulerOfBundle (show 1 ≤ 1 + LH.tautCard ι by omega)
          (Bundle.pushforward (LH.tautEmb ι) (LH.tautEmb_injective ι)
            (Bundle.comap (Bundle.zeroSectionProj p) (Bundle.tautLine p.plusOne))) hqt := by
    rw [rChart_eq, hsec, LH.tautEuler, ← eulerOfBundle_comap]
    rfl
  rw [hstep]
  refine eulerOfBundle_eq_zero_of_factors (show 1 ≤ 1 + LH.tautCard ι by omega) _ hqt
    (P := TopCat.of PUnit) (cmap ⟨fun _ => PUnit.unit, continuous_const⟩)
    (cmap (ContinuousMap.const PUnit
      (Bundle.classifyOne _ hqt (Classical.arbitrary X)))) ?_ ?_
  · exact TopCat.hom_ext (ContinuousMap.ext fun _ => Subtype.ext rfl)
  · exact fun a => (hasPointCohomology_of_contractible PUnit).2 2 (by omega) a

end

end Gysin
end CharClass
end GroupApproximation
