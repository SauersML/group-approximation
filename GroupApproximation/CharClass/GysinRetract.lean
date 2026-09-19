import GroupApproximation.CharClass.GysinCover
import GroupApproximation.CharClass.BundleGysinData
import GroupApproximation.CharClass.LerayHirschRel

/-!
# The two pieces retract onto the base

A Gysin datum reads `H^*(P(p ⊕ 1))` through the two pieces of its cover, and each
reading is a restriction followed by the piece's retraction onto the base.  For the
datum to say anything, each composite has to be a *section* of the projection, and
that is what is proved here.

Both come out of one lemma.  A piece whose homotopy equivalence to the base is the
projection restricted gives a section on cohomology, because the composite
`X → piece → X` is then the equivalence's own round trip, homotopic to the identity.
The hypothesis is `rfl` in both cases:

* on the chart it is `cc-bundle`'s `chartOpensHomotopyEquivBase_toFun_apply`;
* on the complement of the zero section, `projRetract` keeps the base point of the
  line it normalises, and for a rank-one bundle `projRankOneHomeo` is `projPi`.

The second is the one worth naming.  The complement retracts onto `P(p)`, the
hyperplane at infinity, *not* onto the base — `cc-bundle` corrected me on that — and
the two agree only because `p` here is a line bundle.  For higher rank this
construction gives nothing, which is exactly why the Gysin sequence is a statement
about circle bundles.

## Main declarations

* `chartEquivBase`, `notZeroEquivBase` — the two retractions onto the base.
* `rChart`, `rNotZero` — the two readings, as additive maps.
* `rChart_pull`, `rNotZero_pull` — **both are sections of the projection**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory TopologicalSpace

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The projection of the projectivised sum. -/
abbrev gysinProj (p : Bundle X ι) :
    TopCat.of (Bundle.Proj p.plusOne) ⟶ TopCat.of X :=
  cmap (Bundle.projPi p.plusOne)

/-- **The chart retracts onto the base.** -/
def chartEquivBase (p : Bundle X ι) :
    ContinuousMap.HomotopyEquiv ↥(Bundle.chartOpensSet p) X :=
  Bundle.chartOpensHomotopyEquivBase p

/-- **The complement of the zero section retracts onto the base**, for a line
bundle.  It retracts onto `P(p)` in general; the two agree only at rank one. -/
def notZeroEquivBase (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) :
    ContinuousMap.HomotopyEquiv ↥(Bundle.notZeroOpensSet p) X :=
  (Bundle.notZeroOpensHomotopyEquivProj p).trans
    (Bundle.projRankOneHomeo p hp).toHomotopyEquiv

/-- **A piece whose equivalence to the base is the projection gives a section.**
The composite `X → piece → X` is the equivalence's own round trip. -/
theorem pull_retract_pull (p : Bundle X ι)
    (A : Opens (TopCat.of (Bundle.Proj p.plusOne)))
    (e : ContinuousMap.HomotopyEquiv
      ↥((A : Opens (TopCat.of (Bundle.Proj p.plusOne)))
        : Set (Bundle.Proj p.plusOne)) X)
    (he : LH.opIncl A ≫ gysinProj p = cmap e.toFun)
    (k : ℕ) (a : Hmod2 (TopCat.of X) k) :
    pull (cmap e.invFun) k (pull (LH.opIncl A) k (pull (gysinProj p) k a)) = a := by
  have h : pull (cmap (e.toFun.comp e.invFun)) k a = pull (𝟙 (TopCat.of X)) k a :=
    pull_eq_of_homotopic (f := cmap (e.toFun.comp e.invFun)) (g := 𝟙 (TopCat.of X))
      e.right_inv k a
  rw [(pull_comp (LH.opIncl A) (gysinProj p) k a).symm, he,
    (pull_comp (cmap e.invFun) (cmap e.toFun) k a).symm]
  exact h.trans (pull_id k a)

/-- Restriction to the chart, retracted onto the base. -/
def rChart (p : Bundle X ι) (k : ℕ) :
    Hmod2 (TopCat.of (Bundle.Proj p.plusOne)) k →+ Hmod2 (TopCat.of X) k :=
  ((pullLinear (cmap (chartEquivBase p).invFun) k).comp
    (pullLinear (LH.opIncl (chartOpens p)) k)).toAddMonoidHom

/-- Restriction to the complement of the zero section, retracted onto the base. -/
def rNotZero (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) (k : ℕ) :
    Hmod2 (TopCat.of (Bundle.Proj p.plusOne)) k →+ Hmod2 (TopCat.of X) k :=
  ((pullLinear (cmap (notZeroEquivBase p hp).invFun) k).comp
    (pullLinear (LH.opIncl (notZeroOpens p)) k)).toAddMonoidHom

/-- **The chart reading is a section of the projection.** -/
theorem rChart_pull (p : Bundle X ι) (k : ℕ) (a : Hmod2 (TopCat.of X) k) :
    rChart p k (pull (gysinProj p) k a) = a :=
  pull_retract_pull p (chartOpens p) (chartEquivBase p) rfl k a

/-- **And so is the reading on the complement of the zero section.** -/
theorem rNotZero_pull (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) (k : ℕ)
    (a : Hmod2 (TopCat.of X) k) :
    rNotZero p hp k (pull (gysinProj p) k a) = a :=
  pull_retract_pull p (notZeroOpens p) (notZeroEquivBase p hp) rfl k a

end

end Gysin
end CharClass
end GroupApproximation
