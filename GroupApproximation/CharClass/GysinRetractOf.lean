import GroupApproximation.CharClass.GysinTautFields
import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.Meta.AxiomGuard

/-!
# The two pieces retract onto the base, over any commutative ring

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`GysinRetract.lean` and `GysinTautFields.lean` read `H^*(P(p ⊕ 1); F₂)` through the two
pieces of the Gysin cover: restrict to the piece, then pull back along its retraction onto
the base, and both readings are sections of the projection and multiplicative over the
base.  Nothing there uses the coefficient: the only cohomological input is homotopy
invariance, which `KroneckerContractible.pull_eq_of_homotopicOf` supplies over any
commutative ring `K`.

This is a new module beside the `F₂` files rather than an edit of them, so that they gain
no import.  Nothing in `rChartOf K p k` determines the coefficient ring, so it is explicit.

## Main declarations

* `rChartOf`, `rNotZeroOf` — the two readings over `K`.
* `rChartOf_pull`, `rNotZeroOf_pull` — **both are sections of the projection**.
* `rChartOf_cup`, `rNotZeroOf_cup` — both are multiplicative over the base.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace Gysin

open CategoryTheory TopologicalSpace

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. Sections of the projection -/

/-- **A piece whose equivalence to the base is the projection gives a section**, over any
commutative ring `K`. -/
theorem pull_retract_pullOf {K : Type} [CommRing K] (p : Bundle X ι)
    (A : Opens (TopCat.of (Bundle.Proj p.plusOne)))
    (e : ContinuousMap.HomotopyEquiv
      ↥((A : Opens (TopCat.of (Bundle.Proj p.plusOne)))
        : Set (Bundle.Proj p.plusOne)) X)
    (he : LH.opIncl A ≫ gysinProj p = cmap e.toFun)
    (k : ℕ) (a : Hmod K (TopCat.of X) k) :
    pull (cmap e.invFun) k (pull (LH.opIncl A) k (pull (gysinProj p) k a)) = a := by
  have h : pull (cmap (e.toFun.comp e.invFun)) k a = pull (𝟙 (TopCat.of X)) k a :=
    pull_eq_of_homotopicOf K (f := cmap (e.toFun.comp e.invFun)) (g := 𝟙 (TopCat.of X))
      e.right_inv k a
  rw [(pull_comp (LH.opIncl A) (gysinProj p) k a).symm, he,
    (pull_comp (cmap e.invFun) (cmap e.toFun) k a).symm]
  exact h.trans (pull_id k a)

/-- Restriction to the chart, retracted onto the base, over any commutative ring `K`. -/
def rChartOf (K : Type) [CommRing K] (p : Bundle X ι) (k : ℕ) :
    Hmod K (TopCat.of (Bundle.Proj p.plusOne)) k →+ Hmod K (TopCat.of X) k :=
  ((pullLinear (cmap (chartEquivBase p).invFun) k).comp
    (pullLinear (LH.opIncl (chartOpens p)) k)).toAddMonoidHom

/-- Restriction to the complement of the zero section, retracted onto the base, over any
commutative ring `K`. -/
def rNotZeroOf (K : Type) [CommRing K] (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1)
    (k : ℕ) : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) k →+ Hmod K (TopCat.of X) k :=
  ((pullLinear (cmap (notZeroEquivBase p hp).invFun) k).comp
    (pullLinear (LH.opIncl (notZeroOpens p)) k)).toAddMonoidHom

/-- **The chart reading is a section of the projection**, over any commutative ring. -/
theorem rChartOf_pull {K : Type} [CommRing K] (p : Bundle X ι) (k : ℕ)
    (a : Hmod K (TopCat.of X) k) : rChartOf K p k (pull (gysinProj p) k a) = a :=
  pull_retract_pullOf p (chartOpens p) (chartEquivBase p) rfl k a

/-- **And so is the reading on the complement of the zero section.** -/
theorem rNotZeroOf_pull {K : Type} [CommRing K] (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1)
    (k : ℕ) (a : Hmod K (TopCat.of X) k) :
    rNotZeroOf K p hp k (pull (gysinProj p) k a) = a :=
  pull_retract_pullOf p (notZeroOpens p) (notZeroEquivBase p hp) rfl k a

/-! ## 2. Both readings are multiplicative over the base -/

theorem rChartOf_eq {K : Type} [CommRing K] (p : Bundle X ι) (k : ℕ)
    (z : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) k) :
    rChartOf K p k z = pull (chartSectionProj p) k z :=
  (pull_comp _ _ k z).symm

theorem rNotZeroOf_eq {K : Type} [CommRing K] (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1)
    (k : ℕ) (z : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) k) :
    rNotZeroOf K p hp k z = pull (notZeroSectionProj p hp) k z :=
  (pull_comp _ _ k z).symm

theorem rChartOf_cup {K : Type} [CommRing K] (p : Bundle X ι) (k : ℕ)
    (b : Hmod K (TopCat.of X) k) (t : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2) :
    rChartOf K p (k + 2) (cup (pull (gysinProj p) k b) t) = cup b (rChartOf K p 2 t) := by
  have h1 : rChartOf K p (k + 2) (cup (pull (gysinProj p) k b) t)
      = cup (rChartOf K p k (pull (gysinProj p) k b)) (rChartOf K p 2 t) := by
    simp only [rChartOf_eq, pull_cup]
  rw [h1, rChartOf_pull]

theorem rNotZeroOf_cup {K : Type} [CommRing K] (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1)
    (k : ℕ) (b : Hmod K (TopCat.of X) k) (t : Hmod K (TopCat.of (Bundle.Proj p.plusOne)) 2) :
    rNotZeroOf K p hp (k + 2) (cup (pull (gysinProj p) k b) t)
      = cup b (rNotZeroOf K p hp 2 t) := by
  have h1 : rNotZeroOf K p hp (k + 2) (cup (pull (gysinProj p) k b) t)
      = cup (rNotZeroOf K p hp k (pull (gysinProj p) k b)) (rNotZeroOf K p hp 2 t) := by
    simp only [rNotZeroOf_eq, pull_cup]
  rw [h1, rNotZeroOf_pull]

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms rChartOf_cup
#audit_axioms rNotZeroOf_cup

end

end Gysin
end CharClass
end GroupApproximation
