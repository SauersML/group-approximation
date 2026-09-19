import GroupApproximation.CharClass.LerayHirschChartBundle
import GroupApproximation.CharClass.ChernEulerIndex

/-!
# The class identification for the chart step

`LHOver_two_chart` left one hypothesis: that under the chart identification the
tautological class of the `ℂP¹` factor is the restriction of a class `ξ` fixed once
and for all on `P(p ⊕ 1)`.  That is the last thing the chart step needs, and it is
cohomology rather than geometry, which is why it was left open.

The class is the obvious one, the Euler class of the tautological line of
`P(p ⊕ 1)`.  Its index type is `ι ⊕ Unit`, not a `Fin`, so it is defined through
`ChernEulerIndex`: push the tautological line into a `Fin` big enough to descend
from, and take the Euler class there.

The identification is then three definitional steps and one appeal to
`cc-bundle`'s `tautLineIsoCPOne`:

* restricting the class to the part over `U` restricts the bundle, by naturality;
* over `U` the tautological line of `P(p ⊕ 1)` *is* the tautological line of
  `P(p|_U ⊕ 1)`, because `projOverHomeo` preserves the matrix a point carries and
  `restrictTo_plusOne` holds on the nose;
* and `tautLineIsoCPOne` says that one is the pullback of the tautological line of
  `ℂP¹` along the `ℂP¹` component of the trivialisation.

Every transport here is `rfl`, which is the tell that the producers stated things
at the right index rather than at their own convenience.  The index change between
`ι ⊕ Unit` and `Fin 2` is absorbed by `eulerOfBundle_pushforward_eq_of_bundleIso`,
and no generator computation appears.

## Main declarations

* `tautEuler` — **the class `ξ`**.
* `chartTautIso` — the bundle isomorphism over a chart.
* `pull_chartProdIso_cpTaut` — **the identification**.
* `LHOver_two_chart_of_trivialization` — the chart step, with nothing left open.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.CPn

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. The class -/

/-- A `Fin` large enough to hold `ι ⊕ Unit` and to descend from to `ℂP¹`. -/
abbrev tautCard (ι : Type) [Fintype ι] : ℕ := Fintype.card (ι ⊕ Unit)

/-- An injection of the index of `p ⊕ 1` into that `Fin`. -/
def tautEmb (ι : Type) [Fintype ι] : (ι ⊕ Unit) → Fin (1 + tautCard ι + 1) :=
  fun s => Fin.castLE (Nat.le_succ_of_le (Nat.le_add_left _ 1)) (Fintype.equivFin (ι ⊕ Unit) s)

theorem tautEmb_injective (ι : Type) [Fintype ι] : Function.Injective (tautEmb ι) :=
  (Fin.castLE_injective _).comp (Fintype.equivFin (ι ⊕ Unit)).injective

/-- Pulling back commutes with pushing the index forward; both carry the same
matrix at the same point. -/
theorem comap_pushforward {Y : Type} [TopologicalSpace Y] {κ : Type} [Fintype κ]
    [DecidableEq κ] (g : C(Y, X)) (f : ι → κ) (hf : Function.Injective f)
    (q : Bundle X ι) :
    comap g (pushforward f hf q) = pushforward f hf (comap g q) := rfl

/-- **The class `ξ`**: the Euler class of the tautological line of `P(p ⊕ 1)`,
taken at an index large enough to compare with `ℂP¹`. -/
def tautEuler (p : Bundle X ι) : Hmod2 (TopCat.of (Proj p.plusOne)) 2 :=
  eulerOfBundle (show 1 ≤ 1 + tautCard ι by omega)
    (pushforward (tautEmb ι) (tautEmb_injective ι) (tautLine p.plusOne))
    (trace_pushforward_one (tautEmb ι) (tautEmb_injective ι) (tautLine p.plusOne)
      (trace_tautLine p.plusOne))

/-! ## 2. The two maps out of the part over a chart -/

/-- The inclusion of the part of `P(p ⊕ 1)` lying over `U`. -/
def chartIncl (p : Bundle X ι) (U : Opens (TopCat.of X)) :
    C(↥(opSpace (opensComap (projMap p) U)), Proj p.plusOne) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- That part, identified with `P(p|_U ⊕ 1)`. -/
def chartProj (p : Bundle X ι) (U : Opens (TopCat.of X)) :
    C(↥(opSpace (opensComap (projMap p) U)),
      Proj ((p.restrictTo ((U : Opens (TopCat.of X)) : Set X)).plusOne)) :=
  ⟨(projOverHomeo p.plusOne ((U : Opens (TopCat.of X)) : Set X)).symm,
    (projOverHomeo p.plusOne ((U : Opens (TopCat.of X)) : Set X)).symm.continuous⟩

/-- The `ℂP¹` component of the chart identification. -/
def chartCP (p : Bundle X ι) (U : Opens (TopCat.of X))
    (hp : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      ((p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x).trace = 1)
    (i : ι)
    (hi : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      (p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x i i ≠ 0) :
    C(↥(opSpace (opensComap (projMap p) U)), CP 1) :=
  ContinuousMap.snd.comp (ConcreteCategory.hom (chartProdIso p U hp i hi).hom)

/-! ## 3. The bundle isomorphism over a chart -/

/-- **Over a chart the tautological line is the tautological line of `ℂP¹`.**

`cc-bundle`'s `tautLineIsoCPOne`, pulled back along the identification of the part
over `U` with `P(p|_U ⊕ 1)`.  Nothing is transported: the two `comap`s on each side
are definitionally the ones named here, because `projOverHomeo` preserves the
matrix and `restrictTo_plusOne` is `rfl`. -/
def chartTautIso (p : Bundle X ι) (U : Opens (TopCat.of X))
    (hp : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      ((p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x).trace = 1)
    (i : ι)
    (hi : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      (p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x i i ≠ 0) :
    BundleIso (comap (chartIncl p U) (tautLine p.plusOne))
      (comap (chartCP p U hp i hi) (cpTaut 1)) :=
  comapIso (chartProj p U)
    (tautLineIsoCPOne (p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) hp i hi)

/-! ## 4. The identification -/

/-- **The class identification.**  Under the chart trivialisation the tautological
class of the `ℂP¹` factor is the restriction of `tautEuler p`. -/
theorem pull_chartProdIso_cpTaut (p : Bundle X ι) (U : Opens (TopCat.of X))
    (hp : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      ((p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x).trace = 1)
    (i : ι)
    (hi : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      (p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x i i ≠ 0) :
    pull (chartProdIso p U hp i hi).hom 2
        (KnCP.cpTaut ↥((U : Opens (TopCat.of X)) : Set X))
      = lhClass (projMap p) (tautEuler p) U := by
  have hL : pull (chartProdIso p U hp i hi).hom 2
        (KnCP.cpTaut ↥((U : Opens (TopCat.of X)) : Set X))
      = eulerOfBundle (le_refl 1) (comap (chartCP p U hp i hi) (cpTaut 1))
          (fun w => trace_cpTaut 1 (chartCP p U hp i hi w)) := by
    rw [eulerOfBundle_comap, KnCP.cpTaut, eulerOfBundle_cpTaut 1 (le_refl 1)]
    exact (pull_comp _ _ 2 _).symm
  have hR : lhClass (projMap p) (tautEuler p) U
      = eulerOfBundle (show 1 ≤ 1 + tautCard ι by omega)
          (pushforward (tautEmb ι) (tautEmb_injective ι)
            (comap (chartIncl p U) (tautLine p.plusOne)))
          (fun w => trace_pushforward_one (tautEmb ι) (tautEmb_injective ι)
            (tautLine p.plusOne) (trace_tautLine p.plusOne) (chartIncl p U w)) :=
    (eulerOfBundle_comap (show 1 ≤ 1 + tautCard ι by omega)
      (pushforward (tautEmb ι) (tautEmb_injective ι) (tautLine p.plusOne))
      (trace_pushforward_one (tautEmb ι) (tautEmb_injective ι) (tautLine p.plusOne)
        (trace_tautLine p.plusOne))
      (chartIncl p U)).symm
  rw [hL, hR]
  exact (eulerOfBundle_pushforward_eq_of_bundleIso 1 (tautCard ι) (le_refl 1)
    (comap (chartIncl p U) (tautLine p.plusOne))
    (comap (chartCP p U hp i hi) (cpTaut 1)) (chartTautIso p U hp i hi) _
    (tautEmb_injective ι) _).symm

/-- **The chart step, with nothing left open.** -/
theorem LHOver_two_chart_of_trivialization (p : Bundle X ι) (U : Opens (TopCat.of X))
    (hp : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      ((p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x).trace = 1)
    (i : ι)
    (hi : ∀ x : ↥((U : Opens (TopCat.of X)) : Set X),
      (p.restrictTo ((U : Opens (TopCat.of X)) : Set X)) x i i ≠ 0) :
    LHOver (projMap p) (tautEuler p) 2 U :=
  LHOver_two_chart p U hp i hi (tautEuler p) (pull_chartProdIso_cpTaut p U hp i hi)

end

end LH
end CharClass
end GroupApproximation
