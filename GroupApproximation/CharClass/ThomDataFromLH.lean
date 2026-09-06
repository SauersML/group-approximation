import GroupApproximation.CharClass.ThomHabs

/-!
# The degreewise Thom data, from the two Leray–Hirsch instances alone

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXThomAssembly.lean` reduces the second hypothesis of `LIXThomDatum`
to two named inputs, `hinj0` and `habs`.  `CharClass/ThomHabs.lean` discharges the
second.  This file discharges the first and puts them together, so that the whole
Thom datum follows from

* a rank-`(r+1)` Leray–Hirsch instance upstairs,
* a rank-`r` instance on the subspace,
* the two compatibilities `hπ` and `hξ`, and
* `1 ≤ r`.

`hinj0` is injectivity of `relToAbs` at degree `2r`.  Pair-sequence exactness turns
it into surjectivity of the restriction one degree **down**, at `2r - 1`, and that
is `cc-cohom-api`'s `absToSub_surjective_of_graded`: at the odd degree the two
index sets have the same size, so the restriction there is a bijection.  The
hypothesis `1 ≤ r` is theirs and is real — at `r = 0` the truncated subtraction
sends `2r - 1` to `0`, where the cardinals are `1` and `0` and nothing is onto.

## Main declarations

* `ThomChernDeg.relToAbs_injective_of_graded` — `hinj0`.
* `ThomChernDeg.thomData_of_lerayHirsch` — **the Thom data**, from the instances.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace ThomChernDeg

open LH

set_option linter.unusedSectionVars false

variable {X P : TopCat.{0}}

/-- **`relToAbs` is injective at the top degree.**  Exactness moves the question one
degree down, where `cc-cohom-api`'s restriction is onto. -/
theorem relToAbs_injective_of_graded (Z : Set P)
    (π : P ⟶ X) (π' : TopCat.of Z ⟶ X) (hπ : sInclusion Z ≫ π = π')
    (ξ : Hmod2 P 2) (ξ' : Hmod2 (TopCat.of Z) 2) (hξ : pull (sInclusion Z) 2 ξ = ξ')
    {r : ℕ} (hr : 1 ≤ r)
    (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' r) :
    Function.Injective (relToAbs (ZMod 2) P Z (2 * r)).hom := by
  have hsurj : Function.Surjective (absToSub (ZMod 2) Z (2 * r - 1)).hom :=
    LHCast.absToSub_surjective_of_graded Z π π' hπ ξ ξ' hξ r hr L L'
  have hdeg : 2 * r - 1 + 1 = 2 * r := by omega
  rw [← hdeg]
  exact relToAbs_injective_of_absToSub_surjective (ZMod 2) P Z (2 * r - 1) hsurj

/-- **The degreewise Thom data of the pair, from the two Leray–Hirsch instances.**
This is the second hypothesis of `LIXThomDatum`, with nothing left named. -/
theorem thomData_of_lerayHirsch (Z : Set P)
    (π : P ⟶ X) (π' : TopCat.of Z ⟶ X) (hπ : sInclusion Z ≫ π = π')
    (ξ : Hmod2 P 2) (ξ' : Hmod2 (TopCat.of Z) 2) (hξ : pull (sInclusion Z) 2 ξ = ξ')
    {r : ℕ} (hr : 1 ≤ r)
    (L : LerayHirschGraded π ξ (r + 1)) (L' : LerayHirschGraded π' ξ' r) :
    ∃ (jm : ↥(relCohomology (ZMod 2) P Z (2 * r)) →ₗ[ZMod 2]
        ((i : Fin (r + 1)) → Hmod2 X (2 * r - 2 * (i : ℕ))))
      (_ : Function.Injective jm),
      LinearMap.range jm = LinearMap.ker (ThomDeg.restrictMap (R := ZMod 2)
        (M := fun i : Fin (r + 1) => Hmod2 X (2 * r - 2 * (i : ℕ)))
        (fun i => chernMul L' i)) :=
  thomData_of_absToSub (M := fun i : Fin (r + 1) => Hmod2 X (2 * r - 2 * (i : ℕ)))
    L Z (fun i => chernMul L' i) (LinearEquiv.refl (ZMod 2) _)
    (relToAbs_injective_of_graded Z π π' hπ ξ ξ' hξ hr L L')
    (range_thomJm_eq_ker_restrictMap Z π π' hπ ξ ξ' hξ L L')

/-! Printed on every build. -/

#print axioms thomData_of_lerayHirsch

end ThomChernDeg

end

end GroupApproximation.CharClass
