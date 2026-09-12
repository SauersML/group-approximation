import GroupApproximation.CharClass.SliceValueVOf
import GroupApproximation.CharClass.CohomologyLHRingDataOf
import GroupApproximation.CharClass.LerayHirschChartBundleGen
import GroupApproximation.CharClass.LerayHirschChartClassGenK
import GroupApproximation.CharClass.BundlePairs
import GroupApproximation.CharClass.CohomologyTotalNontrivialOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Chern classes over `K` pull back along a pullback of the bundle

Lane `lx-sliceK` of the STW Problem LIX strongest-theorem swarm.

`LerayHirschDataEvenOf.chern_map_of_squareOf` (`SliceValueVOf`) is naturality for abstract data on
a commuting square.  This file specialises it to the geometry every consumer has: even-part
Leray–Hirsch data built by `LerayHirschDataEvenOf.of_graded` for a bundle `E` over `X` and for its
pullback `f^* E` over `Y`, with the dual tautological classes `tautEulerDualK K hgen`.  The square of
projectivisations commutes on the nose, and the tautological class of `f^* E` is the pullback of
the one of `E` (`LH.tautEulerDual_comapOf`), for the same class `hgen`.

## Main declarations

* `chern_comap_of_gradedOf` — **the Chern classes of `f^* E` are the pulled-back Chern classes of `E`.**
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH

noncomputable section

/-- **Naturality of the Chern classes over `K` under pulling the bundle back.**  For even-part
Leray–Hirsch data of `E` and of `f^* E` at the dual tautological classes of one generator `hgen`,
the Chern classes of `f^* E` are the pulled-back Chern classes of `E`. -/
theorem chern_comap_of_gradedOf (K : Type) [Field K] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [Nonempty X] [Nonempty Y] {κ : Type} [Fintype κ] [DecidableEq κ]
    (hgen : Hmod K (CPtop (1 + tautCardOf κ)) 2) (E : Bundle X κ) (f : C(Y, X)) {r : ℕ}
    (LE : LerayHirschGraded (projMapOf E) (LH.tautEulerDualK K hgen E) r)
    (Lf : LerayHirschGraded (projMapOf (comap f E)) (LH.tautEulerDualK K hgen (comap f E)) r)
    (k : ℕ) :
    (LerayHirschDataEvenOf.of_graded Lf).chern k
      = Gen.evenMap K (cmap f) ((LerayHirschDataEvenOf.of_graded LE).chern k) := by
  haveI : Nontrivial (TotalHOf K (TopCat.of X)) :=
    @nontrivial_totalHOf K _ _ (TopCat.of X) ‹Nonempty X›
  haveI : Nontrivial (TotalHOf K (TopCat.of Y)) :=
    @nontrivial_totalHOf K _ _ (TopCat.of Y) ‹Nonempty Y›
  haveI : Nontrivial (Gen.evenPart K (TopCat.of X)) := nontrivial_evenPartOf _
  haveI : Nontrivial (Gen.evenPart K (TopCat.of Y)) := nontrivial_evenPartOf _
  refine LerayHirschDataEvenOf.chern_map_of_squareOf (LerayHirschDataEvenOf.of_graded LE)
    (LerayHirschDataEvenOf.of_graded Lf) (cmap f) (cmap (projComap f E)) ?_ ?_ rfl k
  · apply TopCat.ext
    intro z
    rfl
  · show TotalHOf.of K _ 2 (LH.tautEulerDualK K hgen (comap f E))
      = TotalHOf.map K (cmap (projComap f E)) (TotalHOf.of K _ 2 (LH.tautEulerDualK K hgen E))
    rw [TotalHOf.map_of, LH.tautEulerDual_comapOf]

end

#audit_axioms chern_comap_of_gradedOf

end GroupApproximation.CharClass
