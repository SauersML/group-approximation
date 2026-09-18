import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseJunctionRefute.Diagram
import GroupApproximation.Meta.AxiomGuard

/-!
# Least area of the 24-dart counterexample diagram

Lane gl-p10-51.

Proof route: every relator value is odd (`gc * ga⁻¹` and `ga`), while the boundary value `gc` is
even and not `1`.  A product of `m` conjugates of relator values has sign `(-1)^m`.  So `m = 0`
forces the boundary value to be `1`, `m = 1` forces it to be odd, and hence `m ≥ 2 = rCellCount`
(`OsinPocketFullArcLakeModel.sign_of_isRelatorProduct`).

Manuscript status: counterexample/infrastructure for thm:hull.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf

open Equiv GroupApproximation.HullSC
open OsinPocketPinchedTwoGonModel (D)
open OsinPocketFullArcLakeModel (ga gc sign_ga sign_gc sign_of_isRelatorProduct)

instance roseJunctionRefute_instNeZero : NeZero roseJunctionRefute_X.rCellCount := ⟨by decide⟩
instance roseJunctionRefute_instOfNatX (n : ℕ) : OfNat roseJunctionRefute_X.toCombMap.Dart n :=
  inferInstanceAs (OfNat (Fin 24) n)
instance roseJunctionRefute_instDecEqX : DecidableEq roseJunctionRefute_X.toCombMap.Dart :=
  inferInstanceAs (DecidableEq (Fin 24))

/-- The source cell `S`. -/
def roseJunctionRefute_iS : Fin roseJunctionRefute_X.rCellCount := ⟨0, by decide⟩

/-- The kept cell `K₀`. -/
def roseJunctionRefute_iK0 : Fin roseJunctionRefute_X.rCellCount := ⟨1, by decide⟩

theorem roseJunctionRefute_letters :
    ∀ d, (symmetricLabelAlphabet D).IsLetter (roseJunctionRefute_X.label d) := fun _ =>
  Or.inl (Set.mem_univ _)

theorem roseJunctionRefute_relSigns :
    ∀ r ∈ RelLetter.listVal '' roseJunctionRefute_W, Perm.sign r = -1 := by
  rintro r ⟨word, hword, rfl⟩
  simp only [roseJunctionRefute_W, Set.mem_insert_iff, Set.mem_singleton_iff] at hword
  rcases hword with rfl | rfl
  · rw [show RelLetter.listVal ([.base 1, .base 1, .base 1, .base 1, .base 1, .base gc,
        .base ga⁻¹] : List (RelLetter roseJunctionRefute_G Empty)) = gc * ga⁻¹ by decide,
      Perm.sign_mul, Perm.sign_inv, sign_gc, sign_ga, one_mul]
  · rw [show RelLetter.listVal ([.base ga] : List (RelLetter roseJunctionRefute_G Empty)) = ga
      by decide]
    exact sign_ga

theorem roseJunctionRefute_bdValue : roseJunctionRefute_X.boundaryValue = gc := by
  change RelLetter.listVal (RelWord.revInv
    ((roseJunctionRefute_boundary (roseJunctionRefute_face 5)).darts.map
      roseJunctionRefute_label)) = gc
  rw [roseJunctionRefute_bd_face]
  decide

/-- **The diagram has least area.** -/
theorem roseJunctionRefute_leastArea : roseJunctionRefute_X.LeastArea := by
  intro m hm
  rw [roseJunctionRefute_bdValue] at hm
  have hsign := sign_of_isRelatorProduct roseJunctionRefute_relSigns hm
  rw [sign_gc] at hsign
  change 2 ≤ m
  rcases m with _ | _ | m
  · exact absurd hm.eq_one_of_index_zero (by decide)
  · exact absurd hsign (by decide)
  · omega

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_instNeZero
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_instOfNatX
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_instDecEqX
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_iS
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_iK0
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_letters
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_relSigns
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_bdValue
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.roseJunctionRefute_leastArea
