import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import Mathlib.Data.Int.Order.Units
import GroupApproximation.Meta.AxiomGuard

/-!
# `LeastArea` certificates by relator parity (lane gl-p10-72)

TRUTH AUDIT (gl-p10-72): the 1260 gl-p10-69 seed-5 configurations (N=30, maxeps 10)
are ONE 16-dart planar map (3 vertices, 8 edges, 7 faces) with six choices of
(outer, source, kept) faces.  Every hypothesis of `roseLobeRegion_Statement`,
`roseLobeChoice_Statement`, `roseLobeMulti_Statement` and `roseLobeTriple_Statement`
holds there in the model, and the lobe/lake conclusion fails.  The model labels the
map in `S₃`: the source and kept cells are the two relator cells (odd permutations),
all other inner faces have value `1`, and the boundary value is a `3`-cycle.

`LeastArea` does NOT exclude these configurations: the boundary value is even and
nontrivial, so no relator product of budget `0` or `1` reaches it, and the diagram has
exactly two relator cells.  The lemma `roseLobeArea_leastArea_of_parity` below is that
certificate in Lean.  So, modulo model fidelity, the `roseLobe*` statements are FALSE
as stated; they quantify over all `D, W, eps` and drop the hyperbolicity and
`OsinCCondition` premises of `RoseStepStatement`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open RelatorDefectBudget

/-- A relator product of budget `m` over relators of sign `-1` has sign `(-1) ^ m`. -/
theorem roseLobeArea_parity {G : Type u} [Group G] {R : Set G} (φ : G →* ℤˣ)
    (hR : ∀ r ∈ R, φ r = -1) {m : ℕ} {g : G} (h : IsRelatorProduct R m g) :
    φ g = (-1) ^ m := by
  induction h with
  | one => rw [map_one, pow_zero]
  | base hr => rw [hR _ hr, pow_one]
  | inv _ ih => rw [map_inv, ih, Int.units_inv_eq_self]
  | conj c _ ih =>
      rw [map_mul, map_mul, map_inv, ih, mul_comm (φ c), mul_assoc, mul_inv_cancel, mul_one]
  | mul _ _ iha ihb => rw [map_mul, iha, ihb, pow_add]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeArea_parity

/-- **`LeastArea` by parity.**  If every relator value has sign `-1`, the boundary
value is nontrivial of sign `1`, and the diagram has at most two relator cells, then the
diagram has least area.  This certifies `LeastArea` for the gl-p10-69 seed-5 family. -/
theorem roseLobeArea_leastArea_of_parity {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} (X : DiscDiagram.{u, w, v} W) (φ : G →* ℤˣ)
    (hW : ∀ r ∈ RelLetter.listVal '' W, φ r = -1) (hb1 : X.boundaryValue ≠ 1)
    (hbφ : φ X.boundaryValue = 1) (hcount : X.rCellCount ≤ 2) : X.LeastArea := by
  intro m hm
  have hpar := roseLobeArea_parity φ hW hm
  by_cases hm2 : 2 ≤ m
  · omega
  · exfalso
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · exact hb1 hm.eq_one_of_index_zero
    · rw [hbφ, pow_one] at hpar
      exact absurd (congrArg Units.val hpar) (by norm_num)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeArea_leastArea_of_parity

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
