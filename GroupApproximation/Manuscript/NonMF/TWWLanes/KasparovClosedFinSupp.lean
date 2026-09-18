import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.StandardCoord
import GroupApproximation.Meta.AxiomGuard

/-!
# Closing Kasparov stabilization, lane `nm-tww-24`: the module `c₀₀(B)`

The corpus statement `HilbertModule.StabilizationInput` has no completeness hypothesis.
This file builds the pre-Hilbert module of finitely supported sequences

  `c₀₀(B) = {f ∈ H_B | f i = 0 for all large i}`,

with the inner product and action of `H_B` restricted to it. It is the counterexample
used in `KasparovClosedCounter.lean`.

* `finSupp B`: the finitely supported vectors, as a `ℂ`-submodule of `H_B`.
* `c00 B`: that submodule as a `CStarModule.{v, v} B`.
* `c00Single k b`: the vector with `b` in coordinate `k`.
* `c00_coe_sum_apply`: coordinates of a finite sum in `c₀₀(B)`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovClosed

open GroupApproximation.HilbertModule

universe v

/-- The finitely supported vectors of `H_B`. -/
def finSupp (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] :
    Submodule ℂ (standardModule ℕ B).carrier where
  carrier := {f : (standardModule ℕ B).carrier | ∃ N : ℕ, ∀ i, N ≤ i → f.1 i = 0}
  add_mem' := by
    rintro f g ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, fun i hi => ?_⟩
    show f.1 i + g.1 i = 0
    rw [hN i (le_trans (le_max_left N M) hi), hM i (le_trans (le_max_right N M) hi),
      add_zero]
  zero_mem' := ⟨0, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨N, hN⟩
    refine ⟨N, fun i hi => ?_⟩
    show c • f.1 i = 0
    rw [hN i hi, smul_zero]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.finSupp

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem mem_finSupp (f : (standardModule ℕ B).carrier) :
    f ∈ finSupp B ↔ ∃ N : ℕ, ∀ i, N ≤ i → f.1 i = 0 := Iff.rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.mem_finSupp

/-- The action of `B` preserves finite support. -/
theorem act_mem_finSupp (f : (standardModule ℕ B).carrier) (hf : f ∈ finSupp B) (b : B) :
    (standardModule ℕ B).act f b ∈ finSupp B := by
  obtain ⟨N, hN⟩ := (mem_finSupp f).mp hf
  refine (mem_finSupp _).mpr ⟨N, fun i hi => ?_⟩
  show f.1 i * b = 0
  rw [hN i hi, zero_mul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.act_mem_finSupp

/-- **`c₀₀(B)`**: the finitely supported sequences, with the structure of `H_B`. -/
noncomputable def c00 (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] : CStarModule.{v, v} B where
  carrier := ↥(finSupp B)
  act f b := ⟨(standardModule ℕ B).act f.1 b, act_mem_finSupp f.1 f.2 b⟩
  inner f g := (standardModule ℕ B).inner f.1 g.1
  act_add_left f g b := Subtype.ext ((standardModule ℕ B).act_add_left f.1 g.1 b)
  act_add_right f b c := Subtype.ext ((standardModule ℕ B).act_add_right f.1 b c)
  act_assoc f b c := Subtype.ext ((standardModule ℕ B).act_assoc f.1 b c)
  act_smul c f b := Subtype.ext ((standardModule ℕ B).act_smul c f.1 b)
  inner_add_right f g h := (standardModule ℕ B).inner_add_right f.1 g.1 h.1
  inner_smul_right c f g := (standardModule ℕ B).inner_smul_right c f.1 g.1
  inner_act_right f g b := (standardModule ℕ B).inner_act_right f.1 g.1 b
  inner_star f g := (standardModule ℕ B).inner_star f.1 g.1
  inner_self_isPositive f := (standardModule ℕ B).inner_self_isPositive f.1
  inner_self_eq_zero f hf := Subtype.ext ((standardModule ℕ B).inner_self_eq_zero f.1 hf)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.c00

/-- The norm of `c₀₀(B)` is the norm of `H_B`. -/
theorem c00_norm (f : (c00 B).carrier) : (c00 B).norm f = (standardModule ℕ B).norm f.1 :=
  rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.c00_norm

/-- The vector of `c₀₀(B)` with `b` in coordinate `k` and `0` elsewhere. -/
noncomputable def c00Single (k : ℕ) (b : B) : (c00 B).carrier :=
  ⟨KasparovStab.single k b,
    (mem_finSupp _).mpr ⟨k + 1, fun i hi => KasparovStab.single_coe_of_ne b (by omega)⟩⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.c00Single

theorem c00Single_coe (k : ℕ) (b : B) : (c00Single k b).1 = KasparovStab.single k b := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.c00Single_coe

/-- Coordinates of a finite sum in `c₀₀(B)`. -/
theorem c00_coe_sum_apply {ι : Type*} (s : Finset ι) (g : ι → (c00 B).carrier) (j : ℕ) :
    (∑ i ∈ s, g i).1.1 j = ∑ i ∈ s, (g i).1.1 j := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty] <;> rfl
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih] <;> rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovClosed.c00_coe_sum_apply

end KasparovClosed
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
