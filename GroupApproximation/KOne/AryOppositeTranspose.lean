import GroupApproximation.Leavitt.AryWindowReduction
import Mathlib.Algebra.Algebra.Opposite
import GroupApproximation.Meta.AxiomGuard

/-!
# The transpose anti-automorphism of `L_k(1,d)`

`KOne/OppositeTranspose.lean` at arbitrary arity.  The opposite ring of any ring carrying
a complete matrix family carries one as well, with `s` and `t` exchanged
(`CompleteMatrixFamily.oppositeFamily`); the universal property of the presented algebra
therefore produces `θ : L_k(1,d) →ₐ (L_k(1,d))ᵐᵒᵖ`, whose unopped form `θ̂` is the
classical transpose `sᵢ ↔ tᵢ`.  It is an involution, sends `s_a t_b` to `s_b t_a`, and
flips degree windows `[lo, hi] ↦ [-hi, -lo]`, which transports every one-sided window
theorem to its mirror.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open MulOpposite

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The opposite family: `s` and `t` exchanged in the opposite ring. -/
def oppositeFamily (F : CompleteMatrixFamily A ι) : CompleteMatrixFamily Aᵐᵒᵖ ι where
  left i := op (F.right i)
  right i := op (F.left i)
  orthogonal i j := by
    rw [← op_mul, F.orthogonal j i]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl, op_one]
    · rw [if_neg (Ne.symm h), if_neg h, op_zero]
  complete := by
    rw [show (∑ i, op (F.right i) * op (F.left i)) = op (∑ i, F.left i * F.right i) from by
      rw [op_sum]
      exact Finset.sum_congr rfl fun i _ ↦ (op_mul _ _).symm]
    rw [F.complete, op_one]

end CompleteMatrixFamily

namespace AryLeavitt

open CompleteMatrixFamily MulOpposite

variable (k : Type) [Field k] (d : ℕ)

/-- The universal map to the opposite algebra. -/
noncomputable def theta : AryLeavittAlgebra k d →ₐ[k] (AryLeavittAlgebra k d)ᵐᵒᵖ :=
  lift (family k d).oppositeFamily

/-- The transpose anti-automorphism (unopped form). -/
noncomputable def thetaHat (x : AryLeavittAlgebra k d) : AryLeavittAlgebra k d :=
  unop (theta k d x)

theorem thetaHat_add (x y : AryLeavittAlgebra k d) :
    thetaHat k d (x + y) = thetaHat k d x + thetaHat k d y := by
  unfold thetaHat
  rw [map_add, unop_add]

theorem thetaHat_mul (x y : AryLeavittAlgebra k d) :
    thetaHat k d (x * y) = thetaHat k d y * thetaHat k d x := by
  unfold thetaHat
  rw [map_mul, unop_mul]

theorem thetaHat_one : thetaHat k d 1 = 1 := by
  unfold thetaHat
  rw [map_one, unop_one]

theorem thetaHat_zero : thetaHat k d 0 = 0 := by
  unfold thetaHat
  rw [map_zero, unop_zero]

theorem thetaHat_smul (c : k) (x : AryLeavittAlgebra k d) :
    thetaHat k d (c • x) = c • thetaHat k d x := by
  unfold thetaHat
  rw [map_smul]
  rfl

theorem thetaHat_sub (x y : AryLeavittAlgebra k d) :
    thetaHat k d (x - y) = thetaHat k d x - thetaHat k d y := by
  unfold thetaHat
  rw [map_sub, unop_sub]

theorem thetaHat_genS (i : Fin d) : thetaHat k d (genS k d i) = genT k d i := by
  unfold thetaHat theta
  rw [lift_genS]
  rfl

theorem thetaHat_genT (i : Fin d) : thetaHat k d (genT k d i) = genS k d i := by
  unfold thetaHat theta
  rw [lift_genT]
  rfl

/-- `θ̂` reverses words: `s_a ↦ t_a`. -/
theorem thetaHat_wordS (a : List (Fin d)) :
    thetaHat k d ((family k d).wordS a) = (family k d).wordT a := by
  induction a with
  | nil =>
      rw [wordS_nil, wordT_nil]
      exact thetaHat_one k d
  | cons i a ih =>
      rw [wordS_cons, wordT_cons, thetaHat_mul, ih,
        show (family k d).left i = genS k d i from rfl, thetaHat_genS]
      rfl

theorem thetaHat_wordT (b : List (Fin d)) :
    thetaHat k d ((family k d).wordT b) = (family k d).wordS b := by
  induction b with
  | nil =>
      rw [wordS_nil, wordT_nil]
      exact thetaHat_one k d
  | cons i b ih =>
      rw [wordS_cons, wordT_cons, thetaHat_mul, ih,
        show (family k d).right i = genT k d i from rfl, thetaHat_genT]
      rfl

/-- The generators generate. -/
theorem adjoin_generators_eq_top :
    Algebra.adjoin k
      (Set.range (fun g : Generator d ↦ quotientMap k d (FreeAlgebra.ι k g))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective k (Relation k d) x
  have hp : p ∈ Algebra.adjoin k (Set.range (FreeAlgebra.ι k : Generator d → Free k d)) := by
    rw [FreeAlgebra.adjoin_range_ι]
    exact Algebra.mem_top
  have h1 : RingQuot.mkAlgHom k (Relation k d) p ∈
      Algebra.adjoin k ((RingQuot.mkAlgHom k (Relation k d)) ''
        Set.range (FreeAlgebra.ι k : Generator d → Free k d)) := by
    rw [← AlgHom.map_adjoin]
    exact Set.mem_image_of_mem _ hp
  refine Algebra.adjoin_mono ?_ h1
  rintro y ⟨z, ⟨g, rfl⟩, rfl⟩
  exact ⟨g, rfl⟩

/-- `θ̂` is an involution. -/
theorem thetaHat_thetaHat (x : AryLeavittAlgebra k d) :
    thetaHat k d (thetaHat k d x) = x := by
  have hx : x ∈ Algebra.adjoin k
      (Set.range (fun g : Generator d ↦ quotientMap k d (FreeAlgebra.ι k g))) := by
    rw [adjoin_generators_eq_top]
    exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      rcases g with i | i
      · show thetaHat k d (thetaHat k d (genS k d i)) = genS k d i
        rw [thetaHat_genS, thetaHat_genT]
      · show thetaHat k d (thetaHat k d (genT k d i)) = genT k d i
        rw [thetaHat_genT, thetaHat_genS]
  | algebraMap c =>
      rw [Algebra.algebraMap_eq_smul_one, thetaHat_smul, thetaHat_one, thetaHat_smul,
        thetaHat_one]
  | add y z _ _ hy hz =>
      rw [thetaHat_add, thetaHat_add, hy, hz]
  | mul y z _ _ hy hz =>
      rw [thetaHat_mul, thetaHat_mul, hy, hz]

/-- `θ̂` flips degree windows. -/
theorem thetaHat_mem_span_degree {lo hi : ℤ} {x : AryLeavittAlgebra k d}
    (hx : x ∈ Submodule.span k ((family k d).degreeMonomials lo hi)) :
    thetaHat k d x ∈ Submodule.span k ((family k d).degreeMonomials (-hi) (-lo)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, b, hl, hh, rfl⟩ := hy
      rw [thetaHat_mul, thetaHat_wordS, thetaHat_wordT]
      exact Submodule.subset_span ⟨b, a, by omega, by omega, rfl⟩
  | zero =>
      rw [thetaHat_zero]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      rw [thetaHat_add]
      exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
      rw [thetaHat_smul]
      exact Submodule.smul_mem _ c hy

/-- The unit induced by `θ̂`. -/
noncomputable def thetaUnit (u : (AryLeavittAlgebra k d)ˣ) : (AryLeavittAlgebra k d)ˣ where
  val := thetaHat k d (u : AryLeavittAlgebra k d)
  inv := thetaHat k d ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d)
  val_inv := by
    rw [← thetaHat_mul, Units.inv_mul, thetaHat_one]
  inv_val := by
    rw [← thetaHat_mul, Units.mul_inv, thetaHat_one]

@[simp] theorem thetaUnit_val (u : (AryLeavittAlgebra k d)ˣ) :
    ((thetaUnit k d u : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) =
      thetaHat k d (u : AryLeavittAlgebra k d) := rfl

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavitt.thetaHat_wordS
#audit_axioms GroupApproximation.AryLeavitt.thetaHat_wordT
#audit_axioms GroupApproximation.AryLeavitt.thetaHat_thetaHat
#audit_axioms GroupApproximation.AryLeavitt.thetaHat_mem_span_degree
