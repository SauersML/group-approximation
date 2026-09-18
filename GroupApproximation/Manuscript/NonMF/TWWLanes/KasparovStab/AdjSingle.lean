import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Operator
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: the adjoint on single vectors

* `adjFun_single_fst` and `adjFun_single_snd`: `T⋆ (single n c) = (single n (4⁻ⁿ c), gen x n · c)`.
* `gen_act_inv`: rescaling `c` by the inverse scale recovers `x k · b`.
* `isApprox_inr_act`: `(0, x k · b)` lies in the closure of the range of `T⋆`. Take
  `n = Nat.pair k j`: the error of `T⋆ (single n c)` is `2⁻ⁿ (1 + ‖x k‖) ‖b‖ ≤ 2⁻ʲ K`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovStab

open GroupApproximation.HilbertModule

universe v w

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {E : CStarModule.{v, w} B}

/-- The scale of `gen x n`. -/
noncomputable def rgen (x : ℕ → E.carrier) (n : ℕ) : ℝ :=
  coef n * (1 + E.norm (x (Nat.unpair n).1))⁻¹

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.rgen

theorem rgen_pos (x : ℕ → E.carrier) (n : ℕ) : 0 < rgen x n :=
  mul_pos (coef_pos n) (inv_pos.mpr (by linarith [E.norm_nonneg (x (Nat.unpair n).1)]))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.rgen_pos

theorem gen_eq (x : ℕ → E.carrier) (n : ℕ) :
    gen x n = ((rgen x n : ℝ) : ℂ) • x (Nat.unpair n).1 := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.gen_eq

theorem gen_act_inv (x : ℕ → E.carrier) (n : ℕ) (b : B) :
    E.act (gen x n) ((((rgen x n)⁻¹ : ℝ) : ℂ) • b) = E.act (x (Nat.unpair n).1) b := by
  rw [gen_eq, E.act_smul, act_smul_right E, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (rgen_pos x n).ne', Complex.ofReal_one, one_smul]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.gen_act_inv

theorem wt_mul_rgen_inv (x : ℕ → E.carrier) (n : ℕ) :
    wt n * (rgen x n)⁻¹ = coef n * (1 + E.norm (x (Nat.unpair n).1)) := by
  have hc : coef n ≠ 0 := (coef_pos n).ne'
  calc wt n * (rgen x n)⁻¹
      = coef n * (coef n * (coef n)⁻¹) * (1 + E.norm (x (Nat.unpair n).1)) := by
        rw [wt, rgen, mul_inv, inv_inv]
        ring
    _ = coef n * (1 + E.norm (x (Nat.unpair n).1)) := by rw [mul_inv_cancel₀ hc, mul_one]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.wt_mul_rgen_inv

theorem adjFun_single_fst (hE : IsCompleteModule E) (x : ℕ → E.carrier) (n : ℕ) (c : B) :
    (adjFun hE x (single n c)).1 = single n (((wt n : ℝ) : ℂ) • c) := by
  refine Subtype.ext (funext fun i => ?_)
  show ((wt i : ℝ) : ℂ) • (single n c).1 i = (single n (((wt n : ℝ) : ℂ) • c)).1 i
  by_cases h : i = n
  · rw [h, single_coe_self, single_coe_self]
  · rw [single_coe_of_ne c h, single_coe_of_ne _ h, smul_zero]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.adjFun_single_fst

theorem adjFun_single_snd (hE : IsCompleteModule E) (x : ℕ → E.carrier) (n : ℕ) (c : B) :
    (adjFun hE x (single n c)).2 = E.act (gen x n) c := by
  have hconst : IsLimit E (fun N => ∑ m ∈ Finset.range N, adjSeries x (single n c) m)
      (E.act (gen x n) c) := by
    intro ε hε
    refine ⟨n + 1, fun N hN => ?_⟩
    have hsum : ∑ m ∈ Finset.range N, adjSeries x (single n c) m = E.act (gen x n) c := by
      rw [Finset.sum_eq_single n]
      · show E.act (gen x n) ((single n c).1 n) = E.act (gen x n) c
        rw [single_coe_self]
      · intro m _ hmn
        show E.act (gen x m) ((single n c).1 m) = 0
        rw [single_coe_of_ne c hmn, act_zero_right]
      · intro hn
        exact absurd (Finset.mem_range.mpr (by omega)) hn
    show E.norm (∑ m ∈ Finset.range N, adjSeries x (single n c) m - E.act (gen x n) c) ≤ ε
    rw [hsum, sub_self, E.norm_zero_vector]
    exact hε.le
  exact (adjFun_isLimit hE x (single n c)).unique hconst

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.adjFun_single_snd

/-- **`(0, x k · b)` is approximable by `T⋆`.** -/
theorem isApprox_inr_act (hE : IsCompleteModule E) (x : ℕ → E.carrier) (k : ℕ) (b : B) :
    IsApprox (Adjointable.adjoint (mingoPhillips hE x))
      (((0 : (standardModule ℕ B).carrier), E.act (x k) b) :
        (prod (standardModule ℕ B) E).carrier) := by
  intro ε hε
  have hK0 : 0 ≤ (1 + E.norm (x k)) * ‖b‖ :=
    mul_nonneg (by linarith [E.norm_nonneg (x k)]) (norm_nonneg b)
  have hK : 0 < (1 + E.norm (x k)) * ‖b‖ + 1 := by linarith
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hε hK) (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = Nat.pair k j := ⟨_, rfl⟩
  have hk : (Nat.unpair n).1 = k := by rw [hn, Nat.unpair_pair]
  have hjn : j ≤ n := by
    rw [hn]
    exact Nat.right_le_pair k j
  have hcoef : coef n ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hjn
  refine ⟨single n ((((rgen x n)⁻¹ : ℝ) : ℂ) • b), ?_⟩
  have hfst := adjFun_single_fst hE x n ((((rgen x n)⁻¹ : ℝ) : ℂ) • b)
  have hsnd : (adjFun hE x (single n ((((rgen x n)⁻¹ : ℝ) : ℂ) • b))).2 = E.act (x k) b := by
    rw [adjFun_single_snd, gen_act_inv, hk]
  have hdiff : adjFun hE x (single n ((((rgen x n)⁻¹ : ℝ) : ℂ) • b))
        - (((0 : (standardModule ℕ B).carrier), E.act (x k) b) :
          (prod (standardModule ℕ B) E).carrier)
      = ((single n (((wt n : ℝ) : ℂ) • (((rgen x n)⁻¹ : ℝ) : ℂ) • b), (0 : E.carrier)) :
          (prod (standardModule ℕ B) E).carrier) := by
    refine Prod.ext ?_ ?_
    · show (adjFun hE x (single n ((((rgen x n)⁻¹ : ℝ) : ℂ) • b))).1 - 0
        = single n (((wt n : ℝ) : ℂ) • (((rgen x n)⁻¹ : ℝ) : ℂ) • b)
      rw [sub_zero, hfst]
    · show (adjFun hE x (single n ((((rgen x n)⁻¹ : ℝ) : ℂ) • b))).2 - E.act (x k) b = 0
      rw [hsnd, sub_self]
  show (prod (standardModule ℕ B) E).norm
      (adjFun hE x (single n ((((rgen x n)⁻¹ : ℝ) : ℂ) • b))
        - (((0 : (standardModule ℕ B).carrier), E.act (x k) b) :
          (prod (standardModule ℕ B) E).carrier)) ≤ ε
  rw [hdiff, Adjointable.norm_inl, norm_single, norm_smul, norm_smul,
    Complex.norm_of_nonneg (wt_pos n).le,
    Complex.norm_of_nonneg (inv_nonneg.mpr (rgen_pos x n).le)]
  have hsmall : (1 / 2 : ℝ) ^ j * ((1 + E.norm (x k)) * ‖b‖ + 1) < ε :=
    (lt_div_iff₀ hK).mp hj
  calc wt n * ((rgen x n)⁻¹ * ‖b‖) = (wt n * (rgen x n)⁻¹) * ‖b‖ := (mul_assoc _ _ _).symm
    _ = coef n * ((1 + E.norm (x k)) * ‖b‖) := by rw [wt_mul_rgen_inv, hk, mul_assoc]
    _ ≤ (1 / 2 : ℝ) ^ j * ((1 + E.norm (x k)) * ‖b‖ + 1) :=
        mul_le_mul hcoef (by linarith) hK0 (by positivity)
    _ ≤ ε := hsmall.le

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isApprox_inr_act

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
