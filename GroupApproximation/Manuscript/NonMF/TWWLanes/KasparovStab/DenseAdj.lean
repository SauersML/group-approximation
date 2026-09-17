import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.AdjSingle
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: the adjoint has dense range

Let `x` be a generating sequence of a complete module `E` and `T = mingoPhillips hE x`.
Then `T⋆ : H_B → H_B ⊕ E` has dense range.

* `isApprox_inl_single`: `(single n b, 0) = T⋆ (single n (4ⁿ b)) - (0, x k · c)`, and the
  second vector is approximable by `isApprox_inr_act`.
* `isApprox_inl`: `(z, 0)` is a norm limit of finite sums of such vectors
  (`exists_truncate_norm_le`).
* `isApprox_inr`: `(0, y)` is a norm limit of finite sums `(0, ∑ x kⱼ · bⱼ)`. This is where
  the generating hypothesis enters.
* `hasDenseRange_adjoint_mingoPhillips`: `(z, y) = (z, 0) + (0, y)`.
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

theorem sum_inl {ι : Type*} (s : Finset ι) (f : ι → (standardModule ℕ B).carrier) :
    (∑ i ∈ s, ((f i, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier))
      = ((∑ i ∈ s, f i, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty] <;> rfl
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih]
    exact Prod.ext rfl (add_zero (0 : E.carrier))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.sum_inl

theorem sum_inr {ι : Type*} (s : Finset ι) (f : ι → E.carrier) :
    (∑ i ∈ s, (((0 : (standardModule ℕ B).carrier), f i) :
        (prod (standardModule ℕ B) E).carrier))
      = (((0 : (standardModule ℕ B).carrier), ∑ i ∈ s, f i) :
        (prod (standardModule ℕ B) E).carrier) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty] <;> rfl
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih]
    exact Prod.ext (add_zero (0 : (standardModule ℕ B).carrier)) rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.sum_inr

/-- **`(single n b, 0)` is approximable by `T⋆`.** -/
theorem isApprox_inl_single (hE : IsCompleteModule E) (x : ℕ → E.carrier) (n : ℕ) (b : B) :
    IsApprox (Adjointable.adjoint (mingoPhillips hE x))
      ((single n b, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier) := by
  obtain ⟨c, hc⟩ : ∃ c : B, c = (((wt n)⁻¹ : ℝ) : ℂ) • b := ⟨_, rfl⟩
  have heq : ((single n b, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier)
      = (Adjointable.adjoint (mingoPhillips hE x)).toFun (single n c)
        - (((0 : (standardModule ℕ B).carrier),
            E.act (x (Nat.unpair n).1) (((rgen x n : ℝ) : ℂ) • c)) :
          (prod (standardModule ℕ B) E).carrier) := by
    refine Prod.ext ?_ ?_
    · show single n b = (adjFun hE x (single n c)).1 - 0
      rw [sub_zero, adjFun_single_fst, hc, smul_smul, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (wt_pos n).ne', Complex.ofReal_one, one_smul]
    · show (0 : E.carrier)
        = (adjFun hE x (single n c)).2 - E.act (x (Nat.unpair n).1) (((rgen x n : ℝ) : ℂ) • c)
      rw [adjFun_single_snd, gen_eq, E.act_smul, act_smul_right E, sub_self]
  rw [heq]
  exact (isApprox_apply (Adjointable.adjoint (mingoPhillips hE x)) (single n c)).sub
    (Adjointable.adjoint (mingoPhillips hE x))
    (isApprox_inr_act hE x (Nat.unpair n).1 (((rgen x n : ℝ) : ℂ) • c))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isApprox_inl_single

/-- **`(z, 0)` is approximable by `T⋆`.** -/
theorem isApprox_inl (hE : IsCompleteModule E) (x : ℕ → E.carrier)
    (z : (standardModule ℕ B).carrier) :
    IsApprox (Adjointable.adjoint (mingoPhillips hE x))
      ((z, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier) := by
  refine IsApprox.of_approx (Adjointable.adjoint (mingoPhillips hE x)) fun ε hε => ?_
  obtain ⟨s, hs⟩ := exists_truncate_norm_le z hε
  refine ⟨((truncate s z, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier), ?_, ?_⟩
  · have h := IsApprox.sum (Adjointable.adjoint (mingoPhillips hE x)) s
      (fun i => ((single i (z.1 i), (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier))
      fun i _ => isApprox_inl_single hE x i (z.1 i)
    rw [sum_inl s (fun i => single i (z.1 i)), ← truncate_eq_sum s z] at h
    exact h
  · have hd : ((truncate s z, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier)
          - ((z, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier)
        = ((truncate s z - z, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier) :=
      Prod.ext rfl (sub_self (0 : E.carrier))
    rw [hd, Adjointable.norm_inl]
    exact (modNorm_sub_comm (standardModule ℕ B) (truncate s z) z).trans_le hs

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isApprox_inl

/-- **`(0, y)` is approximable by `T⋆`** when `x` generates `E`. -/
theorem isApprox_inr (hE : IsCompleteModule E) (x : ℕ → E.carrier)
    (hx : ∀ (y : E.carrier) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (b : Fin n → B) (k : Fin n → ℕ),
      E.norm (y - ∑ j, E.act (x (k j)) (b j)) ≤ ε)
    (y : E.carrier) :
    IsApprox (Adjointable.adjoint (mingoPhillips hE x))
      (((0 : (standardModule ℕ B).carrier), y) : (prod (standardModule ℕ B) E).carrier) := by
  refine IsApprox.of_approx (Adjointable.adjoint (mingoPhillips hE x)) fun ε hε => ?_
  obtain ⟨n, b, k, hy⟩ := hx y ε hε
  refine ⟨(((0 : (standardModule ℕ B).carrier), ∑ j, E.act (x (k j)) (b j)) :
    (prod (standardModule ℕ B) E).carrier), ?_, ?_⟩
  · have h := IsApprox.sum (Adjointable.adjoint (mingoPhillips hE x)) Finset.univ
      (fun j => (((0 : (standardModule ℕ B).carrier), E.act (x (k j)) (b j)) :
        (prod (standardModule ℕ B) E).carrier))
      fun j _ => isApprox_inr_act hE x (k j) (b j)
    rw [sum_inr Finset.univ (fun j => E.act (x (k j)) (b j))] at h
    exact h
  · have hd : (((0 : (standardModule ℕ B).carrier), ∑ j, E.act (x (k j)) (b j)) :
          (prod (standardModule ℕ B) E).carrier)
          - (((0 : (standardModule ℕ B).carrier), y) : (prod (standardModule ℕ B) E).carrier)
        = (((0 : (standardModule ℕ B).carrier), ∑ j, E.act (x (k j)) (b j) - y) :
          (prod (standardModule ℕ B) E).carrier) :=
      Prod.ext (sub_self (0 : (standardModule ℕ B).carrier)) rfl
    rw [hd, Adjointable.norm_inr, modNorm_sub_comm]
    exact hy

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isApprox_inr

/-- **The adjoint of the Mingo--Phillips operator has dense range.** -/
theorem hasDenseRange_adjoint_mingoPhillips (hE : IsCompleteModule E) (x : ℕ → E.carrier)
    (hx : ∀ (y : E.carrier) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (b : Fin n → B) (k : Fin n → ℕ),
      E.norm (y - ∑ j, E.act (x (k j)) (b j)) ≤ ε) :
    HasDenseRange (Adjointable.adjoint (mingoPhillips hE x)) := by
  intro p
  have hp : p = ((p.1, (0 : E.carrier)) : (prod (standardModule ℕ B) E).carrier)
      + (((0 : (standardModule ℕ B).carrier), p.2) : (prod (standardModule ℕ B) E).carrier) :=
    Prod.ext (add_zero p.1).symm (zero_add p.2).symm
  have h := (isApprox_inl hE x p.1).add (Adjointable.adjoint (mingoPhillips hE x))
    (isApprox_inr hE x hx p.2)
  rw [← hp] at h
  exact h

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.hasDenseRange_adjoint_mingoPhillips

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
