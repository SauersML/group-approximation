import GroupApproximation.BooneHigman.Metabelian.SuslinNormalOrthogonal
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Ring
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin normality, part 3: Suslin's lemma

Lane `bh-met-39b`.  **Suslin's lemma**: if `n ≥ 3` (encoded as: every two indices avoid a
third one), `uᵀ v = 1` and `wᵀ v = 0`, then `1 + v wᵀ ∈ E_n(A)`
(`suslinNormal_inE_of_unimodular`).  The proof writes
`w = ∑_p ∑_q r_{pq}`, `r_{pq} = (u_p w_q)(v_p e_q - v_q e_p)` (`suslinNormal_decomposition`);
each `r_{pq}` satisfies `r_{pq}ᵀ v = 0` and vanishes at an index `k ∉ {p, q}`, so
`1 + v r_{pq}ᵀ ∈ E_n(A)`, and these multiply to `1 + v wᵀ` because the partial sums stay
orthogonal to `v` (`suslinNormal_inE_sum`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

section SuslinLemma

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A]

/-- Summing orthogonal directions: if each `y b` is orthogonal to `v` and `1 + v (y b)ᵀ` is
elementary, then the same holds for every finite partial sum. -/
theorem suslinNormal_inE_sum {κ : Type*} [DecidableEq κ] (v : ι → A) (y : κ → ι → A)
    (s : Finset κ)
    (hy : ∀ b, y b ⬝ᵥ v = 0 ∧ SuslinNormalInE ι A (1 + Matrix.vecMulVec v (y b))) :
    (∑ b ∈ s, y b) ⬝ᵥ v = 0 ∧
      SuslinNormalInE ι A (1 + Matrix.vecMulVec v (∑ b ∈ s, y b)) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, zero_dotProduct, Matrix.vecMulVec_zero, add_zero]
    exact ⟨rfl, suslinNormal_inE_one⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, add_dotProduct, (hy a).1, ih.1, add_zero,
      Matrix.vecMulVec_add]
    exact ⟨rfl, suslinNormal_inE_add (hy a).2 ih.2 (suslinNormal_vecMulVec_mul_of_dot (hy a).1)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_sum

/-- Suslin's elementary directions `r_{pq} = (u_p w_q)(v_p e_q - v_q e_p)`. -/
def suslinNormalTerm (u v w : ι → A) (p q : ι) : ι → A :=
  (u p * w q) • (Pi.single q (v p) - Pi.single p (v q))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormalTerm

/-- **Suslin's decomposition.**  If `uᵀ v = 1` and `wᵀ v = 0` then `w = ∑_p ∑_q r_{pq}`. -/
theorem suslinNormal_decomposition (u v w : ι → A) (huv : u ⬝ᵥ v = 1) (hwv : w ⬝ᵥ v = 0) :
    (∑ p, ∑ q, suslinNormalTerm u v w p q) = w := by
  funext m
  simp only [suslinNormalTerm, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib]
  have hA : ∀ p, ∑ q, u p * w q * Pi.single q (v p) m = w m * (u p * v p) := by
    intro p
    rw [Finset.sum_eq_single m]
    · rw [Pi.single_eq_same]
      ring
    · intro q _ hqm
      rw [Pi.single_eq_of_ne' hqm, mul_zero]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  have hB : ∑ p, ∑ q, u p * w q * Pi.single p (v q) m = u m * (w ⬝ᵥ v) := by
    rw [Finset.sum_comm, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_eq_single m]
    · rw [Pi.single_eq_same]
      ring
    · intro p _ hpm
      rw [Pi.single_eq_of_ne' hpm, mul_zero]
    · intro hm
      exact absurd (Finset.mem_univ m) hm
  have huv' : ∑ p, u p * v p = 1 := huv
  rw [hB, hwv, mul_zero, sub_zero]
  simp only [hA]
  rw [← Finset.mul_sum, huv', mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_decomposition

/-- Each direction `r_{pq}` gives an elementary transvection `1 + v r_{pq}ᵀ`. -/
theorem suslinNormal_term_spec (h3 : ∀ p q : ι, ∃ k, k ≠ p ∧ k ≠ q) (u v w : ι → A)
    (p q : ι) :
    suslinNormalTerm u v w p q ⬝ᵥ v = 0 ∧
      SuslinNormalInE ι A (1 + Matrix.vecMulVec v (suslinNormalTerm u v w p q)) := by
  have hdot : suslinNormalTerm u v w p q ⬝ᵥ v = 0 := by
    rw [suslinNormalTerm, smul_dotProduct, sub_dotProduct, single_dotProduct,
      single_dotProduct, mul_comm (v p) (v q), sub_self, smul_zero]
  obtain ⟨k, hkp, hkq⟩ := h3 p q
  have hk : suslinNormalTerm u v w p q k = 0 := by
    rw [suslinNormalTerm, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne hkq,
      Pi.single_eq_of_ne hkp, sub_zero, smul_zero]
  exact ⟨hdot, suslinNormal_inE_of_dot_zero hk hdot⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_term_spec

/-- **Suslin's lemma.**  If every two indices avoid a third (`n ≥ 3`), `uᵀ v = 1` and
`wᵀ v = 0`, then `1 + v wᵀ ∈ E_ι(A)`. -/
theorem suslinNormal_inE_of_unimodular (h3 : ∀ p q : ι, ∃ k, k ≠ p ∧ k ≠ q)
    (u v w : ι → A) (huv : u ⬝ᵥ v = 1) (hwv : w ⬝ᵥ v = 0) :
    SuslinNormalInE ι A (1 + Matrix.vecMulVec v w) := by
  have hrow : ∀ p : ι, (∑ q, suslinNormalTerm u v w p q) ⬝ᵥ v = 0 ∧
      SuslinNormalInE ι A (1 + Matrix.vecMulVec v (∑ q, suslinNormalTerm u v w p q)) :=
    fun p => suslinNormal_inE_sum v (fun q => suslinNormalTerm u v w p q) Finset.univ
      (fun q => suslinNormal_term_spec h3 u v w p q)
  have hall := suslinNormal_inE_sum v (fun p => ∑ q, suslinNormalTerm u v w p q)
    Finset.univ hrow
  rw [← suslinNormal_decomposition u v w huv hwv]
  exact hall.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinNormal_inE_of_unimodular

end SuslinLemma

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
