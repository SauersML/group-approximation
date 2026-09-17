import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2LocalLifting.Property
import GroupApproximation.Analysis.CStarMatrixFactorization
import Mathlib.Analysis.InnerProductSpace.Adjoint
import GroupApproximation.Meta.AxiomGuard

/-!
# The Choi functional of a completely positive map on an operator system (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.54–56 (table row A2, Ozawa's remark that the
full C⋆-algebra of a non-hyperlinear Kazhdan group has no local lifting property).  The proof uses
Arveson's extension theorem (Ozawa, *About the QWEP conjecture*, Theorem 2.2); this file is its
Choi step, for a map `ψ : E → B(ℂᵏ)` on an operator system `E`.

Matrices over `E` form an operator system of `Mₖ(A)`, and the **Choi functional**

  `s(b) = ∑ p q, ⟪e_p, ψ (b p q) e_q⟫`

on it is nonnegative on ambient positives exactly because `ψ` is completely positive on `E`.

* `matrixSystem E k`: matrices with entries in `E`; it contains `1` and is closed under the star
  when `E` is an operator system.
* `systemChoiFunctional_nonneg`: factor an ambient positive `b = star N * N`; complete positivity
  on `E` gives `[ψ (b p q)] = star P * P`, and the value is `∑ r ‖∑ q P r q e_q‖²`.
* `systemChoiFunctional_single`: on a single-entry matrix the functional recovers the matrix
  coefficients of `ψ` (the Choi correspondence).

The notions `IsOperatorSystem` and `IsCompletelyPositiveOn` are those of
`Full/A2LocalLifting/Property.lean`.  Re-proof of the never-wired orphan
`Analysis/OperatorSystemChoiFunctional.lean` (left untouched).
-/

namespace GroupApproximation
namespace Full
namespace A2OperatorSystems

open CStarExactness
open GroupApproximation.Full.A2LocalLifting
open scoped InnerProductSpace

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- Matrices with entries in a complex subspace. -/
def matrixSystem (E : Submodule ℂ A) (k : ℕ) :
    Submodule ℂ (CStarMatrix (Fin k) (Fin k) A) where
  carrier := {M | ∀ p q, M p q ∈ E}
  add_mem' := by
    intro M N hM hN p q
    exact add_mem (hM p q) (hN p q)
  zero_mem' := by
    intro p q
    exact zero_mem E
  smul_mem' := by
    intro c M hM p q
    exact E.smul_mem c (hM p q)

theorem mem_matrixSystem_iff {E : Submodule ℂ A} {k : ℕ}
    {M : CStarMatrix (Fin k) (Fin k) A} :
    M ∈ matrixSystem E k ↔ ∀ p q, M p q ∈ E := Iff.rfl

/-- Matrices over an operator system contain the unit. -/
theorem one_mem_matrixSystem {E : Submodule ℂ A} (hE : IsOperatorSystem E)
    (k : ℕ) : (1 : CStarMatrix (Fin k) (Fin k) A) ∈ matrixSystem E k := by
  intro p q
  have h : (1 : CStarMatrix (Fin k) (Fin k) A) p q = if p = q then 1 else 0 :=
    CStarMatrix.one_apply
  rw [h]
  split
  · exact And.left hE
  · exact zero_mem E

/-- Matrices over an operator system are closed under the star. -/
theorem star_mem_matrixSystem {E : Submodule ℂ A} (hE : IsOperatorSystem E)
    {k : ℕ} {M : CStarMatrix (Fin k) (Fin k) A} (hM : M ∈ matrixSystem E k) :
    star M ∈ matrixSystem E k := by
  intro p q
  have h : (star M) p q = star (M q p) := CStarMatrix.star_apply
  rw [h]
  exact And.right hE _ (hM q p)

/-- Matrices over an operator system form an operator system of `Mₖ(A)`. -/
theorem isOperatorSystem_matrixSystem {E : Submodule ℂ A} (hE : IsOperatorSystem E)
    (k : ℕ) : IsOperatorSystem (matrixSystem E k) :=
  And.intro (one_mem_matrixSystem hE k) fun _ hM ↦ star_mem_matrixSystem hE hM

variable (E : Submodule ℂ A) {k : ℕ}

/-- Single-entry matrices over `E` lie in `matrixSystem E k`. -/
theorem single_mem_matrixSystem (c : E) (p₀ q₀ : Fin k) :
    (Matrix.single p₀ q₀ (c : A) : CStarMatrix (Fin k) (Fin k) A)
      ∈ matrixSystem E k := by
  intro p q
  classical
  rw [Matrix.single_apply]
  split
  · exact c.2
  · exact zero_mem E

/-- The entry of a matrix over `E`, as an element of `E`. -/
def systemEntry (b : matrixSystem E k) (p q : Fin k) : E :=
  ⟨(b : CStarMatrix (Fin k) (Fin k) A) p q, b.2 p q⟩

variable (ψ : E →ₗ[ℂ]
  (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)))

/-- **The Choi functional** of `ψ`, on matrices over the operator system. -/
def systemChoiFunctional : matrixSystem E k →ₗ[ℂ] ℂ where
  toFun b := ∑ p : Fin k, ∑ q : Fin k,
    ⟪EuclideanSpace.single p (1 : ℂ),
      ψ (systemEntry E b p q) (EuclideanSpace.single q (1 : ℂ))⟫_ℂ
  map_add' b c := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have h : systemEntry E (b + c) p q
        = systemEntry E b p q + systemEntry E c p q := rfl
    rw [h, map_add, add_apply, inner_add_right]
  map_smul' z b := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have h : systemEntry E (z • b) p q = z • systemEntry E b p q := rfl
    rw [h, map_smul, smul_apply, inner_smul_right, smul_eq_mul]

theorem systemChoiFunctional_apply (b : matrixSystem E k) :
    systemChoiFunctional E ψ b = ∑ p : Fin k, ∑ q : Fin k,
      ⟪EuclideanSpace.single p (1 : ℂ),
        ψ (systemEntry E b p q) (EuclideanSpace.single q (1 : ℂ))⟫_ℂ := rfl

/-- **The Choi functional is nonnegative on ambient positives** (Choi step of Ozawa, Theorem 2.2;
table row A2).  Factor `b = star N * N` over `A`; complete positivity of `ψ` on `E` factors the
matrix of values as `star P * P`, so the value is `∑ r ‖∑ q P r q e_q‖²`. -/
theorem systemChoiFunctional_nonneg [PartialOrder A] [StarOrderedRing A]
    (hψ : IsCompletelyPositiveOn E ψ) (b : matrixSystem E k)
    (hb : 0 ≤ (b : CStarMatrix (Fin k) (Fin k) A)) :
    ∃ r : ℝ, 0 ≤ r ∧ systemChoiFunctional E ψ b = r := by
  obtain ⟨N, hN⟩ := exists_star_mul_self_of_nonneg hb
  let Mc : CStarMatrix (Fin k) (Fin k) E :=
    CStarMatrix.ofMatrix (Matrix.of fun p q ↦ systemEntry E b p q)
  have hMcN : Mc.map (fun x : E ↦ (x : A)) = star N * N := by
    ext p q
    exact congrArg (fun T : CStarMatrix (Fin k) (Fin k) A ↦ T p q) hN
  obtain ⟨P, hP⟩ := hψ k Mc ⟨N, hMcN⟩
  have hentry : ∀ p q : Fin k,
      ψ (systemEntry E b p q) = ∑ r : Fin k, star (P r p) * P r q := by
    intro p q
    calc ψ (systemEntry E b p q) = (Mc.map ⇑ψ) p q := rfl
      _ = (star P * P) p q :=
        congrArg (fun T : CStarMatrix (Fin k) (Fin k)
          (EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k)) ↦ T p q) hP
      _ = ∑ r : Fin k, (star P) p r * P r q := CStarMatrix.mul_apply
      _ = ∑ r : Fin k, star (P r p) * P r q :=
        Finset.sum_congr rfl fun r _ ↦ rfl
  have hval : systemChoiFunctional E ψ b
      = ∑ r : Fin k,
          ⟪∑ p : Fin k, P r p (EuclideanSpace.single p (1 : ℂ)),
            ∑ q : Fin k, P r q (EuclideanSpace.single q (1 : ℂ))⟫_ℂ := by
    rw [systemChoiFunctional_apply]
    calc ∑ p : Fin k, ∑ q : Fin k,
          ⟪EuclideanSpace.single p (1 : ℂ),
            ψ (systemEntry E b p q) (EuclideanSpace.single q (1 : ℂ))⟫_ℂ
        = ∑ p : Fin k, ∑ q : Fin k, ∑ r : Fin k,
            ⟪P r p (EuclideanSpace.single p (1 : ℂ)),
              P r q (EuclideanSpace.single q (1 : ℂ))⟫_ℂ := by
          refine Finset.sum_congr rfl fun p _ ↦
            Finset.sum_congr rfl fun q _ ↦ ?_
          rw [hentry p q, sum_apply, inner_sum]
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          show ⟪EuclideanSpace.single p (1 : ℂ),
              (star (P r p)) (P r q (EuclideanSpace.single q (1 : ℂ)))⟫_ℂ = _
          rw [ContinuousLinearMap.star_eq_adjoint,
            ContinuousLinearMap.adjoint_inner_right]
      _ = ∑ p : Fin k, ∑ r : Fin k, ∑ q : Fin k,
            ⟪P r p (EuclideanSpace.single p (1 : ℂ)),
              P r q (EuclideanSpace.single q (1 : ℂ))⟫_ℂ :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ = ∑ r : Fin k, ∑ p : Fin k, ∑ q : Fin k,
            ⟪P r p (EuclideanSpace.single p (1 : ℂ)),
              P r q (EuclideanSpace.single q (1 : ℂ))⟫_ℂ := Finset.sum_comm
      _ = ∑ r : Fin k,
            ⟪∑ p : Fin k, P r p (EuclideanSpace.single p (1 : ℂ)),
              ∑ q : Fin k, P r q (EuclideanSpace.single q (1 : ℂ))⟫_ℂ := by
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          rw [sum_inner]
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [inner_sum]
  refine ⟨∑ r : Fin k,
      ‖∑ q : Fin k, P r q (EuclideanSpace.single q (1 : ℂ))‖ ^ 2,
    Finset.sum_nonneg fun r _ ↦ sq_nonneg _, ?_⟩
  rw [hval, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Complex.ofReal_pow]
  exact inner_self_eq_norm_sq_to_K _

/-- **The Choi correspondence** (table row A2): evaluation of the Choi functional on a
single-entry matrix recovers the matrix coefficient of `ψ`. -/
theorem systemChoiFunctional_single (c : E) (p₀ q₀ : Fin k) :
    systemChoiFunctional E ψ
        ⟨(Matrix.single p₀ q₀ (c : A) : CStarMatrix (Fin k) (Fin k) A),
          single_mem_matrixSystem E c p₀ q₀⟩
      = ⟪EuclideanSpace.single p₀ (1 : ℂ),
          ψ c (EuclideanSpace.single q₀ (1 : ℂ))⟫_ℂ := by
  classical
  rw [systemChoiFunctional_apply]
  have hzero : ∀ p q : Fin k, ¬(p₀ = p ∧ q₀ = q) →
      systemEntry E
        ⟨(Matrix.single p₀ q₀ (c : A) : CStarMatrix (Fin k) (Fin k) A),
          single_mem_matrixSystem E c p₀ q₀⟩ p q = 0 := by
    intro p q hne
    refine Subtype.ext ?_
    show (Matrix.single p₀ q₀ (c : A)) p q = 0
    rw [Matrix.single_apply, if_neg hne]
  have hsame : systemEntry E
      ⟨(Matrix.single p₀ q₀ (c : A) : CStarMatrix (Fin k) (Fin k) A),
        single_mem_matrixSystem E c p₀ q₀⟩ p₀ q₀ = c := by
    refine Subtype.ext ?_
    show (Matrix.single p₀ q₀ (c : A)) p₀ q₀ = (c : A)
    rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
  rw [Finset.sum_eq_single p₀ (fun p _ hp ↦ ?_)
    (fun h ↦ absurd (Finset.mem_univ p₀) h)]
  · rw [Finset.sum_eq_single q₀ (fun q _ hq ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ q₀) h)]
    · rw [hsame]
    · rw [hzero p₀ q (fun hpq ↦ hq hpq.2.symm), map_zero,
        zero_apply, inner_zero_right]
  · refine Finset.sum_eq_zero fun q _ ↦ ?_
    rw [hzero p q (fun hpq ↦ hp hpq.1.symm), map_zero,
      zero_apply, inner_zero_right]

end

end A2OperatorSystems
end Full
end GroupApproximation

open GroupApproximation.Full.A2OperatorSystems in
#audit_axioms systemChoiFunctional_nonneg

open GroupApproximation.Full.A2OperatorSystems in
#audit_axioms systemChoiFunctional_single
