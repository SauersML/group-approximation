import GroupApproximation.KOne.AryZeroKOne
import GroupApproximation.KOne.AryPureTailNilpotency
import GroupApproximation.Meta.AxiomGuard

/-!
# Every `[0,1]`-window unit of `L_k(1,d)` is a central scalar modulo `stableUnits`

`KOne/WidthTwoReduction.lean` at arbitrary arity.  A unit valued in degrees `{0, 1}` has
invertible balanced part (`AryLeavitt.balanced_component_isUnit`), the balanced part is a
balanced unit (so a central scalar modulo the stably elementary units, by the degree-zero
reduction), the residual tail `1 + η` has nilpotent `η` (`pure_tail_nilpotent`), the corner
transport along the letter `0` turns it into `1 + s₀·(η t₀)` with balanced `η t₀`, and the
nilpotent-tail kill finishes.  The receptacle is `centralClassGroup`, because of the
balanced part.
-/

namespace GroupApproximation
namespace AryLeavitt

open CompleteMatrixFamily MatrixDiagonalization

variable (k : Type) [Field k] (d : ℕ)

/-- **Width-two reduction.** -/
theorem window_zero_one_mem_centralClassGroup (hd : 2 ≤ d) (u : (AryLeavittAlgebra k d)ˣ)
    (hu : (u : AryLeavittAlgebra k d) ∈
      Submodule.span k ((family k d).degreeMonomials 0 1)) :
    u ∈ centralClassGroup (AryLeavittAlgebra k d) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  set F : CompleteMatrixFamily (AryLeavittAlgebra k d) (Fin d) := family k d with hF
  have hdiv : ∀ x : AryLeavittAlgebra k d, x ≠ 0 →
      ∃ p q : AryLeavittAlgebra k d, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k d hd hx
  obtain ⟨y, hymem, hysupp, hysum⟩ := F.exists_components hu
  have hIcc : Finset.Icc (0 : ℤ) 1 = {0, 1} := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hval : (u : AryLeavittAlgebra k d) = y 0 + y 1 := by
    rw [hysum, hIcc, Finset.sum_insert (by simp), Finset.sum_singleton]
  have hcu : IsUnit (y 0) := balanced_component_isUnit k d hd (hymem 0) (hymem 1) u hval
  obtain ⟨uc, hucv⟩ := hcu
  obtain ⟨q, hcq⟩ := F.span_degree_zero_le_levelSpan (k := k) (hymem 0)
  have hucval : (uc : AryLeavittAlgebra k d) ∈ Submodule.span k (F.levelMonomialSet q) := by
    rw [hucv]
    exact hcq
  have hucmem : uc ∈ centralClassGroup (AryLeavittAlgebra k d) :=
    mem_centralClassGroup_of_val_mem_levelSpan k d hd q uc hucval
  have hucinv : ((uc⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) ∈
      Submodule.span k (F.levelMonomialSet q) :=
    F.inv_mem_levelSpan_of_val_mem uc hucval
  set v : (AryLeavittAlgebra k d)ˣ := uc⁻¹ * u with hv
  set η : AryLeavittAlgebra k d :=
    ((uc⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) * y 1 with hη
  have hvval : (v : AryLeavittAlgebra k d) = 1 + η := by
    rw [hv]
    show ((uc⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) *
      (u : AryLeavittAlgebra k d) = 1 + η
    rw [hval, mul_add, hη]
    congr 1
    rw [show y 0 = (uc : AryLeavittAlgebra k d) from hucv.symm, Units.inv_mul]
  have hηd : η ∈ Submodule.span k (F.degreeMonomials 1 1) := by
    rw [hη]
    have h1 := F.window_mul_mem_span (k := k)
      (F.span_levelMonomialSet_le_degree (k := k) q hucinv) (hymem 1)
    refine F.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  obtain ⟨D, hD⟩ := pure_tail_nilpotent k d hd hηd v hvval
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  have hts : F.right i₀ * F.left i₀ = 1 := by rw [F.orthogonal, if_pos rfl]
  set κ : (AryLeavittAlgebra k d)ˣ := pairKappaUnit (F.left i₀) (F.right i₀) hts v with hκ
  have hκval : (κ : AryLeavittAlgebra k d) = 1 + F.left i₀ * (η * F.right i₀) := by
    rw [hκ]
    show F.left i₀ * (v : AryLeavittAlgebra k d) * F.right i₀ +
      (1 - F.left i₀ * F.right i₀) = 1 + F.left i₀ * (η * F.right i₀)
    rw [hvval]
    noncomm_ring
  have hzt : η * F.right i₀ ∈ Submodule.span k (F.degreeMonomials 0 0) := by
    have h1 := F.window_mul_mem_span (k := k) hηd (F.right_mem_window (k := k) i₀)
    refine F.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  have hpow : ∀ m : ℕ, (F.left i₀ * (η * F.right i₀)) ^ (m + 1) =
      F.left i₀ * (η ^ (m + 1) * F.right i₀) := by
    intro m
    induction m with
    | zero => rw [pow_one, pow_one]
    | succ m ih =>
        rw [pow_succ, ih]
        rw [show F.left i₀ * (η ^ (m + 1) * F.right i₀) * (F.left i₀ * (η * F.right i₀)) =
          F.left i₀ * (η ^ (m + 1) * (F.right i₀ * F.left i₀) * (η * F.right i₀)) from by
            noncomm_ring, hts]
        rw [show F.left i₀ * (η ^ (m + 1) * 1 * (η * F.right i₀)) =
          F.left i₀ * (η ^ (m + 1) * η * F.right i₀) from by noncomm_ring, ← pow_succ]
  have hnil : (F.left i₀ * (η * F.right i₀)) ^ (D + 1) = 0 := by
    rw [hpow D, pow_succ, hD, zero_mul, zero_mul, mul_zero]
  have hκmem : κ ∈ stableUnits (AryLeavittAlgebra k d) :=
    F.nilpotent_tail_mem_stableUnits (k := k) i₀ (D + 1) hzt hnil κ hκval
  have hκtrans : κ * v⁻¹ ∈ stableUnits (AryLeavittAlgebra k d) := by
    rw [hκ]
    exact pairKappaUnit_mul_inv_mem_stableUnits (F.left i₀) (F.right i₀) hts hdiv v
  have hassemble : u = uc * ((κ * v⁻¹)⁻¹ * κ) := by
    have h1 : (κ * v⁻¹)⁻¹ * κ = v := by group
    rw [h1, hv]
    group
  rw [hassemble]
  exact mul_mem hucmem (mul_mem (stableUnits_le_centralClassGroup (inv_mem hκtrans))
    (stableUnits_le_centralClassGroup hκmem))

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavitt.window_zero_one_mem_centralClassGroup
