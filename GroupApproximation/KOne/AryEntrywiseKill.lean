import GroupApproximation.KOne.AryPrefixCodes
import GroupApproximation.KOne.AryPencilEntry
import GroupApproximation.KOne.AryGradedComponents
import GroupApproximation.KOne.AryNilpotentTailKill
import GroupApproximation.Meta.AxiomGuard

/-!
# Strict negativity under a full stack, at arbitrary arity

`KOne/EntrywiseKill.lean` and `KOne/StrictNegativePencil.lean` for `L_k(1,d)`.  Let `u` be a
code-pencil unit over `(R, C)` whose `s`-coefficients `Bc i j z` form a letter-indexed stack
with a scalar left inverse `G`.  The strip equations `∑ⱼ xᵢⱼ · yⱼᵢ' = δᵢᵢ'` for the entries
`xᵢⱼ = t_{Rᵢ} u s_{Cⱼ}` (pencil entries) and `yⱼᵢ = t_{Cⱼ} u⁻¹ s_{Rᵢ}` decompose degreewise.
From the top down, the degree-`(D+1)` equation isolates the `s`-part against the degree-`D`
components of `y`; a `t_w`-strip turns it into the scalar relations
`∑ⱼ Bc i j w • Y⁽ᴰ⁾ⱼᵢ' = 0`, and `G` kills every component of degree `D ≥ 0`.  So every
inverse entry lies in a strictly negative window.
-/

namespace GroupApproximation

namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)
variable {k : Type*} [Field k] [Algebra k A]

/-- A `t`-letter strips one coefficient off an `s`-combination. -/
theorem right_mul_sumLeft_mul (b : ι → k) (w : ι) (y : A) :
    F.right w * ((∑ r, b r • F.left r) * y) = b w • y := by
  rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_eq_single w]
  · rw [smul_mul_assoc, mul_smul_comm, ← mul_assoc, F.orthogonal, if_pos rfl, one_mul]
  · intro r _ hr
    rw [smul_mul_assoc, mul_smul_comm, ← mul_assoc, F.orthogonal, if_neg (Ne.symm hr),
      zero_mul, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ w) h

/-- A pencil entry lies in the window `[-1, 1]`. -/
theorem pencilEntry_mem_window (a b : ι → k) (c : k) :
    F.pencilEntry a b c ∈ Submodule.span k (F.degreeMonomials (-1) 1) := by
  unfold pencilEntry
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.sum_mem _ fun r _ ↦ Submodule.smul_mem _ _
      (F.span_degreeMonomials_mono (by omega) (by omega) (F.right_mem_window (k := k) r))
  · exact Submodule.smul_mem _ _
      (F.span_degreeMonomials_mono (by omega) (by omega) (F.one_mem_window (k := k)))
  · exact Submodule.sum_mem _ fun r _ ↦ Submodule.smul_mem _ _
      (F.span_degreeMonomials_mono (by omega) (by omega) (F.left_mem_window (k := k) r))

end CompleteMatrixFamily

namespace AryLeavitt

open CompleteMatrixFamily

variable (k : Type) [Field k] (d : ℕ)

/-- **Strict negativity**: a scalar left inverse of the letter-indexed `s`-coefficient stack
forces every inverse entry `t_{Cⱼ} u⁻¹ s_{Rᵢ}` into a strictly negative window. -/
theorem entry_window_negative_of_B_full (hd : 2 ≤ d)
    {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]
    (R : AryPrefixCode ρ (Fin d)) (C : AryPrefixCode κ (Fin d))
    (hC : (family k d).IsComplete C)
    (Ac Bc : ρ → κ → Fin d → k) (Cm : ρ → κ → k) (u : (AryLeavittAlgebra k d)ˣ)
    (hu : (u : AryLeavittAlgebra k d) = ∑ i, ∑ j, (family k d).wordS (R.word i) *
      (family k d).pencilEntry (Ac i j) (Bc i j) (Cm i j) * (family k d).wordT (C.word j))
    (G : Fin d → κ → ρ → k)
    (hG : ∀ j j' : κ, (∑ z, ∑ i, G z j i * Bc i j' z) = if j = j' then 1 else 0) :
    ∃ N : ℕ, ∀ (j : κ) (i : ρ),
      (family k d).wordT (C.word j) *
          ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) *
          (family k d).wordS (R.word i) ∈
        Submodule.span k ((family k d).degreeMonomials (-(N : ℤ)) (-1)) := by
  classical
  set L : CompleteMatrixFamily (AryLeavittAlgebra k d) (Fin d) := family k d
  set y : κ → ρ → AryLeavittAlgebra k d := fun j i ↦
    L.wordT (C.word j) * ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) *
      L.wordS (R.word i)
  -- a common window for all entries
  have hex : ∀ p : κ × ρ, ∃ n : ℕ,
      y p.1 p.2 ∈ Submodule.span k (L.degreeMonomials (-(n : ℤ)) n) := by
    intro p
    obtain ⟨lo, hi, h⟩ := exists_mem_span_degreeMonomials k d (y p.1 p.2)
    refine ⟨max lo.natAbs hi.natAbs, L.span_degreeMonomials_mono ?_ ?_ h⟩ <;> omega
  choose f hf using hex
  obtain ⟨N, hNf⟩ : ∃ N : ℕ, ∀ p, f p ≤ N :=
    ⟨Finset.univ.sup f, fun p ↦ Finset.le_sup (Finset.mem_univ p)⟩
  have hN : ∀ j i, y j i ∈ Submodule.span k (L.degreeMonomials (-(N : ℤ)) N) := by
    intro j i
    have hle := hNf (j, i)
    refine L.span_degreeMonomials_mono ?_ ?_ (hf (j, i)) <;> omega
  -- graded components of every entry
  have hcomp : ∀ p : κ × ρ, ∃ Y : ℤ → AryLeavittAlgebra k d,
      (∀ n, Y n ∈ Submodule.span k (L.degreeMonomials n n)) ∧
      (∀ n, n < -(N : ℤ) ∨ (N : ℤ) < n → Y n = 0) ∧
      y p.1 p.2 = ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Y n :=
    fun p ↦ L.exists_components (hN p.1 p.2)
  choose Y hYmem hYsupp hYsum using hcomp
  -- the three pencil-entry parts
  set tP : ρ → κ → AryLeavittAlgebra k d := fun i j ↦ ∑ r, Ac i j r • L.right r
  set cP : ρ → κ → AryLeavittAlgebra k d := fun i j ↦ Cm i j • (1 : AryLeavittAlgebra k d)
  set sP : ρ → κ → AryLeavittAlgebra k d := fun i j ↦ ∑ r, Bc i j r • L.left r
  have htPmem : ∀ i j, tP i j ∈ Submodule.span k (L.degreeMonomials (-1) (-1)) :=
    fun i j ↦ Submodule.sum_mem _ fun r _ ↦
      Submodule.smul_mem _ _ (L.right_mem_window (k := k) r)
  have hcPmem : ∀ i j, cP i j ∈ Submodule.span k (L.degreeMonomials 0 0) :=
    fun i j ↦ Submodule.smul_mem _ _ (L.one_mem_window (k := k))
  have hsPmem : ∀ i j, sP i j ∈ Submodule.span k (L.degreeMonomials 1 1) :=
    fun i j ↦ Submodule.sum_mem _ fun r _ ↦
      Submodule.smul_mem _ _ (L.left_mem_window (k := k) r)
  -- the strip equations
  have hstrip : ∀ i i' : ρ, (∑ j, (tP i j + cP i j + sP i j) * y j i') =
      if i = i' then (1 : AryLeavittAlgebra k d) else 0 := by
    intro i i'
    have h1 := L.strip_insert C hC (u : AryLeavittAlgebra k d)
      ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) (R.word i) (R.word i')
    rw [Units.mul_inv, mul_one, L.prefixCode_orthogonal R i i'] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have h2 : L.wordT (R.word i) * (u : AryLeavittAlgebra k d) * L.wordS (C.word j) =
        tP i j + cP i j + sP i j := by
      rw [hu]
      exact L.wordT_pencilVal_wordS R C _ i j
    exact congrArg (· * y j i') h2.symm
  -- degreewise equations
  have hzmem : ∀ (i i' : ρ) (D : ℤ),
      (∑ j, (tP i j * Y (j, i') (D + 1) + cP i j * Y (j, i') D +
        sP i j * Y (j, i') (D + (-1)))) ∈ Submodule.span k (L.degreeMonomials D D) := by
    intro i i' D
    refine Submodule.sum_mem _ fun j _ ↦
      Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · have h := L.window_mul_mem_span (htPmem i j) (hYmem (j, i') (D + 1))
      refine L.span_degreeMonomials_mono ?_ ?_ h <;> omega
    · have h := L.window_mul_mem_span (hcPmem i j) (hYmem (j, i') D)
      refine L.span_degreeMonomials_mono ?_ ?_ h <;> omega
    · have h := L.window_mul_mem_span (hsPmem i j) (hYmem (j, i') (D + (-1)))
      refine L.span_degreeMonomials_mono ?_ ?_ h <;> omega
  have hzsum : ∀ i i' : ρ,
      (∑ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
        ∑ j, (tP i j * Y (j, i') (D + 1) + cP i j * Y (j, i') D +
          sP i j * Y (j, i') (D + (-1)))) =
      if i = i' then (1 : AryLeavittAlgebra k d) else 0 := by
    intro i i'
    rw [Finset.sum_comm, ← hstrip i i']
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hsh1 : ∑ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1), Y (j, i') (D + 1) = y j i' := by
      have hm := Finset.sum_map (Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1))
        (addRightEmbedding (1 : ℤ)) (Y (j, i'))
      simp only [addRightEmbedding_apply] at hm
      rw [Finset.map_add_right_Icc] at hm
      rw [show -(N : ℤ) - 1 + 1 = -(N : ℤ) by ring,
        show (N : ℤ) + 1 + 1 = (N : ℤ) + 2 by ring] at hm
      rw [← hm, hYsum (j, i')]
      exact (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega))
        (fun n hn hn' ↦ hYsupp (j, i') n (Or.inr (by
          rw [Finset.mem_Icc] at hn hn'
          omega)))).symm
    have hsh0 : ∑ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1), Y (j, i') D = y j i' := by
      rw [hYsum (j, i')]
      exact (Finset.sum_subset (Finset.Icc_subset_Icc (by omega) (by omega))
        (fun n hn hn' ↦ hYsupp (j, i') n (by
          rw [Finset.mem_Icc] at hn hn'
          omega))).symm
    have hsh2 : ∑ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1), Y (j, i') (D + (-1)) =
        y j i' := by
      have hm := Finset.sum_map (Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1))
        (addRightEmbedding (-1 : ℤ)) (Y (j, i'))
      simp only [addRightEmbedding_apply] at hm
      rw [Finset.map_add_right_Icc] at hm
      rw [show -(N : ℤ) - 1 + (-1) = -(N : ℤ) - 2 by ring,
        show (N : ℤ) + 1 + (-1) = (N : ℤ) by ring] at hm
      rw [← hm, hYsum (j, i')]
      exact (Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
        (fun n hn hn' ↦ hYsupp (j, i') n (Or.inl (by
          rw [Finset.mem_Icc] at hn hn'
          omega)))).symm
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hsh1, hsh0, hsh2, ← add_mul, ← add_mul]
  -- uniqueness of components gives the degreewise equations
  have huniq : ∀ i i' : ρ, ∀ D ∈ Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1),
      (∑ j, (tP i j * Y (j, i') (D + 1) + cP i j * Y (j, i') D +
        sP i j * Y (j, i') (D + (-1)))) =
      (if D = 0 then (if i = i' then (1 : AryLeavittAlgebra k d) else 0) else 0) := by
    intro i i'
    have h := components_unique k d hd
      (D := Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1))
      (y := fun D ↦ ∑ j, (tP i j * Y (j, i') (D + 1) + cP i j * Y (j, i') D +
        sP i j * Y (j, i') (D + (-1))))
      (z := fun D ↦ if D = 0 then
        (if i = i' then (1 : AryLeavittAlgebra k d) else 0) else 0)
      (fun D _ ↦ hzmem i i' D)
      (fun D _ ↦ by
        split_ifs with h1 h2
        · rw [h1]
          exact L.one_mem_window (k := k)
        · exact Submodule.zero_mem _
        · exact Submodule.zero_mem _)
      (by
        rw [hzsum i i', Finset.sum_ite_eq' (Finset.Icc (-(N : ℤ) - 1) ((N : ℤ) + 1))
          (0 : ℤ) (fun _ ↦ if i = i' then (1 : AryLeavittAlgebra k d) else 0),
          if_pos (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)])
    intro D hD
    exact h D hD
  -- kill the nonnegative components from the top down
  have hkill : ∀ n : ℕ, ∀ D : ℤ, 0 ≤ D → (N : ℤ) + 1 - n ≤ D →
      ∀ j i', Y (j, i') D = 0 := by
    intro n
    induction n with
    | zero =>
        intro D _ h2 j i'
        exact hYsupp (j, i') D (Or.inr (by omega))
    | succ m ih =>
        intro D hD1 hD2 j₀ i'
        by_cases hcase : (N : ℤ) + 1 - m ≤ D
        · exact ih D hD1 hcase j₀ i'
        have hsPrel : ∀ i : ρ, (∑ j, sP i j * Y (j, i') D) = 0 := by
          intro i
          have heq := huniq i i' (D + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          rw [if_neg (show ¬(D + 1 = 0) by omega), show D + 1 + 1 = D + 2 by ring,
            show D + 1 + (-1) = D by ring] at heq
          have h2 : ∀ j, Y (j, i') (D + 2) = 0 := fun j ↦ ih (D + 2) (by omega) (by omega) j i'
          have h1 : ∀ j, Y (j, i') (D + 1) = 0 := fun j ↦ ih (D + 1) (by omega) (by omega) j i'
          simpa only [h1, h2, mul_zero, zero_add] using heq
        have hBrel : ∀ (i : ρ) (w : Fin d), (∑ j, Bc i j w • Y (j, i') D) = 0 := by
          intro i w
          calc ∑ j, Bc i j w • Y (j, i') D
              = L.right w * ∑ j, sP i j * Y (j, i') D := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun j _ ↦
                  (L.right_mul_sumLeft_mul (Bc i j) w (Y (j, i') D)).symm
            _ = 0 := by rw [hsPrel i, mul_zero]
        calc Y (j₀, i') D
            = ∑ j, (if j₀ = j then (1 : k) else 0) • Y (j, i') D := by
              simp only [ite_smul, one_smul, zero_smul]
              rw [Finset.sum_ite_eq Finset.univ j₀, if_pos (Finset.mem_univ j₀)]
          _ = ∑ j, (∑ z, ∑ i, G z j₀ i * Bc i j z) • Y (j, i') D := by
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              rw [hG j₀ j]
          _ = ∑ z, ∑ i, G z j₀ i • ∑ j, Bc i j z • Y (j, i') D := by
              simp only [Finset.sum_smul, Finset.smul_sum, smul_smul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun z _ ↦ ?_
              rw [Finset.sum_comm]
          _ = 0 := Finset.sum_eq_zero fun z _ ↦ Finset.sum_eq_zero fun i _ ↦ by
              rw [hBrel i z, smul_zero]
  -- reassemble the entries
  refine ⟨N, fun j i ↦ ?_⟩
  show y j i ∈ Submodule.span k (L.degreeMonomials (-(N : ℤ)) (-1))
  rw [hYsum (j, i)]
  have hsplit : ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Y (j, i) n =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (-1), Y (j, i) n :=
    (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega))
      (fun n hn hn' ↦ by
        rw [Finset.mem_Icc] at hn hn'
        exact hkill ((N : ℤ) + 1 - n).toNat n (by omega) (by omega) j i)).symm
  rw [hsplit]
  refine Submodule.sum_mem _ fun n hn ↦ ?_
  rw [Finset.mem_Icc] at hn
  exact L.span_degreeMonomials_mono (by omega) (by omega) (hYmem (j, i) n)

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.right_mul_sumLeft_mul
#audit_axioms GroupApproximation.CompleteMatrixFamily.pencilEntry_mem_window
#audit_axioms GroupApproximation.AryLeavitt.entry_window_negative_of_B_full
