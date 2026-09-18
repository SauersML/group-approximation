import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZeroCore.Independence

/-!
# The idempotent dichotomy for `L_k(1,2)`

Manuscript `simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`,
question Q2), input `K₀(L_k(1,2)) = 0`.  Over the binary Leavitt algebra
`L = L_k(1,2)` of a field `k`, every idempotent `e` is either `0` or
equivalent to `1`: there are `a, b` with `a b = e` and `b a = 1`.

Proof.  Choose clearing bounds `(m, N)` for `e` and look at the column
`q = qvec k e m`, whose entries lie in `fil k (N + m)`.  The adapted
generators `w_0, …, w_{r-1}` of `colFil k e m (N + m)` are independent modulo
constant terms, so they are left `L`-linearly independent
(`eq_zero_of_sum_smul_eq_zero`).

Write `q = ∑ μ_j w_j` and `w_j = l_j q` with `l_j e = l_j`.  Then
`w_i = ∑_j l_i μ_j w_j`, so freeness gives `l_i μ_j = δ_ij`.  Also
`(∑ μ_j l_j) q = q`, which forces `∑ μ_j l_j = e`.

* If `r = 0`, the sum `∑ μ_j l_j` is empty, so `e = 0`.
* If `r ≥ 1`, the Leavitt relations give a row `u` and a column `v` with
  `v_i u_j = δ_ij` and `∑ u_j v_j = 1` (`exists_row_col_units`).  Then
  `a = ∑ μ_i v_i` and `b = ∑ u_j l_j` satisfy `a b = e` and `b a = 1`.
-/

namespace GroupApproximation.Full.LVLowKZeroCore

open GroupApproximation.BinaryLeavitt

/-- **Rows and columns of units.**  With a binary Leavitt family, `1` is
equivalent to `1 ⊕ ⋯ ⊕ 1` (`r + 1` copies).  Concretely, there are `u, v` with
`v_i u_j = δ_ij` and `∑ u_j v_j = 1`. -/
theorem exists_row_col_units {A : Type*} [Ring A] (L : LeavittFamily A) (r : ℕ) :
    ∃ u v : Fin (r + 1) → A,
      (∀ i j, v i * u j = if i = j then 1 else 0) ∧ ∑ j, u j * v j = 1 := by
  induction r with
  | zero =>
      refine ⟨fun _ => 1, fun _ => 1, fun i j => ?_, ?_⟩
      · induction i using Fin.cases with
        | zero =>
            induction j using Fin.cases with
            | zero => rw [if_pos rfl, mul_one]
            | succ j => exact (Nat.not_lt_zero _ j.2).elim
        | succ i => exact (Nat.not_lt_zero _ i.2).elim
      · rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, mul_one]
  | succ r ih =>
      obtain ⟨u, v, huv, hsum⟩ := ih
      refine ⟨Fin.cons L.s0 fun j => L.s1 * u j, Fin.cons L.t0 fun i => v i * L.t1,
        fun i j => ?_, ?_⟩
      · induction i using Fin.cases with
        | zero =>
            induction j using Fin.cases with
            | zero =>
                rw [if_pos rfl]
                simp only [Fin.cons_zero]
                exact L.t0_s0
            | succ j =>
                rw [if_neg (Fin.succ_ne_zero j).symm]
                simp only [Fin.cons_zero, Fin.cons_succ]
                rw [← mul_assoc, L.t0_s1, zero_mul]
        | succ i =>
            induction j using Fin.cases with
            | zero =>
                rw [if_neg (Fin.succ_ne_zero i)]
                simp only [Fin.cons_zero, Fin.cons_succ]
                rw [mul_assoc, L.t1_s0, mul_zero]
            | succ j =>
                simp only [Fin.cons_succ]
                rw [mul_assoc, ← mul_assoc L.t1, L.t1_s1, one_mul, huv i j]
                by_cases hij : i = j
                · rw [if_pos hij, if_pos (congrArg Fin.succ hij)]
                · rw [if_neg hij, if_neg fun h : i.succ = j.succ => hij (Fin.succ_injective _ h)]
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have h : ∑ i, L.s1 * u i * (v i * L.t1) = L.s1 * L.t1 := by
          calc ∑ i, L.s1 * u i * (v i * L.t1) = L.s1 * (∑ i, u i * v i) * L.t1 := by
                rw [Finset.mul_sum, Finset.sum_mul]
                exact Finset.sum_congr rfl fun i _ => by simp only [mul_assoc]
            _ = L.s1 * L.t1 := by rw [hsum, mul_one]
        rw [h, L.sum_range]

/-- **Idempotent dichotomy for `L_k(1,2)`** (`simple_kazhdan_sofic_group.tex`
l.733-735, `sec:questions` Q2).  Every idempotent of the binary Leavitt
algebra over a field is `0` or equivalent to `1`. -/
theorem binaryLeavitt_idempotent_dichotomy (k : Type) [Field k]
    (e : BinaryLeavittAlgebra k) (he : IsIdempotentElem e) :
    e = 0 ∨ ∃ a b : BinaryLeavittAlgebra k, a * b = e ∧ b * a = 1 := by
  obtain ⟨m, N, hcl⟩ := exists_clearing k e
  obtain ⟨r, w, hwM, hli, hspan⟩ := exists_adapted_generators k e m (N + m)
  obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun (BinaryLeavittAlgebra k)).mp
    (hspan _ (qvec_mem_colFil k hcl))
  have hq' : e • qvec k e m = qvec k e m :=
    funext fun δ => mul_qvec_of_idempotent k he m δ
  -- Each generator is a left multiple `l_j • q` with `l_j e = l_j`.
  have hl : ∀ j, ∃ l : BinaryLeavittAlgebra k, l * e = l ∧ w j = l • qvec k e m := by
    intro j
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp ((mem_colFil k).mp (hwM j)).1
    refine ⟨a * e, by rw [mul_assoc, he.eq], ?_⟩
    rw [← ha, ← smul_smul, hq']
  obtain ⟨l, hl'⟩ := Classical.skolem.mp hl
  have hle : ∀ j, l j * e = l j := fun j => (hl' j).1
  have hwl : ∀ j, w j = l j • qvec k e m := fun j => (hl' j).2
  have hw : ∀ j δ, w j δ ∈ fil k (N + m) := fun j δ => ((mem_colFil k).mp (hwM j)).2 δ
  -- `(∑ μ_j l_j) q = q`, hence `∑ μ_j l_j = e`.
  have hq_eq : (∑ j, μ j * l j) • qvec k e m = qvec k e m := by
    rw [Finset.sum_smul]
    calc ∑ j, (μ j * l j) • qvec k e m = ∑ j, μ j • w j :=
          Finset.sum_congr rfl fun j _ => by rw [hwl j, smul_smul]
      _ = qvec k e m := hμ
  have hsum_e : ∑ j, μ j * l j = e := by
    have h : (∑ j, μ j * l j - 1) * e = 0 := by
      refine mul_eq_zero_of_mul_qvec_eq_zero k (m := m) fun δ => ?_
      have h1 : (∑ j, μ j * l j) * qvec k e m δ = qvec k e m δ := congrFun hq_eq δ
      rw [sub_mul, one_mul, h1, sub_self]
    rw [sub_mul, one_mul, sub_eq_zero, Finset.sum_mul] at h
    calc ∑ j, μ j * l j = ∑ j, μ j * l j * e :=
          Finset.sum_congr rfl fun j _ => by rw [mul_assoc, hle j]
      _ = e := h
  cases r with
  | zero =>
      left
      rw [← hsum_e, Fin.sum_univ_zero]
  | succ r =>
      right
      obtain ⟨u, v, huv, hsum⟩ := exists_row_col_units (family k) r
      -- Freeness gives `l_i μ_j = δ_ij`.
      have hrel : ∀ i j, l i * μ j = if i = j then 1 else 0 := by
        intro i
        have hA : ∑ j, (l i * μ j) • w j = w i := by
          calc ∑ j, (l i * μ j) • w j = ∑ j, l i • μ j • w j :=
                Finset.sum_congr rfl fun j _ => (smul_smul (l i) (μ j) (w j)).symm
            _ = l i • qvec k e m := by rw [← Finset.smul_sum, hμ]
            _ = w i := (hwl i).symm
        have hB : ∑ j, (if i = j then (1 : BinaryLeavittAlgebra k) else 0) • w j = w i := by
          rw [Finset.sum_eq_single i]
          · rw [if_pos rfl, one_smul]
          · intro j _ hj
            rw [if_neg (Ne.symm hj), zero_smul]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
        have hrow : ∑ j, (l i * μ j - (if i = j then 1 else 0)) • w j = 0 := by
          calc ∑ j, (l i * μ j - (if i = j then 1 else 0)) • w j
              = ∑ j, ((l i * μ j) • w j -
                  (if i = j then (1 : BinaryLeavittAlgebra k) else 0) • w j) :=
                Finset.sum_congr rfl fun j _ => sub_smul _ _ _
            _ = w i - w i := by rw [Finset.sum_sub_distrib, hA, hB]
            _ = 0 := sub_self _
        have h0 := eq_zero_of_sum_smul_eq_zero k w hw hli _ hrow
        intro j
        exact sub_eq_zero.mp (congrFun h0 j)
      refine ⟨∑ i, μ i * v i, ∑ j, u j * l j, ?_, ?_⟩
      · rw [Finset.sum_mul]
        calc ∑ i, μ i * v i * ∑ j, u j * l j = ∑ i, μ i * l i := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              calc ∑ j, μ i * v i * (u j * l j) = ∑ j, if i = j then μ i * l j else 0 :=
                    Finset.sum_congr rfl fun j _ => by
                      rw [mul_assoc, ← mul_assoc (v i), huv i j]
                      by_cases hij : i = j
                      · rw [if_pos hij, if_pos hij, one_mul]
                      · rw [if_neg hij, if_neg hij, zero_mul, mul_zero]
                _ = μ i * l i := by rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
          _ = e := hsum_e
      · rw [Finset.sum_mul]
        calc ∑ j, u j * l j * ∑ i, μ i * v i = ∑ j, u j * v j := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.mul_sum]
              calc ∑ i, u j * l j * (μ i * v i) = ∑ i, if j = i then u j * v i else 0 :=
                    Finset.sum_congr rfl fun i _ => by
                      rw [mul_assoc, ← mul_assoc (l j), hrel j i]
                      by_cases hji : j = i
                      · rw [if_pos hji, if_pos hji, one_mul]
                      · rw [if_neg hji, if_neg hji, zero_mul, mul_zero]
                _ = u j * v j := by rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
          _ = 1 := hsum

end GroupApproximation.Full.LVLowKZeroCore
