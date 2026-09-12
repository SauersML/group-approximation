import GroupApproximation.KOne.AryWidthTwoReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Nonnegative windows die, at arbitrary arity: the block-move induction

`KOne/WindowNonnegReduction.lean` for `L_k(1,d)`: every unit whose value lies in the span of
the degree window `[0, N]` is a central scalar modulo the stably elementary units.  The
induction peels the top degree.  Writing the top component as `η = Σ_z s_z (t_z η)`, the
depth-two corner insertion `κ(u) = 1 + s_{00}(u - 1)t_{00}` is squeezed between two products
of incomparable unipotents, one factor for each letter `z`, supported on the words `[1, z]`.
The cross terms collapse through the partition of unity `Σ_z s_z t_z = 1` and produce a unit
with tail of degrees `[1, N-1]`.  The binary file uses the two words `01`, `10`; at arity
`d` the `d` words `1z` do the same job, all incomparable with `00` and with each other.
The base case is the width-two reduction.
-/

namespace GroupApproximation

/-- A product of units `1 + X z` with pairwise vanishing products has value `1 + Σ X z`. -/
theorem prod_ofFn_val_of_mul_eq_zero {A : Type*} [Ring A] :
    ∀ {n : ℕ} (U : Fin n → Aˣ) (X : Fin n → A),
      (∀ z, (U z : A) = 1 + X z) → (∀ z z', X z * X z' = 0) →
      (((List.ofFn U).prod : Aˣ) : A) = 1 + ∑ z, X z
  | 0, U, X, _, _ => by simp
  | n + 1, U, X, hval, hzero => by
      rw [List.ofFn_succ, List.prod_cons, Units.val_mul,
        prod_ofFn_val_of_mul_eq_zero (fun z ↦ U z.succ) (fun z ↦ X z.succ)
          (fun z ↦ hval z.succ) (fun z z' ↦ hzero z.succ z'.succ),
        hval 0, Fin.sum_univ_succ]
      have h0 : X 0 * ∑ z : Fin n, X z.succ = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun z _ ↦ hzero 0 z.succ
      calc (1 + X 0) * (1 + ∑ z : Fin n, X z.succ)
          = 1 + (X 0 + ∑ z : Fin n, X z.succ) + X 0 * ∑ z : Fin n, X z.succ := by
            noncomm_ring
        _ = 1 + (X 0 + ∑ z : Fin n, X z.succ) := by rw [h0, add_zero]

namespace AryLeavitt

open CompleteMatrixFamily MatrixDiagonalization

variable (k : Type) [Field k] (d : ℕ)

/-- **Nonnegative-window units are central scalars modulo the stably elementary units.** -/
theorem window_nonneg_mem_centralClassGroup (hd : 2 ≤ d) :
    ∀ (N : ℕ) (u : (AryLeavittAlgebra k d)ˣ),
      (u : AryLeavittAlgebra k d) ∈
        Submodule.span k ((family k d).degreeMonomials 0 ((N : ℤ) + 1)) →
      u ∈ centralClassGroup (AryLeavittAlgebra k d) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  set F : CompleteMatrixFamily (AryLeavittAlgebra k d) (Fin d) := family k d with hF
  have hdiv : ∀ x : AryLeavittAlgebra k d, x ≠ 0 →
      ∃ p q : AryLeavittAlgebra k d, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k d hd hx
  intro N
  induction N with
  | zero =>
      intro u hu
      exact window_zero_one_mem_centralClassGroup k d hd u
        (F.span_degreeMonomials_mono (by omega) (by omega) hu)
  | succ N ih =>
      intro u hu
      rw [show (((N + 1 : ℕ) : ℤ) + 1) = (N : ℤ) + 2 from by push_cast; ring] at hu
      have hzmem : (u : AryLeavittAlgebra k d) - 1 ∈
          Submodule.span k (F.degreeMonomials 0 ((N : ℤ) + 2)) :=
        Submodule.sub_mem _ hu
          (F.span_degreeMonomials_mono (by omega) (by omega) (F.one_mem_window (k := k)))
      obtain ⟨y, hymem, hysupp, hysum⟩ := F.exists_components hzmem
      set η : AryLeavittAlgebra k d := y ((N : ℤ) + 2) with hη
      set a : AryLeavittAlgebra k d := ∑ j ∈ Finset.Icc (0 : ℤ) ((N : ℤ) + 1), y j with ha
      have hτsplit : (u : AryLeavittAlgebra k d) - 1 = a + η := by
        rw [hysum, ha, hη]
        have hins : Finset.Icc (0 : ℤ) ((N : ℤ) + 2) =
            insert ((N : ℤ) + 2) (Finset.Icc (0 : ℤ) ((N : ℤ) + 1)) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hins, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]
      have hu1 : (u : AryLeavittAlgebra k d) = 1 + (a + η) := by
        rw [← hτsplit]
        abel
      have haw : a ∈ Submodule.span k (F.degreeMonomials 0 ((N : ℤ) + 1)) := by
        rw [ha]
        refine Submodule.sum_mem _ fun j hj ↦ ?_
        have hj' := Finset.mem_Icc.mp hj
        exact F.span_degreeMonomials_mono (by omega) (by omega) (hymem j)
      have hηw : η ∈ Submodule.span k
          (F.degreeMonomials ((N : ℤ) + 2) ((N : ℤ) + 2)) := hymem _
      -- the letters, the corner word `[i₀, i₀]`, and the sibling words `[i₁, z]`
      set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
      set i₁ : Fin d := ⟨1, by omega⟩ with hi₁
      have hi01 : i₀ ≠ i₁ := by
        rw [hi₀, hi₁]
        simp
      have hinc : ∀ z : Fin d, ¬([i₀, i₀] : List (Fin d)) <+: [i₁, z] :=
        fun z hp ↦ hi01 (List.cons_prefix_cons.mp hp).1
      have hinc' : ∀ z : Fin d, ¬([i₁, z] : List (Fin d)) <+: [i₀, i₀] :=
        fun z hp ↦ hi01 (List.cons_prefix_cons.mp hp).1.symm
      have hww : ∀ z z' : Fin d,
          F.wordT [i₁, z] * F.wordS [i₁, z'] = if z = z' then 1 else 0 := by
        intro z z'
        by_cases hzz : z = z'
        · rw [if_pos hzz, hzz]
          exact F.wordT_mul_wordS_self _
        · rw [if_neg hzz]
          have hne : ∀ {x x' : Fin d}, x ≠ x' → ¬([i₁, x] : List (Fin d)) <+: [i₁, x'] := by
            intro x x' hxx hp
            exact hxx (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp hp).2).1
          exact F.wordT_mul_wordS_of_incomparable _ _ (hne hzz) (hne (Ne.symm hzz))
      have hz₁ : ∀ z : Fin d, F.wordT [i₁, z] * F.wordS [i₀, i₀] = 0 := fun z ↦
        F.wordT_mul_wordS_of_incomparable _ _ (hinc' z) (hinc z)
      have hz₃ : ∀ z : Fin d, F.wordT [i₀, i₀] * F.wordS [i₁, z] = 0 := fun z ↦
        F.wordT_mul_wordS_of_incomparable _ _ (hinc z) (hinc' z)
      -- the branch coefficients of the top component
      set q : Fin d → AryLeavittAlgebra k d := fun z ↦ F.right z * η with hq
      have hsplitη : ∑ z, F.left z * q z = η := by
        simp only [hq, ← mul_assoc]
        rw [← Finset.sum_mul, F.complete, one_mul]
      have hqw : ∀ z, q z ∈ Submodule.span k
          (F.degreeMonomials ((N : ℤ) + 1) ((N : ℤ) + 1)) := by
        intro z
        have h1 := F.window_mul_mem_span (k := k) (F.right_mem_window (k := k) z) hηw
        refine F.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
      -- the corner embedding at `[i₀, i₀]`
      have hts : F.wordT [i₀, i₀] * F.wordS [i₀, i₀] = 1 := F.wordT_mul_wordS_self _
      set κ : (AryLeavittAlgebra k d)ˣ :=
        pairKappaUnit (F.wordS [i₀, i₀]) (F.wordT [i₀, i₀]) hts u with hκ
      have hκmem : κ * u⁻¹ ∈ stableUnits (AryLeavittAlgebra k d) :=
        pairKappaUnit_mul_inv_mem_stableUnits _ _ hts hdiv u
      set K : AryLeavittAlgebra k d := F.wordS [i₀, i₀] * (a + η) * F.wordT [i₀, i₀] with hK
      have hκval : (κ : AryLeavittAlgebra k d) = 1 + K := by
        show F.wordS [i₀, i₀] * (u : AryLeavittAlgebra k d) * F.wordT [i₀, i₀] +
          (1 - F.wordS [i₀, i₀] * F.wordT [i₀, i₀]) = 1 + K
        rw [hu1, hK]
        noncomm_ring
      -- the unipotent factors
      set X : Fin d → AryLeavittAlgebra k d :=
        fun z ↦ F.wordS [i₀, i₀] * F.left z * F.wordT [i₁, z] with hX
      set Y : Fin d → AryLeavittAlgebra k d :=
        fun z ↦ F.wordS [i₁, z] * q z * F.wordT [i₀, i₀] with hY
      have hXX : ∀ z z', X z * X z' = 0 := by
        intro z z'
        simp only [hX]
        rw [show F.wordS [i₀, i₀] * F.left z * F.wordT [i₁, z] *
            (F.wordS [i₀, i₀] * F.left z' * F.wordT [i₁, z']) =
          F.wordS [i₀, i₀] * F.left z * (F.wordT [i₁, z] * F.wordS [i₀, i₀]) *
            F.left z' * F.wordT [i₁, z'] from by noncomm_ring, hz₁]
        noncomm_ring
      have hYY : ∀ z z', Y z * Y z' = 0 := by
        intro z z'
        simp only [hY]
        rw [show F.wordS [i₁, z] * q z * F.wordT [i₀, i₀] *
            (F.wordS [i₁, z'] * q z' * F.wordT [i₀, i₀]) =
          F.wordS [i₁, z] * q z * (F.wordT [i₀, i₀] * F.wordS [i₁, z']) *
            q z' * F.wordT [i₀, i₀] from by noncomm_ring, hz₃]
        noncomm_ring
      have hXK : ∀ z, X z * K = 0 := by
        intro z
        simp only [hX, hK]
        rw [show F.wordS [i₀, i₀] * F.left z * F.wordT [i₁, z] *
            (F.wordS [i₀, i₀] * (a + η) * F.wordT [i₀, i₀]) =
          F.wordS [i₀, i₀] * F.left z * (F.wordT [i₁, z] * F.wordS [i₀, i₀]) *
            (a + η) * F.wordT [i₀, i₀] from by noncomm_ring, hz₁]
        noncomm_ring
      have hKY : ∀ z, K * Y z = 0 := by
        intro z
        simp only [hY, hK]
        rw [show F.wordS [i₀, i₀] * (a + η) * F.wordT [i₀, i₀] *
            (F.wordS [i₁, z] * q z * F.wordT [i₀, i₀]) =
          F.wordS [i₀, i₀] * (a + η) * (F.wordT [i₀, i₀] * F.wordS [i₁, z]) *
            q z * F.wordT [i₀, i₀] from by noncomm_ring, hz₃]
        noncomm_ring
      have hXY : ∀ z z', X z * Y z' =
          if z = z' then F.wordS [i₀, i₀] * (F.left z * q z) * F.wordT [i₀, i₀] else 0 := by
        intro z z'
        simp only [hX, hY]
        rw [show F.wordS [i₀, i₀] * F.left z * F.wordT [i₁, z] *
            (F.wordS [i₁, z'] * q z' * F.wordT [i₀, i₀]) =
          F.wordS [i₀, i₀] * F.left z * (F.wordT [i₁, z] * F.wordS [i₁, z']) *
            q z' * F.wordT [i₀, i₀] from by noncomm_ring, hww z z']
        split_ifs with hzz
        · subst hzz
          noncomm_ring
        · noncomm_ring
      have hSXK : (∑ z, X z) * K = 0 := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_zero fun z _ ↦ hXK z
      have hSKY : K * ∑ z, Y z = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun z _ ↦ hKY z
      have hSXY : (∑ z, X z) * (∑ z, Y z) = F.wordS [i₀, i₀] * η * F.wordT [i₀, i₀] := by
        rw [Finset.sum_mul]
        calc ∑ z, X z * ∑ z', Y z'
            = ∑ z, F.wordS [i₀, i₀] * (F.left z * q z) * F.wordT [i₀, i₀] := by
              refine Finset.sum_congr rfl fun z _ ↦ ?_
              rw [Finset.mul_sum, Finset.sum_eq_single z]
              · rw [hXY z z, if_pos rfl]
              · intro z' _ hz'
                rw [hXY z z', if_neg (Ne.symm hz')]
              · intro hz
                exact absurd (Finset.mem_univ z) hz
          _ = F.wordS [i₀, i₀] * (∑ z, F.left z * q z) * F.wordT [i₀, i₀] := by
              rw [Finset.mul_sum, Finset.sum_mul]
          _ = F.wordS [i₀, i₀] * η * F.wordT [i₀, i₀] := by rw [hsplitη]
      -- the two class-group multipliers
      set m₂ : (AryLeavittAlgebra k d)ˣ :=
        (List.ofFn fun z ↦ F.incomparableUnit (hinc z) (hinc' z) (-(F.left z))).prod with hm₂
      set m₁ : (AryLeavittAlgebra k d)ˣ :=
        (List.ofFn fun z ↦ F.incomparableUnit (hinc' z) (hinc z) (q z)).prod with hm₁
      have hm₂mem : m₂ ∈ stableUnits (AryLeavittAlgebra k d) := by
        rw [hm₂]
        refine list_prod_mem fun x hx ↦ ?_
        obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hx
        exact F.incomparableUnit_mem _ _ _
      have hm₁mem : m₁ ∈ stableUnits (AryLeavittAlgebra k d) := by
        rw [hm₁]
        refine list_prod_mem fun x hx ↦ ?_
        obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hx
        exact F.incomparableUnit_mem _ _ _
      have hm₂val : (m₂ : AryLeavittAlgebra k d) = 1 - ∑ z, X z := by
        rw [hm₂, prod_ofFn_val_of_mul_eq_zero _ (fun z ↦ -X z)
          (fun z ↦ by rw [incomparableUnit_val, mul_neg, neg_mul]; rfl)
          (fun z z' ↦ by rw [neg_mul_neg, hXX]),
          Finset.sum_neg_distrib, sub_eq_add_neg]
      have hm₁val : (m₁ : AryLeavittAlgebra k d) = 1 + ∑ z, Y z := by
        rw [hm₁, prod_ofFn_val_of_mul_eq_zero _ (fun z ↦ Y z)
          (fun z ↦ by rw [incomparableUnit_val]; rfl) (fun z z' ↦ hYY z z')]
      -- the block-move product and its value
      set u' : (AryLeavittAlgebra k d)ˣ := m₂ * κ * m₁ with hu'
      have hu'val : (u' : AryLeavittAlgebra k d) =
          1 + (F.wordS [i₀, i₀] * a * F.wordT [i₀, i₀] - ∑ z, X z + ∑ z, Y z) := by
        rw [hu', Units.val_mul, Units.val_mul, hm₂val, hκval, hm₁val]
        calc (1 - ∑ z, X z) * (1 + K) * (1 + ∑ z, Y z)
            = 1 + K + ∑ z, Y z - ∑ z, X z - (∑ z, X z) * (∑ z, Y z) + K * ∑ z, Y z -
                (∑ z, X z) * K - (∑ z, X z) * K * ∑ z, Y z := by noncomm_ring
          _ = 1 + K + ∑ z, Y z - ∑ z, X z - (∑ z, X z) * (∑ z, Y z) := by
              rw [hSKY, hSXK, zero_mul]
              abel
          _ = 1 + (F.wordS [i₀, i₀] * a * F.wordT [i₀, i₀] - ∑ z, X z + ∑ z, Y z) := by
              rw [hSXY, hK]
              noncomm_ring
      -- the new tail lives one degree lower
      have hs00w : F.wordS [i₀, i₀] ∈ Submodule.span k (F.degreeMonomials 2 2) :=
        Submodule.subset_span ⟨[i₀, i₀], [], by simp, by simp, by simp⟩
      have ht00w : F.wordT [i₀, i₀] ∈ Submodule.span k (F.degreeMonomials (-2) (-2)) :=
        Submodule.subset_span ⟨[], [i₀, i₀], by simp, by simp, by simp⟩
      have hsww : ∀ z : Fin d, F.wordS [i₁, z] ∈ Submodule.span k (F.degreeMonomials 2 2) :=
        fun z ↦ Submodule.subset_span ⟨[i₁, z], [], by simp, by simp, by simp⟩
      have hXw : ∀ z, X z ∈ Submodule.span k (F.degreeMonomials 1 1) := by
        intro z
        refine Submodule.subset_span ⟨[i₀, i₀, z], [i₁, z], by simp, by simp, ?_⟩
        simp only [hX, wordS_cons, wordT_cons, wordS_nil, wordT_nil, mul_one, one_mul,
          mul_assoc]
      have hu'mem : (u' : AryLeavittAlgebra k d) ∈
          Submodule.span k (F.degreeMonomials 0 ((N : ℤ) + 1)) := by
        rw [hu'val]
        refine Submodule.add_mem _
          (F.span_degreeMonomials_mono (by omega) (by omega) (F.one_mem_window (k := k))) ?_
        refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
        · have h1 := F.window_mul_mem_span (k := k)
            (F.window_mul_mem_span (k := k) hs00w haw) ht00w
          refine F.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
        · exact Submodule.sum_mem _ fun z _ ↦
            F.span_degreeMonomials_mono (by omega) (by omega) (hXw z)
        · refine Submodule.sum_mem _ fun z _ ↦ ?_
          have h1 := F.window_mul_mem_span (k := k)
            (F.window_mul_mem_span (k := k) (hsww z) (hqw z)) ht00w
          refine F.span_degreeMonomials_mono ?_ ?_ h1 <;> omega
      have hu'H : u' ∈ centralClassGroup (AryLeavittAlgebra k d) := ih u' hu'mem
      have hassemble : u = (κ * u⁻¹)⁻¹ * (m₂⁻¹ * u' * m₁⁻¹) := by
        rw [hu']
        group
      rw [hassemble]
      exact mul_mem (stableUnits_le_centralClassGroup (inv_mem hκmem))
        (mul_mem (mul_mem (stableUnits_le_centralClassGroup (inv_mem hm₂mem)) hu'H)
          (stableUnits_le_centralClassGroup (inv_mem hm₁mem)))

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.prod_ofFn_val_of_mul_eq_zero
#audit_axioms GroupApproximation.AryLeavitt.window_nonneg_mem_centralClassGroup
