import GroupApproximation.KOne.AryPencilForm
import GroupApproximation.KOne.AryStackDichotomy
import GroupApproximation.KOne.AryEntrywiseKill
import GroupApproximation.KOne.AryCodeSupply
import GroupApproximation.KOne.AryPencilReshape
import GroupApproximation.KOne.AryRefineStep
import GroupApproximation.KOne.AryWindowNonposReduction
import GroupApproximation.KOne.GLVectorNormalization
import GroupApproximation.Meta.AxiomGuard

/-!
# The refine-loop discharge at arbitrary arity: `NarrowReduction` holds

`KOne/RefineLoopDischarge.lean` for `L_k(1,d)`.  A pencil unit over a row code with `d^r`
words and a column code with `d^r + s·(d-1)` words is reduced by one loop on `s`:

* while the letter-indexed `s`-coefficient stack has a kernel, a scalar column move along the
  column code (`codeScalar_unit_mem`) makes one column `s`-free, and the refinement step
  splits it into its `d` children, so `s` grows by one at a fixed row code;
* at `s = d^r` the column code has `d^{r+1}` words; reshaping to exact-depth codes (rows at
  depth `r`, columns at depth `r+1`) puts the value in the window `[-2, 0]` (free exit);
* when the stack has a scalar left inverse, the inverse entries are strictly negative
  (`entry_window_negative_of_B_full`); reshaping the inverse to depth-`[r, r+1]` rows and
  depth-`r` columns puts its value in a nonpositive window (full exit).

Both exits land in `window_nonpos_mem_centralClassGroup`.  The receptacle is
`centralClassGroup` throughout: at `d ≥ 3` the binary collapse to `stableUnits` is false.
-/

namespace GroupApproximation

namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- **Code-pair expansion**: any element is the transport of its compressions along a pair
of complete codes. -/
theorem codePair_expansion {ρ κ : Type*} [Fintype ρ] [Fintype κ]
    (C : AryPrefixCode κ ι) (hC : F.IsComplete C)
    (R : AryPrefixCode ρ ι) (hR : F.IsComplete R) (x : A) :
    x = ∑ j, ∑ i, F.wordS (C.word j) * (F.wordT (C.word j) * x * F.wordS (R.word i)) *
      F.wordT (R.word i) := by
  calc x = (∑ j, F.cylinder (C.word j)) * x * (∑ i, F.cylinder (R.word i)) := by
        rw [show (∑ j, F.cylinder (C.word j)) = 1 from hC,
          show (∑ i, F.cylinder (R.word i)) = 1 from hR, one_mul, mul_one]
    _ = ∑ j, ∑ i, F.wordS (C.word j) * (F.wordT (C.word j) * x * F.wordS (R.word i)) *
          F.wordT (R.word i) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp only [cylinder, mul_assoc]

end CompleteMatrixFamily

namespace AryLeavitt

open CompleteMatrixFamily MatrixDiagonalization

variable (k : Type) [Field k] (d : ℕ)

/-- **The free exit**: once the column code has `d^{r+1}` words over a row code with `d^r`
words, reshaping to exact-depth codes puts the value in `[-2, 0]`. -/
theorem pencil_free_exit (hd : 2 ≤ d) (r : ℕ)
    {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]
    (hρ : Fintype.card ρ = d ^ r) (hκ : Fintype.card κ = d ^ (r + 1))
    (R : AryPrefixCode ρ (Fin d)) (hR : (family k d).IsComplete R)
    (C : AryPrefixCode κ (Fin d)) (hC : (family k d).IsComplete C)
    (Ac Bc : ρ → κ → Fin d → k) (Cm : ρ → κ → k) (u : (AryLeavittAlgebra k d)ˣ)
    (hu : (u : AryLeavittAlgebra k d) = ∑ i, ∑ j, (family k d).wordS (R.word i) *
      (family k d).pencilEntry (Ac i j) (Bc i j) (Cm i j) * (family k d).wordT (C.word j)) :
    u ∈ centralClassGroup (AryLeavittAlgebra k d) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  have hdiv : ∀ x : AryLeavittAlgebra k d, x ≠ 0 →
      ∃ p q : AryLeavittAlgebra k d, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k d hd hx
  obtain ⟨P, hP, hPd⟩ := (family k d).exists_exact_depth_code r
    (κT := ρ) (by rw [hρ, Fintype.card_fin])
  obtain ⟨Q, hQ, hQd⟩ := (family k d).exists_exact_depth_code (r + 1)
    (κT := κ) (by rw [hκ, Fintype.card_fin])
  obtain ⟨v, hv, hiff⟩ := (family k d).exists_reshaped_pencil (k := k) hdiv R P hR hP C Q hC hQ
    (fun i j ↦ (family k d).pencilEntry (Ac i j) (Bc i j) (Cm i j)) u hu
  refine hiff.mpr (window_nonpos_mem_centralClassGroup k d hd 1 v ?_)
  rw [hv]
  refine (family k d).pencilVal_window_mem (a := -1) (b := 1) P.word Q.word _
    (fun i j ↦ (family k d).pencilEntry_mem_window _ _ _) ?_ ?_
  · intro i j
    have h1 := hPd i
    have h2 := hQd j
    omega
  · intro i j
    have h1 := hPd i
    have h2 := hQd j
    omega

/-- **The full-stack exit**: a scalar left inverse of the `s`-coefficient stack pins the
inverse entries strictly negative, and reshaping the inverse makes its value nonpositive. -/
theorem pencil_full_exit (hd : 2 ≤ d) (r s : ℕ) (hs : s ≤ d ^ r)
    {ρ κ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]
    (hρ : Fintype.card ρ = d ^ r) (hκ : Fintype.card κ = d ^ r + s * (d - 1))
    (R : AryPrefixCode ρ (Fin d)) (hR : (family k d).IsComplete R)
    (C : AryPrefixCode κ (Fin d)) (hC : (family k d).IsComplete C)
    (Ac Bc : ρ → κ → Fin d → k) (Cm : ρ → κ → k) (u : (AryLeavittAlgebra k d)ˣ)
    (hu : (u : AryLeavittAlgebra k d) = ∑ i, ∑ j, (family k d).wordS (R.word i) *
      (family k d).pencilEntry (Ac i j) (Bc i j) (Cm i j) * (family k d).wordT (C.word j))
    (G : Fin d → κ → ρ → k)
    (hG : ∀ j j' : κ, (∑ z, ∑ i, G z j i * Bc i j' z) = if j = j' then 1 else 0) :
    u ∈ centralClassGroup (AryLeavittAlgebra k d) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  have hdiv : ∀ x : AryLeavittAlgebra k d, x ≠ 0 →
      ∃ p q : AryLeavittAlgebra k d, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k d hd hx
  obtain ⟨N, hX⟩ := entry_window_negative_of_B_full k d hd R C hC Ac Bc Cm u hu G hG
  have hexp := (family k d).codePair_expansion C hC R hR
    ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d)
  obtain ⟨Q, hQ, hQd⟩ := (family k d).exists_depth_code (M := r) (s := s)
    (by rw [Fintype.card_fin]; exact hs) (κT := κ) (by rw [hκ, Fintype.card_fin])
  obtain ⟨P, hP, hPd⟩ := (family k d).exists_exact_depth_code r
    (κT := ρ) (by rw [hρ, Fintype.card_fin])
  obtain ⟨v, hv, hiff⟩ := (family k d).exists_reshaped_pencil (k := k) hdiv C Q hC hQ R P hR hP
    (fun j i ↦ (family k d).wordT (C.word j) *
      ((u⁻¹ : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) *
      (family k d).wordS (R.word i)) u⁻¹ hexp
  refine inv_mem_iff.mp (hiff.mpr (window_nonpos_mem_centralClassGroup k d hd N v ?_))
  rw [hv]
  refine (family k d).pencilVal_window_mem (a := -(N : ℤ)) (b := -1) Q.word P.word _
    (fun j i ↦ hX j i) ?_ ?_
  · intro j i
    have h1 := (hQd j).1
    have h2 := hPd i
    omega
  · intro j i
    have h1 := (hQd j).2
    have h2 := hPd i
    omega

theorem pow_add_pow_mul_pred (hd : 2 ≤ d) (r : ℕ) : d ^ r + d ^ r * (d - 1) = d ^ (r + 1) := by
  obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [he, Nat.add_sub_cancel, pow_succ]
  ring

/-- **The refine loop**: every pencil unit over a row code with `d^r` words and a column code
with `d^r + (d^r - n)·(d - 1)` words is a central scalar modulo the stably elementary units. -/
theorem pencil_unit_mem (hd : 2 ≤ d) (r : ℕ) :
    ∀ n : ℕ, ∀ {κ : Type} [Fintype κ] [DecidableEq κ],
    n ≤ d ^ r → Fintype.card κ = d ^ r + (d ^ r - n) * (d - 1) →
    ∀ {ρ : Type} [Fintype ρ] [DecidableEq ρ], Fintype.card ρ = d ^ r →
    ∀ (R : AryPrefixCode ρ (Fin d)), (family k d).IsComplete R →
    ∀ (C : AryPrefixCode κ (Fin d)), (family k d).IsComplete C →
    ∀ (Ac Bc : ρ → κ → Fin d → k) (Cm : ρ → κ → k) (u : (AryLeavittAlgebra k d)ˣ),
    (u : AryLeavittAlgebra k d) = ∑ i, ∑ j, (family k d).wordS (R.word i) *
      (family k d).pencilEntry (Ac i j) (Bc i j) (Cm i j) * (family k d).wordT (C.word j) →
    u ∈ centralClassGroup (AryLeavittAlgebra k d) := by
  intro n
  induction n with
  | zero =>
      intro κ _ _ _ hκ ρ _ _ hρ R hR C hC Ac Bc Cm u hu
      refine pencil_free_exit k d hd r hρ ?_ R hR C hC Ac Bc Cm u hu
      rw [hκ, Nat.sub_zero, pow_add_pow_mul_pred d hd r]
  | succ m ih =>
      intro κ _ _ hm hκ ρ _ _ hρ R hR C hC Ac Bc Cm u hu
      classical
      haveI : NeZero d := ⟨by omega⟩
      haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
      have hdiv : ∀ x : AryLeavittAlgebra k d, x ≠ 0 →
          ∃ p q : AryLeavittAlgebra k d, p * x * q = 1 :=
        fun x hx ↦ exists_mul_mul_eq_one k d hd hx
      rcases stack_left_inverse_or_kernel_ary (fun z i j ↦ Bc i j z) with ⟨G, hG⟩ | ⟨v, hv, hkB⟩
      · exact pencil_full_exit k d hd r (d ^ r - (m + 1)) (by omega) hρ hκ R hR C hC
          Ac Bc Cm u hu G hG
      · set L : CompleteMatrixFamily (AryLeavittAlgebra k d) (Fin d) := family k d
        have hkv : ∀ z i, ∑ j, Bc i j z * v j = 0 := hkB
        obtain ⟨j₀, -⟩ := Function.ne_iff.mp hv
        obtain ⟨G, hGu, hGcol⟩ := exists_isUnit_matrix_col hv j₀
        have hGent : ∀ l, G l j₀ = v l := by
          intro l
          have h := congrFun hGcol l
          simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply] at h
          exact h
        obtain ⟨Gm, hGm⟩ := id hGu
        set uG : (AryLeavittAlgebra k d)ˣ :=
          ⟨L.codeScalar (k := k) C G,
           L.codeScalar (k := k) C ((Gm⁻¹ : (Matrix κ κ k)ˣ) : Matrix κ κ k),
           by rw [L.codeScalar_mul, ← hGm, Units.mul_inv, L.codeScalar_one C hC],
           by rw [L.codeScalar_mul, ← hGm, Units.inv_mul, L.codeScalar_one C hC]⟩
        have huGmem : uG ∈ centralClassGroup (AryLeavittAlgebra k d) :=
          L.codeScalar_unit_mem hdiv C hC G uG rfl
        set u1 : (AryLeavittAlgebra k d)ˣ := u * uG
        have hu1 : (u1 : AryLeavittAlgebra k d) =
            ∑ i, ∑ j, L.wordS (R.word i) *
              L.pencilEntry (fun r ↦ ∑ l, Ac i l r * G l j) (fun r ↦ ∑ l, Bc i l r * G l j)
                (∑ l, Cm i l * G l j) * L.wordT (C.word j) := by
          rw [Units.val_mul, hu]
          exact L.pencilVal_mul_codeScalar R C Ac Bc Cm G
        have hBfree : ∀ i, (fun r ↦ ∑ l, Bc i l r * G l j₀) = fun _ ↦ (0 : k) := by
          intro i
          funext r
          simp only [hGent]
          exact hkv r i
        have hrc := L.refine_column R C (fun i j r ↦ ∑ l, Ac i l r * G l j)
          (fun i j r ↦ ∑ l, Bc i l r * G l j) (fun i j ↦ ∑ l, Cm i l * G l j) j₀ hBfree
        have hu1' : (u1 : AryLeavittAlgebra k d) =
            ∑ i, ∑ p : Fin d ⊕ {j : κ // j ≠ j₀}, L.wordS (R.word i) *
              L.pencilEntry
                (Sum.elim (fun _ _ ↦ (0 : k)) (fun q r ↦ ∑ l, Ac i l r * G l q.1) p)
                (Sum.elim (fun z w ↦ if w = z then ∑ l, Cm i l * G l j₀ else 0)
                  (fun q r ↦ ∑ l, Bc i l r * G l q.1) p)
                (Sum.elim (fun z ↦ ∑ l, Ac i l z * G l j₀) (fun q ↦ ∑ l, Cm i l * G l q.1) p) *
              L.wordT ((C.split j₀).word p) := by
          rw [hu1, hrc]
          refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun p _ ↦ ?_
          rcases p with z | q <;> rfl
        have hcard : Fintype.card (Fin d ⊕ {j : κ // j ≠ j₀}) = Fintype.card κ + (d - 1) := by
          rw [Fintype.card_sum, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
            Fintype.card_fin]
          have : 1 ≤ Fintype.card κ := Fintype.card_pos_iff.mpr ⟨j₀⟩
          omega
        have hX : d ^ r - m = (d ^ r - (m + 1)) + 1 := by omega
        have hmem1 : u1 ∈ centralClassGroup (AryLeavittAlgebra k d) := by
          refine ih (κ := Fin d ⊕ {j : κ // j ≠ j₀}) (by omega) ?_ hρ R hR (C.split j₀)
            (L.split_isComplete C hC j₀) _ _ _ u1 hu1'
          rw [hcard, hκ, hX, add_mul, one_mul]
          omega
        have hueq : u = u1 * uG⁻¹ := by
          show u = u * uG * uG⁻¹
          group
        rw [hueq]
        exact mul_mem hmem1 (inv_mem huGmem)

/-- **The narrow reduction holds at every arity**: every unit of `L_k(1,d)` with value in
the window `[-1, 1]` is a central scalar modulo the stably elementary units. -/
theorem narrowReduction_holds (hd : 2 ≤ d) : NarrowReduction k d := by
  intro u hu
  obtain ⟨m, Ac, Bc, Cm, hval⟩ := (family k d).exists_pencil_form hu
  have hcard : Fintype.card (Fin m → Fin d) = d ^ m := by simp
  exact pencil_unit_mem k d hd m (d ^ m) le_rfl
    (by rw [hcard, Nat.sub_self, zero_mul, add_zero]) hcard
    (fullCode m) ((family k d).fullCode_isComplete m)
    (fullCode m) ((family k d).fullCode_isComplete m) Ac Bc Cm u hval

/-- **`ScalarReduction (L_k(1,d))` holds at every arity.** -/
theorem scalarReduction_holds (hd : 2 ≤ d) : ScalarReduction (AryLeavittAlgebra k d) :=
  scalarReduction_of_narrowReduction k d hd (narrowReduction_holds k d hd)

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.codePair_expansion
#audit_axioms GroupApproximation.AryLeavitt.pencil_free_exit
#audit_axioms GroupApproximation.AryLeavitt.pencil_full_exit
#audit_axioms GroupApproximation.AryLeavitt.pencil_unit_mem
#audit_axioms GroupApproximation.AryLeavitt.narrowReduction_holds
#audit_axioms GroupApproximation.AryLeavitt.scalarReduction_holds
