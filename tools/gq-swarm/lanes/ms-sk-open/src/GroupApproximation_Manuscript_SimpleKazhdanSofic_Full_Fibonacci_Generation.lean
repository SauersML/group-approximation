import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.Fibonacci.Model
import GroupApproximation.Meta.AxiomGuard

/-!
# The Fibonacci example: `φ(S)` generates `M_5(F₂)`

`simple_kazhdan_sofic_group.tex`, subsection "An example", l.435–439:

> But $P^3D_1(e_1)P^{-3}$ is diagonal with entry $y_{t-3}$ at $t$, so
> $D_1(e_1)\,P^3D_1(e_1)P^{-3}=E_{44}$. Then $P^{t-4}E_{44}P^{4-t}=E_{tt}$
> and $P^{t'-t}E_{tt}=E_{t't}$ give every matrix unit. So $\varphi(S)$
> generates $M_5(\F_2)$ [...]

`P = φ(u)` is the unit `fibP` of `M_5(F₂)` (so `P^j` makes sense for `j ∈ ℤ`, and
`φ(u^j) = P^j`), `E_{t't} = Matrix.single t' t 1`, and `S = {1, u, u⁻¹} ∪ {e_a : a ∈ A}`
(tex l.364) is `fibGenerators`.

Main statements: `fibonacciConjugateE44` (l.435–437), `fibonacciMatrixUnits` (l.437–438),
`fibonacciModelGeneratesMatrixRing` (l.438–439).
-/

namespace GroupApproximation.Full.SK08

open SymbolicDynamics.FullShift

/-- The shift homeomorphism `T` of the Fibonacci subshift. -/
local notation "𝓣" => SimpleKazhdanSofic.subshiftHomeo fibonacciSubshift

/-- The ring `R_X = LC(X, F₂) ⋊_T ℤ` of the Fibonacci subshift. -/
local notation "𝓡" => SimpleKazhdanSofic.R fibonacciSubshift

/-- The matrix ring `M_5(F₂)`, rows and columns indexed by `t ∈ Z/5`. -/
local notation "𝓜" => Matrix (ZMod 5) (ZMod 5) (ZMod 2)

section Units

/-- The permutation matrix `P = φ(u)` as a unit of `M_5(F₂)`, with inverse `P^{-1} = φ(u⁻¹)`. -/
noncomputable def fibP : 𝓜ˣ where
  val := Pestov91.shiftMatrix (ZMod 2) 5 1
  inv := Pestov91.shiftMatrix (ZMod 2) 5 (-1)
  val_inv := by rw [← Pestov91.shiftMatrix_add, add_neg_cancel, Pestov91.shiftMatrix_zero]
  inv_val := by rw [← Pestov91.shiftMatrix_add, neg_add_cancel, Pestov91.shiftMatrix_zero]

theorem fibP_val : ((fibP : 𝓜ˣ) : 𝓜) = Pestov91.shiftMatrix (ZMod 2) 5 1 :=
  rfl

theorem fibP_inv_val : ((fibP⁻¹ : 𝓜ˣ) : 𝓜) = Pestov91.shiftMatrix (ZMod 2) 5 (-1) :=
  rfl

/-- `P^j = shiftMatrix j` for every `j ∈ ℤ`. -/
theorem fibP_zpow (j : ℤ) : ((fibP ^ j : 𝓜ˣ) : 𝓜) = Pestov91.shiftMatrix (ZMod 2) 5 j := by
  induction j using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, Pestov91.shiftMatrix_zero]
  | succ i ih => rw [zpow_add_one, Units.val_mul, ih, fibP_val, ← Pestov91.shiftMatrix_add]
  | pred i ih =>
    rw [zpow_sub_one, Units.val_mul, ih, fibP_inv_val, ← Pestov91.shiftMatrix_add,
      sub_eq_add_neg]

/-- `φ(u^j) = P^j`. -/
theorem fibonacciModel_unit_zpow_eq_fibP (j : ℤ) :
    fibonacciModel ((ClopenCrossedProduct.unit 𝓣 (ZMod 2) ^ j : 𝓡ˣ) : 𝓡) =
      ((fibP ^ j : 𝓜ˣ) : 𝓜) := by
  rw [fibonacciModel_unit_zpow, fibP_zpow]

end Units

section Matrices

/-- Conjugating a diagonal matrix by `P^i` shifts its diagonal: `P^i D(d) P^{-i} = D(d(· - i))`. -/
theorem shiftMatrix_conj_diagonal (i j : ℤ) (hij : i + j = 0) (d : ZMod 5 → ZMod 2) :
    Pestov91.shiftMatrix (ZMod 2) 5 i * Matrix.diagonal d * Pestov91.shiftMatrix (ZMod 2) 5 j =
      Matrix.diagonal fun a => d (a - (i : ZMod 5)) := by
  rw [Pestov91.shiftMatrix_mul_diagonal, mul_assoc, ← Pestov91.shiftMatrix_add, hij,
    Pestov91.shiftMatrix_zero, mul_one]

/-- `P^3 D_1(e_1) P^{-3}` is diagonal with entry `y_{t-3}` at `t`. -/
theorem shiftMatrix_conj_letter :
    Pestov91.shiftMatrix (ZMod 2) 5 3 * fibonacciModel (fibLetter true) *
        Pestov91.shiftMatrix (ZMod 2) 5 (-3) =
      Matrix.diagonal fun t : ZMod 5 =>
        if fibonacciY (((t.val : ℕ) : ℤ) - 3) = true then (1 : ZMod 2) else 0 := by
  rw [fibonacciModel_letter, shiftMatrix_conj_diagonal 3 (-3) (add_neg_cancel 3)]
  refine congrArg Matrix.diagonal ?_
  funext t
  revert t
  decide +kernel

/-- `D_1(e_1) P^3 D_1(e_1) P^{-3} = E_{44}`. -/
theorem letter_mul_shiftMatrix_conj_letter :
    fibonacciModel (fibLetter true) *
        (Pestov91.shiftMatrix (ZMod 2) 5 3 * fibonacciModel (fibLetter true) *
          Pestov91.shiftMatrix (ZMod 2) 5 (-3)) =
      Matrix.single (4 : ZMod 5) (4 : ZMod 5) (1 : ZMod 2) := by
  rw [shiftMatrix_conj_letter, fibonacciModel_letter, Matrix.diagonal_mul_diagonal]
  ext a b
  revert a b
  decide +kernel

/-- `P^{t-4} E_{44} P^{4-t} = E_{tt}`. -/
theorem shiftMatrix_conj_single (t : ZMod 5) :
    Pestov91.shiftMatrix (ZMod 2) 5 (((t.val : ℕ) : ℤ) - 4) *
        Matrix.single (4 : ZMod 5) (4 : ZMod 5) (1 : ZMod 2) *
        Pestov91.shiftMatrix (ZMod 2) 5 (4 - ((t.val : ℕ) : ℤ)) =
      Matrix.single t t (1 : ZMod 2) := by
  have hsum : (((t.val : ℕ) : ℤ) - 4) + (4 - ((t.val : ℕ) : ℤ)) = 0 := by ring
  rw [← Matrix.diagonal_single, ← Matrix.diagonal_single, shiftMatrix_conj_diagonal _ _ hsum]
  refine congrArg Matrix.diagonal ?_
  funext a
  clear hsum
  revert t a
  decide +kernel

/-- `P^i E_{ts} = E_{t+i, s}`. -/
theorem shiftMatrix_mul_single (i : ℤ) (t s : ZMod 5) :
    Pestov91.shiftMatrix (ZMod 2) 5 i * Matrix.single t s (1 : ZMod 2) =
      Matrix.single (t + (i : ZMod 5)) s (1 : ZMod 2) := by
  ext a b
  by_cases hb : b = s
  · rw [hb, Matrix.mul_single_apply_same, mul_one, Pestov91.shiftMatrix_apply,
      Matrix.single_apply]
    by_cases ha : t + (i : ZMod 5) = a
    · rw [if_pos ha, if_pos (show t + (i : ZMod 5) = a ∧ s = s from ⟨ha, rfl⟩)]
    · rw [if_neg ha, if_neg (show ¬ (t + (i : ZMod 5) = a ∧ s = s) from fun h => ha h.1)]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ hb, Matrix.single_apply,
      if_neg (show ¬ (t + (i : ZMod 5) = a ∧ s = b) from fun h => hb h.2.symm)]

/-- `P^{t'-t} E_{tt} = E_{t't}`. -/
theorem shiftMatrix_mul_single_sub (t' t : ZMod 5) :
    Pestov91.shiftMatrix (ZMod 2) 5 (((t'.val : ℕ) : ℤ) - ((t.val : ℕ) : ℤ)) *
        Matrix.single t t (1 : ZMod 2) =
      Matrix.single t' t (1 : ZMod 2) := by
  have hcast : ∀ s s' : ZMod 5,
      s + ((((s'.val : ℕ) : ℤ) - ((s.val : ℕ) : ℤ) : ℤ) : ZMod 5) = s' := by
    decide +kernel
  rw [shiftMatrix_mul_single, hcast]

end Matrices

/-- **Sentence l.435 (tex l.435–437).** `P = φ(u)` with `φ(u^j) = P^j`; `P^3 D_1(e_1) P^{-3}` is
diagonal with entry `y_{t-3}` at `t`, so `D_1(e_1) P^3 D_1(e_1) P^{-3} = E_{44}`. -/
theorem fibonacciConjugateE44 :
    (∀ j : ℤ, fibonacciModel ((ClopenCrossedProduct.unit 𝓣 (ZMod 2) ^ j : 𝓡ˣ) : 𝓡) =
      ((fibP ^ j : 𝓜ˣ) : 𝓜)) ∧
      ((fibP ^ (3 : ℤ) : 𝓜ˣ) : 𝓜) * fibonacciModel (fibLetter true) *
          ((fibP ^ (-3 : ℤ) : 𝓜ˣ) : 𝓜) =
        Matrix.diagonal (fun t : ZMod 5 =>
          if fibonacciY (((t.val : ℕ) : ℤ) - 3) = true then (1 : ZMod 2) else 0) ∧
      fibonacciModel (fibLetter true) *
          (((fibP ^ (3 : ℤ) : 𝓜ˣ) : 𝓜) * fibonacciModel (fibLetter true) *
            ((fibP ^ (-3 : ℤ) : 𝓜ˣ) : 𝓜)) =
        Matrix.single (4 : ZMod 5) (4 : ZMod 5) (1 : ZMod 2) := by
  refine ⟨fibonacciModel_unit_zpow_eq_fibP, ?_⟩
  rw [fibP_zpow, fibP_zpow]
  exact ⟨shiftMatrix_conj_letter, letter_mul_shiftMatrix_conj_letter⟩

#audit_closed_axioms GroupApproximation.Full.SK08.fibonacciConjugateE44

/-- **Sentence l.437 (tex l.437–438).** `P^{t-4} E_{44} P^{4-t} = E_{tt}` and
`P^{t'-t} E_{tt} = E_{t't}`, for `t, t' = 0, …, 4`. -/
theorem fibonacciMatrixUnits :
    (∀ t : ZMod 5, ((fibP ^ (((t.val : ℕ) : ℤ) - 4) : 𝓜ˣ) : 𝓜) *
        Matrix.single (4 : ZMod 5) (4 : ZMod 5) (1 : ZMod 2) *
        ((fibP ^ (4 - ((t.val : ℕ) : ℤ)) : 𝓜ˣ) : 𝓜) = Matrix.single t t (1 : ZMod 2)) ∧
      ∀ t' t : ZMod 5, ((fibP ^ (((t'.val : ℕ) : ℤ) - ((t.val : ℕ) : ℤ)) : 𝓜ˣ) : 𝓜) *
        Matrix.single t t (1 : ZMod 2) = Matrix.single t' t (1 : ZMod 2) := by
  refine ⟨fun t => ?_, fun t' t => ?_⟩
  · rw [fibP_zpow, fibP_zpow]
    exact shiftMatrix_conj_single t
  · rw [fibP_zpow]
    exact shiftMatrix_mul_single_sub t' t

#audit_closed_axioms GroupApproximation.Full.SK08.fibonacciMatrixUnits

section Generation

/-- The printed generators `S = {1, u, u⁻¹} ∪ {e_a : a ∈ A}` of `R_X` (tex l.364). -/
noncomputable def fibGenerators : Set 𝓡 :=
  insert 1 (SimpleKazhdanSofic.ringGenerators fibonacciSubshift)

theorem fibU_mem_fibGenerators : fibU ∈ fibGenerators :=
  Set.mem_insert_of_mem _ (Or.inl (Or.inl rfl))

theorem fibUInv_mem_fibGenerators : fibUInv ∈ fibGenerators :=
  Set.mem_insert_of_mem _ (Or.inl (Or.inr rfl))

theorem fibLetter_mem_fibGenerators (a : Bool) : fibLetter a ∈ fibGenerators :=
  Set.mem_insert_of_mem _ (Or.inr ⟨a, rfl⟩)

theorem zmodTwo_eq_zero_or_one : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by
  decide +kernel

/-- A subring of `M_5(F₂)` containing `P`, `P^{-1}` and `D_1(e_1)` contains every matrix unit. -/
theorem single_mem_of_mem (M : Subring 𝓜) (hP : Pestov91.shiftMatrix (ZMod 2) 5 1 ∈ M)
    (hPinv : Pestov91.shiftMatrix (ZMod 2) 5 (-1) ∈ M)
    (hD : fibonacciModel (fibLetter true) ∈ M) (t' t : ZMod 5) :
    Matrix.single t' t (1 : ZMod 2) ∈ M := by
  have hPj : ∀ j : ℤ, Pestov91.shiftMatrix (ZMod 2) 5 j ∈ M := by
    intro j
    induction j using Int.induction_on with
    | zero =>
      rw [Pestov91.shiftMatrix_zero]
      exact M.one_mem
    | succ i ih =>
      rw [Pestov91.shiftMatrix_add]
      exact M.mul_mem ih hP
    | pred i ih =>
      rw [sub_eq_add_neg, Pestov91.shiftMatrix_add]
      exact M.mul_mem ih hPinv
  have h44 : Matrix.single (4 : ZMod 5) (4 : ZMod 5) (1 : ZMod 2) ∈ M := by
    rw [← letter_mul_shiftMatrix_conj_letter]
    exact M.mul_mem hD (M.mul_mem (M.mul_mem (hPj 3) hD) (hPj (-3)))
  have htt : Matrix.single t t (1 : ZMod 2) ∈ M := by
    rw [← shiftMatrix_conj_single t]
    exact M.mul_mem (M.mul_mem (hPj _) h44) (hPj _)
  rw [← shiftMatrix_mul_single_sub t' t]
  exact M.mul_mem (hPj _) htt

/-- **Sentence l.438 (tex l.438–439).** `φ(S)` generates `M_5(F₂)` as a ring. -/
theorem fibonacciModelGeneratesMatrixRing :
    Subring.closure (fibonacciModel '' fibGenerators) = ⊤ := by
  have hP : Pestov91.shiftMatrix (ZMod 2) 5 1 ∈
      Subring.closure (fibonacciModel '' fibGenerators) :=
    Subring.subset_closure ⟨fibU, fibU_mem_fibGenerators, fibonacciModel_unit⟩
  have hPinv : Pestov91.shiftMatrix (ZMod 2) 5 (-1) ∈
      Subring.closure (fibonacciModel '' fibGenerators) :=
    Subring.subset_closure ⟨fibUInv, fibUInv_mem_fibGenerators, fibonacciModel_unit_inv⟩
  have hD : fibonacciModel (fibLetter true) ∈
      Subring.closure (fibonacciModel '' fibGenerators) :=
    Subring.subset_closure ⟨fibLetter true, fibLetter_mem_fibGenerators true, rfl⟩
  refine (Subring.eq_top_iff' _).mpr fun A => ?_
  rw [Matrix.matrix_eq_sum_single A]
  refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
  rcases zmodTwo_eq_zero_or_one (A i j) with h | h
  · rw [h, Matrix.single_zero]
    exact Subring.zero_mem _
  · rw [h]
    exact single_mem_of_mem _ hP hPinv hD i j

#audit_closed_axioms GroupApproximation.Full.SK08.fibonacciModelGeneratesMatrixRing

end Generation

end GroupApproximation.Full.SK08
