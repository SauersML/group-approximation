import GroupApproximation.Manuscript.SimpleKazhdanSofic.CylinderTables
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Multiplying out a word in the elementary generators

`simple_kazhdan_sofic_group.tex`, section "Word problems", first paragraph of the proof:

> Multiplying out a word in the generators in `LC(A^ℤ, F₂) ⋊ ℤ`, which maps onto `R`, gives a matrix
> with entries `∑_j f_j u^j`, each `f_j` given by a table on the words of some length, ...

A generator letter is an off-diagonal position `(i, j)` with a coefficient table `s`, standing for the
elementary matrix `I + s E_ij`.  Multiplying out a word gives a `3 × 3` matrix of tables, and
evaluation of tables is multiplicative:

* `matEval_matMul`, `matEval_matOne`: evaluation of matrices of tables is multiplicative;
* `matEval_elemMat`: the letter `(i, j, s)` evaluates to the elementary unit `x_ij(eval s)`;
* `matEval_wordMat`: multiplying out a word evaluates to the product of its elementary matrices.
-/

namespace GroupApproximation
namespace CylinderTables

open SymbolicDynamics.FullShift
open Multiplicative (ofAdd toAdd)

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] {X : Set (ℤ → A)}

/-- A `3 × 3` matrix of tables. -/
abbrev Mat (A : Type*) : Type _ := Fin 3 → Fin 3 → Table A

/-- Entrywise evaluation of a matrix of tables. -/
noncomputable def matEval (T : ↥X ≃ₜ ↥X) (M : Mat A) :
    Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T (ZMod 2)) :=
  Matrix.of fun i j => eval T (M i j)

theorem matEval_apply (T : ↥X ≃ₜ ↥X) (M : Mat A) (i j : Fin 3) :
    matEval T M i j = eval T (M i j) :=
  rfl

/-- The product of matrices of tables. -/
def matMul (M N : Mat A) (i j : Fin 3) : Table A :=
  tableMul (M i 0) (N 0 j) ++ tableMul (M i 1) (N 1 j) ++ tableMul (M i 2) (N 2 j)

theorem matEval_matMul [DecidableEq A] (T : ↥X ≃ₜ ↥X) (hT : ∀ x : ↥X, (T x).1 = shift 1 x.1)
    (M N : Mat A) : matEval T (matMul M N) = matEval T M * matEval T N := by
  refine Matrix.ext fun i j ↦ ?_
  simp only [matEval_apply, Matrix.mul_apply, Fin.sum_univ_three, matMul, eval_append,
    eval_tableMul T hT]

theorem eval_nil (T : ↥X ≃ₜ ↥X) : eval T ([] : Table A) = 0 :=
  rfl

theorem cylInd_nil : cylInd X ([] : Cyl A) = 1 :=
  LocallyConstant.ext fun x =>
    (LocallyConstant.charFn_eq_one (Y := ZMod 2) x (isClopen_cyl X [])).2 fun _ hp => nomatch hp

omit [DiscreteTopology A] in
theorem single_one_one (T : ↥X ≃ₜ ↥X) :
    (SkewMonoidAlgebra.single 1 1 : ClopenCrossedProduct T (ZMod 2)) = 1 :=
  SkewMonoidAlgebra.ext fun a => by
    rw [SkewMonoidAlgebra.coeff_single, SkewMonoidAlgebra.coeff_one]

/-- The table of `1`. -/
theorem eval_unitTable (T : ↥X ≃ₜ ↥X) : eval T ([(0, [])] : Table A) = 1 := by
  rw [eval_cons, eval_nil, add_zero]
  show SkewMonoidAlgebra.single (ofAdd (0 : ℤ)) (ClopenCoeff.of T (ZMod 2) (cylInd X [])) = 1
  rw [cylInd_nil, map_one, ofAdd_zero, single_one_one]

/-- The identity matrix of tables. -/
def matOne (i j : Fin 3) : Table A :=
  if i = j then [(0, [])] else []

theorem matEval_matOne (T : ↥X ≃ₜ ↥X) : matEval T (matOne : Mat A) = 1 := by
  refine Matrix.ext fun i j ↦ ?_
  rw [matEval_apply, matOne, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, eval_unitTable]
  · rw [if_neg h, if_neg h, eval_nil]

/-- The elementary matrix `I + s E_ij` of tables. -/
def elemMat (i j : Fin 3) (s : Table A) (p q : Fin 3) : Table A :=
  if p = q then [(0, [])] else if p = i ∧ q = j then s else []

theorem val_elementaryUnit {R : Type*} [Ring R] {i j : Fin 3} (h : i ≠ j) (a : R) :
    ((elementaryUnit i j h a : (Matrix (Fin 3) (Fin 3) R)ˣ) : Matrix (Fin 3) (Fin 3) R) =
      1 + Matrix.single i j a :=
  rfl

omit [DiscreteTopology A] in
/-- The entries of `1 + a E_ij`. -/
theorem one_add_single_apply {R : Type*} [Ring R] (i j p q : Fin 3) (a : R) :
    (1 + Matrix.single i j a : Matrix (Fin 3) (Fin 3) R) p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then a else 0) :=
  rfl

/-- **The letter `(i, j, s)` evaluates to `x_ij(eval s)`.** -/
theorem matEval_elemMat (T : ↥X ≃ₜ ↥X) {i j : Fin 3} (h : i ≠ j) (s : Table A) :
    matEval T (elemMat i j s) =
      ((elementaryUnit i j h (eval T s) : (Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T (ZMod 2)))ˣ) :
        Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T (ZMod 2))) := by
  rw [val_elementaryUnit]
  refine Matrix.ext fun p q => Eq.trans ?_ (one_add_single_apply i j p q (eval T s)).symm
  rw [matEval_apply, elemMat]
  by_cases hpq : p = q
  · rw [if_pos hpq, if_pos hpq, eval_unitTable,
      if_neg fun e : i = p ∧ j = q => h (e.1.trans (hpq.trans e.2.symm)), add_zero]
  · rw [if_neg hpq, if_neg hpq, zero_add]
    by_cases hij : p = i ∧ q = j
    · rw [if_pos hij, if_pos (⟨hij.1.symm, hij.2.symm⟩ : i = p ∧ j = q)]
    · rw [if_neg hij, eval_nil, if_neg fun e : i = p ∧ j = q => hij ⟨e.1.symm, e.2.symm⟩]

/-- Multiplying out a word of letters `(i, j, s)`. -/
def wordMat : List ((Fin 3 × Fin 3) × Table A) → Mat A
  | [] => matOne
  | g :: w => matMul (elemMat g.1.1 g.1.2 g.2) (wordMat w)

/-- **Multiplying out a word evaluates to the product of its elementary matrices.** -/
theorem matEval_wordMat [DecidableEq A] (T : ↥X ≃ₜ ↥X) (hT : ∀ x : ↥X, (T x).1 = shift 1 x.1)
    (w : List ((Fin 3 × Fin 3) × Table A)) (hw : ∀ g ∈ w, g.1.1 ≠ g.1.2) :
    matEval T (wordMat w) =
      (w.map fun g => (1 + Matrix.single g.1.1 g.1.2 (eval T g.2) :
        Matrix (Fin 3) (Fin 3) (ClopenCrossedProduct T (ZMod 2)))).prod := by
  induction w with
  | nil => rw [wordMat, matEval_matOne, List.map_nil, List.prod_nil]
  | cons g w ih =>
    rw [wordMat, matEval_matMul T hT, matEval_elemMat T (hw g (List.mem_cons.2 (Or.inl rfl))),
      val_elementaryUnit, ih fun g' hg' => hw g' (List.mem_cons.2 (Or.inr hg')), List.map_cons,
      List.prod_cons]

end CylinderTables
end GroupApproximation

#audit_axioms GroupApproximation.CylinderTables.matEval_matMul
#audit_axioms GroupApproximation.CylinderTables.matEval_elemMat
#audit_axioms GroupApproximation.CylinderTables.matEval_wordMat
