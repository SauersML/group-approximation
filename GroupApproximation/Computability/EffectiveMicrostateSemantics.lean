import GroupApproximation.Computability.CodedMicrostate
import GroupApproximation.Computability.EffectiveMatrixCode

/-!
# Semantics of executable matrix microstates

This file connects the Gaussian-rational matrix evaluator to the analytic
microstates used in the MF normal form.  A finite list of exactly unitary
matrix codes gives a genuine microstate, and evaluating a raw word with
`EffectiveMatrixCode.wordMatrix` agrees exactly with the free-group
homomorphism of that microstate.
-/

namespace GroupApproximation
namespace EffectiveMicrostateSemantics

open PresentationCodes RawWord
open EffectiveMatrixCode
open MFMicrostate
open scoped Matrix

/-- Every generator named by the presentation code evaluates to an exactly
unitary coded matrix.  Missing list entries are the coded identity. -/
def GeneratorsUnitary (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) : Prop :=
  ∀ i : Fin (genCount c), isUnitary d (generator d gens i)

instance generatorsUnitaryDecidable (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) : Decidable (GeneratorsUnitary c d gens) := by
  unfold GeneratorsUnitary
  infer_instance

/-- The complex matrix represented by one signed raw letter. -/
def matrixLetter (c : PresentationCode) (d : ℕ) (gens : List MatrixCode)
    (p : ℕ × Bool) : Matrix (Fin (dim d)) (Fin (dim d)) ℂ :=
  let A := toMatrix d (generator d gens (p.1 % genCount c))
  if p.2 then A else Aᴴ

theorem toMatrix_letterMatrix (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) (p : ℕ × Bool) :
    toMatrix d (letterMatrix d c.1 gens p) = matrixLetter c d gens p := by
  obtain ⟨i, s⟩ := p
  cases s <;> simp [letterMatrix, matrixLetter, genCount]

/-- Interpreting a coded matrix fold is multiplying the interpreted matrices.
The accumulator form avoids any syntactic associativity claim about list
codes themselves. -/
theorem toMatrix_foldl_matrixMul (d : ℕ) (a : MatrixCode) :
    ∀ l : List MatrixCode,
      toMatrix d (l.foldl (matrixMul d) a) =
        toMatrix d a * (l.map (toMatrix d)).prod
  | [] => by simp
  | b :: l => by
      rw [List.foldl_cons, toMatrix_foldl_matrixMul]
      simp only [toMatrix_mul, List.map_cons, List.prod_cons]
      rw [mul_assoc]

/-- Exact semantics of the executable word evaluator. -/
theorem toMatrix_wordMatrix (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) (w : List (ℕ × Bool)) :
    toMatrix d (wordMatrix d c.1 gens w) =
      (w.map (matrixLetter c d gens)).prod := by
  rw [wordMatrix, toMatrix_foldl_matrixMul, toMatrix_identity, one_mul]
  congr 1
  simp only [List.map_map, Function.comp_apply, toMatrix_letterMatrix]

/-- Turn exactly unitary executable generator data into a genuine analytic
microstate on the represented natural basis. -/
noncomputable def toMicrostate (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) (hunitary : GeneratorsUnitary c d gens) :
    Microstate c where
  model := Fin (dim d)
  card_pos := by simp [dim]
  gen := fun i =>
    ⟨toMatrix d (generator d gens i),
      (isUnitary_iff d (generator d gens i)).1 (hunitary i)⟩

@[simp] theorem toMicrostate_gen_coe (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) (hunitary : GeneratorsUnitary c d gens)
    (i : Fin (genCount c)) :
    (((toMicrostate c d gens hunitary).gen i :
        Matrix.unitaryGroup (Fin (dim d)) ℂ) :
      Matrix (Fin (dim d)) (Fin (dim d)) ℂ) =
        toMatrix d (generator d gens i) := rfl

/-- The microstate's free-group evaluation agrees with the product of the
interpreted signed letters. -/
theorem toMicrostate_hom_wordOf (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) (hunitary : GeneratorsUnitary c d gens) :
    ∀ w : List (ℕ × Bool),
      (((toMicrostate c d gens hunitary).hom (wordOf c w) :
          Matrix.unitaryGroup (Fin (dim d)) ℂ) :
        Matrix (Fin (dim d)) (Fin (dim d)) ℂ) =
          (w.map (matrixLetter c d gens)).prod
  | [] => by
      simp [Microstate.hom]
  | (i, false) :: w => by
      rw [wordOf_cons_neg, map_mul, map_inv, toMicrostate_hom_wordOf]
      simp [Microstate.hom, toMicrostate, matrixLetter, letterOf]
  | (i, true) :: w => by
      rw [wordOf_cons_pos, map_mul, toMicrostate_hom_wordOf]
      simp [Microstate.hom, toMicrostate, matrixLetter, letterOf]

/-- Executable word evaluation is exactly the matrix underlying the analytic
microstate evaluation. -/
theorem toMicrostate_hom_wordOf_eq_wordMatrix (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) (hunitary : GeneratorsUnitary c d gens)
    (w : List (ℕ × Bool)) :
    (((toMicrostate c d gens hunitary).hom (wordOf c w) :
        Matrix.unitaryGroup (Fin (dim d)) ℂ) :
      Matrix (Fin (dim d)) (Fin (dim d)) ℂ) =
        toMatrix d (wordMatrix d c.1 gens w) := by
  rw [toMicrostate_hom_wordOf, toMatrix_wordMatrix]

/-- The analytic displacement is the norm of the executable word matrix minus
the identity. -/
theorem toMicrostate_len (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) (hunitary : GeneratorsUnitary c d gens)
    (w : List (ℕ × Bool)) :
    (toMicrostate c d gens hunitary).len w =
      ‖toMatrix d (wordMatrix d c.1 gens w) - 1‖ := by
  rw [Microstate.len_def, opLength, toMicrostate_hom_wordOf_eq_wordMatrix]

/-- The same displacement through the executable subtraction operation. -/
theorem toMicrostate_len_eq_matrixSub (c : PresentationCode) (d : ℕ)
    (gens : List MatrixCode) (hunitary : GeneratorsUnitary c d gens)
    (w : List (ℕ × Bool)) :
    (toMicrostate c d gens hunitary).len w =
      ‖toMatrix d (matrixSub d (wordMatrix d c.1 gens w) (identity d))‖ := by
  rw [toMicrostate_len, toMatrix_sub, toMatrix_identity]

end EffectiveMicrostateSemantics
end GroupApproximation
