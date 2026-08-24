import GroupApproximation.Computability.RationalComplexCode
import GroupApproximation.Analysis.OperatorNormCertificate

/-!
# Executable finite matrices over Gaussian rational codes

Matrices and vectors are stored as flat lists.  A natural `d` denotes the
nonempty dimension `d+1`; missing list entries read as zero.  All operations
below are therefore total functions on primitive-recursive data.
-/

namespace GroupApproximation
namespace EffectiveMatrixCode

open RationalComplexCode
open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-- A row-major matrix code. -/
abbrev MatrixCode := List (List ComplexCode)

/-- A flat vector code. -/
abbrev VectorCode := List ComplexCode

/-- The represented dimension is always nonempty. -/
def dim (d : ℕ) : ℕ := d + 1

def entry (_d : ℕ) (A : MatrixCode) (i j : ℕ) : ComplexCode :=
  (A.getD i []).getD j complexZero

def vectorEntry (v : VectorCode) (i : ℕ) : ComplexCode :=
  v.getD i complexZero

def complexSub (z w : ComplexCode) : ComplexCode := complexAdd z (complexNeg w)

def complexNormSq (z : ComplexCode) : RatCode :=
  ratAdd (ratMul z.1 z.1) (ratMul z.2 z.2)

def complexSum (l : List ComplexCode) : ComplexCode :=
  l.foldl complexAdd complexZero

def matrixEntryMul (d : ℕ) (A B : MatrixCode) (i j : ℕ) : ComplexCode :=
  complexSum ((List.range (dim d)).map fun k =>
    complexMul (entry d A i k) (entry d B k j))

def matrixMul (d : ℕ) (A B : MatrixCode) : MatrixCode :=
  List.ofFn fun i : Fin (dim d) =>
    List.ofFn fun j : Fin (dim d) => matrixEntryMul d A B i j

def identity (d : ℕ) : MatrixCode :=
  List.ofFn fun i : Fin (dim d) =>
    List.ofFn fun j : Fin (dim d) => if i = j then complexOne else complexZero

def conjTranspose (d : ℕ) (A : MatrixCode) : MatrixCode :=
  List.ofFn fun i : Fin (dim d) =>
    List.ofFn fun j : Fin (dim d) => complexConj (entry d A j i)

def matrixSub (d : ℕ) (A B : MatrixCode) : MatrixCode :=
  List.ofFn fun i : Fin (dim d) =>
    List.ofFn fun j : Fin (dim d) => complexSub (entry d A i j) (entry d B i j)

def matrixEq (d : ℕ) (A B : MatrixCode) : Prop :=
  ∀ i < dim d, ∀ j < dim d, ComplexEq (entry d A i j) (entry d B i j)

instance matrixEqDecidable (d : ℕ) : DecidableRel (matrixEq d) := fun A B => by
  unfold matrixEq
  infer_instance

def isUnitary (d : ℕ) (A : MatrixCode) : Prop :=
  matrixEq d (matrixMul d (conjTranspose d A) A) (identity d)

instance isUnitaryDecidable (d : ℕ) (A : MatrixCode) : Decidable (isUnitary d A) := by
  unfold isUnitary
  infer_instance

def generator (d : ℕ) (gens : List MatrixCode) (i : ℕ) : MatrixCode :=
  gens.getD i (identity d)

def letterMatrix (d rank : ℕ) (gens : List MatrixCode) (p : ℕ × Bool) : MatrixCode :=
  let A := generator d gens (p.1 % (rank + 1))
  if p.2 then A else conjTranspose d A

def wordMatrix (d rank : ℕ) (gens : List MatrixCode)
    (w : List (ℕ × Bool)) : MatrixCode :=
  (w.map (letterMatrix d rank gens)).foldl (matrixMul d) (identity d)

def mulVecEntry (d : ℕ) (A : MatrixCode) (v : VectorCode) (i : ℕ) : ComplexCode :=
  complexSum ((List.range (dim d)).map fun j =>
    complexMul (entry d A i j) (vectorEntry v j))

def vectorNormSq (d : ℕ) (v : VectorCode) : RatCode :=
  (List.range (dim d)).foldl
    (fun q i => ratAdd q (complexNormSq (vectorEntry v i))) ratZero

def mulVecNormSq (d : ℕ) (A : MatrixCode) (v : VectorCode) : RatCode :=
  (List.range (dim d)).foldl
    (fun q i => ratAdd q (complexNormSq (mulVecEntry d A v i))) ratZero

/-- Exact unitarity for every supplied generator. -/
def generatorsUnitary (d : ℕ) (gens : List MatrixCode) : Prop :=
  ∀ A ∈ gens, isUnitary d A

instance generatorsUnitaryDecidable (d : ℕ) (gens : List MatrixCode) :
    Decidable (generatorsUnitary d gens) := by
  unfold generatorsUnitary
  infer_instance

def ratOfNat (n : ℕ) : RatCode := ((n, 0), 0)

@[simp] theorem toRat_ratOfNat (n : ℕ) : toRat (ratOfNat n) = n := by
  simp [ratOfNat, toRat, numeratorPos, numeratorNeg, denominator]

/-- Entrywise strict relator test.  The dimensional factor is chosen so that
passing implies the desired operator-norm bound. -/
def entrySmall (d k : ℕ) (z : ComplexCode) : Prop :=
  RatLt
    (ratMul (ratOfNat ((k + 1) ^ 2 * (dim d) ^ 4)) (complexNormSq z))
    ratOne

instance entrySmallDecidable (d k : ℕ) (z : ComplexCode) :
    Decidable (entrySmall d k z) := by
  unfold entrySmall
  infer_instance

def matrixSmall (d k : ℕ) (A : MatrixCode) : Prop :=
  ∀ i < dim d, ∀ j < dim d, entrySmall d k (entry d A i j)

instance matrixSmallDecidable (d k : ℕ) (A : MatrixCode) :
    Decidable (matrixSmall d k A) := by
  unfold matrixSmall
  infer_instance

/-- A rational vector witnesses `‖A‖ > 1/3`: its squared displacement is
strictly more than one ninth of its squared norm. -/
def vectorWitness (d : ℕ) (A : MatrixCode) (v : VectorCode) : Prop :=
  RatLt (vectorNormSq d v) (ratMul (ratOfNat 9) (mulVecNormSq d A v))

instance vectorWitnessDecidable (d : ℕ) (A : MatrixCode) (v : VectorCode) :
    Decidable (vectorWitness d A v) := by
  unfold vectorWitness
  infer_instance

/-! ## Semantics -/

def toMatrix (d : ℕ) (A : MatrixCode) : Matrix (Fin (dim d)) (Fin (dim d)) ℂ :=
  fun i j => toComplex (entry d A i j)

def toVector (d : ℕ) (v : VectorCode) : Fin (dim d) → ℂ :=
  fun i => toComplex (vectorEntry v i)

@[simp] theorem entry_ofFn (d : ℕ)
    (f : Fin (dim d) → Fin (dim d) → ComplexCode) (i j : Fin (dim d)) :
    entry d (List.ofFn fun a => List.ofFn fun b => f a b) i j = f i j := by
  simp [entry, List.getD_eq_getElem?_getD, i.isLt, j.isLt]

@[simp] theorem toComplex_complexSub (z w : ComplexCode) :
    toComplex (complexSub z w) = toComplex z - toComplex w := by
  simp [complexSub, sub_eq_add_neg]

@[simp] theorem toRat_complexNormSq (z : ComplexCode) :
    (toRat (complexNormSq z) : ℝ) = ‖toComplex z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [complexNormSq, Complex.normSq_apply, toComplex]

theorem toComplex_foldl (a : ComplexCode) : ∀ l : List ComplexCode,
    toComplex (l.foldl complexAdd a) = toComplex a + (l.map toComplex).sum
  | [] => by simp
  | z :: l => by
      rw [List.foldl_cons, toComplex_foldl]
      simp
      ring

@[simp] theorem toComplex_complexSum (l : List ComplexCode) :
    toComplex (complexSum l) = (l.map toComplex).sum := by
  rw [complexSum, toComplex_foldl, toComplex_zero, zero_add]

theorem entry_matrixMul (d : ℕ) (A B : MatrixCode) (i j : Fin (dim d)) :
    toComplex (entry d (matrixMul d A B) i j) =
      ∑ k : Fin (dim d), toComplex (entry d A i k) * toComplex (entry d B k j) := by
  simp only [matrixMul, entry_ofFn, matrixEntryMul, toComplex_complexSum,
    List.map_map]
  rw [← List.sum_toFinset _ List.nodup_range]
  rw [List.toFinset_range, Finset.sum_range]
  simp [Function.comp_apply]

@[simp] theorem toMatrix_mul (d : ℕ) (A B : MatrixCode) :
    toMatrix d (matrixMul d A B) = toMatrix d A * toMatrix d B := by
  ext i j
  exact entry_matrixMul d A B i j

@[simp] theorem toMatrix_identity (d : ℕ) :
    toMatrix d (identity d) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [toMatrix, identity, entry]
  · simp [toMatrix, identity, entry, h]

@[simp] theorem toMatrix_conjTranspose (d : ℕ) (A : MatrixCode) :
    toMatrix d (conjTranspose d A) = (toMatrix d A)ᴴ := by
  ext i j
  simp [toMatrix, conjTranspose, entry, Matrix.conjTranspose_apply]

@[simp] theorem toMatrix_sub (d : ℕ) (A B : MatrixCode) :
    toMatrix d (matrixSub d A B) = toMatrix d A - toMatrix d B := by
  ext i j
  simp [toMatrix, matrixSub, entry]

theorem matrixEq_iff (d : ℕ) (A B : MatrixCode) :
    matrixEq d A B ↔ toMatrix d A = toMatrix d B := by
  constructor
  · intro h
    ext i j
    exact (complexEq_iff _ _).1 (h i i.isLt j j.isLt)
  · intro h i hi j hj
    apply (complexEq_iff _ _).2
    have := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
    exact this

theorem isUnitary_iff (d : ℕ) (A : MatrixCode) :
    isUnitary d A ↔ toMatrix d A ∈ Matrix.unitaryGroup (Fin (dim d)) ℂ := by
  rw [isUnitary, matrixEq_iff, toMatrix_mul, toMatrix_conjTranspose,
    toMatrix_identity]
  exact Matrix.mem_unitaryGroup_iff'.symm

theorem entrySmall_iff (d k : ℕ) (z : ComplexCode) :
    entrySmall d k z ↔
      (((k + 1 : ℕ) : ℝ) ^ 2 * ((dim d : ℕ) : ℝ) ^ 4) * ‖toComplex z‖ ^ 2 < 1 := by
  rw [entrySmall, ratLt_iff, toRat_mul, toRat_ratOfNat, toRat_one]
  constructor <;> intro h
  · have h' :
        (((((k + 1 : ℕ) ^ 2 * (dim d) ^ 4 : ℕ) : ℚ) *
          toRat (complexNormSq z) : ℚ) : ℝ) < 1 := by exact_mod_cast h
    push_cast at h'
    rw [toRat_complexNormSq] at h'
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow] using h'
  · have h' :
        (((((k + 1 : ℕ) ^ 2 * (dim d) ^ 4 : ℕ) : ℚ) *
          toRat (complexNormSq z) : ℚ) : ℝ) < 1 := by
      push_cast
      rw [toRat_complexNormSq]
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_pow] using h
    exact_mod_cast h'

/-- The entrywise arithmetic test implies the requested operator-norm
relator tolerance. -/
theorem opNorm_le_of_matrixSmall (d k : ℕ) (A : MatrixCode)
    (h : matrixSmall d k A) : ‖toMatrix d A‖ ≤ 1 / ((k : ℝ) + 1) := by
  let D : ℝ := dim d
  let K : ℝ := (k : ℝ) + 1
  have hD : 0 < D := by simp only [D, dim, Nat.cast_add, Nat.cast_one]; positivity
  have hK : 0 < K := by positivity
  have hentry : ∀ i j : Fin (dim d), ‖toMatrix d A i j‖ < 1 / (K * D ^ 2) := by
    intro i j
    have hs := (entrySmall_iff d k (entry d A i j)).1 (h i i.isLt j j.isLt)
    have hn : 0 ≤ ‖toComplex (entry d A i j)‖ := norm_nonneg _
    have hden : 0 < K * D ^ 2 := mul_pos hK (sq_pos_of_pos hD)
    have hcastK : (((k + 1 : ℕ) : ℝ) ^ 2) = K ^ 2 := by simp [K]
    have hcastD : (((dim d : ℕ) : ℝ) ^ 4) = D ^ 4 := by rfl
    rw [hcastK, hcastD] at hs
    have hsq : ‖toComplex (entry d A i j)‖ ^ 2 < (1 / (K * D ^ 2)) ^ 2 := by
      field_simp
      nlinarith
    exact (sq_lt_sq₀ hn (by positivity)).1 hsq
  have hop := OperatorNormCertificate.opNorm_le_of_entry_bound
    (toMatrix d A) (show 0 ≤ 1 / (K * D ^ 2) by positivity)
    (fun i j => (hentry i j).le)
  have hcard : ((Fintype.card (Fin (dim d)) : ℕ) : ℝ) = D := by simp [D]
  rw [hcard] at hop
  have hcalc : D ^ 2 * (1 / (K * D ^ 2)) = 1 / K := by
    field_simp
  rw [hcalc] at hop
  simpa [K] using hop

end EffectiveMatrixCode
end GroupApproximation
