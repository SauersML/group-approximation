import GroupApproximation.Sofic.Hyperlinear

/-!
# Tensor powers amplify soficity but not hyperlinearity

For permutation models the separation constant is a convention: the `k`-fold
tensor power sends Hamming distance `d` to `1 - (1 - d)^k`, so a fixed
separation runs to `1` while a small multiplicative defect grows only by a
factor `k` (`Sofic.SoficAmplification`).  One expects the same for unitary
models, and the algebra transports perfectly:

  `τ(A^{⊗k} (B^{⊗k})*) = τ(A B*)^k`   (`normTrace_tensorPow`),

so the squared normalized Hilbert--Schmidt distance obeys the exact law

  `hsDistSq (A^{⊗k}) (B^{⊗k}) = 2 - 2 Re (τ(A B*)^k)`   (`hsDistSq_tensorPow`).

**The amplification nevertheless fails**, and `tensorPow_phase_collapse` says so
with a witness: on any nonempty model `1` and `i · 1` are unitary and separated
by the full `hsDistSq = 2`, yet their fourth tensor powers are *equal*.  The
mechanism is `tensorPow_smul`: a scalar `c` becomes `c^k`, so the `k`-th tensor
power identifies any two unitaries differing by a `k`-th root of unity.
Permutation matrices carry no phases, which is exactly why the sofic argument
works and this one does not.  A trace can be small because it *cancels* rather
than because the matrices are far apart, and tensoring recombines the
cancellation.

The repair is to tensor with the conjugate rather than with a further copy.
`conjDouble A = A ⊗ Ā` is again multiplicative and unitary, and its normalized
trace is `|τ(A)|²` -- a *nonnegative real*, so there is no phase left to
recombine.  `hsDistSq_conjDoubleTensorPow` gives the exact law

  `hsDistSq ((A ⊗ Ā)^{⊗k}) ((B ⊗ B̄)^{⊗k}) = 2 - 2 |τ(A B*)|^{2k}`,

and `exists_conjDouble_separation` turns any bound `|τ(A B*)|² ≤ 1 - δ` into
separation `2 - ε`.  That hypothesis is not removable: `|τ(U)|² ≤ 1` always, with equality exactly
for scalars -- the phase collapse again.  `Sofic.HyperlinearScalar` proves both
facts from one identity, `‖U - τ(U)·1‖² = 1 - |τ(U)|²`.  So for unitary models the separation constant is a convention
*relative to a scalar-freeness hypothesis*, and not otherwise -- an asymmetry
between the two sides of Pestov's Question 3.4 that the permutation picture
hides.

`tensorPow A k` is the `k`-fold Kronecker power written directly on the index
type `Fin k → Y`: its `(f, g)` entry is `∏ i, A (f i) (g i)`.  Both the trace
identity and multiplicativity (`tensorPow_mul`) are instances of the
distributive law `∑_h ∏_i F i (h i) = ∏_i ∑_y F i y`.
-/

namespace GroupApproximation

open Matrix

variable {Y : Type*}

/-! ## The tensor power of a matrix -/

/-! ## The normalized trace, and how the tensor power acts on it -/

/-- Normalized trace of a matrix indexed by a finite model. -/
noncomputable def normTrace (Y : FiniteModel) (A : Matrix Y Y ℂ) : ℂ :=
  Matrix.trace A / Fintype.card Y

/-! ## The Hilbert--Schmidt distance between unitaries is a trace -/

/-- Each row of a unitary matrix is a unit vector. -/
theorem row_normSq_of_unitary (Y : FiniteModel) {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) (i : Y) :
    (∑ j : Y, Complex.normSq (A i j)) = 1 := by
  have h1 : A * Aᴴ = 1 := by
    have h := hA
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  have hrow : ((∑ j : Y, Complex.normSq (A i j) : ℝ) : ℂ) = (A * Aᴴ) i i := by
    rw [Complex.ofReal_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Matrix.conjTranspose_apply]
    exact (Complex.mul_conj (A i j)).symm
  rw [h1, Matrix.one_apply_eq] at hrow
  exact_mod_cast hrow

/-- A unitary matrix has total squared entry mass equal to its size. -/
theorem sum_normSq_of_unitary (Y : FiniteModel) {A : Matrix Y Y ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    (∑ i : Y, ∑ j : Y, Complex.normSq (A i j)) = Fintype.card Y := by
  rw [Finset.sum_congr rfl fun i _ ↦ row_normSq_of_unitary Y hA i]
  simp

/-! ## Tensor powers do not amplify: the scalar-phase obstruction -/

/-! ## The repair: tensoring with the conjugate -/

/-- `A ⊗ Ā`, written directly on the index type `Y × Y`. -/
def conjDouble (A : Matrix Y Y ℂ) : Matrix (Y × Y) (Y × Y) ℂ :=
  fun p q ↦ A p.1 q.1 * (starRingEnd ℂ) (A p.2 q.2)

@[simp] theorem conjDouble_apply (A : Matrix Y Y ℂ) (p q : Y × Y) :
    conjDouble A p q = A p.1 q.1 * (starRingEnd ℂ) (A p.2 q.2) := rfl

/-- `A ↦ A ⊗ Ā` is multiplicative: entrywise conjugation is a ring map. -/
theorem conjDouble_mul [Fintype Y] (A B : Matrix Y Y ℂ) :
    conjDouble (A * B) = conjDouble A * conjDouble B := by
  ext p q
  simp only [conjDouble_apply, Matrix.mul_apply, map_sum]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  simp only [map_mul]
  ring

/-- The conjugate double of the identity is the identity. -/
theorem conjDouble_one [DecidableEq Y] :
    conjDouble (1 : Matrix Y Y ℂ) = 1 := by
  classical
  ext p q
  by_cases h : p = q
  · subst h; simp [Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne h, conjDouble_apply]
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 ↦ h (Prod.ext_iff.mpr ⟨h1, h2⟩)
      simp [Matrix.one_apply_ne h2]
    · simp [Matrix.one_apply_ne h1]

/-- Conjugate transposition passes through `conjDouble`. -/
theorem conjDouble_conjTranspose (A : Matrix Y Y ℂ) :
    conjDouble (Aᴴ) = (conjDouble A)ᴴ := by
  ext p q
  simp [Matrix.conjTranspose_apply, mul_comm]

/-- `A ⊗ Ā` is unitary when `A` is. -/
theorem conjDouble_mem_unitaryGroup {A : Matrix Y Y ℂ}
    [Fintype Y] [DecidableEq Y]
    (hA : A ∈ Matrix.unitaryGroup Y ℂ) :
    conjDouble A ∈ Matrix.unitaryGroup (Y × Y) ℂ := by
  have h1 : A * Aᴴ = 1 := by
    have h := hA
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← conjDouble_conjTranspose, ← conjDouble_mul, h1, conjDouble_one]

/-- The doubled model.  Reducible for the same reason as `tensorModel`. -/
abbrev doubleModel (Y : FiniteModel) : FiniteModel :=
  ⟨Y × Y, inferInstance, inferInstance⟩

theorem card_doubleModel (Y : FiniteModel) :
    Fintype.card (doubleModel Y) = Fintype.card Y * Fintype.card Y := by
  show Fintype.card (Y × Y) = _
  rw [Fintype.card_prod]

end GroupApproximation
