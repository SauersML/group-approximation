import GroupApproximation.KOne.AryPencilCore
import GroupApproximation.Meta.AxiomGuard

/-!
# Pencil entries at arbitrary arity

`KOne/PencilEntryArith.lean` carries the five-coefficient pencil entry of the
binary elimination,

`pE(a₀,a₁,c,b₀,b₁) = a₀·t₀ + a₁·t₁ + c·1 + b₀·s₀ + b₁·s₁`,

the general element of the degree window `[-1, 1]` at one matrix position.  At
arity `d` the same element has `2d + 1` coefficients, so the pair `(a₀, a₁)`
becomes a function `ι → k` and likewise for `(b₀, b₁)`:

`pencilEntry a b c = ∑ᵢ aᵢ·tᵢ + c·1 + ∑ᵢ bᵢ·sᵢ`.

This is the shape change the whole port turns on, and it is confined to this
definition: the arithmetic below is coefficientwise and the proofs are sums
where the binary ones were two-term.

## What the scalar moves become

The binary file states the two scalar moves against `codeScalar` and
`codePair_mul` of `KOne/CodeScalarMoves.lean`, over a prefix code.  None of that
is needed here.  A pencil value at depth `n` is
`(F.powerFamily n).matrixRingEquiv` of its coefficient matrix, and that map is a
ring **isomorphism**, so the two moves are `map_mul` together with the
coefficientwise arithmetic; the prefix-code layer disappears from the port.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

open scoped BigOperators

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

section Entry

variable {k : Type*} [Field k] [Algebra k A]

/-! ### Two arity-blind scalar facts

`LeavittFamily.smul_mul_algebraMap` and `algebraMap_mul_smul` of
`KOne/PencilEntryArith.lean` are the same statements; they are restated here
rather than imported, because that file sits on top of the whole binary
prefix-code chain and this port does not otherwise depend on it. -/

theorem smul_mul_algebraMap' (x : k) (y : A) (μ : k) :
    (x • y) * algebraMap k A μ = (x * μ) • y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc,
    ← Algebra.commutes μ y, ← mul_assoc]

theorem algebraMap_mul_smul' (μ : k) (x : k) (y : A) :
    algebraMap k A μ * (x • y) = (μ * x) • y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]

/-! ### The pencil entry -/

/-- The general element of the degree window `[-1, 1]`, with `2·|ι| + 1`
coefficients: `∑ᵢ aᵢ tᵢ + c + ∑ᵢ bᵢ sᵢ`. -/
noncomputable def pencilEntry (a b : ι → k) (c : k) : A :=
  (∑ i, a i • F.right i) + c • (1 : A) + (∑ i, b i • F.left i)

/-- Right multiplication by a scalar acts on the coefficients. -/
theorem pencilEntry_mul_algebraMap (a b : ι → k) (c μ : k) :
    F.pencilEntry a b c * algebraMap k A μ =
      F.pencilEntry (fun i ↦ a i * μ) (fun i ↦ b i * μ) (c * μ) := by
  unfold pencilEntry
  rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul,
    smul_mul_algebraMap' c 1 μ]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ ↦ smul_mul_algebraMap' (a i) _ μ
  · exact Finset.sum_congr rfl fun i _ ↦ smul_mul_algebraMap' (b i) _ μ

/-- Left multiplication by a scalar acts on the coefficients. -/
theorem algebraMap_mul_pencilEntry (μ : k) (a b : ι → k) (c : k) :
    algebraMap k A μ * F.pencilEntry a b c =
      F.pencilEntry (fun i ↦ μ * a i) (fun i ↦ μ * b i) (μ * c) := by
  unfold pencilEntry
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum,
    algebraMap_mul_smul' μ c 1]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ ↦ algebraMap_mul_smul' μ (a i) _
  · exact Finset.sum_congr rfl fun i _ ↦ algebraMap_mul_smul' μ (b i) _

/-- Sums of pencil entries collect coefficientwise. -/
theorem sum_pencilEntry {γ : Type*} (s : Finset γ) (a b : γ → ι → k)
    (c : γ → k) :
    ∑ l ∈ s, F.pencilEntry (a l) (b l) (c l) =
      F.pencilEntry (fun i ↦ ∑ l ∈ s, a l i) (fun i ↦ ∑ l ∈ s, b l i)
        (∑ l ∈ s, c l) := by
  unfold pencilEntry
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_smul]
  congr 1
  · congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_smul.symm
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_smul.symm

/-! ### The two scalar moves -/

/-- **Right scalar move**: multiplying a depth-`n` pencil value by the embedding
of a scalar matrix multiplies the three coefficient families on the right. -/
theorem pencilVal_mul_matrixEmbedding (n : ℕ)
    (Ac Bc : (Fin n → ι) → (Fin n → ι) → ι → k)
    (Cc : (Fin n → ι) → (Fin n → ι) → k)
    (G : Matrix (Fin n → ι) (Fin n → ι) k) :
    (F.powerFamily n).matrixRingEquiv
          (Matrix.of fun i j ↦ F.pencilEntry (Ac i j) (Bc i j) (Cc i j)) *
        (F.powerFamily n).matrixEmbedding G =
      (F.powerFamily n).matrixRingEquiv
        (Matrix.of fun i j ↦ F.pencilEntry
          (fun r ↦ ∑ l, Ac i l r * G l j) (fun r ↦ ∑ l, Bc i l r * G l j)
          (∑ l, Cc i l * G l j)) := by
  classical
  show _ * (F.powerFamily n).matrixRingEquiv
      ((algebraMap k A).mapMatrix G) = _
  rw [← map_mul]
  congr 1
  ext i j
  rw [Matrix.mul_apply]
  calc ∑ l, F.pencilEntry (Ac i l) (Bc i l) (Cc i l) * algebraMap k A (G l j)
      = ∑ l, F.pencilEntry (fun r ↦ Ac i l r * G l j)
          (fun r ↦ Bc i l r * G l j) (Cc i l * G l j) :=
        Finset.sum_congr rfl fun l _ ↦ F.pencilEntry_mul_algebraMap _ _ _ _
    _ = _ := F.sum_pencilEntry Finset.univ _ _ _

/-- **Left scalar move**: multiplying on the left multiplies the three
coefficient families on the left. -/
theorem matrixEmbedding_mul_pencilVal (n : ℕ)
    (Ac Bc : (Fin n → ι) → (Fin n → ι) → ι → k)
    (Cc : (Fin n → ι) → (Fin n → ι) → k)
    (G : Matrix (Fin n → ι) (Fin n → ι) k) :
    (F.powerFamily n).matrixEmbedding G *
        (F.powerFamily n).matrixRingEquiv
          (Matrix.of fun i j ↦ F.pencilEntry (Ac i j) (Bc i j) (Cc i j)) =
      (F.powerFamily n).matrixRingEquiv
        (Matrix.of fun i j ↦ F.pencilEntry
          (fun r ↦ ∑ l, G i l * Ac l j r) (fun r ↦ ∑ l, G i l * Bc l j r)
          (∑ l, G i l * Cc l j)) := by
  classical
  show (F.powerFamily n).matrixRingEquiv
      ((algebraMap k A).mapMatrix G) * _ = _
  rw [← map_mul]
  congr 1
  ext i j
  rw [Matrix.mul_apply]
  calc ∑ l, algebraMap k A (G i l) * F.pencilEntry (Ac l j) (Bc l j) (Cc l j)
      = ∑ l, F.pencilEntry (fun r ↦ G i l * Ac l j r)
          (fun r ↦ G i l * Bc l j r) (G i l * Cc l j) :=
        Finset.sum_congr rfl fun l _ ↦ F.algebraMap_mul_pencilEntry _ _ _ _
    _ = _ := F.sum_pencilEntry Finset.univ _ _ _

end Entry

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.pencilEntry_mul_algebraMap
#audit_axioms GroupApproximation.CompleteMatrixFamily.algebraMap_mul_pencilEntry
#audit_axioms GroupApproximation.CompleteMatrixFamily.sum_pencilEntry
#audit_axioms
  GroupApproximation.CompleteMatrixFamily.pencilVal_mul_matrixEmbedding
#audit_axioms
  GroupApproximation.CompleteMatrixFamily.matrixEmbedding_mul_pencilVal
