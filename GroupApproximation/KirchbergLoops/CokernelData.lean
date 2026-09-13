import GroupApproximation.KirchbergLoops.InvariantMatrix
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Integer data of the K-theory of `C*(E(1,1,2))` and `C*(E(1,2))`

For a graph with adjacency matrix `M`, `K₀ = coker(1 - Mᵀ)` and `K₁ = ker(1 - Mᵀ)` on `ℤⁿ`. That is
standard graph-algebra K-theory, and it is not formalized here. This file proves the integer facts
the STW Problem L artifact (`research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md`) feeds into
it.

* `graphMatrix_C`, `graphMatrix_B`: `M(1,1,2)` and `M(1,2)` are the printed adjacency matrices.
* `one_sub_transpose_graphMatrix`: `1 - M(u)ᵀ = -u 1ᵀ`.
* `one_sub_transpose_graphMatrix_mulVec`: the image of `1 - M(u)ᵀ` is `ℤu`.
* `det_cokernelBasis`: `(1,1,2), (1,1,1), (1,0,0)` is a `ℤ`-basis of `ℤ³`.
* `two_mul_sub_eq_zero_iff`, `two_mul_sub_surjective`: `(x, y) ↦ 2x - y` maps `ℤ²` onto `ℤ` with
  kernel `ℤ(1,2)`.
* `det_kernelMinor`: the kernel columns (18) have a `4 × 4` minor of determinant `1`.
-/

namespace GroupApproximation
namespace KirchbergLoops

open Matrix

/-- The adjacency matrix `M(u)_{ij} = δ_{ij} + u_j` of `E(u)`. -/
def graphMatrix {n : ℕ} (u : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℤ := 1 + of fun _ j => u j

theorem graphMatrix_C : graphMatrix ![1, 1, 2] = !![2, 1, 2; 1, 2, 2; 1, 1, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem graphMatrix_B : graphMatrix ![1, 2] = !![2, 2; 1, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **`1 - M(u)ᵀ = -u 1ᵀ`.** -/
theorem one_sub_transpose_graphMatrix {n : ℕ} (u : Fin n → ℤ) :
    1 - (graphMatrix u)ᵀ = of fun i _ => -u i := by
  rw [graphMatrix, transpose_add, transpose_one]
  ext i j
  show (1 : Matrix (Fin n) (Fin n) ℤ) i j - ((1 : Matrix (Fin n) (Fin n) ℤ) i j + u i) = -u i
  abel

/-- **The image of `1 - M(u)ᵀ` is `ℤu`.** -/
theorem one_sub_transpose_graphMatrix_mulVec {n : ℕ} (u v : Fin n → ℤ) :
    (1 - (graphMatrix u)ᵀ) *ᵥ v = (-∑ j, v j) • u := by
  rw [one_sub_transpose_graphMatrix]
  ext i
  show ∑ j, -u i * v j = -(∑ j, v j) * u i
  rw [← Finset.mul_sum]
  ring

/-- **`(1,1,2), (1,1,1), (1,0,0)` is a `ℤ`-basis of `ℤ³`.** The first column spans the image of
`1 - M(1,1,2)ᵀ`, so the classes of `(1,1,1)` and `(1,0,0)` form a basis of the cokernel. -/
theorem det_cokernelBasis : (!![1, 1, 1; 1, 1, 0; 2, 1, 0] : Matrix (Fin 3) (Fin 3) ℤ).det = -1 := by
  rw [det_fin_three]
  rfl

/-- **The kernel of `(x, y) ↦ 2x - y` is `ℤ(1,2)`**, the image of `1 - M(1,2)ᵀ`. -/
theorem two_mul_sub_eq_zero_iff (x y : ℤ) : 2 * x - y = 0 ↔ ∃ t : ℤ, x = t ∧ y = 2 * t :=
  ⟨fun h => ⟨x, rfl, by omega⟩, fun ⟨_, hx, hy⟩ => by omega⟩

theorem two_mul_sub_surjective (t : ℤ) : ∃ x y : ℤ, 2 * x - y = t :=
  ⟨0, -t, by omega⟩

/-- The rows `(Δx)_β, (Δy)_β, (Δβ)_x, (Δβ)_y` of the kernel minor. -/
def kernelCoord : Fin 2 ⊕ Fin 2 → Coord := Sum.elim ![.inl 1, .inl 3] ![.inr 0, .inr 1]

/-- The columns `κ₁, κ₂, κ₃, κ₄` of the kernel minor. -/
def kernelIndex : Fin 2 ⊕ Fin 2 → Fin 4 := Sum.elim ![0, 1] ![2, 3]

/-- The `4 × 4` minor of the kernel columns (18). -/
def kernelMinor : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  of fun i k => kernelColumn (kernelIndex k) (kernelCoord i)

theorem kernelMinor_eq : kernelMinor = fromBlocks 1 0 0 rotationQuotientBlock := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;> fin_cases i <;> fin_cases k <;> rfl

/-- **The kernel minor has determinant `1`.** -/
theorem det_kernelMinor : kernelMinor.det = 1 := by
  rw [kernelMinor_eq, det_fromBlocks_zero₂₁, det_one, rotationQuotientBlock, det_fin_two_of]
  norm_num

end KirchbergLoops
end GroupApproximation
