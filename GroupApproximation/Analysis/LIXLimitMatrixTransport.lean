import GroupApproximation.Analysis.LIXLimitCompletion
import GroupApproximation.Analysis.CStarMatrixBlockInclusion
import GroupApproximation.Analysis.LIXEndpointStatement

/-!
# Transporting a null-homotopy of `diag (u, 1)` along a ⋆-homomorphism

The LIX witness needs both halves of `K₁`-non-injectivity transported from the base stage into
the inductive limit.  `Analysis/LIXLimitCompletion` does the negative half (`v ∉ U₀(A)`); this
file does the positive half.

`diag (u, 1)` lives in `M₂` of the algebra, so the transport needs `M₂(−)` to be functorial in
unital ⋆-homomorphisms.  Mathlib's `CStarMatrix.map` applies a function entrywise but is not
bundled; `matrixHom n f` bundles it as a unital ⋆-homomorphism `M_n(B) →⋆ₐ[ℂ] M_n(C)`, which is
then automatically continuous (a ⋆-homomorphism of C⋆-algebras is contractive), so
`unitaryHom` and `mapsTo_pathComponentOne` carry a null-homotopy across it.

The block inclusion `M ↦ diag (M, 1)` of `Analysis/CStarMatrixBlockInclusion` commutes with the
entrywise map — `blockOne_map` — which is what turns "`diag(u,1)` contracts over the base" into
"`diag(f u, 1)` contracts over the target".

Everything here is stated for an arbitrary unital ⋆-homomorphism of C⋆-algebras; the LIX
instance is `f := T.limIota 0`.

The order instances are the repository's standing idiom: `CStarMatrix` asks for
`[PartialOrder A] [StarOrderedRing A]`, which carry no information, and the canonical choice is
`CStarAlgebra.spectralOrder`.  A downstream file must open with the same two local instances for
its `diag` to be the same term as this one's.
-/

namespace GroupApproximation

namespace LIX

universe u

noncomputable local instance instSpectralPartialOrder (D : Type u) [CStarAlgebra D] :
    PartialOrder D := CStarAlgebra.spectralOrder D

local instance instSpectralStarOrderedRing (D : Type u) [CStarAlgebra D] :
    StarOrderedRing D := CStarAlgebra.spectralOrderedRing D

noncomputable section

variable {B C : Type u} [CStarAlgebra B] [CStarAlgebra C]

/-! ### `M_n(−)` is functorial in unital ⋆-homomorphisms -/

/-- Entrywise application of a unital ⋆-homomorphism, bundled as a unital ⋆-homomorphism of the
`n × n` matrix algebras. -/
def matrixHom (n : ℕ) (f : B →⋆ₐ[ℂ] C) : CStarMat n B →⋆ₐ[ℂ] CStarMat n C where
  toFun M := M.map f
  map_one' := CStarMatrix.ext fun i j => by
    rw [CStarMatrix.map_apply, CStarMatrix.one_apply, CStarMatrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h, map_one]
    · rw [if_neg h, if_neg h, map_zero]
  map_mul' M N := CStarMatrix.ext fun i j => by
    rw [CStarMatrix.map_apply, CStarMatrix.mul_apply, CStarMatrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, CStarMatrix.map_apply, CStarMatrix.map_apply]
  map_zero' := CStarMatrix.ext fun i j => by
    rw [CStarMatrix.map_apply, CStarMatrix.zero_apply, CStarMatrix.zero_apply, map_zero]
  map_add' M N := CStarMatrix.ext fun i j => by
    rw [CStarMatrix.map_apply, CStarMatrix.add_apply, CStarMatrix.add_apply,
      CStarMatrix.map_apply, CStarMatrix.map_apply, map_add]
  commutes' r := by
    show (algebraMap ℂ (CStarMat n B) r).map f = algebraMap ℂ (CStarMat n C) r
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    refine CStarMatrix.ext fun i j => ?_
    rw [CStarMatrix.map_apply, CStarMatrix.smul_apply, CStarMatrix.smul_apply, map_smul]
    congr 1
    rw [CStarMatrix.one_apply, CStarMatrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h, if_pos h, map_one]
    · rw [if_neg h, if_neg h, map_zero]
  map_star' M := CStarMatrix.ext fun i j => by
    rw [CStarMatrix.map_apply, CStarMatrix.star_apply, CStarMatrix.star_apply,
      CStarMatrix.map_apply, map_star]

@[simp] theorem matrixHom_apply (n : ℕ) (f : B →⋆ₐ[ℂ] C) (M : CStarMat n B) :
    matrixHom n f M = M.map f := rfl

@[simp] theorem matrixHom_apply_entry (n : ℕ) (f : B →⋆ₐ[ℂ] C) (M : CStarMat n B)
    (i j : Fin n) : matrixHom n f M i j = f (M i j) := rfl

/-! ### The block inclusion commutes with the entrywise map -/

theorem blockOne_map {n : ℕ} (m : ℕ) (f : B →⋆ₐ[ℂ] C) (M : CStarMat n B) :
    (blockOne M m).map f = blockOne (M.map f) m := by
  refine CStarMatrix.ext fun i j => ?_
  rw [CStarMatrix.map_apply, blockOne_apply, blockOne_apply]
  by_cases hi : (i : ℕ) < n
  · rw [dif_pos hi, dif_pos hi]
    by_cases hj : (j : ℕ) < n
    · rw [dif_pos hj, dif_pos hj, CStarMatrix.map_apply]
    · rw [dif_neg hj, dif_neg hj, map_zero]
  · rw [dif_neg hi, dif_neg hi]
    by_cases hj : (j : ℕ) < n
    · rw [if_pos hj, if_pos hj, map_zero]
    · rw [if_neg hj, if_neg hj]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij, map_one]
      · rw [if_neg hij, if_neg hij, map_zero]

theorem unitaryHom_matrixHom_blockOneUnitary {n m : ℕ} (h : n ≤ m) (f : B →⋆ₐ[ℂ] C)
    (v : unitary (CStarMat n B)) :
    unitaryHom (matrixHom m f) (blockOneUnitary h v)
      = blockOneUnitary h (unitaryHom (matrixHom n f) v) :=
  Subtype.ext (blockOne_map m f (v : CStarMat n B))

/-! ### Transport of `U₀` -/

/-- A null-homotopy in `M_n(B)` transports to one in `M_n(C)` along any unital
⋆-homomorphism `f : B →⋆ₐ[ℂ] C`. -/
theorem matrixHom_mem_unitaryComponentOne (n : ℕ) (f : B →⋆ₐ[ℂ] C)
    {v : unitary (CStarMat n B)} (hv : v ∈ unitaryComponentOne (CStarMat n B)) :
    unitaryHom (matrixHom n f) v ∈ unitaryComponentOne (CStarMat n C) :=
  unitaryHom_mem_unitaryComponentOne (matrixHom n f) hv

/-- The block inclusion of the image of a null-homotopic matrix unitary is null-homotopic. -/
theorem blockOneUnitary_map_mem_unitaryComponentOne {n m : ℕ} (h : n ≤ m) (f : B →⋆ₐ[ℂ] C)
    {v : unitary (CStarMat n B)} (hv : blockOneUnitary h v ∈ unitaryComponentOne (CStarMat m B)) :
    blockOneUnitary h (unitaryHom (matrixHom n f) v) ∈ unitaryComponentOne (CStarMat m C) := by
  rw [← unitaryHom_matrixHom_blockOneUnitary h f v]
  exact matrixHom_mem_unitaryComponentOne m f hv

/-! ### `diag (u, 1)` -/

/-- The block sum `diag (u, 1)` commutes with the entrywise map: this is `blockOne_map` at
`n = 1`, `m = 2`, read through the `1 × 1` identification. -/
theorem matrixHom_diagOne (f : B →⋆ₐ[ℂ] C) (u : unitary B) :
    unitaryHom (matrixHom 2 f) (diagOne u) = diagOne (unitaryHom f u) := by
  refine Subtype.ext (CStarMatrix.ext fun i j => ?_)
  show f (((diagOne u : unitary (CStarMat 2 B)) : CStarMat 2 B) i j)
      = ((diagOne (unitaryHom f u) : unitary (CStarMat 2 C)) : CStarMat 2 C) i j
  rw [coe_diagOne_apply, coe_diagOne_apply, coe_unitaryHom]
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi, if_pos hi]
    by_cases hj : (j : ℕ) = 0
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, map_zero]
  · rw [if_neg hi, if_neg hi]
    by_cases hj : (j : ℕ) = 0
    · rw [if_pos hj, if_pos hj, map_zero]
    · rw [if_neg hj, if_neg hj, map_one]

/-- **The positive half of the LIX witness, transported.**  If `diag (u, 1)` is null-homotopic
in `M₂(B)` then so is `diag (f u, 1)` in `M₂(C)`, for any unital ⋆-homomorphism `f`. -/
theorem diagOne_mem_unitaryComponentOne_map (f : B →⋆ₐ[ℂ] C) {u : unitary B}
    (hu : diagOne u ∈ unitaryComponentOne (CStarMat 2 B)) :
    diagOne (unitaryHom f u) ∈ unitaryComponentOne (CStarMat 2 C) := by
  rw [← matrixHom_diagOne f u]
  exact matrixHom_mem_unitaryComponentOne 2 f hu

end

/-! ### The witness in the inductive limit -/

namespace CStarTower

noncomputable section

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] (T : CStarTower A)

/-- **The LIX witness, assembled in the limit.**  A unitary `u` of the stage `A k` which

* is null-homotopic in no later stage, and
* has `diag (u, 1)` null-homotopic already in `M₂(A k)`

produces a unitary `v` of the inductive limit with `v ∉ U₀` and `diag (v, 1) ∈ U₀(M₂)` — exactly
the hypothesis of `not_k1Inj_of_witness`. -/
theorem exists_unitary_witness {k : ℕ} (u : unitary (A k))
    (hstage : ∀ (j : ℕ) (hj : k ≤ j),
      unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (A j))
    (hdiag : diagOne u ∈ unitaryComponentOne (CStarMat 2 (A k))) :
    ∃ v : unitary T.Limit, v ∉ unitaryComponentOne T.Limit ∧
      diagOne v ∈ unitaryComponentOne (CStarMat 2 T.Limit) :=
  ⟨unitaryHom (T.limIota k) u, T.notMem_unitaryComponentOne_limit hstage,
    diagOne_mem_unitaryComponentOne_map (T.limIota k) hdiag⟩

end

end CStarTower

end LIX

end GroupApproximation
