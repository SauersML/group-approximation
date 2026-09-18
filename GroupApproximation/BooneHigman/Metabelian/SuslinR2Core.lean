import GroupApproximation.BooneHigman.Metabelian.SuslinR2Block
import GroupApproximation.Meta.AxiomGuard

/-!
# Stabilizer step (R2), part 2: normalizing to a coordinate block with value `1` at `X = 0`

Lane `bh-met-90k`.  Proved outright, for every commutative ring `B`:

* `suslinR2_constantCoeff_map`: a coefficient map preserves the normalization `τ(0) = 1`;
* `suslinR2_cc_C`: `(C u)(0) = u` for constant matrices;
* `suslinR2_block_core`: over `B[X]`, if `T(0) = 1`, `F ∈ E_ι(B[X])` and row `r` of `T F` is
  `e_r`, then there is `F' ∈ E_ι(B[X])` with `T F'` in `coordinateBlock (B[X]) r` and
  `(T F')(0) = 1`.

Proof of the core.  Put `M = T F`.  Right multiplication by the transvections `x_{k r}(W k r)`,
`k ≠ r`, where `W = M⁻¹`, clears column `r` (`suslinR2_mul_colFactors_mem`); call the product
`P`.  Then `D₀ = (M P)(0) = T(0) F(0) P(0) = F(0) P(0)` is elementary over `B` and is a
coordinate block at `r`.  Take `F' = F P C(D₀⁻¹)`: `T F' = (M P) C(D₀⁻¹)` is a product of two
coordinate blocks and `(T F')(0) = D₀ D₀⁻¹ = 1`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open RankNElimination

section Core

variable {A B ι : Type*} [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]

/-- A coefficient map preserves the normalization `τ(0) = 1`. -/
theorem suslinR2_constantCoeff_map (f : A →+* B) (τ : (Matrix ι ι (Polynomial A))ˣ)
    (h0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := A)) τ = 1) :
    elementaryMatrixUnitMap (Polynomial.constantCoeff (R := B))
      (elementaryMatrixUnitMap (Polynomial.mapRingHom f) τ) = 1 := by
  have h : elementaryMatrixUnitMap (ι := ι) f
      (elementaryMatrixUnitMap (Polynomial.constantCoeff (R := A)) τ) = 1 := by
    rw [h0, map_one]
  rw [← h]
  apply Units.ext
  ext i j
  change Polynomial.constantCoeff (((τ : Matrix ι ι (Polynomial A)) i j).map f) =
    f (Polynomial.constantCoeff ((τ : Matrix ι ι (Polynomial A)) i j))
  rw [Polynomial.constantCoeff_apply, Polynomial.constantCoeff_apply, Polynomial.coeff_map]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_constantCoeff_map

/-- The constant term of a constant matrix. -/
theorem suslinR2_cc_C (u : (Matrix ι ι B)ˣ) :
    elementaryMatrixUnitMap (Polynomial.constantCoeff (R := B))
      (elementaryMatrixUnitMap (Polynomial.C (R := B)) u) = u := by
  apply Units.ext
  ext i j
  change Polynomial.constantCoeff (Polynomial.C ((u : Matrix ι ι B) i j)) =
    (u : Matrix ι ι B) i j
  rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_cc_C

/-- **Normalization to a coordinate block.**  If `T(0) = 1`, `F ∈ E_ι(B[X])` and row `r` of
`T F` is `e_r`, then some `F' ∈ E_ι(B[X])` makes `T F'` a coordinate block at `r` with
`(T F')(0) = 1`. -/
theorem suslinR2_block_core (T : (Matrix ι ι (Polynomial B))ˣ)
    (hT0 : elementaryMatrixUnitMap (Polynomial.constantCoeff (R := B)) T = 1)
    (F : (Matrix ι ι (Polynomial B))ˣ) (hF : F ∈ elementaryGroup ι (Polynomial B)) (r : ι)
    (hrow : ∀ c : ι,
      ((T * F : (Matrix ι ι (Polynomial B))ˣ) : Matrix ι ι (Polynomial B)) r c =
        if c = r then 1 else 0) :
    ∃ F' ∈ elementaryGroup ι (Polynomial B),
      T * F' ∈ coordinateBlock (Polynomial B) r ∧
        elementaryMatrixUnitMap (Polynomial.constantCoeff (R := B)) (T * F') = 1 := by
  obtain ⟨M, hM⟩ : ∃ M : (Matrix ι ι (Polynomial B))ˣ, T * F = M := ⟨_, rfl⟩
  rw [hM] at hrow
  obtain ⟨P, hPdef⟩ : ∃ P : (Matrix ι ι (Polynomial B))ˣ,
      (leftClearFactors r (fun k ↦ ((M⁻¹ : (Matrix ι ι (Polynomial B))ˣ) :
        Matrix ι ι (Polynomial B)) k r) (otherIndices r)).prod = P := ⟨_, rfl⟩
  have hP : P ∈ elementaryGroup ι (Polynomial B) := by
    rw [← hPdef]
    exact leftClearFactors_prod_mem r _
  have hMP : M * P ∈ coordinateBlock (Polynomial B) r := by
    rw [← hPdef]
    exact suslinR2_mul_colFactors_mem M _ r (Units.mul_inv M) hrow
  obtain ⟨D0, hD0⟩ : ∃ D0 : (Matrix ι ι B)ˣ,
      elementaryMatrixUnitMap (Polynomial.constantCoeff (R := B)) (M * P) = D0 := ⟨_, rfl⟩
  have hD0E : D0 ∈ elementaryGroup ι B := by
    rw [← hD0, ← hM, map_mul, map_mul, hT0, one_mul]
    exact Subgroup.mul_mem _
      (elementaryGroup_map_le (Polynomial.constantCoeff (R := B))
        (Subgroup.mem_map_of_mem _ hF))
      (elementaryGroup_map_le (Polynomial.constantCoeff (R := B))
        (Subgroup.mem_map_of_mem _ hP))
  have hD0B : D0 ∈ coordinateBlock B r := by
    rw [← hD0]
    exact suslinR2_map_mem_coordinateBlock _ hMP
  refine ⟨F * P * elementaryMatrixUnitMap (Polynomial.C (R := B)) D0⁻¹,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hF hP)
      (elementaryGroup_map_le (Polynomial.C (R := B))
        (Subgroup.mem_map_of_mem _ (inv_mem hD0E))), ?_, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, hM]
    exact Subgroup.mul_mem _ hMP (suslinR2_map_mem_coordinateBlock _ (inv_mem hD0B))
  · rw [← mul_assoc, ← mul_assoc, hM, map_mul, hD0, suslinR2_cc_C, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinR2_block_core

end Core

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
