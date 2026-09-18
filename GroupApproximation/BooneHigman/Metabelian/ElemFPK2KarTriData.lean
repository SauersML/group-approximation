import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarTriCol
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarTriClose
import GroupApproximation.Meta.AxiomGuard

/-!
# A root times a rank-one datum is again a rank-one datum (two cases)

Lane `bh-met-93k`, data module.  Let `(y₂, α, ρ)` be a rank-one datum (`ElemFPK2KarTriClose`)
with `ρ ⬝ᵥ α = 0`, over a commutative ring with no zero divisors.

* `k2KarTri_rowCase`: if `α` is supported on `{i}`, then `(x_ij(b) y₂, e_i(1), b e_j + α_i ρ)`
  is a rank-one datum.  Both commutators are rewritten as `⁅x_{i,N}(1), padRow _⁆`.
* `k2KarTri_colCase`: if `ρ` is supported on `{j}`, then `(x_ij(b) y₂, ρ_j α + e_i(b), e_j(1))`
  is a rank-one datum.  Both commutators are rewritten as `⁅padCol _, x_{N,j}(1)⁆`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped Matrix commutatorElement

section KarTriDataRing

variable {R : Type*} [Ring R] {n : ℕ}

/-- `stab x_ij(b) = ⁅padCol e_i(b), padRow e_j(1)⁆`. -/
theorem k2KarTri_stab_x (i j : Fin n) (hij : i ≠ j) (b : R) :
    stab n R (x i j hij b) = ⁅padCol (Pi.single i b), padRow (Pi.single j (1 : R))⁆ := by
  have e := k2KarInd_stab_conj_x (1 : St n R) i j hij b
  rwa [inv_one, mul_one, one_mul, map_one (padMat (R := R) (n := n)), Matrix.one_mulVec,
    Matrix.vecMul_one] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_stab_x

/-- `padMat x_ij(b) = 1 + e_i(b) e_j(1)ᵀ`. -/
theorem k2KarTri_padMat_x (i j : Fin n) (hij : i ≠ j) (b : R) :
    padMat (x i j hij b) = 1 + Matrix.vecMulVec (Pi.single i b) (Pi.single j (1 : R)) := by
  have e := k2KarTri_padMat_conj (1 : St n R) i j hij b
  rwa [inv_one, mul_one, one_mul, map_one (padMat (R := R) (n := n)), Matrix.one_mulVec,
    Matrix.vecMul_one] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_padMat_x

/-- `(1 + V Wᵀ)(1 + V' W'ᵀ) = 1 + V Wᵀ + V' W'ᵀ` when `(W ⬝ᵥ V') W' = 0`. -/
theorem k2KarTri_rankOne_mul {V W V' W' : Fin n → R} (h : (W ⬝ᵥ V') • W' = 0) :
    (1 + Matrix.vecMulVec V W) * (1 + Matrix.vecMulVec V' W') =
      1 + (Matrix.vecMulVec V W + Matrix.vecMulVec V' W') := by
  simp only [mul_add, add_mul, mul_one, one_mul]
  rw [Matrix.vecMulVec_mul_vecMulVec, h, Matrix.vecMulVec_zero, add_zero]
  abel

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_rankOne_mul

end KarTriDataRing

section KarTriDataComm

variable {R : Type*} [CommRing R] {n : ℕ}

theorem k2KarTri_rowSum (i j : Fin n) (b a : R) {α ρ : Fin n → R} (hαe : α = Pi.single i a) :
    Matrix.vecMulVec (Pi.single i b) (Pi.single j (1 : R)) + Matrix.vecMulVec α ρ =
      Matrix.vecMulVec (Pi.single i (1 : R)) (b • Pi.single j (1 : R) + a • ρ) := by
  rw [hαe, Matrix.vecMulVec_add, Matrix.vecMulVec_smul, Matrix.vecMulVec_smul,
    ← Matrix.smul_vecMulVec, ← Matrix.smul_vecMulVec, k2KarTri_smul_single, k2KarTri_smul_single]
  simp only [mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_rowSum

theorem k2KarTri_colSum (i j : Fin n) (b r : R) {α ρ : Fin n → R} (hρe : ρ = Pi.single j r) :
    Matrix.vecMulVec (Pi.single i b) (Pi.single j (1 : R)) + Matrix.vecMulVec α ρ =
      Matrix.vecMulVec (r • α + Pi.single i b) (Pi.single j (1 : R)) := by
  rw [hρe, Matrix.add_vecMulVec, Matrix.smul_vecMulVec, ← Matrix.vecMulVec_smul,
    k2KarTri_smul_single, mul_one]
  exact add_comm _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_colSum

/-- **Row case**: `α` supported on `{i}`. -/
theorem k2KarTri_rowCase (hR : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) {y₂ : St n R}
    {α ρ : Fin n → R} (hs₂ : stab n R y₂ = ⁅padCol α, padRow ρ⁆)
    (hm₂ : padMat y₂ = 1 + Matrix.vecMulVec α ρ) (hd₂ : ρ ⬝ᵥ α = 0) (i j : Fin n) (hij : i ≠ j)
    (b : R) (hα : ∀ p, p ≠ i → α p = 0) :
    stab n R (x i j hij b * y₂) =
        ⁅padCol (Pi.single i (1 : R)), padRow (b • Pi.single j (1 : R) + α i • ρ)⁆ ∧
      padMat (x i j hij b * y₂) =
        1 + Matrix.vecMulVec (Pi.single i (1 : R)) (b • Pi.single j (1 : R) + α i • ρ) := by
  have hαe : α = Pi.single i (α i) := by
    funext p
    by_cases hp : p = i
    · rw [hp, Pi.single_eq_same]
    · rw [hα p hp, Pi.single_eq_of_ne hp]
  have hd : ρ i * α i = 0 := by
    have e := hd₂
    rw [hαe, dotProduct_single] at e
    exact e
  have hj0 : (Pi.single j (1 : R) : Fin n → R) i = 0 := Pi.single_eq_of_ne hij (1 : R)
  have hρi : (α i • ρ) i = 0 := by rw [Pi.smul_apply, smul_eq_mul, mul_comm, hd]
  have hrow : ⁅x i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne (α i), padRow ρ⁆ =
      ⁅x i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne 1, padRow (α i • ρ)⁆ := by
    rcases hR _ _ hd with h0 | h0
    · exact k2KarTri_row_smul i (α i) h0
    · rw [h0, x_zero, zero_smul, padRow_zero, commutatorElement_one_left,
        commutatorElement_one_right]
  have hx : (Pi.single j (1 : R) ⬝ᵥ α) • ρ = 0 := by
    rw [single_dotProduct, hα j hij.symm, mul_zero, zero_smul]
  rw [hαe] at hs₂
  constructor
  · rw [map_mul (stab n R) (x i j hij b) y₂, k2KarTri_stab_x, hs₂]
    simp only [padCol_single]
    rw [k2KarTri_row_smul i b hj0, hrow,
      ← k2KarTri_row_add i 1 (k2KarTri_smul_apply_eq_zero b hj0) hρi]
  · rw [map_mul padMat (x i j hij b) y₂, k2KarTri_padMat_x, hm₂, k2KarTri_rankOne_mul hx,
      k2KarTri_rowSum i j b (α i) hαe]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_rowCase

/-- **Column case**: `ρ` supported on `{j}`. -/
theorem k2KarTri_colCase (hR : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0) {y₂ : St n R}
    {α ρ : Fin n → R} (hs₂ : stab n R y₂ = ⁅padCol α, padRow ρ⁆)
    (hm₂ : padMat y₂ = 1 + Matrix.vecMulVec α ρ) (hd₂ : ρ ⬝ᵥ α = 0) (i j : Fin n) (hij : i ≠ j)
    (b : R) (hρ : ∀ q, q ≠ j → ρ q = 0) :
    stab n R (x i j hij b * y₂) =
        ⁅padCol (ρ j • α + Pi.single i b), padRow (Pi.single j (1 : R))⁆ ∧
      padMat (x i j hij b * y₂) =
        1 + Matrix.vecMulVec (ρ j • α + Pi.single i b) (Pi.single j (1 : R)) := by
  have hρe : ρ = Pi.single j (ρ j) := by
    funext q
    by_cases hq : q = j
    · rw [hq, Pi.single_eq_same]
    · rw [hρ q hq, Pi.single_eq_of_ne hq]
  have hd : ρ j * α j = 0 := by
    have e := hd₂
    rw [hρe, single_dotProduct] at e
    exact e
  have hi0 : (Pi.single i b : Fin n → R) j = 0 := Pi.single_eq_of_ne hij.symm b
  have hαj : (ρ j • α) j = 0 := by rw [Pi.smul_apply, smul_eq_mul, hd]
  have hcol : ⁅padCol α, x (Fin.last n) j.castSucc (Fin.castSucc_lt_last j).ne' (ρ j)⁆ =
      ⁅padCol (ρ j • α), x (Fin.last n) j.castSucc (Fin.castSucc_lt_last j).ne' 1⁆ := by
    rcases hR _ _ hd with h0 | h0
    · rw [h0, x_zero, zero_smul, padCol_zero, commutatorElement_one_left,
        commutatorElement_one_right]
    · exact k2KarTri_col_smul j (ρ j) h0
  have hx : (Pi.single j (1 : R) ⬝ᵥ α) • ρ = 0 := by
    rw [single_dotProduct, one_mul, hρe, k2KarTri_smul_single, mul_comm, hd, Pi.single_zero]
  rw [hρe] at hs₂
  constructor
  · rw [map_mul (stab n R) (x i j hij b) y₂, k2KarTri_stab_x, hs₂]
    simp only [padRow_single]
    rw [hcol, ← k2KarTri_col_add j 1 hαj hi0]
  · rw [map_mul padMat (x i j hij b) y₂, k2KarTri_padMat_x, hm₂, k2KarTri_rankOne_mul hx,
      k2KarTri_colSum i j b (ρ j) hρe]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_colCase

end KarTriDataComm

end GroupApproximation.BooneHigman.Metabelian.ElemFP
